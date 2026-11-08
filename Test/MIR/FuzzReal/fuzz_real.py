"""Differential test of the MIR optimizer on the plutus-core 1.65 CEK machine.

  python3 -I Test/MIR/FuzzReal/fuzz_real.py OUTDIR [--from N] [--count N]
      [--inputs N] [--depth N] [--model-all] [--jobs N] [--semantics E,C]

1. `lake exe fuzz_real` writes the programs, their variants and the Lean
   model's runs (see Test/MIR/FuzzReal/Run.lean);
2. `cross-bench batch` (plinth-plutarch-comparison, branch
   cross-language-bench) evaluates every job on the real machine, sharded over
   several processes, and renders the Lean model's result values;
3. `compare` checks every variant against the unoptimized `base` lowering on
   the real machine (base halts => variant halts with an equal value; base
   fails => variant fails), and the Lean model against the real machine on the
   jobs it ran.

`python3 -I fuzz_real.py OUTDIR --compare-only` re-runs step 3.
"""
import argparse
import collections
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
HARNESS = os.environ.get('CROSS_BENCH', (
    '/Users/sho/fun/plinth-plutarch-comparison/dist-newstyle/build/aarch64-osx/'
    'ghc-9.6.6/plinth-plutarch-paper-code-0.1.0.0/x/cross-bench/opt/build/cross-bench/cross-bench'))


# The budget of every run (Limits in Run.lean): running out is divergence.
CPU_LIMIT = 10000000000
MEM_LIMIT = 100000000


def run_batch(jobs_path, out_path, shards, semantics):
    """Evaluate a job file with `cross-bench batch`, in `shards` processes.

    Program definitions (`P` lines) go to every shard; each argument block (an
    `A` line and the `J` lines after it) and each self-contained job line goes
    to one shard."""
    definitions = []
    blocks = []
    with open(jobs_path) as f:
        for line in f:
            if line.startswith('P\t'):
                definitions.append(line)
            elif line.startswith('A\t') or line.rstrip('\n') == 'A':
                blocks.append([line])
            elif line.startswith('J\t'):
                blocks[-1].append(line)
            elif line.strip():
                blocks.append([line])
    if not blocks:
        open(out_path, 'w').close()
        return
    parts = [blocks[i::shards] for i in range(shards)]

    def one(index):
        part = parts[index]
        if not part:
            return ''
        text = ''.join(definitions) + ''.join(''.join(block) for block in part)
        result = subprocess.run([HARNESS, 'batch', '--semantics', semantics,
                                 '--cpu', str(CPU_LIMIT), '--mem', str(MEM_LIMIT)],
                                input=text, capture_output=True, text=True)
        if result.returncode != 0:
            raise RuntimeError('cross-bench batch failed: ' + result.stderr[-2000:])
        return result.stdout

    with ThreadPoolExecutor(max_workers=shards) as pool:
        outputs = list(pool.map(one, range(shards)))
    with open(out_path, 'w') as f:
        for output in outputs:
            f.write(output)


def load_results(path):
    results = {}
    with open(path) as f:
        for line in f:
            fields = line.rstrip('\n').split('\t')
            if len(fields) < 6:
                fields += [''] * (6 - len(fields))
            job, outcome, cpu, mem, result, traces = fields[:6]
            results[job] = (outcome, int(cpu or 0), int(mem or 0), result, traces)
    return results


def load_model(directory, values_name='model-values.real.tsv', runs_name='model.tsv'):
    model = {}
    if not os.path.exists(os.path.join(directory, runs_name)):
        return model, {}
    with open(os.path.join(directory, runs_name)) as f:
        for line in f:
            fields = line.rstrip('\n').split('\t')
            fields += [''] * (5 - len(fields))
            job, outcome, cpu, mem, traces = fields[:5]
            model[job] = (outcome, int(cpu), int(mem), traces)
    values = {}
    path = os.path.join(directory, values_name)
    if os.path.exists(path):
        for job, (outcome, _, _, result, _) in load_results(path).items():
            values[job] = result if outcome == 'OK' else 'unrenderable(%s:%s)' % (outcome, result)
    return model, values


def decode_traces(field):
    if not field:
        return []
    return [bytes.fromhex(h).decode('utf-8', 'replace') for h in field.split(',')]


def coverage(directory):
    """How often each variant differs from base, and each pipeline stage from the previous one."""
    changed = collections.Counter()
    stage_changed = collections.Counter()
    programs = 0
    for line in open(os.path.join(directory, 'manifest.jsonl')):
        entry = json.loads(line)
        programs += 1
        variants = entry['variants']
        for name, index in variants.items():
            reference = variants['lower'] if name.startswith('alone/') else variants['base']
            if index != reference:
                changed[name] += 1
        stages = sorted(n for n in variants if n.startswith('pipe/'))
        previous = variants['base']
        for name in stages:
            if variants[name] != previous:
                stage_changed[name] += 1
            previous = variants[name]
    return programs, changed, stage_changed


def compare(directory, show=12, results_name='results.tsv', quiet=False,
            values_name='model-values.real.tsv', report_name='report.json', runs_name='model.tsv'):
    real = load_results(os.path.join(directory, results_name))
    model, model_values = load_model(directory, values_name, runs_name)
    findings = collections.defaultdict(list)
    fidelity = collections.defaultdict(list)
    stats = collections.Counter()
    programs = 0
    for line in open(os.path.join(directory, 'manifest.jsonl')):
        entry = json.loads(line)
        programs += 1
        label = entry['label']
        variants = entry['variants']
        for name, index in variants.items():
            if isinstance(index, str):
                findings[('compile-error', name)].append({'label': label, 'detail': index})
        for input_index, row in enumerate(entry['jobs']):
            stats['inputs'] += 1
            base_job = row[variants['base']]
            base = real.get(base_job)
            if base is None:
                stats['missing'] += 1
                continue
            stats['base-' + base[0]] += 1
            for name, index in variants.items():
                if isinstance(index, str) or name == 'base':
                    continue
                stats['comparisons'] += 1
                if index == variants['base']:
                    stats['identical-to-base'] += 1
                    continue
                got = real.get(row[index])
                if got is None:
                    stats['missing'] += 1
                    continue
                record = {'label': label, 'input': input_index, 'job': row[index], 'base': base_job,
                          'expected': base[0] + ' ' + base[3], 'actual': got[0] + ' ' + got[3]}
                if got[0] == 'BAD':
                    findings[('bad-job', name)].append(record)
                elif base[0] == 'OK':
                    if got[0] != 'OK':
                        findings[('halt->' + got[0], name)].append(record)
                    elif got[3] != base[3]:
                        findings[('value', name)].append(record)
                    elif got[4] != base[4]:
                        record['expected'] = decode_traces(base[4])
                        record['actual'] = decode_traces(got[4])
                        findings[('trace(halting)', name)].append(record)
                elif base[0] == 'FAIL':
                    if got[0] != 'FAIL':
                        findings[('error->' + got[0], name)].append(record)
                    elif got[4] != base[4]:
                        stats['trace-diff-on-error'] += 1
                else:
                    stats['base-diverges-skipped'] += 1
            # Lean model against the real machine, on every job the model ran
            for index, job in enumerate(row):
                if job not in model:
                    continue
                stats['model-comparisons'] += 1
                m = model[job]
                r = real.get(job)
                if r is None:
                    continue
                record = {'label': label, 'input': input_index, 'job': job,
                          'term': index, 'real': r[0] + ' ' + r[3], 'model': m[0]}
                if m[0] != r[0]:
                    fidelity[('outcome', m[0] + '/real-' + r[0])].append(record)
                    continue
                if m[0] == 'OK':
                    value = model_values.get(job, 'missing')
                    record['model'] = 'OK ' + value
                    if value != r[3]:
                        fidelity[('value', '')].append(record)
                    if m[3] != r[4]:
                        record['model-traces'] = decode_traces(m[3])
                        record['real-traces'] = decode_traces(r[4])
                        fidelity[('trace', '')].append(record)
    report = {'programs': programs, 'stats': dict(stats),
              'findings': {'%s %s' % k: v for k, v in findings.items()},
              'fidelity': {'%s %s' % k: v for k, v in fidelity.items()}}
    if quiet:
        return report
    with open(os.path.join(directory, report_name), 'w') as f:
        json.dump(report, f, indent=1)
    print('programs %d, inputs %d, variant comparisons %d (%d with a term identical to base), '
          'model comparisons %d' % (programs, stats['inputs'], stats['comparisons'],
                                     stats['identical-to-base'], stats['model-comparisons']))
    print('base outcomes: ' + ', '.join('%s %d' % (k[5:], v) for k, v in sorted(stats.items())
                                         if k.startswith('base-')))
    print('optimizer discrepancies: %d kinds, %d instances' % (
        len(findings), sum(len(v) for v in findings.values())))
    for (kind, name), items in sorted(findings.items()):
        print('  %-18s %-40s %6d  e.g. %s' % (kind, name, len(items), json.dumps(items[0])[:300]))
    print('model/real disagreements: %d kinds, %d instances' % (
        len(fidelity), sum(len(v) for v in fidelity.values())))
    for (kind, name), items in sorted(fidelity.items()):
        print('  %-10s %-26s %6d  e.g. %s' % (kind, name, len(items), json.dumps(items[0])[:300]))
    return report


def negative_control(directory, results_name='results.tsv'):
    """Perturb copies of real results and check that `compare` reports them."""
    real_path = os.path.join(directory, results_name)
    lines = open(real_path).read().splitlines()
    by_job = {line.split('\t')[0]: k for k, line in enumerate(lines)}
    flipped = {}
    for line in open(os.path.join(directory, 'manifest.jsonl')):
        entry = json.loads(line)
        variants = entry['variants']
        default = variants.get('prod/default')
        if not isinstance(default, int) or default == variants['base']:
            continue
        for row in entry['jobs']:
            base = lines[by_job[row[variants['base']]]].split('\t')
            if base[1] in flipped:
                continue
            target = by_job[row[default]]
            fields = lines[target].split('\t')
            if base[1] == 'OK':
                fields[4] = fields[4] + ' perturbed'
            elif base[1] == 'FAIL':
                fields[1], fields[4] = 'OK', '(con unit ())'
            else:
                continue
            flipped[base[1]] = target
            lines[target] = '\t'.join(fields)
        if len(flipped) == 2:
            break
    if len(flipped) < 2:
        print('negative control: not enough material')
        return
    with open(os.path.join(directory, 'results.perturbed.tsv'), 'w') as f:
        f.write('\n'.join(lines) + '\n')
    report = compare(directory, results_name='results.perturbed.tsv', quiet=True)
    kinds = set(report['findings'])
    if 'value prod/default' not in kinds or 'error->OK prod/default' not in kinds:
        raise SystemExit('negative control FAILED: perturbations not detected: %s' % sorted(kinds))
    print('negative control: a perturbed value and a perturbed failure were both detected')


def evaluate_and_compare(out, semantics, jobs, run=True):
    """Evaluate the jobs on the real machine under each builtin semantics variant
    (comma-separated, e.g. "E,C") and compare. Returns True when the optimizer
    variants agree with the unoptimized lowering under every variant."""
    clean = True
    for index, variant in enumerate(semantics.split(',')):
        results = 'results.%s.tsv' % variant
        values = 'model-values.real.%s.tsv' % variant
        if run:
            run_batch(os.path.join(out, 'jobs.tsv'), os.path.join(out, results), jobs, variant)
            run_batch(os.path.join(out, 'model-values.%s.tsv' % variant), os.path.join(out, values),
                      jobs, variant)
        print('=== builtin semantics variant %s' % variant)
        if index == 0:
            negative_control(out, results)
        report = compare(out, results_name=results, values_name=values,
                         report_name='report.%s.json' % variant, runs_name='model.%s.tsv' % variant)
        clean = clean and not report['findings']
    return clean


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('outdir')
    parser.add_argument('--from', dest='start', type=int, default=0)
    parser.add_argument('--count', type=int, default=100)
    parser.add_argument('--inputs', type=int, default=8)
    parser.add_argument('--depth', type=int, default=4)
    parser.add_argument('--model-all', action='store_true')
    parser.add_argument('--untyped', action='store_true',
                        help='programs of the untyped Lean-model audit generator')
    parser.add_argument('--probes', action='store_true',
                        help='the fixed machine-semantics probes (Test/MIR/FuzzReal/Probes.lean)')
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--semantics', default='E,C',
                        help='builtin semantics variants of the real machine, comma-separated')
    parser.add_argument('--compare-only', action='store_true')
    args = parser.parse_args()
    out = os.path.abspath(args.outdir)
    if not args.compare_only:
        command = [os.path.join(ROOT, '.lake/build/bin/fuzz_real'), out, '--from', str(args.start),
                   '--count', str(args.count), '--inputs', str(args.inputs), '--depth', str(args.depth)]
        if args.model_all:
            command.append('--model-all')
        if args.untyped:
            command.append('--untyped')
        if args.probes:
            command.append('--probes')
        subprocess.run(command, check=True, cwd=ROOT)
    clean = evaluate_and_compare(out, args.semantics, args.jobs, not args.compare_only)
    programs, changed, stage_changed = coverage(out)
    with open(os.path.join(out, 'coverage.json'), 'w') as f:
        json.dump({'programs': programs, 'differs-from-base': changed,
                   'stage-changes-term': stage_changed}, f, indent=1)
    print('pipeline stages changing the term (of %d programs): %s' % (
        programs, ', '.join('%s %d' % (k[5:], v) for k, v in sorted(stage_changed.items()))))
    print('passes alone changing the term: %s' % ', '.join(
        '%s %d' % (k[6:], v) for k, v in sorted(changed.items()) if k.startswith('alone/')))
    sys.exit(0 if clean else 1)


if __name__ == '__main__':
    main()
