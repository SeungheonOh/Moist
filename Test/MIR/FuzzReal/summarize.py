"""Totals of a campaign directory written by run_campaign.sh.

  python3 -I Test/MIR/FuzzReal/summarize.py OUTDIR

For every run directory (one holding manifest.jsonl and report.<variant>.json):
programs, inputs, variant comparisons, model comparisons, base outcomes,
optimizer discrepancies and model/real disagreements, per builtin semantics
variant; then the stress sweep's problems.
"""
import collections
import json
import os
import sys


def runs(root):
    for directory, _, files in sorted(os.walk(root)):
        if 'manifest.jsonl' in files:
            yield directory


def main():
    root = os.path.abspath(sys.argv[1])
    totals = collections.defaultdict(collections.Counter)
    findings = []
    for directory in runs(root):
        family = os.path.relpath(directory, root).split(os.sep)[0]
        family = family.rstrip('0123456789') if family.startswith('typed') else family
        for variant in ('E', 'C'):
            path = os.path.join(directory, 'report.%s.json' % variant)
            if not os.path.exists(path):
                totals[(family, variant)]['missing reports'] += 1
                continue
            report = json.load(open(path))
            stats = report['stats']
            counter = totals[(family, variant)]
            counter['runs'] += 1
            counter['programs'] += report['programs']
            for key in ('inputs', 'comparisons', 'identical-to-base', 'model-comparisons',
                        'base-OK', 'base-FAIL', 'base-BUDGET'):
                counter[key] += stats.get(key, 0)
            for kind, items in report['findings'].items():
                counter['discrepancies'] += len(items)
                findings.append(('optimizer', variant, os.path.relpath(directory, root), kind,
                                 len(items), items[0]))
            for kind, items in report['fidelity'].items():
                counter['model/real'] += len(items)
                findings.append(('model', variant, os.path.relpath(directory, root), kind,
                                 len(items), items[0]))
    grand = collections.Counter()
    for (family, variant), counter in sorted(totals.items()):
        print('%-12s %s  %s' % (family, variant, ', '.join(
            '%s %d' % (k, v) for k, v in counter.items())))
        grand.update(counter)
    print('ALL (E+C)     %s' % ', '.join('%s %d' % (k, v) for k, v in grand.items()))
    for kind, variant, where, what, count, example in findings:
        print('%s %s %s %s x%d e.g. %s' % (kind, variant, where, what, count, json.dumps(example)[:300]))
    stress = os.path.join(root, 'stress.log')
    if os.path.exists(stress):
        lines = open(stress).read().splitlines()
        print('stress: %d pairs, %d problems' % (
            sum(1 for l in lines if l.startswith(('ok', 'PROBLEM'))),
            sum(1 for l in lines if l.startswith('PROBLEM'))))
        for line in lines:
            if line.startswith('PROBLEM'):
                print('  ' + line[:150])


if __name__ == '__main__':
    main()
