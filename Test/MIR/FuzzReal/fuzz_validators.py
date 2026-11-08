"""Differential test of the cross-language validators on the plutus-core 1.65
CEK machine: every optimizer variant of each validator's MIR against the same
MIR compiled without optimization, on every exported case and on mutations of
its user-supplied Data.

  python3 -I Test/MIR/FuzzReal/fuzz_validators.py OUTDIR [--validator V]...
      [--max-depth N] [--data DIR] [--jobs N] [--compare-only]
"""
import argparse
import csv
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fuzz_real  # noqa: E402
import mutate  # noqa: E402
import pdata  # noqa: E402

VALIDATORS = ['Voting', 'Certifying', 'Vesting', 'Sample', 'Constitution', 'Crowdfund', 'Settings',
              'Hydra', 'ProgrammableLogicGlobal', 'EdgeListSum', 'EdgeMapFilterCount',
              'EdgeWideRecord', 'EdgeValueLookup', 'EdgeEnumDispatch', 'EdgeGuardOrder',
              'EdgeByteSearch', 'EdgeNestedLists', 'EdgeHorner', 'EdgeAllAny']


def write_cases(data, validators, cases_dir, max_depth):
    os.makedirs(cases_dir, exist_ok=True)
    for validator in validators:
        rows = []
        with open(os.path.join(data, validator, 'cases.csv')) as f:
            for row in csv.DictReader(f):
                args = [pdata.decode(bytes.fromhex(a)) for a in row['args'].split(';') if a]
                rows.append((row['kind'] + ':' + row['name'], args))
        cases = mutate.cases(validator, rows, max_depth)
        with open(os.path.join(cases_dir, validator + '.tsv'), 'w') as f:
            for label, encoded in cases:
                f.write(label.replace('\t', ' ') + '\t' + encoded + '\n')
        print('%s: %d cases (%d exported)' % (validator, len(cases), len(rows)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('outdir')
    parser.add_argument('--validator', action='append')
    parser.add_argument('--max-depth', type=int, default=3)
    parser.add_argument('--data', default='/Users/sho/fun/cross-bench-data')
    parser.add_argument('--jobs', type=int, default=8)
    parser.add_argument('--semantics', default='E,C')
    parser.add_argument('--model-all', action='store_true')
    parser.add_argument('--compare-only', action='store_true')
    parser.add_argument('--mutants', type=int, default=0,
                        help='per validator: random local mutants of its MIR instead of the MIR itself')
    parser.add_argument('--sample', type=int, default=40, help='cases per mutant')
    parser.add_argument('--mutant-from', type=int, default=0,
                        help='first mutant index (mutants --mutant-from .. --mutants-1), to shard')
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--model-every', type=int, default=1,
                        help='run the Lean model on every N-th input only')
    args = parser.parse_args()
    out = os.path.abspath(args.outdir)
    validators = args.validator or VALIDATORS
    if not args.compare_only:
        cases_dir = os.path.join(out, 'cases')
        if not os.path.isdir(cases_dir):
            write_cases(args.data, validators, cases_dir, args.max_depth)
        command = [os.path.join(fuzz_real.ROOT, '.lake/build/bin/fuzz_validators'), out, cases_dir]
        for validator in validators:
            command += ['--validator', validator]
        if args.model_all:
            command.append('--model-all')
        command += ['--mutants', str(args.mutants), '--mutant-from', str(args.mutant_from),
                    '--sample', str(args.sample),
                    '--seed', str(args.seed), '--model-every', str(args.model_every)]
        subprocess.run(command, check=True, cwd=fuzz_real.ROOT)
    clean = fuzz_real.evaluate_and_compare(out, args.semantics, args.jobs, not args.compare_only)
    sys.exit(0 if clean else 1)


if __name__ == '__main__':
    main()
