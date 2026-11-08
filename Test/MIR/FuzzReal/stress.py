"""Run every (huge value, path) pair of Test/MIR/FuzzReal/Stress.lean in its
own process and report the ones that crash (stack overflow, abort) or fail.

  python3 -I Test/MIR/FuzzReal/stress.py
"""
import os
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
EXE = os.path.join(ROOT, '.lake/build/bin/fuzz_real')


def main():
    pairs = subprocess.run([EXE, '--stress-list'], capture_output=True, text=True,
                           check=True).stdout.split('\n')
    bad = 0
    for pair in filter(None, pairs):
        value, path = pair.split()
        try:
            result = subprocess.run([EXE, '--stress', value, path], capture_output=True,
                                    text=True, timeout=int(os.environ.get('STRESS_TIMEOUT', '120')))
            out = (result.stdout + result.stderr).strip().replace('\n', ' | ')
            status = 'ok' if result.returncode == 0 and out.startswith('ok') else 'PROBLEM'
            if result.returncode != 0:
                out = 'exit %d: %s' % (result.returncode, out[-200:])
        except subprocess.TimeoutExpired:
            status, out = 'PROBLEM', 'timeout'
        bad += status != 'ok'
        print('%-8s %-24s %-15s %s' % (status, value, path, out[:160]), flush=True)
    print('%d problem(s)' % bad)


if __name__ == '__main__':
    main()
