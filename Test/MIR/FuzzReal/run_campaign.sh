#!/bin/sh
# The full differential campaign (builtin semantics variants E and C) against the plutus-core 1.65 CEK machine,
# with the seeds of the reported run. Usage: run_campaign.sh OUTDIR
#
# Needs `cross-bench` with the `batch` command (plinth-plutarch-comparison,
# branch cross-language-bench; override its path with CROSS_BENCH) and the
# cross-bench data directory (/Users/sho/fun/cross-bench-data).
set -eu
out=${1:?usage: run_campaign.sh OUTDIR}
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
cd "$root"
lake build fuzz_real fuzz_validators
mkdir -p "$out"

# Machine-semantics probes, every variant also on the Lean model.
python3 -I "$here/fuzz_real.py" "$out/probes" --probes --model-all --jobs 4 > "$out/probes.log" 2>&1 || true

# Typed generator: seeds 1000-5999, 8 argument lists each, Lean model on every job.
pids=""
for k in 0 1 2 3; do
  python3 -I "$here/fuzz_real.py" "$out/typed$k" --from $((1000 + k * 1250)) --count 1250 \
    --model-all --jobs 2 > "$out/typed$k.log" 2>&1 &
  pids="$pids $!"
done
# Untyped generator of the Lean-model audit: seeds 0-1999.
python3 -I "$here/fuzz_real.py" "$out/untyped" --from 0 --count 2000 --untyped --model-all \
  --jobs 2 > "$out/untyped.log" 2>&1 &
pids="$pids $!"

# The 19 validators: every exported case and its mutations (depth 3).
python3 -I "$here/fuzz_validators.py" "$out/validators" --model-every 10 --jobs 6 \
  > "$out/validators.log" 2>&1 &
pids="$pids $!"

# Mutants of the validators' MIR: 100 per validator, 40 cases each.
python3 -I "$here/fuzz_validators.py" "$out/mutants" --mutants 100 --sample 40 --seed 1 \
  --model-every 5 --jobs 6 > "$out/mutants.log" 2>&1 &
pids="$pids $!"
for p in $pids; do wait "$p" || true; done

grep -h -A6 "^=== builtin\|^optimizer discrepancies\|^model/real" "$out"/*.log 2>/dev/null || true
