#!/bin/sh
# The full differential campaign against the plutus-core 1.65 CEK machine under
# builtin semantics variants E and C, with the seeds of the reported run.
# Usage: run_campaign.sh OUTDIR
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
validators="Voting Certifying Vesting Sample Constitution Crowdfund Settings Hydra
  ProgrammableLogicGlobal EdgeListSum EdgeMapFilterCount EdgeWideRecord EdgeValueLookup
  EdgeEnumDispatch EdgeGuardOrder EdgeByteSearch EdgeNestedLists EdgeHorner EdgeAllAny"

# Machine-semantics probes (case on builtins, list/pair/Data builtins, crypto,
# BLS, Value, variant-E bounds, key comparisons), every variant on the model too.
python3 -I "$here/fuzz_real.py" "$out/probes" --probes --model-all --jobs 4 \
  > "$out/probes.log" 2>&1 || true

pids=""
# Typed generator: seeds 1000-5999, 8 argument lists each, Lean model on every job.
for k in 0 1 2 3; do
  python3 -I "$here/fuzz_real.py" "$out/typed$k" --from $((1000 + k * 1250)) --count 1250 \
    --model-all --jobs 2 > "$out/typed$k.log" 2>&1 &
  pids="$pids $!"
done
# Untyped generator of the Lean-model audit: seeds 0-1999.
python3 -I "$here/fuzz_real.py" "$out/untyped" --from 0 --count 2000 --untyped --model-all \
  --jobs 2 > "$out/untyped.log" 2>&1 &
pids="$pids $!"
# Huge constants through serialisation, model, printing and compile.
python3 -I "$here/stress.py" > "$out/stress.log" 2>&1 &
pids="$pids $!"
# Each validator on every exported case and its mutations (depth 3), and 100
# mutants of its MIR on 40 cases each; one process per validator.
for v in $validators; do
  python3 -I "$here/fuzz_validators.py" "$out/validators/$v" --validator "$v" --model-every 10 \
    --jobs 2 > "$out/validators-$v.log" 2>&1 &
  pids="$pids $!"
  if [ "$v" = Hydra ]; then
    # Hydra's mutants take minutes each: five shards of 20
    for k in 0 1 2 3 4; do
      python3 -I "$here/fuzz_validators.py" "$out/mutants/Hydra-$k" --validator Hydra \
        --mutants $((k * 20 + 20)) --mutant-from $((k * 20)) --sample 40 --seed 1 \
        --model-every 5 --jobs 2 > "$out/mutants-Hydra-$k.log" 2>&1 &
      pids="$pids $!"
    done
    continue
  fi
  python3 -I "$here/fuzz_validators.py" "$out/mutants/$v" --validator "$v" --mutants 100 \
    --sample 40 --seed 1 --model-every 5 --jobs 2 > "$out/mutants-$v.log" 2>&1 &
  pids="$pids $!"
done
for p in $pids; do wait "$p" || true; done

grep -H -A8 "^=== builtin" "$out"/*.log 2>/dev/null | grep -E "===|programs|optimizer|model/real" || true
grep -h "problem(s)" "$out/stress.log" || true
