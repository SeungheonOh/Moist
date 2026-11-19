# UPLC-CAPE measurements

All 246 cases from [UPLC-CAPE `b88d0d5`](https://github.com/IntersectMBO/UPLC-CAPE/tree/b88d0d5d0664015b5b1378d6bd3e3fafec55c75a/scenarios) passed with Moist's default compiler options and CAPE's production evaluator (`PlutusTx.Eval-1.63.0.0`). CPU and memory are sums over the 71 measurement cases; the 175 checks do not contribute. Bytes and AST nodes are CAPE's measurements of each unapplied program.

| Scenario | Measured | Checks | CPU units (sum) | Memory units (sum) | Bytes | AST nodes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `ecd` | 14 | 0 | 29,787,572 | 140,396 | 58 | 49 |
| `factorial` | 10 | 0 | 31,299,296 | 139,495 | 49 | 41 |
| `factorial_naive_recursion` | 10 | 0 | 28,019,280 | 107,235 | 34 | 27 |
| `fibonacci` | 11 | 0 | 82,376,267 | 375,759 | 71 | 59 |
| `fibonacci_naive_recursion` | 11 | 0 | 131,228,350,599 | 494,866,143 | 43 | 36 |
| `htlc` | 4 | 21 | 69,733,700 | 193,132 | 656 | 678 |
| `linear_vesting` | 6 | 23 | 170,663,364 | 490,700 | 1,038 | 1,013 |
| `two_party_escrow` | 5 | 131 | 117,904,077 | 312,519 | 1,974 | 1,733 |

Naive Fibonacci at inputs 20 and 25 returns the expected values but exceeds CAPE's per-transaction CPU and memory limits. CAPE tallies costs without stopping at those limits.

## Reproduce

From the Moist root, with Aiken 1.1.24 and the pinned CAPE checkout's production `measure` executable on `PATH`. Set `CAPE` to that checkout. Aiken only decodes Flat to text; CAPE applies the inputs, checks the results and measures the scripts.

```sh
set -eu
: "${CAPE:?set CAPE to the UPLC-CAPE checkout}"
out=$(mktemp -d)
lake -Kci=true build Test.Cape.Export
lake -Kci=true env lean --run Test/Cape/Export.lean "$out"
for flat in "$out"/*.flat; do
  name=$(basename "$flat" .flat)
  aiken uplc decode "$flat" > "$out/$name.uplc"
  measure -i "$out/$name.uplc" -t "$CAPE/scenarios/$name/cape-tests.json" -o "$out/$name.json"
done
printf 'Per-case metrics: %s\n' "$out"
```
