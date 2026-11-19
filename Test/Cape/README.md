# UPLC-CAPE measurements

All 246 cases passed with CAPE's production evaluator (`PlutusTx.Eval-1.63.0.0`). CPU and memory are summed over the 71 measurement cases; the 175 checks are excluded. CPU change is relative to the [first Moist port](https://github.com/SeungheonOh/Moist/tree/1c2787f/Test/Cape). Peer CPU is the lowest sum across [published submissions at the same CAPE revision](https://github.com/IntersectMBO/UPLC-CAPE/tree/b88d0d5d0664015b5b1378d6bd3e3fafec55c75a/submissions). Lower is better.

| Scenario | Measured | Checks | Moist CPU | CPU change | Best peer CPU | Moist memory | Bytes | AST nodes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ecd` | 14 | 0 | 23,259,572 | -21.9% | 18,747,572 (Plinth) | 99,596 | 45 | 37 |
| `factorial` | 10 | 0 | 16,728,710 | -46.6% | 18,574,552 (Scalus) | 61,549 | 71 | 62 |
| `factorial_naive_recursion` | 10 | 0 | 26,499,195 | -5.4% | 26,979,195 (Pebble) | 97,235 | 39 | 33 |
| `fibonacci` | 11 | 0 | 3,633,986 | -95.6% | 3,961,677 (Scalus) | 18,519 | 155 | 85 |
| `fibonacci_naive_recursion` | 11 | 0 | 112,401,095,906 | -14.3% | 112,400,919,906 (Pebble) | 374,771,843 | 50 | 44 |
| `htlc` | 4 | 21 | 46,661,964 | -33.1% | 47,923,502 (Plinth) | 146,990 | 845 | 877 |
| `linear_vesting` | 6 | 23 | 138,285,992 | -19.0% | 142,593,776 (Scalus) | 390,908 | 810 | 835 |
| `two_party_escrow` | 5 | 131 | 84,931,318 | -28.0% | 87,996,670 (Plinth) | 262,904 | 1,417 | 1,341 |

Unrestricted factorial uses [Scalus's four-step unroll](https://github.com/IntersectMBO/UPLC-CAPE/tree/b88d0d5d0664015b5b1378d6bd3e3fafec55c75a/submissions/factorial/Scalus_1.4.0_nau): with `outer = n * (n - 3)`, the product of four consecutive factors is `outer * (outer + 2)`. Unrestricted Fibonacci uses [Scalus's bounded table strategy](https://github.com/IntersectMBO/UPLC-CAPE/tree/b88d0d5d0664015b5b1378d6bd3e3fafec55c75a/submissions/fibonacci/Scalus_1.4.0_nau): Moist generates the entries for 0–25 and computes larger inputs with a loop. The fixed-algorithm ports use curried recursion in Moist's Ptah frontend; the two naive scripts share partially applied builtins as in [Pebble](https://github.com/IntersectMBO/UPLC-CAPE/tree/b88d0d5d0664015b5b1378d6bd3e3fafec55c75a/submissions/fibonacci_naive_recursion/Pebble_0.5.0_michele-nuzzi), without changing the prescribed recursive calls.

The validators use [Plinth-style](https://github.com/IntersectMBO/UPLC-CAPE/tree/b88d0d5d0664015b5b1378d6bd3e3fafec55c75a/submissions/two_party_escrow/Plinth_1.71.0.0_Unisay) field access, unique-output searches and lookups on encoded values. Each validator enables Moist's existing builtin-sharing and constant-pooling options. The comparisons are for execution cost, not a claim of smallest scripts: for example, unrestricted Fibonacci grows from 71 to 155 bytes.

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
