# Cross-language benchmark: Moist, Aiken, Plinth, Plutarch

Date: 2026-11-07. Raw data: [benchmarks/cross-language.csv](benchmarks/cross-language.csv).

## What was measured

Nine contracts from `plinth-plutarch-comparison` (branch `cross-language-bench`): Voting, Certifying, Vesting,
Constitution, Crowdfund, Settings, the Hydra head validator, CIP-143 ProgrammableLogicGlobal, and the `Sample`
recursive function. Each exists in four languages:

| Compiler | Version | Source |
|---|---|---|
| Moist | this branch, Lean 4.24 | `Test/Comparison/Validators.lean`, `Test/Comparison/Cross/*.lean` |
| Aiken | 1.1.24, stdlib v4.0.0, `-t silent` | `plinth-plutarch-comparison/aiken/<Validator>/` |
| Plinth | plutus-tx 1.65.0.0, GHC 9.6.6 | `plinth-plutarch-comparison/src/*/*Plinth.hs` |
| Plutarch | 1.12 fork `011f6e18` | `plinth-plutarch-comparison/src/*` |

Moist is measured with default options (`moist`) and with builtin sharing and constant pooling (`moist-size`).

Every script runs through one evaluator, the plutus-core 1.65.0.0 CEK machine in counting mode
(`cross-bench` in the comparison repo), on identical arguments. Each validator is checked against two input sets:

- **bench:** the repository's 152 benchmark scenarios. The tables use only these.
- **test:** its 169 named accept/reject unit cases.

Costs are reported for cost-model variant C. Variant E differs by at most 0.01% in total CPU and gives identical
ratios. Size is the CBOR-wrapped flat script as stored on chain.

## Faithfulness

The Plinth source is the specification.

- **Conformance:** every Moist and Aiken port agrees with Plinth and Plutarch on all 321 bench and test cases under
  both variants.
- **Malformed input:** user-supplied Data (datums, redeemers, script parameters) is accepted or rejected exactly as
  Plinth does. Differential testing ran every port against `plinth.flat` on mutated inputs: wrong constructor tags,
  extra or missing fields, wrongly typed fields, and list edits, to depth 4. In total that was over 100,000 mutated
  contexts, with 0 mismatches for every Moist and Aiken script.
- **Ledger-built data:** structures the ledger builds are read with the guarantees the ledger gives a real V3
  ScriptContext, for example normalized, sorted `Value`s.
- **Plutarch:** the Plutarch scripts are the repository's originals. They differ from Plinth on some malformed data.
- **Plinth fix:** the repository's Plinth ProgrammableLogicGlobal rejected every valid SeizeAct. Its final check
  `check || error ()` evaluated `error ()` even when the check held. The fix (`e9edfbb`) rewrites it as an `if`.
  The conformance suite now passes all 465 tests, against 461 before.

## Results

### Total bench CPU (variant C)

| Validator | moist | moist-size | aiken | plinth | plutarch |
|---|---|---|---|---|---|
| Voting | 58.3M | **58.1M** | 66.5M | 78.0M | 82.8M |
| Certifying | 34.3M | **34.2M** | 40.0M | 38.0M | 38.9M |
| Vesting | 586.9M | **569.5M** | 750.0M | 1,015.6M | 884.3M |
| Constitution | 307.9M | **299.0M** | 340.5M | 485.3M | 355.2M |
| Crowdfund | 510.0M | **492.6M** | 702.7M | 965.6M | 1,178.9M |
| Settings | 1,385.4M | **1,369.2M** | 2,126.7M | 2,427.8M | 2,235.1M |
| Hydra | 412.0M | **399.9M** | 754.8M | 1,539.6M | 435.8M |
| ProgrammableLogicGlobal | 1,244.4M | **1,214.5M** | 1,564.1M | 1,594.7M | 1,382.7M |
| Sample | 330.8M | **324.9M** | 566.4M | 608.1M | 631.8M |

### Total bench Memory (variant C)

| Validator | moist | moist-size | aiken | plinth | plutarch |
|---|---|---|---|---|---|
| Voting | 116.0k | **114.9k** | 212.3k | 184.7k | 200.9k |
| Certifying | 93.1k | **92.3k** | 93.5k | 98.3k | 98.1k |
| Vesting | 1.6M | **1.5M** | 2.0M | 2.8M | 2.4M |
| Constitution | 1.1M | **1.1M** | 1.2M | 1.7M | 1.2M |
| Crowdfund | 1.4M | **1.3M** | 1.9M | 2.9M | 3.2M |
| Settings | 3.8M | **3.7M** | 5.7M | 6.8M | 5.6M |
| Hydra | 1.2M | **1.2M** | 2.2M | 6.3M | 1.2M |
| ProgrammableLogicGlobal | 3.3M | **3.1M** | 4.1M | 4.8M | 3.8M |
| Sample | 1.5M | **1.4M** | 1.8M | 2.1M | 2.2M |

### Script size (CBOR bytes)

| Validator | moist | moist-size | aiken | plinth | plutarch |
|---|---|---|---|---|---|
| Voting | **182** | 186 | 295 | 244 | 272 |
| Certifying | 346 | 342 | **316** | 381 | 317 |
| Vesting | 807 | **792** | 859 | 1,177 | 1,219 |
| Constitution | 986 | 981 | 817 | 791 | **769** |
| Crowdfund | 1,534 | **1,510** | 1,604 | 2,169 | 1,888 |
| Settings | 2,153 | 2,122 | **1,922** | 2,405 | 2,162 |
| Hydra | 6,869 | 6,177 | 7,548 | 9,615 | **6,001** |
| ProgrammableLogicGlobal | 3,571 | **3,498** | 3,828 | 3,918 | 4,080 |
| Sample | **93** | 94 | 118 | 131 | 109 |

### Geometric mean vs Plinth over all bench cases (variant C; lower is better)

| Compiler | CPU | Memory | Size |
|---|---|---|---|
| moist | 0.55x | 0.51x | 0.82x |
| moist-size | 0.55x | 0.49x | 0.81x |
| aiken | 0.78x | 0.72x | 0.88x |
| plinth | 1.00x | 1.00x | 1.00x |
| plutarch | 0.83x | 0.75x | 0.90x |


Bold marks the best value in each row.

### Summary

- **Execution cost:** Moist is cheapest in total CPU and memory on all nine validators. Compared with Plinth, its
  per-case CPU is 0.55× and its memory 0.49 to 0.51×. Next best are Aiken (0.78× CPU) and Plutarch (0.83×).
- **Per case:** Moist is cheapest in CPU on 143 of 152 bench cases. The other nine are all early-rejecting cases,
  where a script that reaches a cheaper failure first wins:
  - Aiken wins one Voting case and two Settings cases.
  - Plutarch wins two Constitution cases and three Hydra cases. Its biggest margin is Hydra "invalid transition",
    at 5.9M against Moist's 20.3M.
  - Plinth wins one Constitution case.
- **Size:** mixed.
  - Moist is smallest on Voting, Vesting, Crowdfund, ProgrammableLogicGlobal and Sample.
  - Aiken is smallest on Certifying and Settings, and Plutarch on Constitution and Hydra.
  - Constitution is Moist's weakest result: 981 bytes against Plutarch's 769. Moist was already about 100 bytes
    larger before matching Plinth's decoding of malformed configs, and those checks added roughly 100 more.
  - The geometric-mean size is 0.81× Plinth, against 0.88× for Aiken and 0.90× for Plutarch.
- **`moist-size`:** this profile is slightly cheaper than `moist` in CPU and memory. It is also smaller on 7 of 9
  validators; the exceptions are Voting and Sample.

## Moist issues found while porting

- **Translator bug.** A partially applied `@[plutus_sop]` constructor is lowered to a `constr` with missing fields.
  For example, `let make := Pair.mk 1; make x` becomes `constr(0 1) x`, which errors at runtime. The fully applied
  form is correct. The bug is in the Lean-to-MIR translator, which runs before the verified pipeline. The Hydra port
  works around it with an explicit lambda.
- **eDSL bindings added:** `serialiseData` and `chooseData` were missing from `Moist/Onchain/Prelude.lean`. They are
  new builtin bindings only; the optimizer and proofs are unchanged.
- **eDSL limits.** These are worked around in the ports:
  - The translator does not support mutual recursion.
  - Recursion over nested inductive types needs `termination_by sizeOf`.
  - Recursion on two lists packs both arguments into a tuple on every step.
  - Each reference to a recursive helper is inlined as a separate copy, so the ports share helpers by passing them
    as arguments.
  - `DropList` is not exposed.

## Reproduction

```sh
# Moist scripts
lake build cross_bench_export && .lake/build/bin/cross_bench_export
# Aiken scripts: in each plinth-plutarch-comparison/aiken/<Validator>, run aiken build -t silent and copy
# validators[0].compiledCode to /Users/sho/fun/cross-bench-data/<Validator>/aiken.cbor.hex
# Inputs, Plinth/Plutarch scripts, and the evaluation (in plinth-plutarch-comparison)
cabal run cross-bench -- export
cabal run cross-bench -- run > cross-language.csv
```
