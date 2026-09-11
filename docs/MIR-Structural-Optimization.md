# Structural optimization beyond arithmetic

## Implemented

The production pipeline now adds these changes after checked simplification:

1. **Pair deconstruction specialization:** replace direct FstPair/SndPair
   applications on proven builtin pairs with native Case. Unbox projection-only
   pair bindings once when a projection is on the first evaluation frontier.
2. **List-branch/destructor fusion:** replace a NullList Boolean test on a
   proven list with native list Case; reuse its head/tail fields throughout the
   nonempty branch instead of calling the list destructors again.
3. **Partial-builtin call-state elimination:** move or discard total,
   unsaturated builtin states rather than retaining unnecessary ANF bindings.

These are active through the shared Onchain/Ptah compiler. Size-oriented
pooling/sharing controls remain separate. The optimization trace now includes
the structural stage.

## Real compiled workloads

Before enabling the changes, the existing compiler's UPLC was serialized into
`docs/benchmarks/mir-structural-baseline.csv`. Scripts and runtime arguments are
stored separately; all optimizer invocations receive only the script. The
snapshot is not regenerated when the compiler or test binary rebuilds.

There are 13 workload designs and 32 workload/input rows: the 12 existing
native/compiler-policy workloads plus one new source-level list-redeemer
minting-policy test. The new workload validates two decoded redeemer fields;
it is a test policy, not a deployed validator or an existing production fixture.

Successful inputs, comparing the frozen compiler output with the new defaults:

| Workload | CPU before → after | Memory before → after | Flat bytes before → after |
| --- | --- | --- | --- |
| Existing NFT policy | 2,343,773 → 2,059,886 | 8,251 → 8,187 | 68 → 69 |
| Existing redeemer policy | 1,476,199 → 1,192,312 | 4,690 → 4,626 | 42 → 43 |
| Existing currency-symbol policy | 1,818,792 → 1,676,897 | 6,122 → 6,090 | 51 → 52 |
| Existing Data action matching | 1,056,802 → 564,915 | 3,961 → 2,597 | 44 → 34 |
| Existing lovelace field extraction | 510,574 → 368,582 | 1,728 → 1,696 | 15 → 15 |
| New source-level list-redeemer policy | 2,407,704 → 1,454,988 | 8,114 → 6,190 | 72 → 58 |

These gains are not arithmetic constant-folding results. The frozen native
matrix additionally includes rejection and malformed-redeemer paths, and the
test suite asserts CPU and memory non-increase on every one of its 32 inputs.
That empirical check is not a universal resource theorem. A few scripts grow
by one byte, consistent with the requested CPU/memory priority.

The list pass has its own ablation: on the new list-redeemer policy, the core
compiler plus list fusion alone uses 1,834,875 CPU, 6,854 memory, and 62 bytes.
Pair specialization supplies the additional savings in the combined result.

## Guard audit

### Pair deconstruction

**Purpose:** avoid general pair projection builtins when the result shape is
already established. Reuse components without re-evaluating their producer.

**Inputs and assumptions:** finite MIR; origin-aware lexical identities;
unique binders; sequential nonrecursive Lets; strict left-to-right evaluation.
Positive evidence comes from successful UnConstrData or MkPairData, including
dominating producer aliases, not from source parameter types.

**Blocks and invariants:** the producer is evaluated exactly once at its old
frontier. Whole-pair unboxing requires every use to be a direct projection and
at least one such use at the first evaluation frontier; an escaping pair keeps
its original binding. Fresh component binders preserve captured/deferred uses.
Only direct, fully forced projection heads are lowered individually. Why not
already-shared projection functions? They have already paid the forcing cost,
so replacing them with two component binders can increase execution memory.

**Dependencies:** `Advanced/Products.lean` uses `builtin` protocol syntax,
`firstEvaluationUse`, global binder preparation, and fresh allocation. Final
pre-lowering cleanup removes aliases introduced by unboxing. The benchmark
therefore includes a cleanup-only control rather than attributing all cleanup
savings to pair specialization.

### List-branch fusion

**Purpose:** combine empty/nonempty discrimination and field access into one
native deconstruction. Head/tail values are bound only in the nonempty branch.

**Inputs and assumptions:** the same lexical/strictness assumptions; exactly
two Boolean alternatives; a Var positively known to hold a list from an
evaluated producer. Unknown lambda parameters do not supply shape evidence.

**Blocks and invariants:** match the correct NullList force/application protocol;
retain list validation; replace projections only inside the nonempty branch;
keep the empty branch unchanged, including any deliberately failing HeadList.
Branch-local replacements cannot capture shadowed variables. Why not rewrite
an arbitrary NullList argument to native Case? Other native caseable values
would otherwise bypass the builtin's list-type validation.

**Dependencies:** `Advanced/Shapes.lean` reuses dominating list facts and binder
hygiene. This pass runs before pair lowering, while SndPair/UnConstrData list
provenance is still syntactically available. No inference from a branch's lambda
count or from an external source annotation is used.

### Partial builtin states

**Purpose:** avoid reintroducing call-state bindings when optimizing already
compiled programs. This applies to data/comparison/cryptographic builtins too,
not just arithmetic.

**Inputs and assumptions:** a correctly forced, still-unsaturated builtin with
total/effect-free captured arguments. One use allows movement; zero uses allows
removal. Saturated calls and invalid protocols remain outside this rule.

**Blocks and invariants:** `PreLower.lean` consults the existing guarded
`builtinRemainder`; it does not weaken general purity or its proof contract.
Why distinguish partial from saturated calls? A saturated call can still fail
its runtime type check. Why inspect captured arguments? Creating even an unused
partial application must preserve their Trace messages and failures.

## Regressions caught during implementation

- Reoptimizing the frozen recursive program initially inserted an extra partial
  builtin binding on each call. The new guarded call-state rule removes that
  ANF overhead; the unchanged factorial case is now a non-regression check,
  not the headline optimization benchmark.
- An initial pair rewrite expanded cached projection functions. On the external
  cooperative workload, memory rose from the core pipeline's 892,050 to 950,506.
  The direct-head guard fixes this: the guarded result remains at 892,050.
- Unboxing first introduced redundant aliases that obscured resource savings.
  Checked pre-lowering cleanup removes them without undoing native pair Cases.

## External cross-check and ablations

Five distinct existing Flat workloads are exercised: auction, cooperative,
Uniswap, token-account, and vesting. A SHA-256 manifest records the exact files.
All recorded configurations preserve each workload's returned result/failure.
These corpus files are optimized as provided, including any embedded arguments;
unlike the frozen Moist validators, they are not an input-withholding benchmark.

The native and external CSVs include nine configurations: baseline,
pre-lowering only, core pipeline, core plus pairs, core plus list fusion,
standalone pair pass, standalone list pass, both structural passes, and full
production defaults. This separates new structural gains from older compiler
passes and cleanup. Measurements use the pinned native evaluator, not current
network cost parameters or host wall-clock memory.

There are still scheduling opportunities: on the cooperative workload, applying
structural optimization directly is better than running the whole pipeline
first. Earlier builtin sharing removes profitable direct projection sites.
List fusion does not fire on the raw external programs' old-style Boolean
encoding. No claim of a globally best pass order or universal dominance is made.

## Verification and artifacts

- **441 full-suite tests, 59 focused audit tests pass**, with all nine Ptah
  smoke checks passing.
- 3,630 targeted native and matching Lean trace comparisons, plus 800 malformed
  context comparisons against frozen versions of five policy designs.
- 4,608 additional generated structural/context trace comparisons; the prior
  129,024 generated comparisons and 18,432 original comparisons still run.
- Cached-projection resource regressions and all frozen native workloads have
  explicit CPU/memory assertions. The 21 changed golden fixtures retain their
  exact result/error sections; only their measured costs change.
- Four new kernel-checked local CEK joins cover first/second pair projection and
  cons/nil list-choice fusion. There are now **17 local schemas**, all with only
  `propext` and `Quot.sound` dependencies. These are not proofs of the complete
  analyses, traversal, unboxing, partial-state inliner, or pipeline; the legacy
  invalid budget axiom remains unresolved and outside these local proofs.

Artifacts:

- `docs/benchmarks/mir-structural-baseline.csv`: frozen scripts and separate inputs.
- `docs/benchmarks/mir-structural-native.csv`: 288 measured native rows.
- `docs/benchmarks/mir-structural-external.csv`: 45 external ablation rows.
- `docs/benchmarks/mir-structural-external.sha256`: external workload identities.
- `docs/benchmarks/mir-structural-golden-costs.csv`: source-level integration costs.

Reproduce with `lake build tests mir_audit mir_opportunity_bench`, the full and
focused test executables, and `mir_opportunity_bench --structural`. External
reproduction uses `--structural-external DIRECTORY FILENAMES...`. Never use
`--snapshot-validators` to overwrite the frozen baseline during verification.
