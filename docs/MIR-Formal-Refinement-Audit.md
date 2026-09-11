# MIR formal refinement audit

Subsequent implementation: [whole-pass proof progress](MIR-Formal-Pass-Implementation.md)
certifies the actual scalar and data folding passes and updates the Inline proof
work. The remaining text records the preceding audit checkpoint.

Date: 2026-09-08. Target selected by the user: the existing ANF/DCE refinement.

## Verdict

**The production pipeline does not currently have a sound whole-pipeline formal
certificate. Nor do all its individual passes.** ANF and DCE have whole-pass
`MIRCtxRefines` theorems. The legacy Inline theorem depends on a false axiom;
it is not a sound baseline to emulate. The new optimizations have bounded
differential evidence and selected local proofs, not whole-pass certificates.

This audit fixes a data-constructor folding counterexample, repairs two pure
inlining proof paths, removes native compiler trust from the DCE proof chain,
and adds six contextual rewrite certificates. It does **not** claim to have
finished the impure inlining proof or proved every production pass.

## Exact contract

`Contextual.ObsRefines` preserves existence of a terminating result and explicit
CEK error in the forward direction. `CtxRefines` requires this in every closing
UPLC context, together with preservation of closedness. Contextual observation
can distinguish results by applying or scrutinizing them; this is not merely a
top-level success/failure test. However, the relation has no trace observation
and does not require a diverging source to remain divergent.

`MIRCtxRefines` also preserves successful lowering for every lexical environment,
using `lowerTotalExpr`. It is not directly a theorem about `compileOptimized`,
`lowerExpr`, Flat serialization, native evaluation, or a particular resource cap.
The native validator budgets and the stronger trace regression checks remain
separate evidence, not conclusions of these theorems.

## Fixed: data-list representation changed failure behavior

`Advanced.foldDataConstructors` previously converted every folded data `MkCons`
to `ConstDataList`, including when its tail was represented as `ConstList`.
The Lean evaluator distinguishes these representations: generic-list `MkCons`
accepts a constant head without checking element metadata, whereas specialized
data-list `MkCons` requires a `Data` head.

Counterexample, with the empty literal annotated as a list of Data:

```text
let discarded = MkCons 7 (MkCons (Data.I 3) (ConstList []))
in 9
```

The reference evaluator returned 9 before folding and errored afterwards. This
violates even the selected weak refinement: a closing context halts before and
fails after. Native evaluation rejects the wrong-type prepend in both versions;
therefore a native-only differential test misses this proof-model bug.

The repair retains generic versus specialized list representation. It does not
remove the optimization. Correctly typed generic/specialized data-list literals
serialize identically, and the existing validator benchmark CSVs reproduce
byte-for-byte. Tests cover empty/nonempty tails, both representations, valid and
invalid prepend consumers, 17 isolated transformations and all eight production
option combinations.

## Repaired proof paths

- `StrictOcc.same_env_beta_single_obsRefines` and
  `StrictOcc.same_env_beta_multi_obsRefines` already receive actual RHS return
  witnesses. They now use those witnesses directly instead of invoking
  `halt_or_error`. Their contextual pure-inlining wrappers consequently no
  longer depend on `budget_exhaustion` either.
- Four closed builtin checks in `Verified/Purity.lean` now use kernel `decide`
  instead of `native_decide`. The DCE theorem no longer depends on
  `Lean.ofReduceBool` or `Lean.trustCompiler`.
- `AdvancedRefinement.finite_join_refines` proves that a finite CEK join implies
  the selected observation refinement without assuming termination. Terminal
  states before either join prefix are handled explicitly using absorption.
- `contextual_of_uniform_refinement` and `contextual_of_uniform_join` lift
  uniform environment/continuation evidence plus closedness preservation to
  the existing `CtxRefines` relation.

Six concrete contextual schemas are instantiated: generic data `MkCons`,
specialized data `MkCons`, evaluated binary builtin folding, literal Boolean
choice lowering, force-through-delayed-Boolean-case, and delayed list choice
on a bound variable. The last covers every runtime value, including non-lists
and missing lookup; it is not limited to well-typed list inputs. It is still
not a theorem about the complete alias-aware MIR traversal.

`Test/MIR/Opt/FormalAxioms.lean` fails its build if any audited sound declaration
depends on an axiom other than `propext`, `Classical.choice`, or `Quot.sound`.
The legacy Inline and pipeline declarations are printed separately and are
deliberately **not** counted as passing certificates.

## Unresolved: impure Inline certificate

The CEK `step` relation is unbounded; it has no transition from an infinite
execution to budget exhaustion. `budget_exhaustion` asserts that non-halting
implies explicit error. `BudgetModel.unbounded_budget_exhaustion_is_false`
constructively refutes it using an invariant execution cycle.

There is also a direct counterexample to the old strict-occurrence argument:

```text
omega = (lambda x. x x) (lambda x. x x)
before = (lambda saved. omega saved) Error
after  = omega Error
```

`before` errors in four steps. `after` enters an invariant five-state cycle
after six steps and never errors. `StrictSingleOcc 1` nevertheless accepts
the body: it excludes deferred positions but not diverging predecessors.
`Test/MIR/Opt/StrictFrontier.lean` proves all these relevant properties and
the failure of observation refinement without using the false axiom.

Production already has the stronger `firstEvaluationUse` guard. The new runtime
regression verifies this counterexample stays rejected by the guard and
preserves failure through every tested transform/production option. The proof
bridge currently discards that stronger evidence. Repair requires transporting
the evaluation-frontier invariant through lowering and proving that preceding
expressions return before the substituted use. Source terminal derivations,
not a universal halt-or-error dichotomy, must drive the simulation. The legacy
constructor-tail, application-right and let-body error lemmas need this repair
too. No optimization was disabled and the false assumption was not relabeled
as a valid certificate.

## Coverage and remaining obligations

| Production component | Whole-pass formal status | Remaining proof work |
|---|---|---|
| ANF normalization | `anfNormalize_refines`, standard axioms only | Production composition and lowering bridge |
| DCE | `dce_refines`, standard axioms only after this repair | Production composition and lowering bridge |
| Inline | Pure local paths repaired; whole pass still depends on false axiom | Evaluation-frontier lowering and impure error propagation |
| Float-out | No whole-pass certificate established | Movement order, totality, scope and binder freshness |
| Beta reduction | Local beta infrastructure exists, not full pass coverage | Actual traversal, substitutions and fresh state |
| CSE | No whole-pass certificate established | Repeatability, dominating availability, aliases and scope |
| Eta reduction | No whole-pass certificate established | Callable-head evidence, argument order and partial application |
| Force/delay and pre-lowering | No whole-pass certificate established | Forced-use analysis, sharing, capture and lowering integration |
| Known constructor cases | No whole-pass certificate established | Field order, arity, provenance and evaluator-specific list behavior |
| Scalar/data constant folding | Binary and both data-cons contextual schemas | Complete folding evaluator, builtin allowlist, other constructors and traversal |
| Boolean choices, shape DCE, integer identities, checked round trips | Selected local/contextual schemas | Soundness of post-success shape facts, dominating checks and totality distinctions |
| Boolean recursive result summaries | No whole-pass certificate established | Exact saturation and successful-result induction for recursive functions |
| List destructor/choice fusion | Local finite joins | Alias provenance, field substitution and recursive traversal |
| Checked nonempty branches | Local finite join | Branch fact induction, checked aliases and hygienic replacement |
| Delayed list-choice lowering | Contextual bound-variable schema | Arbitrary input evaluation, selector aliases and traversal |
| Product destructuring | Local pair projection joins | Producer shape, projection-only uses and generated binders |
| Static recursive arguments | No whole-pass certificate established | Recursive call invariant, argument removal, closure capture and Fix lowering |
| Delay sharing/dead Fix | No whole-pass certificate established | Forced-use replacement, total delayed bodies and recursive occurrence checks |
| Application packing | Three-literal-argument local join | General arity, evaluation order, total moved operands and post-lowering placement |
| Builtin sharing/constant pooling | No whole-pass certificate established | Closed reusable state, exact force protocol, typed equality and fresh names |
| Complete production pipeline | Not covered by `verifiedOptimize_refines` | Every actual pass, finite iteration, input validation and both lowering stages |

Many advanced workers use Lean `partial def`, whose implementations are opaque
to kernel reasoning. Whole-function proofs need terminating logical definitions
with usable equations, or a proved connection to a logical specification. A
proof of a similarly named replacement algorithm would not certify the current
executable. Analysis facts and traversal congruence must be connected to the
actual implementation; local rewrite theorems alone are insufficient.

These are concrete proof obligations, not a claim that every current pass is
already sound or automatically provable. There is no semantic obstruction
established for the corrected production frontier rule, but the old weaker
strictness theorem is disproved and cannot be proved without changing its
premises. Additional counterexamples may surface when formalizing other passes.

## Evaluation and reproduction

Pinned native evaluator: `33b812dbcf88f6851286e54cb93a4a443353f94c`.
The prior extra-alternative builtin-list mismatch remains documented in
`MIR-New-Passes-Soundness-Audit.md`; this change does not make the Lean and
native evaluators universally conformant. Native traces are not recorded by
the pinned engine; trace comparison uses the separate Lean step harness.

Run from the repository root:

```sh
lake build tests mir_audit checked_branch_bench Test.MIR.Opt.FormalAxioms Test.MIR.Opt.AdvancedAxioms
.lake/build/bin/tests
.lake/build/bin/tests mir/opt/unit/formal-coverage
.lake/build/bin/checked_branch_bench > /tmp/formal-validator.csv
.lake/build/bin/checked_branch_bench --scaling > /tmp/formal-scaling.csv
cmp /tmp/formal-validator.csv docs/benchmarks/mir-checked-branches.csv
cmp /tmp/formal-scaling.csv docs/benchmarks/mir-checked-branches-scaling.csv
```

The full executable suite passes 470 tests with zero failures, including 18,432
deterministic generated pass/context comparisons. The focused suite passes all
four regressions; the Ptah smoke executable passes its nine checks.
The 63 validator scenarios and
36 scaling scenarios reproduce all four profiles exactly: CPU, memory, script
size and checked outcomes are unchanged by this repair. Existing benchmark
snapshots and manifests are historical and were not overwritten. Fresh evidence
and source checksums are stored in `audits/mir-formal-refinement/`.
