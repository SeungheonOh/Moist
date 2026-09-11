# Soundness audit of the accumulated MIR optimizations

This is the earlier audit checkpoint. The subsequent
[formal refinement audit](MIR-Formal-Refinement-Audit.md) fixes an additional
data-folding reference-model counterexample and updates proof coverage under
the user-selected ANF/DCE refinement target. Its results supersede any broader
interpretation of this checkpoint's bounded findings.

## Result

**One new reproducible miscompilation found and fixed.** Known-constructor case
simplification could replace a successful builtin-list case with `Error` in the
pinned native evaluator. No additional counterexample was found for the two
newest checked-branch passes, static arguments, Boolean result summaries,
checked shape rewrites, folding, or allocation passes within this audit's scope.
That is a bounded audit result, not a proof of the entire compiler.

The repair leaves all 99 recorded real-validator/scaling workload budgets and
outcomes unchanged. Both benchmark CSVs reproduce byte-for-byte; the previous
script snapshots and benchmark manifests were not rewritten.

## Finding: evaluator-specific list branch counts

Affected code: `Moist/MIR/Optimize/CaseMerge.lean`, particularly
`knownConstructor`, `selectAlternative`, and `caseMerge`. This pass runs inside
both the main simplification loop and advanced pre-lowering cleanup.

The Lean CEK's `constToTagAndFields` assigns builtin lists a maximum of two case
alternatives. The pinned native evaluator's `caseOnConstant` instead accepts
additional alternatives for lists: it selects branch 0 for a nonempty list or
branch 1 for an empty list. The extra branches are not evaluated. Native Bool,
Unit and Pair handling does impose its own branch-count restrictions, so it is
not correct to remove all constructor-count checks indiscriminately.

Minimal witness, in schematic MIR with a correctly typed integer-list constant:

```text
Case [] [λhead. λtail. 7, 8, trace "unreachable" 9]
```

- Original native execution returns **8**.
- Previous `caseMergePass` emits **Error**, which fails natively.
- Lean CEK rejects the original as well, so a Lean-only differential test would
  approve the incorrect native rewrite.

The same discrepancy affects nonempty lists, data lists, and facts propagated
through dominating list bindings/aliases. It is a genuine optimizer mismatch
against the evaluator used for the production benchmarks; this report does
not infer a network-wide protocol rule from that evaluator.

Before-fix native evidence is preserved in
`audits/mir-soundness/list-extra-branches-before-fix.log`.

### Repair

`KnownCtor` now preserves whether a fact originated from a builtin list.
`caseMerge` retains list cases with more than two alternatives instead of
folding either evaluator's incompatible outcome. Existing Bool/Unit/Pair
restrictions and normal constructor reductions remain intact. This preserves
each evaluator's original behavior without changing the vendored evaluator or
claiming that the Lean CEK and native engine now agree universally.

The regression matrix checks empty/nonempty integer and data lists, 0–4
alternatives, direct literals and bound aliases, and unreachable traces/errors.
All eight production option combinations are included, not only the standalone
case pass.

## Scope and semantic contract

Reviewed the eight modules under `Moist/MIR/Optimize/Advanced/`, their driver,
the compilation entry point, and the purity, freshness, repeatability,
evaluation-frontier, case-simplification and pre-lowering helpers they rely on.
The audit also followed the relevant native builtin/constant-case implementations
and checked the existing local theorem dependencies.

The contract is contextual preservation of terminating values, explicit failure,
divergence and trace order for lexically valid MIR with supported, consistently
typed literals. Numeric budget equality is not part of that contract. A
different cost can change behavior under a particular finite resource cap;
resource regression testing is a separate obligation.

`compileOptimized` validates lexical scope and the required `Fix` lambda before
optimization. Direct MIR producers must still respect literal payload/type and
serialization invariants; that entry point is not a complete validator for
arbitrarily forged literal metadata. Standalone analyses additionally rely on
their documented environments/free-variable assumptions.

### Pass-by-pass reasoning

| Pass family | Required invariant and checked failure mode | Audit result |
|---|---|---|
| Static arguments | Every recursive reference must directly receive the same invariant variable; a worker lambda remains. Check changed arguments, partial calls, closure results, and shadowing. | No new counterexample found. |
| Boolean summaries | A successful result is Boolean, not necessarily terminating. Recursive hypotheses concern saturated calls and unknown formal parameters; branch fields may cause failure, never justify a non-Boolean successful result. | No new counterexample found. |
| Checked list branches | Nonempty facts follow actual discrimination, not source annotations; eager ChooseList arguments do not receive a fact. Fresh identities protect captured values and shadowing. | No new counterexample found. |
| Delayed list choices | Exact builtin force/argument protocol; two literal delays; input evaluated once; NullList retains type rejection. | Native source review, regression tests and existing local CEK joins agree on the rewrite. |
| Shape DCE and integer identities | Post-success shape is distinct from producer totality; prefix facts govern deletion. Wrong runtime types, tracing operands and checked producers remain observable. | No new counterexample found. |
| Checked round trips | The dominating validating producer remains evaluated. Only justified inverse pairs are used; list/map construction-to-destruction is not generally assumed to preserve runtime list type metadata. | No new counterexample found. |
| List/pair structural rewrites | Positive producer evidence, correct field order, original failure behavior, hygienic component names and conservative use classification. | No new counterexample found in these passes; the interacting case simplifier had the finding above. |
| Scalar/data folding | Allowlisted builtins, exact force protocol, literal type checks, UTF-8 validation, constructor-tag bounds, and bounded folded output. | Native boundary tests pass. |
| Delay sharing/dead Fix | Only total nonlogging delayed bodies move; only forced uses change; nonrecursive Fix removal retains a lambda. | Contextual and trace tests pass. |
| Packing/sharing/pooling | Moved arguments are total; hoisted states are closed, correctly forced and unsaturated; literal equality includes types; fresh IDs avoid capture. | All option combinations and hostile partial-builtin arguments pass. |
| Known constructor cases | Concrete runtime fields, strict field evaluation, alias provenance and target-compatible branch counts. | Extra-list-alternative miscompilation fixed. |
| Supporting CSE/inlining | Repeatability is not mere equal return value; unknown/logging calls cannot disappear. Moving an impure producer requires the first evaluation frontier. | Source review and accumulated differential tests found no additional counterexample. |

## High-risk analysis details

### `checkedBranchWalk` and `lowerDelayedChoicesWalk`

**Purpose:** These traversals remove repeated list selection/deconstruction work.
They must not turn an unknown parameter into a trusted list simply because a
source-language type claims it is one.

**Inputs and assumptions:** The expression is valid MIR; the environment holds
dominating immutable bindings; nonempty facts identify evaluated list values;
lexical identities have been freshened; and native HeadList/TailList fields
agree with native Case fields. None of these assumptions grants totality to an
arbitrary producer.

**Outputs and effects:** The traversals return MIR and perform no external IO.
They preserve discriminator/input evaluation and branch effects while reducing
projection or delay/application work; exact resource costs can change.

**Block analysis:** Why preserve the discriminator? Native Case also accepts
non-list runtime shapes, whereas NullList/ChooseList reject them. Why restrict
the ChooseList fact to a literal delay? Its arguments evaluate before the
builtin validates the list. How do facts survive a captured closure? The
captured value is immutable and unique binder identities distinguish later
worker parameters from that value. How are effects ordered? Adjacent head/tail
projections are replaced only after nonempty evidence, and arbitrary input
expressions are neither duplicated nor moved across branch bodies.

**Dependencies:** `uniqueOptimizationBinders` supplies lexical hygiene;
`checkedHead` resolves only bounded dominating aliases; `mapChildren` preserves
syntax boundaries; lowering and native list/Case implementations establish the
field-application order. Boundary risks examined were wrong runtime types,
strict/eager arguments, and mismatched builtin protocols.

### `booleanResultCore` and `simplifyWithFacts`

**Purpose:** Result summaries permit cheaper Boolean control flow even for
recursive helpers. Their role is to describe a value after successful
evaluation, not to erase a computation that might fail or diverge.

**Inputs and assumptions:** Expressions have valid lexical identities;
environment entries describe dominating bindings; parameters of a recursive
summary are initially unknown; a recursive hypothesis applies only to exact
saturation; and supported Boolean builtins return a Boolean only after their
runtime checks succeed.

**Outputs and effects:** The analysis returns a conservative Boolean and does
not execute the source computation. Consumers may replace control-flow syntax,
but must retain an effectful/failing producer; costs may change.

**Block analysis:** Why exclude partial and over-applied workers? Their results
may be functions or failures, not the checked terminal result. Why hide formal
parameter facts on recursive analysis? One call's initial argument does not
describe later recursive arguments. How is the recursive claim justified?
Reason by finite successful evaluation of saturated calls, not by assumed
termination; base results and every successful recursive result must satisfy
the same shape property. How are errors retained? Shape-based deletion uses
separate totality evidence from the prefix environment, or retains a strict
binding for the producer. Case alternatives with runtime fields can fail when
applied; that does not produce an arbitrary successful value from an already
Boolean alternative.

**Dependencies:** `resultHead` and builtin protocol checks recover bounded
provenance; `knownBooleanLocal` supplies direct facts; `totalWithFacts` controls
deletion; `shapeDCE` establishes binder hygiene. Boundary risks examined were
changed recursive parameter types, closure capture/alias reuse, and errors or
divergence hidden by identical branches.

### `knownConstructor` and `caseMerge`

**Purpose:** These functions turn actual constructor evidence into branch
selection without guessing field arity from branch lambdas. They also mediate
between the runtime model and the generated code, which is where the newly
confirmed mismatch occurred.

**Inputs and assumptions:** Facts must dominate the case; fields are actual
runtime fields; non-atomic constructor fields execute first; constants carry
consistent type annotations; and any compile-time rejection must agree with
the target runtime rather than merely one reference evaluator.

**Outputs and effects:** The pass returns transformed MIR plus a change flag.
Field evaluations are retained and branch applications receive the original
fields in order. Uncertain list branch counts now remain runtime cases instead
of becoming unconditional errors.

**Block analysis:** Why record list provenance separately? Lists and Booleans
can share tag/count information but have different native extra-branch rules.
Why retain, rather than choose, the native result? Folding the native result
would instead change Lean CEK failure behavior. How do aliases retain the guard?
The list-origin flag travels with `KnownCtor` through dominating bindings.
How are shadows prevented? The public pass freshens binders and filters facts
that would refer to a newly bound identifier or its free fields.

**Dependencies:** `constToTagAndFields` supplies reference-model structure;
`selectAlternative` implements normal count checks; `caseMergeBinds` propagates
facts; the native `caseOnConstant` is the independently inspected target.
Boundary risks examined were model disagreement, silently skipped field effects,
and stale alias facts.

## Executable evidence

Final validation: **466 full-suite tests passed, zero failed**; all nine Ptah
smoke checks passed. The verified optimizer and 21-lemma axiom audit build.

`Test/MIR/Opt/SoundnessAudit.lean` adds **33,825 candidate comparisons**: 17
individual transformations and all eight production option combinations across
1,353 closed test contexts. Each compares native value/failure and, separately,
Lean CEK value/failure/trace observations against unoptimized execution.

| Corpus | Contexts |
|---|---:|
| Deterministic generated terms in nine observation contexts | 576 |
| Higher-order recursive result shapes and changed arguments | 432 |
| Captured values, repeated aliases and lexical shadowing | 20 |
| Hostile partial-builtin states and forced states | 200 |
| List case branch counts, including aliases | 40 |
| Arithmetic, UTF-8 and constructor-tag boundaries | 85 |

Budget exhaustion, memory exhaustion, encoding/decoding errors and unbound
variables are treated as inconclusive test failures, not ordinary equivalent
script rejection. Divergence checks remain in the earlier recursion and
checked-branch suites. The native Trace implementation does not currently
collect logs, so this report does **not** claim independent native trace
verification; trace-order evidence comes from the Lean CEK harness.

## Remaining assurance limits

- The 21 advanced local CEK lemmas still build with only `propext` and
  `Quot.sound`. They do not prove the traversals, fact analyses, lowering,
  serialization or full native compiler correct.
- The previously reported `Moist.Verified.budget_exhaustion` axiom remains
  false for its unbounded transition relation. The existing verified inlining
  certificate depends on it; this audit does not repair or rely on that axiom.
- The list-case witness demonstrates why a local Lean proof is not by itself
  native conformance evidence. Other model/representation differences are not
  assumed absent merely because this corpus passes.
- Universal CPU/memory non-increase and global optimality are not established.
  All 99 retained benchmark workloads reproduce unchanged after the fix.

## Reproduce

```sh
lake build tests checked_branch_bench ptah_test \
  Moist.Verified.VerifiedOptimize Test.MIR.Opt.AdvancedAxioms
.lake/build/bin/tests mir/opt/unit/soundness-audit
.lake/build/bin/tests
.lake/build/bin/checked_branch_bench > /tmp/audit-validator.csv
cmp /tmp/audit-validator.csv docs/benchmarks/mir-checked-branches.csv
.lake/build/bin/checked_branch_bench --scaling > /tmp/audit-scaling.csv
cmp /tmp/audit-scaling.csv docs/benchmarks/mir-checked-branches-scaling.csv
.lake/build/bin/ptah_test
shasum -a 256 -c docs/audits/mir-soundness/checksums.sha256
```

Native evaluator pin: `33b812dbcf88f6851286e54cb93a4a443353f94c`.
The shared worktree's prior changes and historical benchmarks remain intact;
no commits, pushes or evaluator upgrades were performed.
