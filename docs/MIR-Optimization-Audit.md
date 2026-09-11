# MIR optimization audit

Historical audit checkpoint. For the maintained compiler guide and current
proof inventory, see [MIR optimization maintenance](MIR-Optimization.md).

The follow-up production implementation, additional repairs, and updated
verification results are in `docs/MIR-Optimization-Implementation.md:1`.

## Status and scope

Audited the production MIR optimizer, its pre-lowering cleanup, freshness and
scope helpers, relevant lowering behavior, and the existing verified subset.
The base is GitHub `origin/main`, commit `cc23952`. Work is isolated in
`/Users/sho/fun/moist-mir-audit`; the original checkout and its uncommitted SMT
work are preserved. The MIR sources and tests matched the original checkout
when inspection began.

The per-stage execution, scope, state, and dependency record is in
`docs/MIR-Optimization-Context.md:1`.

**Runtime miscompilations below are repaired and regression-tested. The full
optimizer is not formally certified. An existing false proof axiom remains
an explicit unresolved finding, pending a decision on the proof API.**

The intended semantic contract is preservation of results, explicit failures,
evaluation order, captured environments, and trace messages for closed,
well-formed MIR, or open MIR evaluated in an environment providing its free
variables. Valid recursive nodes have the form `Fix f (Lam x body)`.
Cost equivalence and universal CPU/memory non-increase are not established.

## Confirmed findings and repairs

| Finding | Original counterexample / consequence | Repair |
| --- | --- | --- |
| Eta argument reversal | Applying `λx y. subtractInteger y x` to 10 and 3 changed -7 to 7. The old unit test explicitly expected the incorrect rewrite. | Remove the reversed-parameter matcher; reduce one justified lambda layer at a time. |
| Eta violates call-by-value | An unused `λx. Error x` became an eager error. Forcing `λx. (delay 42) x` changed failure into success. Unknown heads could be non-functions. | Require a syntactically justified callable value, including correct builtin force/application protocol. Preserve unknown heads and deferred work. |
| Fix shape destruction | Eta could turn `Fix f (Lam x (addInteger x))` into `Fix f addInteger`, which lowering rejects. Float-out could leave a Let between Fix and its required lambda. | Preserve the outer Fix lambda. Float its body bindings only when independent of both the recursive name and parameter. |
| Case arity inference | CaseMerge treated the number of branch lambdas as the runtime field count. Under-/over-applied alternatives changed failures, returned functions, or continuation execution. | Derive facts only from concrete constructors/constants or their dominating bindings. Apply exactly the real fields using ordinary MIR applications. Unknown arity remains unknown. |
| Case strictness and constant shape | Dropping extra fields or selecting a branch too early could suppress field failures/traces; constant cases also have alternative-count restrictions. | Evaluate all non-atomic constructor fields once before branch selection/application, including missing-branch cases. Preserve constant-specific constructor limits. |
| Scope capture | Force-delay substitution under a shadowing lambda changed a captured 1 into 2. CSE replacement and case float-out could capture unrelated bindings. Split inlining was unsafe without its global-binder convention. | Establish globally unique binders at scope-moving boundaries, preserve free identities, and use the hygienic inline entry point. Keep the raw recursive inliner as an invariant-requiring worker. |
| Substitution crosses a later rebinding | Substituting a free x into `let x = 1; x = 2; constr [a,x]` renamed occurrences past the second binder, changing the second field from 2 to 1. | Rename the remaining bindings and body together with the scope-aware renameLet helper. This fixes the underlying substitution operation, including simultaneous renameMany. |
| Fresh-ID collisions | Fixed starts of 1000/5000/10000 could collide with existing generated names, including the Z-combinator's fresh binders. | Reserve each relevant fresh supply above the complete input/prepared expression's maximum UID. |
| CSE suppresses tracing | A repeated application/force may log even if it returns the same value. An unknown function may alias Trace or a logging closure. | Add conservative repeatability analysis through dominating aliases. Retain unknown/logging calls; keep sharing safe allocations and known nonlogging builtin calls. |
| Inlining reorders effects | `let a = trace "first" 1; b = trace "second" 2; constr [b,a]` could reverse messages. An eager error could move behind a trace. | Require the unique occurrence to be at the evaluation frontier, allowing only proven-pure predecessors. Apply the same condition to pre-lowering beta/let substitution. |
| Alpha equivalence ignores origin | A generated free variable and source binder with the same numeric UID were confused by `Expr.alphaEq`. | Key environments by full VarId identity, not UID alone. This protects fixed-point detection. |
| Misleading progress flag | An unused/shadowed delay binding reported a force-delay change despite replacing no use. | Require an actual free occurrence before reporting through-let cancellation. |

Primary regression coverage is in `Test/MIR/Opt/Soundness.lean:76`.
The common safety analyses are in `Moist/MIR/Optimize/Safety.lean:9`.

## Critical unresolved proof finding

`Moist/Verified/Definitions/BudgetExhaustion.lean:20` asserts:

```text
For every unbounded CEK state:
  if it never reaches halt, it reaches error.
```

This is false for the relation it actually uses. That relation iterates
`Moist.CEK.step`, which has no budget state or budget-exhaustion transition.
A finite execution budget in a different evaluator does not justify adding
an error transition to this unbounded relation.

`Test/MIR/Opt/BudgetModel.lean:48` proves the negation of this axiom's exact
proposition. It constructs a five-state self-application cycle, proves that
every step remains in the cycle, and derives that neither halt nor error is
reachable. The counterexample module imports only the base definitions, not
the offending axiom. This is a machine-checked counterexample, not an inference
from a timeout. Its axiom audit contains only Lean's foundational propext and
Quot.sound, not the budget axiom or a compiler-backed decision procedure.

The current axiom dependency audit reports:

- `anfNormalize_refines`: propext, Classical.choice, Quot.sound.
- `dce_refines`: those plus Lean.ofReduceBool and Lean.trustCompiler.
- `inline_refines` and `verifiedOptimize_refines`: those plus
  **Moist.Verified.budget_exhaustion**.

Consequently, successfully compiling the verified inlining theorem is not a
sound certificate. No new axiom or sorry was added by the runtime repairs.
The existing proof scripts were adapted to the stronger inlining gate and
reserved fresh state, but their existing assumption is not thereby discharged.

Recommended full repair: prove ordered/frontier substitution directly over
the unbounded semantics, preserving the distinction between divergence and
explicit error. Alternatively, introduce a genuinely budget-indexed machine
and state the appropriate budget relation in every affected theorem. Merely
renaming or reasserting the old axiom is not a repair. Exposing the assumption
as an explicit unproved API condition would remove the global logical axiom
but would still not constitute an unconditional inlining proof.

The production optimizer also contains passes outside `verifiedOptimize`.
That verified subset must not be presented as a proof of FloatOut, CSE,
CaseMerge, eta, force-delay, or the complete production pipeline.
Its pure CEK observation relation does not record Trace messages either;
trace preservation is exercised separately by the regression harness.

## Verification

- `lake build tests mir_audit Moist.Verified.VerifiedOptimize`.
- `.lake/build/bin/tests`: the complete MIR test tree, including on-chain
  compilation/evaluation and the new audit suites: **411 passed, 0 failed**.
- `.lake/build/bin/mir_audit`: focused semantic regressions and differential
  testing: **29 passed, 0 failed**, plus compilation of the budget-model
  counterexample.
- 256 deterministic generated closed terms, each tested in six observing
  contexts against twelve individual/composed transformations:
  **18,432 differential comparisons**.
- Separate constructor-field/lambda-arity matrix for counts zero through
  three, targeted recursion, lexical shadowing, mixed origins, low fresh
  starts, direct/aliased traces, eager field failures, errors preceding divergent
  continuations, and trace-driver parity.

The differential generator deliberately includes malformed applications,
errors, delays, constructors, partial builtin states, and reused identifiers.
Its generated terms are finite nonrecursive syntax without arbitrary
self-application; dedicated tests exercise Fix separately. This is bounded
testing, not exhaustive proof over all programs or builtins.

Trace checks instrument the existing pure CEK step function at actual Trace
builtin execution. They do not replace the evaluator with an optimizer-shaped
interpreter. The pinned Zig implementation currently has a TODO rather than
recording Trace messages, so it cannot independently validate trace order.
UPLC Trace is observably logging in the
[official builtin implementation](https://plutus.cardano.intersectmbo.org/haddock/1.63.0.0/plutus-core/src/PlutusCore.Default.Builtins.html).

The original suite referenced a nonexistent `Test.MIR.Lower.FixTotal` module.
Its dangling import/registration was removed; existing real tests were retained
and new suites registered. Several old purity expectations and 17 ANF snapshots
already disagreed with the pre-audit implementation. Those expectations now
reflect the conservative predicate rather than making purity unsound to satisfy
the tests.

Golden output was regenerated outside the checkout, compared, and applied
selectively. All changed evaluation fixtures retained exactly the same
result/error sections; their differences are CPU/memory accounting. Structural
optimizer snapshots now reflect the sound rewrites and hygienic names.

## Measured cost tradeoffs

These numbers compare the repository's original recorded goldens with the
corrected compiler on the checked-in evaluator, not a new independent
ledger benchmark. Correctness guards can cost more than the old unsafe
rewrites. Savings are not claimed across the board.

| Fixture | CPU before → after | Memory before → after |
| --- | --- | --- |
| factorial_10 | 8,453,912 → 8,501,912 | 32,162 → 32,462 |
| sop_struct_access | 4,252,702 → 4,588,702 | 14,494 → 16,594 |
| data_nested_match | 48,100 → 16,100 | 400 → 200 |
| rdm_gate_ok | 1,524,199 → 1,874,191 | 4,990 → 6,322 |
| nft_ok | 2,531,822 → 2,929,814 | 8,952 → 10,584 |

Retest deployment budgets for affected validators. In particular, restoring
sharing without effect/shape evidence would recover some costs by reintroducing
the very unsoundness this audit removes.

## Additional optimization opportunities

The additional timed investigation, measured prototypes, and a newly confirmed
Lean/native Data-projection discrepancy are recorded in
`docs/MIR-Optimization-Opportunities.md:1`. That report supersedes the preliminary
candidate assessment below; experimental passes remain outside production.

| Candidate | Concrete implementation | Required safety condition | Priority |
| --- | --- | --- | --- |
| Partial-builtin purity | Promote correctly forced, unsaturated builtin states into a separately proven total-allocation analysis; reuse builtinRemainder. | Validate the next argument kind at each spine step; arguments must themselves be safe. Never infer saturation safety from arity alone. | High |
| Effect and value-shape propagation | Track callable, delayed, builtin-state, constructor-tag/arity, and may-log facts through let bindings. | Invalidate facts on rebinding; unknown external arguments remain unknown. Constructor arity from a source type alone is not evidence for malformed on-chain inputs. | High |
| Guarded constant folding | Fold a small whitelist of closed, fully applied integer/boolean builtins; reuse the selected CEK semantics. | Preserve failures, force protocol, result type, and traces. Bound compiler work and result size. | High |
| Known-branch simplification | Extend the repaired concrete-constructor pass to proven scalar predicates and selected IfThenElse/ChooseList branches. | Retain CBV evaluation of all eagerly evaluated arguments; don't erase an error just because its result is unused. | Medium |
| Mixed-use force-delay cancellation | Cancel individual Force uses even when the same delayed value has bare uses; retain its binding for the latter. | Hygienic substitution and unchanged forcing multiplicity; cap duplicated body size. | Medium |
| Linear-time DCE | Maintain a right-to-left live-variable set instead of recomputing freeVars of each surviving suffix. | Erase a binder at the correct sequential scope point; retain every impure binding and its dependencies. | High, low semantic risk |
| Indexed CSE | Hash alpha-normalized expressions and index dominating repeatable bindings. | Include origin, binding depth, literal type, and builtin protocol; preserve shadow invalidation and the logging guard. | Medium |
| Avoid ANF/inline oscillation | Keep a stable let graph or use incremental worklists rather than repeatedly re-ANFing/re-freshening the whole tree. | Fixed-point evidence must cover all rewrites and fresh names, not just unreliable changed flags. | Medium |
| Cost-aware float-out | Estimate allocation/CPU costs and branch/closure multiplicity before hoisting safe expressions. | Pure speculation is not necessarily budget-nonincreasing, especially in unselected branches. | Medium |

Known-constructor specialization is already implemented as part of the case
correctness repair. The remaining candidates are proposals, not silently
enabled passes. Algebraic identities such as `x + 0 → x` are unsafe without
proof that x is an integer, because the original operation performs a runtime
type check.

## Integration

No remote branch was pushed. The original dirty checkout was not reset,
stashed, switched, or merged. Commit signing was canceled; permission to use
unsigned local commits and the destination branch remain pending.

Suggested granular integration groups: eta/origin correctness; constructor
specialization; scope/freshness/Fix shape; effect-aware CSE and ordered inlining
with proof adaptations; regression harness/fixtures; audit documentation and
the independent proof counterexample.
