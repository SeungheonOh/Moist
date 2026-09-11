# Implemented whole-pass MIR refinement proofs

Date: 2026-09-08. Follow-up to `MIR-Formal-Refinement-Audit.md`.

Subsequent update: [the Inline frontier proof is now complete](MIR-Inline-Frontier-Proof.md).
Both `inline_refines` and `verifiedOptimize_refines` now pass the standard-axiom
allowlist. The remaining-gap discussion below records the earlier checkpoint,
not their current proof status.

## Implemented certificates

Two actual production passes now have complete `MIRCtxRefines` theorems under
the user-selected ANF/DCE contract:

| Executable pass | Whole-pass theorem | Coverage |
|---|---|---|
| `Advanced.constantFold` | `Moist.Verified.MIR.constantFold_refines` | Every MIR input and every lexical lowering environment; complete scalar evaluator and traversal |
| `Advanced.foldDataConstructors` | `Moist.Verified.MIR.foldDataConstructors_refines` | Every MIR input and every lexical lowering environment; all six constructor patterns, representation checks, output-size gate and traversal |
| Their adjacent production composition | `Moist.Verified.MIR.constantFoldingSegment_refines` | Scalar folding followed by data-constructor folding |

These are not just proofs of sample arithmetic expressions or local redexes.
They mention the executable pass functions directly and include closure bodies,
delays, applications, constructor fields, case alternatives, sequential lets,
and valid recursive `Fix` bodies. They preserve successful proof-model lowering
and the contextual halting/error refinement used by ANF/DCE.

The declarations pass the build-time axiom allowlist in
`Test/MIR/Opt/FormalAxioms.lean`: only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. No `sorry`, `native_decide`, compiler-trust axiom,
budget-exhaustion assumption, or semantic premise supplied by the caller is
needed for either whole-pass theorem.

## Reusable traversal implementation

`Advanced.mapChildren` is now a total definition. A total, fuel-indexed
`Advanced.rewriteBottomUp` replaces the opaque partial recursion in these two
passes. Each public pass supplies `exprSize expression` as its fuel.

`AdvancedTraversal.lean` proves:

- `rewriteBottomUp_refines`: any locally refining rewrite that retains lambda
  nodes lifts to a whole MIR traversal. This includes binding-list congruence
  and the canonical `Fix` lowering wrapper; malformed `Fix` inputs have the
  same vacuous failed-source-lowering treatment as the existing DCE theorem.
- `rewriteBottomUp_fuel_irrel`: fuels at or above the input's node count give
  identical results.
- `rewriteBottomUp_complete`: the selected fuel satisfies the exact recursive
  bottom-up equation. Fuel does not truncate the traversal or turn difficult
  cases into identity optimizations.

The bounded traversals are compared against the original recursive traversal
shape on 512 deterministic generated trees and 14 deeply nested trees, with
both folding passes checked on every tree. Production rewrite behavior is
retained; no pass was disabled to obtain a proof.

## Constant evaluation and data rules

`constantValue_evaluates` proves that every successful result of the executable
scalar evaluator corresponds to actual CEK evaluation, for every continuation
and environment. It covers partial builtin states, the force protocol,
left-to-right application, argument accumulation and saturated builtin results.
Rejected inputs are retained by the pass. The proof does not assume that all
builtins terminate or that an unsuccessful computation is an error.

`DataFoldingSoundness.lean` covers `IData`, `BData`, `MkNilData`, `MkCons`,
`ListData`, and `ConstrData`. It proves the literal extraction checks and
generic-list conversion facts used by those rules. Both generic and specialized
data-list representations remain distinct, preserving the repair from the
previous audit. The existing constructor-tag and 1024-byte gates remain in the
executable; rejection falls back to the unchanged expression.

The small internal folding/extraction helpers and CEK `constListToData` now have
public Lean names so the proofs can refer to their actual definitions. Their
computational behavior is unchanged. Proof modules are not imported by the
production optimizer.

## Impure Inline progress and remaining gap

The pure/value branch of `InlineSoundness.lean` no longer detours through the
invalid impure strictness theorem when an occurrence happens to be strict.
It uses actual totality witnesses for pure expressions or the `Fix` lambda
wrapper for all occurrence counts.

The proof-side `InlineGate` now includes exactly the production
`firstEvaluationUse` condition; the old guard-dropping helper has been removed.
`InlineGate_impure_frontier` proves that accepting an impure, non-value RHS
entails this frontier condition.

`InlineSoundness/Frontier.lean` provides:

- `outcome_of_terminal`: if a computation with a continuation actually halts
  or errors, the inner computation must have returned or errored. This uses
  a finite derivation and stack lifting, not a universal termination axiom.
- `same_env_beta_frontier_refines` and `beta_frontier_ctxRefines`: correct
  single-occurrence beta-refinement theorems given an explicit error-frontier
  property. The halt case uses the actual RHS return witness; the error case
  distinguishes an RHS error from a later continuation error.

The main Inline proof now uses this corrected terminal-outcome argument.
**Inline is still not a sound whole-pass certificate:** its final error-frontier
obligation is currently discharged by the old, overly broad
`strict_subst_reaches_error`, which depends on `budget_exhaustion`. The remaining
work is to derive that obligation from the retained MIR `firstEvaluationUse`
evidence through lowering, including total predecessors and binder shifts.
The new contextual theorem's explicit premise is an obligation, not a renamed
axiom or a claim that the production guard has already been proved sufficient.
The axiom audit continues to report Inline and `verifiedOptimize_refines` as
dependent on the false legacy axiom and excludes them from the sound allowlist.

## Verification and boundaries

The full suite passes 472 tests with zero failures, including all six focused
formal-coverage tests. The native benchmark run reproduces
the existing 63 validator and 36 scaling scenarios across all four profiles
byte-for-byte: CPU, memory and serialized sizes are identical. No budget
trade-off or size-oriented default was introduced. The nine Ptah smoke checks
also pass. Full-suite and proof-build logs are archived with the current source
checksums under `audits/mir-whole-pass-proofs/`.

```sh
lake build tests mir_audit checked_branch_bench Test.MIR.Opt.FormalAxioms Test.MIR.Opt.AdvancedAxioms
.lake/build/bin/tests
.lake/build/bin/tests mir/opt/unit/formal-coverage
.lake/build/bin/checked_branch_bench > /tmp/whole-pass-validators.csv
.lake/build/bin/checked_branch_bench --scaling > /tmp/whole-pass-scaling.csv
cmp /tmp/whole-pass-validators.csv docs/benchmarks/mir-checked-branches.csv
cmp /tmp/whole-pass-scaling.csv docs/benchmarks/mir-checked-branches-scaling.csv
```

These certificates target `lowerTotalExpr` and the Lean CEK relation, not a
formal equivalence to production `lowerExpr`, Flat decoding, the native engine,
trace order, or fixed resource caps. Other optimization passes and the complete
production pipeline remain outside the newly certified coverage. Earlier
benchmark/proof manifests remain historical snapshots and are not overwritten.
