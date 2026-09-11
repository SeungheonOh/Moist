# Completed Inline evaluation-frontier proof

Date: 2026-09-08. Follow-up to `MIR-Formal-Pass-Implementation.md`.

## Completed whole-pass certificates

The remaining impure Inline error-preservation obligation is discharged from
the actual production `firstEvaluationUse` guard. The whole-pass theorems
`Moist.Verified.MIR.inline_refines` and
`Moist.Verified.MIR.verifiedOptimize_refines` now depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Both are enforced by the build-time
allowlist in `Test/MIR/Opt/FormalAxioms.lean`, not merely printed for inspection.

`verifiedOptimize` is specifically ANF normalization, DCE, and canonicalized
Inline. This does **not** certify every pass in the larger production pipeline.
The previously completed scalar/data folding certificates remain intact.

No optimization was disabled, no guard was weakened, and no executable
optimizer behavior was changed to make the proofs pass.

## Proof construction

### Total predecessors

`Moist/Verified/InlineSoundness/Totality.lean` defines a structural `TotalTerm`
certificate and proves its connection to the actual MIR purity analysis.

- `lowerTotal_total` covers every successfully lowered expression accepted by
  `isPure`, including nested sequential lets, constructor fields, force-delay
  cancellation, and both supported builtin type-force depths.
- `TotalTerm.halts` supplies an actual finite successful CEK execution in a
  well-sized environment. It does not infer termination from non-halting.
- `TotalTerm.rename` and `TotalTerm.subst_halts` prove that removing an absent
  binding preserves totality after the necessary de Bruijn index adjustments.
- Variable certificates require positive indices explicitly. The existing
  `closedAt` predicate alone permits index zero; the new totality proof does
  not accidentally treat that invalid lookup as successful.

### Lowering the production guard

`Moist/Verified/InlineSoundness/EvaluationPath.lean` proves:

- The actual `firstEvaluationUse` condition survives `expandFix`, including
  purity evidence for computations before the selected occurrence.
- Successful `lowerTotal`/`lowerTotalLet` compilation translates that condition
  into `EvaluationPath`, tracking sequential bindings and shadowing.
- Combining an evaluation path with the existing exact strict-occurrence
  certificate produces `CheckedPath`. Every skipped predecessor is both
  total and free of the substituted variable. Disagreeing occurrence paths
  are ruled out rather than silently choosing one.

`inlineGate_evaluationPath` packages the complete MIR-to-UPLC guard bridge used
by the production-pass proof.

### Error propagation and contextual refinement

`Moist/Verified/InlineSoundness/FrontierError.lean` proves that substituting an
erroring RHS at a checked frontier also errors, for arbitrary continuations.

The proof constructs the finite execution prefix explicitly: evaluate each
certified predecessor, obtain its returned value, and continue to the selected
occurrence. For let bodies, it proves the returned value is well formed,
extends the runtime environment, shifts the RHS, and preserves its error
under the extended environment. Constructor prefixes are handled left-to-right.

`beta_evaluationPath_ctxRefines` combines this error theorem with the earlier
finite-terminal-outcome argument. Its premises are syntactic certificates and
scope conditions, not an assumed semantic error-frontier property. Inline's
impure branch now calls this theorem instead of the false legacy
`strict_subst_reaches_error` theorem.

## Regression protection

`Test/MIR/Opt/FrontierCertificates.lean` checks nested let/constructor/application
frontiers, force/case frontiers, arbitrary scoped RHS terms, and rejection of
index-zero totality. `StrictFrontier.lean` also proves that the new evaluation
path certificate rejects the known divergent-predecessor counterexample.
These kernel-checked regressions join the standard-axiom allowlist.

The axiom audit covers the totality, lowering, checked-path, error-propagation,
contextual beta, whole Inline, and composed ANF/DCE/Inline theorems. A future
dependency on `sorryAx`, `budget_exhaustion`, or any other nonstandard axiom
fails the build.

## Evidence and boundaries

Validation logs and source checksums are archived separately under
`docs/audits/mir-inline-frontier-proof/`; earlier audit snapshots are retained.

- Full build: 513 jobs, successful.
- Proof/axiom audit: 368 jobs, successful; the whole Inline and composed
  ANF/DCE/Inline certificates contain only standard logical axioms.
- Full runtime suite: 472 passed, zero failed.
- Focused formal-coverage suite: six passed, zero failed.
- Ptah smoke checks: all passed.
- All 63 validator and 36 scaling scenarios across four profiles reproduce
  the existing CSVs byte-for-byte, including CPU, memory, and serialized size.
- `git diff --check` passes.

The contract remains the user-selected ANF/DCE contextual halting/error
refinement through `lowerTotalExpr` and the Lean CEK semantics. This is not a
proof of native-engine correspondence, exact resource caps, trace ordering,
or every optimization pass. The false legacy budget axiom and its obsolete
dependent lemmas still exist in the repository, but are outside the dependency
closure of the newly audited certificates. Their earlier counterexamples are
retained; they must not be reused as trusted optimization lemmas.
