# Packing, hygiene, and list-shape verification

Date: 2026-09-09. Contract: the existing ANF/DCE contextual halting/error
refinement through `lowerTotalExpr`. The complete production pipeline is not
yet certified; this report distinguishes the completed whole transformations
from supporting lemmas and tests.

## Completed production certificates

### General application packing

`Moist.Verified.MIR.packApplications_refines` certifies the actual
`Advanced.packApplications minimum expression`, for every minimum, arbitrary
MIR expressions, all lexical lowering environments, and arbitrary surrounding
UPLC contexts. The proof is not restricted to three arguments, lambda heads,
integer arguments, or successful programs.

The proof establishes that every argument accepted by the existing `isPure`
guard returns a value on every continuation in a well-sized environment. It
then relates ordinary argument frames to pre-evaluated argument frames,
preserving the exact terminal outcome through every remaining continuation.
The constructor packages the same argument values in the same order, and
Case applies those values to the original function. Erroring and diverging
function evaluations are not assumed to terminate.

The production worker now has structural fuel. `packApplicationsFuel_irrel`,
`packApplications_recursive_eq`, and `packApplications_unique` prove that the
node-count entry point performs the complete original spine traversal, with
no skipped rewrites. The reference regression retains the original partial
implementation for independent output comparisons. No packing threshold,
purity condition, or optimization default changed.

`finish_default_refines` additionally certifies the actual `Advanced.finish`
with the existing production execution defaults. `finish_without_sharing_refines`
covers packing enabled or disabled while builtin sharing and constant pooling
are disabled. It does not certify those optional sharing transformations.

### Binder freshening

`Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_lower` proves exact
equality of the actual production hygiene stage's `lowerTotalExpr` output,
including failure to lower, in every lexical environment. Its refinement
corollary is `uniqueOptimizationBinders_refines`.

The proof follows the actual fresh-variable state, the substitution map,
sequential let scope, shadowing, and both variable-origin namespaces. It
establishes fresh-counter monotonicity and an alpha-equivalence certificate
for every expression, list, and binding traversal. The new
`AlphaEq.lowerTotalExpr_eq` bridge handles the real recursive-function
expansion, rather than proving only the Fix-free lowerer correct. No hygiene
algorithm or generated variable identities changed.

This proves hygiene's semantic correctness. It is not a certificate for CSE,
float-out, beta reduction, or another caller's separate rewrite rules.

## Soundness repair found during the work

`Advanced.knownList` formerly accepted any literal carrying a list annotation.
The untyped reference evaluator uses the constant payload, not its annotation,
to determine runtime behavior. For an integer-zero payload with a list
annotation, HeadList fails, but the fused Case can select constructor tag zero
and return a lambda successfully. This violates even the selected weaker
halting/error refinement.

The checker now requires an actual generic-list, data-list, or pair-data-list
payload as well as a list annotation. Valid native representations remain
eligible; the fix does not blanket-disable list optimization.

`Test.MIR.Opt.ListShapeCertificates.annotation_only_list_fusion_not_refines`
is a kernel-checked counterexample to the old rewrite premise. It establishes
the original error, transformed successful closure, and failure of contextual
refinement. `corrected_checker_rejects_forged_list` proves rejection by the
actual repaired predicate for every fuel and fact environment.
`knownList_literal_returns` certifies accepted literal payloads and their
returned CEK values. It does not assert that the Lean and native evaluators
support every specialized list representation identically.

## Proof trust and validation

All new whole-pass theorems, supporting certificates, and the counterexample
are checked by `Test/MIR/Opt/FormalAxioms.lean`. The allowed axiom set remains
`propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, extra axiom, native
proof oracle, or assumed correctness of a production pass was introduced.

The focused suite includes:

- 512 generated trees and 28 depth-64 trees, comparing the complete original
  scalar/data/dead-Fix traversals and packing at minima 0, 1, 2, 3, and 8.
- Exact hygiene lowering comparisons in empty and nonempty lexical scopes.
- General packing with 0–12 arguments, failing and noncallable heads, captured
  lambdas, deferred errors, constructors, and partial builtin states.
- Forged list annotations across seven non-list payloads and six actual
  transformations; valid generic, data, and pair-data list representations.
- Native validator benchmarks measuring CPU, memory, and serialized size.

Final reproducibility evidence is stored separately in
`docs/audits/mir-packing-hygiene-proofs/`. Historical audit directories are not
overwritten. The certificates do not establish native CEK correspondence,
trace equivalence, preservation of arbitrary budget caps, or optimality.

Final results:

- Full build: 528 jobs; explicit proof/axiom audit: 383 jobs.
- Focused formal coverage: 11 passed, 0 failed.
- Full regression suite: 477 passed, 0 failed; all Ptah lifting tests passed.
- All 63 validator and 36 scaling scenarios, each under four profiles,
  reproduce the recorded CPU, memory, and serialized-size rows exactly.
- Source whitespace checks and `git diff --check` passed.

Reproduce from the repository root:

```sh
lake build tests mir_audit checked_branch_bench ptah_test \
  Test.MIR.Opt.FormalAxioms Test.MIR.Opt.AdvancedAxioms
.lake/build/bin/tests mir/opt/unit/formal-coverage
.lake/build/bin/tests
.lake/build/bin/ptah_test
.lake/build/bin/checked_branch_bench
.lake/build/bin/checked_branch_bench --scaling
shasum -a 256 -c docs/audits/mir-packing-hygiene-proofs/checksums.sha256
```

## Remaining whole-pass obligations

General BetaReducePass, eta reduction, float-out, CSE, force/delay with
through-let replacement, delay sharing, pre-lowering Inline, known-constructor
case simplification, shape/fact propagation, list and product transformations,
static recursive arguments, builtin sharing, and constant pooling still need
their whole-pass certificates. Their existing local lemmas and differential
tests are not substitutes for those certificates. The complete production
pipeline theorem remains outstanding.
