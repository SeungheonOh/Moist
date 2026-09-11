# Additional MIR pass certificates

Date: 2026-09-08; coverage updated 2026-09-09. Continuation of `MIR-Inline-Frontier-Proof.md`.
Contract: the user-selected contextual halting/error refinement through
`lowerTotalExpr`, with the same scope as the ANF/DCE certificates.

## Newly completed whole pass

`Moist.Verified.MIR.eliminateDeadFix_refines` proves the actual
`Advanced.eliminateDeadFix` transformation for every MIR expression and lexical
lowering environment. This is not a bounded test or a proof of one sample.

The local proof unfolds the real recursive-function lowering into its
call-by-value fixed-point wrapper. It then:

1. Removes the unused recursive binding using a proved pure dead-application
   refinement; the recursive thunk is a value, not an assumed terminating call.
2. Reduces the wrapper's self-application using the certified pure beta rule.
3. Removes the remaining unused self binding. Freshness is proved against both
   the original function and its expanded body, preserving captured variables.
4. Lifts the rule through the complete MIR traversal, including valid nested
   recursive functions, deferred bodies, constructor fields, and sequential lets.

An erroring function body stays deferred until application. Lambda shadowing
of the recursive name is handled correctly. Functions that actually use their
recursive binding are retained. As with the existing certificates, failed
source lowering is treated by the definition of `MIRCtxRefines`; this does not
assert native validity for malformed `Fix` inputs.

The executable now separates `eliminateDeadFixRoot` from the already certified
total bottom-up traversal. `eliminateDeadFix_recursive_eq` proves exactly the
original bottom-up recursive equation. The new general
`rewriteBottomUp_unique` theorem shows that this equation uniquely determines
the output; the node-count fuel does not omit rewrites. The test reference
retains the previous recursive traversal shape for independent output checks.

## Newly completed supporting proofs

`Moist/Verified/BuiltinStateSoundness.lean` certifies the real safety checks
shared by eta reduction, pre-lowering, and builtin-state sharing:

| Theorem | Established fact |
|---|---|
| `builtinRemainder_returns` | Every accepted expression returns the exact checked unsaturated builtin state, with evaluated arguments, on every continuation |
| `builtinRemainder_halts` | The accepted partial state actually terminates successfully |
| `builtinRemainder_expandFix` | Acceptance and the remaining argument protocol survive recursive-function expansion |
| `isTotalPreLowerValue_halts` | Every successfully lowered value accepted by the actual pre-lowering totality predicate halts |
| `isTotalPreLowerValue_no_error` | Such a value cannot produce an explicit CEK error |
| `isCallableValue_returns` | An accepted head returns a lambda or a builtin state whose next argument is a value argument |

These proofs track type forces, value arguments, evaluation order, and the
remaining builtin signature. They never treat a saturated call as an
unsaturated value. Partial states may contain arguments that would fail a
later saturated call; the certificate does not claim those future calls are
valid. The original builtin allowlist and safety behavior are unchanged.

These are **supporting analysis certificates**, not whole-pass certificates
for eta reduction, sharing, or pre-lowering. In particular, totality alone does
not prove a scope-moving transformation correct.

All new certificates are in `Test/MIR/Opt/FormalAxioms.lean`'s build-time
allowlist: only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
No new axiom, `sorry`, native compiler trust, or assumed pass-correctness
premise was introduced. Existing Inline, ANF/DCE/Inline, and folding certificates
continue to pass the same audit.

## Current whole-pass coverage

The 2026-09-09 packing, hygiene, and list-shape work is described in
`MIR-Packing-Hygiene-Proofs.md`; the validation snapshot below remains the
2026-09-08 checkpoint.

| Pass or composition | Status |
|---|---|
| ANF normalization | Certified |
| DCE | Certified |
| Canonicalized Inline | Certified, including the impure evaluation frontier |
| Scalar constant folding | Certified |
| Data-constructor folding | Certified |
| Nonrecursive Fix elimination | Newly certified |
| Production binder freshening | Certified exact lowering, including recursive functions |
| ANF → DCE → Inline; scalar → data folding | Certified compositions, not the full production pipeline |
| General BetaReducePass | Local beta/let rules available; its own complete traversal and hygiene integration remain |
| Eta reduction | Callable-head analysis now certified; extensional eta refinement and traversal remain |
| Float-out and CSE | Binding-motion, dominance/alias environments, hygiene integration, and full traversals remain |
| Force/delay cancellation and delay sharing | Forced-use replacement, capture avoidance, and deferred/eager substitution proofs remain |
| Pre-lowering Inline | Total-value analysis now certified; substitution loop, policy guards, and full wrapper remain |
| Known-constructor cases; checked shapes and result summaries | Producer/branch facts, aliases, recursive result invariants, and full traversals remain |
| List/branch fusion and product destructuring | Local joins exist; fact environments, generated binders, and full traversals remain |
| Static recursive arguments | Recursive-call invariant and changed closure environment remain |
| Application packing | Certified for every minimum and arbitrary arity, including complete spine traversal |
| Default final allocation stage | Certified with production defaults; optional sharing/pooling remain uncertified |
| Builtin sharing and constant pooling | Builtin-state safety now certified; matching, shared bindings, and hygiene remain |
| Complete production pipeline | Not yet certified |

Eta involving a builtin also needs a proof technique that relates a lambda
wrapper to a builtin value. The current step-indexed `ValueRefinesK` matches
those shapes separately, so the new callable-head theorem is a prerequisite,
not sufficient by itself to instantiate that existing logical relation.

## Validation

The focused tests compare all three total traversals against their previous
recursive shape on 512 generated trees and 21 depth-64 trees. Additional
regressions cover dead-Fix capture, shadowing, deferred failure, application,
and rejection of saturated, incorrectly forced, or effectful builtin states.

Validation completed successfully:

- Full build: 515 jobs; explicit proof/axiom audit: 370 jobs.
- Focused formal-coverage suite: 8 passed, 0 failed.
- Complete regression suite: 474 passed, 0 failed; Ptah lifting tests passed.
- All 63 validator scenarios and 36 scaling scenarios, each under four profiles,
  reproduce the recorded CPU, memory, and serialized-size rows exactly.
- `git diff --check` passed.

Full build, proof-audit, regression, and native benchmark evidence is archived
under `docs/audits/mir-additional-pass-proofs/`, with source checksums. Previous
audit directories remain historical snapshots. Validator comparisons include
CPU, memory, and serialized size across all four existing profiles; no
size-versus-execution trade-off or new optimization default was introduced.

The certificates still do not prove native CEK correspondence, Flat decoding,
trace preservation, exact resource bounds, or global optimization optimality.
