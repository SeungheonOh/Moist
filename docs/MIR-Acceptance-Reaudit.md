# MIR acceptance-preservation re-audit

Date: 2026-09-25. Production source: `858b4676a81f93e8c135228d6608964c5b4e98ca`.

## Result and contract

No additional success/failure-changing rewrite was found in the reviewed passes
or the new differential corpus. No production optimization, option default,
evaluator, or existing formal certificate was changed. This revision adds
repeatable verification rather than changing passes without a counterexample.

The requested property is that a program and its optimized version, given the
same runtime inputs, either both evaluate successfully or both fail. The audit
checks both directions; turning rejection into acceptance is not allowed.
The domain is lexically valid MIR with valid `Fix` bodies and supported,
consistently typed/serializable literals. `compileOptimized` rejects invalid
scope and `Fix` structure before a pass can hide them.

Budget exhaustion is an inconclusive test, not semantic rejection. Both sides
use the same generous limits; their consumed budgets need not be identical.
An optimization that changes cost can change acceptance at a particular tight
budget boundary. Neither this audit nor the existing refinement certificates
claim equality at every finite budget cap.

This is source review plus bounded differential verification, **not a universal
formal proof of every pass or the complete compiler**. Existing whole-pass
proof coverage remains in [MIR-Remaining-Pass-Proofs.md](MIR-Remaining-Pass-Proofs.md).
The prior halting/error refinement certificates have not been relabeled as a
new theorem about the production evaluator.

## Pass inventory and reviewed failure conditions

All rows below participate in the differential checks. Supporting analyses were
reviewed at their consumers: `isPure`, `builtinRemainder`, `isRepeatable`,
`firstEvaluationUse`, head-alias resolution, post-success result summaries,
free-variable analysis, and fresh-name reservation.

| Pass | Condition that prevents changing acceptance |
| --- | --- |
| Binder hygiene | Preserve lexical identity, origins, shadowing and captured variables; reserve fresh identifiers above input identifiers. |
| Static recursive arguments | Remove only the same directly supplied invariant variable; retain a worker lambda and reject escaping/changed recursive uses. |
| Delayed-value sharing | Only total nonlogging bodies may become eager; every use must be an immediate force. |
| Nonrecursive `Fix` elimination | The recursive identifier is genuinely unused; the returned lambda still defers its body. |
| Float-out | Moved bindings are total and independent of crossed binders and retained dependencies. |
| Beta reduction | Evaluate a non-atomic argument through a strict let before the body; only atoms substitute directly. |
| ANF normalization/flattening | Retain left-to-right evaluation and use fresh binders and guarded let flattening. |
| Known-constructor cases | Use actual fields, not branch-lambda counts; evaluate all fields; preserve missing/extra-branch behavior. |
| Scalar constant folding | Match literal types and the complete builtin protocol; fold only successful allowlisted computations. |
| Data-constructor folding | Retain list element types, constructor-tag bounds, and serialization validity. |
| Boolean-choice simplification | Require post-success Boolean evidence; do not move effects out of strict branch arguments. |
| Shape DCE, integer identities and checked round trips | A post-success shape is not a termination proof; retain the validating producer and discarded operand effects. |
| CSE | Reuse only a dominating immutable result with stable dependencies; do not merge potentially logging calls. |
| DCE | Drop an unused binding only when its RHS is guaranteed to succeed. |
| Inlining | Preserve capture and multiplicity; an impure single use must be on the first evaluation frontier, not merely in a strict position. |
| Eta reduction | The replacement is a known callable value; unknown heads, saturated calls and delayed values are not assumed callable. |
| Force/delay cancellation | Substitute the delayed body at each original force, retaining its captured environment and deferred failure behavior. |
| Pre-lowering inlining | Distinguish total partial builtin states from saturated calls; retain the evaluation-frontier guard. |
| Adjacent list-destructor fusion | Require list evidence; retain the empty-list error and head/tail field order. |
| List-choice fusion | Require list evidence before replacing a null discriminator with list case; preserve empty and nonempty branches. |
| Pair destructuring | Require a known pair producer; keep producer evaluation, projections and fresh component binders. |
| Delayed list-choice lowering | Match the exact selector protocol and literal delayed branches; the replacement still rejects non-list inputs. |
| Checked list-branch fusion | Nonempty facts follow actual discrimination and stay branch-local, including aliases and captured lambdas. |
| Application packing | All reordered arguments are total; function failures and calls remain observable. |
| Builtin-state sharing, optional | Hoist only closed, correctly forced, unsaturated states with total supplied arguments. |
| Constant pooling, optional | Share identical literal payloads and types with fresh binders, without changing evaluation behavior. |

`prepare`, iterative simplification, checked pre-lowering, structural cleanup and
the final allocation stage were also checked as compositions. The test registry
has 33 pass/phase configurations, including composites and the existing duplicate
case-pass coverage, plus all eight combinations of packing/sharing/pooling.
Each registered transformation must change at least one witness; an entirely
no-op run is not counted as exercising a pass.

## New test design

`Test/MIR/Opt/Acceptance.lean` compiles each script **before supplying runtime
inputs**. The original and transformed scripts then receive exactly the same
arguments. This avoids accidentally validating only a rewrite specialized to
the test input.

The corpus consists of:

- 32 structured scripts and 34 runtime inputs, including wrong runtime types,
  empty/nonempty collections, constructor arities, explicit errors, failing
  thunks/functions, traces, shadowing, checked conversions and recursion.
- 128 reproducible generated closures, each receiving six runtime inputs.
- 200 partial builtin protocol prefixes covering all 101 builtin definitions,
  each receiving five runtime argument shapes. These exercise force count,
  argument count, invalid eventual argument types and validation timing.
- Four common observer contexts: evaluate, force, apply, and case-analyze the
  result. A final strict wrapper returns unit after successful evaluation so
  closure pretty-printing cannot be mistaken for semantic equivalence.

This yields **468,384 before/after comparisons** in native Plutuz. The same
comparisons check the Lean CEK's outcome and explicit trace sequence separately.
Resource, encoding, decoding, unknown and unbound-variable errors cannot be
silently counted as ordinary native rejection.

`Test/MIR/PassAuditMain.lean` exports the same scripts, variants and arguments as
Flat programs. `Test/MIR/ReferencePassAudit.hs` independently repeats the corpus
in actual **plutus-core 1.65.0.0**, using its testing parameters (variant E),
restricting mode, log emission, 10-billion CPU and 10-million memory limits.
It compares the original and transformed results directly, rather than trusting
an expected acceptance flag supplied by Moist. Out-of-budget evaluation,
decoding failures, open-term errors and evaluator panics fail the audit.

The reference run verifies **468,384 comparisons: 79,909 successful and 388,475
failing**, with no acceptance mismatch. Negative controls deliberately change
acceptance in both directions and require the checker to reject each mutation.
Its exported-request SHA-256 is:

```text
e4abc005f60f2e56d31bb350cbc4bf409386d83074aa76fa4894c6c5abb9ad27
```

### Failure diagnostics are not identical

There are 52 reference comparisons with different evaluator logs, all on the
empty-list destructor fixture: both sides fail, but the original builtin emits
an empty-list diagnostic and the transformed case reaches `Error` without that
diagnostic. The 52 rows represent 13 configurations under four observer contexts.
This satisfies the requested pass/fail criterion but is **not exact preservation
of all evaluator diagnostic messages**. The runner retains these differences in
`.lake/pass-audit/diagnostics.log`; it does not report them as identical traces.
Existing Lean trace checks continue to test explicit user `Trace` operations.

## Reproduce

Validation also passes the full 495-test suite, the 82-declaration formal axiom
allowlist, the library build, and the Ptah lifting tests. No new axiom or proof
placeholder is introduced.

With the repository's Lean and Zig toolchains:

```sh
lake exe pass_audit
lake test
lake build
lake build ptah_test
.lake/build/bin/ptah_test
```

For the independent evaluator, use GHC with plutus-core 1.65.0.0, its Flat
sublibrary, aeson and text installed:

```sh
python3 Test/MIR/run_reference_pass_audit.py --ghc /path/to/ghc
```

The runner requires the exact installed package version and compiles its Haskell
checker with `-Wall -Werror`. It writes the exact requests, diagnostic changes,
package identifiers, request hash, negative-control count and result summary
under `.lake/pass-audit/`. None of these generated binaries or requests need to
be committed. The runtime caps are safety limits, not an equality assertion
about resource usage or a proof of divergence preservation.

The independent sample repository also passes its 53 ABI checks, typed collection
checks, 2,080 token-operation checks, 1,350 currency-delta comparisons, and all
254 validator scenarios under the three compiler profiles. Its source and
benchmark results were not changed by this audit.
