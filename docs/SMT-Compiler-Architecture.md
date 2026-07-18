# SMT compiler architecture and correctness boundary

This document records the production boundary of the UPLC-to-SMT compiler.
It is intentionally stricter than saying that `Semantics.eval` "models Z3".
That phrase is only accurate on the checked, guarded fragment emitted by the
compiler.

## Portable executable layers

The portable path is ordered as follows:

1. `Moist.SMT.Syntax` defines sorts, expressions, commands, scripts, and the
   injective external-name encoding.
2. `Moist.SMT.Optimize` contains executable expression rewrites only.
3. `Moist.SMT.Compiler.UPLC` physically separates the executable UPLC compiler
   into `Expressions`, `Prelude`, `SymbolicValue`, `Compaction`, `Projection`,
   `Evaluation`, `Declarations`, and `Query` modules.  Their declarations keep
   the stable `Moist.SMT.UPLC` namespace, and `Moist.SMT.UPLC` is now only the
   compatibility facade.  The compiler reuses the CEK builtin evaluator for
   fully static calls, but deliberately does not import the CEK transition
   machine; the latter belongs to the proof side of the boundary.
4. `Moist.SMT.Compiler.Validation` contains fail-closed structural validation
   for the supported builtin fragment and public SMT expressions. Its
   executable definitions live in the matching
   `Moist.SMT.Compiler.Validation` namespace. The proof-only
   `Moist.SMT.Soundness.ValidationCompatibility` module preserves the former
   `Moist.SMT.UPLC.Soundness` spellings for existing Lean proof callers without
   leaking that namespace through the compiler facade.
5. `Moist.SMT.Compiler.OutputAnalysis` contains the sharing-aware, fused
   renderer/sort analysis used to postvalidate compiler-owned assertions. Its
   bounded cache is an executable optimization only: fingerprints merely
   select candidates, and exact structural equality gates every cache hit.
   Lean's isolated pointer-identity accelerator is optional; a port needs
   only an exact equality decision at this boundary.
6. `Moist.SMT.Compiler.InputChecked` exposes the proof-free, explicitly named
   `*InputChecked?` entry points. They validate caller-controlled input and
   construct one canonical script. These are low-level first-stage functions,
   not the production acceptance boundary.
7. `Moist.SMT.Compiler.Checked` exposes `compile?` and its three specialized
   entry points. It consumes the exact first-stage result and validates
   command forms, solver control, renderer safety, and assertion sorts. Its
   renderer/sort pass is the sharing-aware analysis above; symbolic evaluation
   is not repeated.
8. `Moist.SMT.Render` is the transparent reference SMT-LIB renderer.
9. `Moist.SMT.Compiler` is the public portable facade over those modules.

None of these modules imports the simulated semantics or the soundness proof
tree. `Moist.SMT.Compiler.Operational` is a separate opt-in facade for the
pointer-sharing DAG renderer. That renderer is `unsafe`; it is tested against
the reference renderer with real Z3, but it is not silently treated as a
kernel theorem.

`Command.raw`, arbitrary `Expr.app` heads, custom sort strings, and direct
structure constructors are low-level escape hatches. The explicitly named
`*InputChecked?` functions certify only caller input. Production proof-free
callers use `Compiler.compile?`, which validates the exact generated output
AST as well. Callers that need the CEK theorem use the proof-carrying query
constructors; erasing their certificate is proved equal to that same
`Compiler.compile?` result. The compiler itself reserves raw commands for the
reviewed, fixed prelude.

## Proof and model layers

The proof side is separate:

- `Moist.SMT.Semantics` interprets observations in the guarded compiler
  fragment.
- `Soundness.Optimize` proves every executable rewrite preserves that
  interpretation.
- `Soundness.Compiler` contains compiler and script-accounting contracts.
- `Soundness.Foundations`, builtin proofs, compaction proofs, and `Simulation`
  connect every active symbolic outcome to exact big-step evaluation.
- the public endpoints convert exact big-step results to actual CEK transition
  reachability.
- `Soundness.SolverInput` proves that checked symbolic inputs decode to one CEK
  environment.
- the generated-output contract checks the compiler's command allowlist,
  solver-control suffix, assertion renderer grammar, and assertion sorts,
  rather than checking only caller-supplied declarations. The executable
  assertion pass preserves sharing with a bounded memo cache;
  `Soundness.OutputAnalysis` proves it exactly equals the transparent
  renderer and sort validators before `OutputContract` stores either fact.
- `Soundness.CheckedCompiler` proves successful proof-free compilation gives
  the canonical script plus all input facts and all four output facts. Its
  proof-carrying result maps exactly to `Compiler.compile?`; it has no separate
  proof-side compiler or acceptance path.
- `Soundness.SolverBoundary` ties a checked query to its canonical script and
  consumes a decoded, semantically certified solver model.

The public direction is deliberately one-way: a certified satisfiable SMT
query implies the identical CEK value, or an actual reachable CEK error. No
converse (`CEK result -> SMT sat`) is required.

## What the executable semantics does and does not claim

Z3's term language is total in places where the CEK operation is partial or
where the Lean observation decoder intentionally returns `none`:

| SMT operation | Z3 outside the CEK domain | Lean observation | Compiler rule |
| --- | --- | --- | --- |
| datatype selector on the wrong constructor | solver-chosen value | `none` | constructor test guards the selector |
| `seq.nth` out of bounds | solver-chosen value | `none` | nonnegative/in-range guard |
| `seq.unit` outside byte range | valid `Seq Int` | `none` as a byte | `0 <= n <= 255` guard |
| integer division by zero | total but underspecified | `none` | nonzero guard |
| invalid UTF-8 decoding | helper remains an SMT term | `none` | exact UTF-8 validity guard |
| negative byte-slice start/length | SMT sequence extraction rules | CEK clamping | compiler clamps both operands before extraction |

Strong Boolean conjunction/disjunction in `Semantics.eval` models the only
observation needed from an inactive partial branch: a false conjunct or true
disjunct determines the result regardless of Z3's arbitrary total value.
It is not a license to evaluate arbitrary unguarded SMT expressions.

`Bytes` and `UString` are both represented as `Seq Int` in SMT for solver
performance. They remain distinct semantic sorts in Lean. The production sort
checker therefore rejects cross-sort use even where Z3's aliases coincide.

## External SMT-LIB/Z3 obligation

Lean does not prove Z3 correct and does not parse the raw recursive prelude
back into a second formal syntax. A bare `sat` token is never accepted as a
soundness premise. A solver integration must:

1. submit exactly the checked query's stored script using the reference
   renderer, or separately validate the operational renderer;
2. reject parser/type errors even if later output contains `sat`;
3. decode every declared symbol at its checked sort;
4. establish the fixed prelude's reviewed interpretation; and
5. transfer truth of every script assertion into the same
   `Semantics.Model`.

Those obligations construct `CertifiedZ3Model`. Once it exists, the remainder
of the result-to-CEK argument is kernel checked.

## Porting checklist

A port must preserve all of the following together:

- source-order versus CEK-stack-order builtin arguments;
- declaration order (`Var 1` is the first `SymDecl`, not the last);
- exact force/arity handling and the distinction between error and symbolic
  fuel timeout;
- static CEK-backed evaluation when all saturated arguments are literals;
- every symbolic type/domain guard and all inactive-branch masking;
- byte, Unicode scalar, data, list, pair, array, and constructor encodings;
- demand-prelude dependency families and their canonical declaration order;
- supported-builtin scanning (crypto, `SerializeData`, and Value-family
  builtins remain explicitly unsupported);
- reference rendering of negative integers and recursive literals;
- injective/safe names, unique declarations, sort checking, and generated
  output validation;
- exact expression equality before reusing any cached output analysis (a
  pointer shortcut is optional and must not be the logical equality test);
- computational revalidation of every mandatory decoding assumption in the
  proof-free `SymDecl` record; and
- the CEK/Z3 differential, raw-prelude differential, renderer differential,
  prelude-family, axiom, and no-hole test gates.

Changing only the generated SMT text without updating its Lean semantics,
guards, proof, and differential tests is not a sound compiler change.
