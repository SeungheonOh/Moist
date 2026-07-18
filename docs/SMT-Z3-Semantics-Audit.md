# SMT-LIB and Z3 semantics audit

This document records the manual and differential review of the boundary
between the compiler's Lean observation semantics, its rendered SMT-LIB, and
Z3. It complements the kernel proofs; it is not a claim that Z3 itself or the
SMT-LIB parser has been formalized in Lean.

## Reviewed configuration

- Lean 4.24.0
- Z3 4.13.3, 64 bit
- the transparent renderer in `Moist.SMT.Render`
- the fixed prelude and physically separated compiler modules in
  `Moist.SMT.Compiler.UPLC`
- the proof-free, input-and-output checked API in `Moist.SMT.Compiler.Checked`
- the exact static-folding adapter in `Moist.SMT.Compiler.GroundBuiltin`
- the guarded observation semantics in `Moist.SMT.Semantics`
- the proof-carrying solver boundary in
  `Moist.SMT.Soundness.SolverBoundary`

The public theorem does not accept a `sat` token. A solver integration must
provide a `CertifiedZ3Model` for the exact stored query script. That structure
contains the decoded values of the checked declarations and a proof that every
typed script assertion is true in the same Lean model. From that premise, the
kernel proof reaches the actual CEK transition relation:

- Boolean success reaches exactly `VCon (Bool true)`;
- integer equality reaches exactly `VCon (Integer expected)`; and
- error reaches the CEK `.error` state in finitely many transitions.

The error theorem additionally proves that the error-aware evaluator returns
`.error` at every larger fuel. It therefore cannot be discharged by symbolic
or concrete fuel exhaustion.

The executable compiler does not import the semantics or soundness trees.
Static saturated calls cross one data-only boundary into the canonical CEK
builtin evaluator. Separate iff theorems characterize all three adapter
results—identical constant, actual CEK error, or successful nonconstant
deferral—over every builtin and literal argument list.

## Operations reviewed against Z3

| Area | Lean observation | Z3 behavior and compiler restriction |
| --- | --- | --- |
| Integers | unbounded `Int`; UPLC truncating and floor division helpers | Z3 `Int`; every division observation is guarded by a nonzero divisor |
| Booleans | strong three-valued `and`/`or` around partial observations | Z3 terms are total; a false conjunct or true disjunct masks the arbitrary value of an inactive term |
| Datatypes | wrong-constructor selectors return `none` | Z3 selectors are total but unspecified on the wrong constructor; every emitted selector is dominated by its tester |
| Byte sequences | `ByteArray`, elements restricted to 0 through 255 | `Bytes` is `(Seq Int)`; declarations assert `bytes_valid`, and emitted `seq.unit` and `seq.nth` observations carry range guards |
| Strings | sequences of Unicode scalar values | `UString` is a distinct Lean sort rendered as `(Seq Int)`; declarations assert scalar validity and the checked sort system rejects Bytes/UString aliasing |
| Sequence extraction | CEK-compatible byte slicing | negative UPLC start and length operands are clamped before `seq.extract` is emitted |
| UTF-8 | Lean's exact UTF-8 validator and decoder | decode results are observed only under the emitted `valid_utf8` guard; scalar edge cases are covered by real-Z3 regressions |
| Data and constant values | recursive `Data`, `Val`, and list decoders | model inputs carry recursive validity assertions; selectors and indexes are tester/range guarded |
| Advanced byte builtins | ground meaning delegated to the CEK builtin evaluator | raw recursive helpers were compared with CEK across endian, width, bit, shift, rotate, replication, and list-index cases |
| Modular exponentiation | CEK success/domain behavior | the helper's result is observed only when its `_defined` predicate holds |

The manual table audit matched all 115 ordinary application signatures (114
distinct heads because `seq.++` has separate Bytes and UString signatures)
and all 27 datatype tester heads to an executable `Semantics.evalApp` or
`evalIsCtor` branch. No signature accepted by the production sort checker was
missing from the modeled semantics.

`Bytes` and `UString` deliberately share Z3's underlying `(Seq Int)` sort for
performance. They do not share a Lean semantic sort. The production sort
checker rejects cross-sort equality and application even when Z3 would accept
the aliases as the same underlying sort.

## Generated SMT-LIB controls

`Compiler.compile?` stores one canonical script and checks both its input and
that exact generated output without rerunning symbolic evaluation. The
proof-carrying compiler is proved to erase to precisely this proof-free result,
and checked queries carry a kernel equality tying it to the relevant compiler
constructor. Before returning a production script, the generated-output
contract verifies:

- every raw command is an exact member of the fixed reviewed prelude;
- every declaration command belongs to the checked declaration environment or
  is one of the fixed opaque defaults;
- the script ends with the fixed solver tactic and a model request;
- every assertion is in the renderer-safe expression grammar; and
- every assertion has sort `Bool` under exactly those declarations.

Unknown prelude application heads conservatively select the complete prelude,
then remain rejected by the expression signature checker and by Z3. Prelude
families are named, dependency-closed sections rather than numeric slices.
The full assembled prelude remains byte-for-byte identical to the reviewed
85-command baseline.

The explicitly named `*InputChecked?` functions remain low-level first-stage
APIs. They do not claim output validation; production callers use
`Compiler.compile?` or one of its Bool/Int/Error specializations.

## Differential gates

The following tests exercise the external part of the boundary with real Z3:

- all 65 certified builtins on ground success/error and symbolic
  success/type/domain-error paths;
- 1,892 raw-prelude cases across all advanced builtin families;
- integer, bytes, string, data, and name-collision equivalence between the
  transparent and DAG renderers;
- UTF-8 maximum-scalar, guarded-selector, and symbolic-string cases;
- every demand-selected prelude family, plus rejection of an unknown helper;
  and
- malformed generated outputs covering delimiter injection, wrong arity,
  cross-sort equality, unknown helpers, non-Boolean assertions, raw reset,
  tactic injection, missing solver control, and undeclared command output.

The July 2026 audit ran the builtin differential in both ground and symbolic
modes (65 ground successes, 14 advanced ground errors, 65 symbolic successes,
65 symbolic type errors, 5 symbolic domain errors, 18 additional edge cases,
and 10 declaration-shape cases). The raw advanced-prelude differential passed
all 1,892 cases. A separate adversarial renderer suite exercises wrong
datatype selectors, out-of-bounds `seq.nth`, division by zero, recursive
validators over model-provided sequences, hostile Unicode/name content, and
the two deliberately excluded raw-AST differences below.

## Deliberately excluded raw-AST differences

The checked compiler fragment is narrower than the public low-level `Expr`
datatype. Two concrete global differences are intentional and regression
tested:

1. Z3 identifies `Bytes` and `UString` because both aliases expand to
   `(Seq Int)`, while the Lean observation semantics keeps them distinct.
   `expressionHasSort` rejects every cross-sort use before production
   compilation.
2. For a raw negative-offset `seq.extract`, Z3 returns the empty sequence,
   while the Lean byte extraction observation clamps the start to zero.
   `expressionTotalitySafe` rejects raw extraction in declarations, and the
   UPLC `SliceByteString` compiler inserts explicit nonnegative clamps for
   both start and length.

These examples are why the review claims adequacy only for generated,
checked expressions and not a global equivalence between arbitrary `Expr`
values and arbitrary Z3 terms.

The complete proof build also prints the axiom dependencies of the public
Bool, Int, and Error endpoints. They use only Lean's standard logical
principles (`propext`, `Classical.choice`, and `Quot.sound`), with no project
axiom, `sorryAx`, or admitted theorem.

CI builds the checked-compiler, output-contract, complete builtin-policy,
ground-adapter, namespace-layering, and axiom-audit modules in addition to
running every real-Z3 differential executable.

## Exact remaining trust boundary

Two components remain deliberately outside the Lean theorem:

1. Z3's implementation and the correctness of parsing/rendering the raw
   recursive prelude are reviewed and differentially tested, not proved in the
   kernel.
2. The opt-in DAG renderer uses runtime pointer identity. Its solver behavior
   is compared against the transparent renderer, but it is not substituted
   into a kernel theorem.

Consequently, the proved statement is precise: a `CertifiedZ3Model` for the
exact checked script implies the identical CEK result. Turning an actual Z3
process result into that certificate is the acknowledged external integration
obligation. There is no axiom or parser shortcut in the repository that turns
the text `sat` directly into a CEK conclusion.

The relevant external specifications used for this review are the SMT-LIB
integer theory and language reference, plus Z3's sequence and recursive
function documentation:

- <https://smt-lib.org/theories-Ints.shtml>
- <https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf>
- <https://microsoft.github.io/z3guide/docs/theories/Sequences>
- <https://microsoft.github.io/z3guide/docs/logic/Recursive%20Functions/>
