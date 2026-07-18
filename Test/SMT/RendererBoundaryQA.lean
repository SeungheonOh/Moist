import Moist.SMT.Compiler
import Moist.SMT.Semantics

/-!
# Adversarial renderer / raw-prelude QA

These executable checks exercise the portion of the SMT boundary that is
deliberately reviewed and tested against Z3 rather than proved in Lean:

* total-but-unspecified selectors, sequence indexing, and division;
* recursive byte and Unicode validity predicates;
* the intentional `Bytes`/`UString` alias at the Z3 level;
* numeric rendering of hostile string contents; and
* injective sanitization of hostile declaration names.

The formulas are small, targeted complements to the full builtin differential
suites.  In particular, the false guards below must dominate Z3's arbitrary
values for partial CEK observations.
-/

namespace Test.SMT.RendererBoundaryQA

open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

private def firstLine (text : String) : String :=
  (text.splitOn "\n").head?.getD ""

private def solverScript (declarations : List Command)
    (formula : SExpr) : Script :=
  ⟨preludeForAssertions [formula] ++ declarations ++
    [.assert formula, .checkSat]⟩

private def expectStatus (name expected : String) (script : Script) : IO Unit := do
  let path : System.FilePath := s!"/tmp/moist-renderer-boundary-{name}.smt2"
  IO.FS.writeFile path script.render
  let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
  IO.FS.removeFile path
  let status := firstLine result.stdout
  unless result.exitCode == 0 && result.stderr.isEmpty &&
      (result.stdout.splitOn "(error").length == 1 && status == expected do
    throw <| IO.userError
      s!"{name}: expected {expected}, got {status}\n{result.stdout}{result.stderr}"

private def emptyBytes : SExpr := SExpr.seqEmpty "Bytes"

private def wrongSelectorMasked : SExpr :=
  let value : SExpr := .app "VBool" [.bool true]
  SExpr.and (SExpr.isCtor "VInt" value)
    (SExpr.eq (.app "unVInt" [value]) (.int 17))

private def wrongSelectorOrMasked : SExpr :=
  let value : SExpr := .app "VBool" [.bool true]
  SExpr.or (SExpr.not (SExpr.isCtor "VInt" value))
    (SExpr.eq (.app "unVInt" [value]) (.int 17))

private def wrongSelectorInactiveIte : SExpr :=
  let value : SExpr := .app "VBool" [.bool true]
  SExpr.eq
    (SExpr.ite (.bool false) (.app "unVInt" [value]) (.int 17))
    (.int 17)

private def outOfBoundsNthMasked : SExpr :=
  SExpr.and (SExpr.lt (.int 0) (SExpr.seqLen emptyBytes))
    (SExpr.eq (SExpr.seqNth emptyBytes (.int 0)) (.int 17))

private def divisionByZeroMasked : SExpr :=
  SExpr.and (SExpr.ne (.int 0) (.int 0))
    (SExpr.eq (.app "uplc_div" [.int 7, .int 0]) (.int 17))

private def invalidBytesRejected : SExpr :=
  SExpr.not (.app "bytes_valid"
    [SExpr.seqAppend (SExpr.seqUnit (.int 0)) (SExpr.seqUnit (.int 256))])

private def surrogateStringRejected : SExpr :=
  SExpr.not (.app "ustring_valid" [SExpr.seqUnit (.int 0xD800)])

private def symbolicBytesName : String := Moist.SMT.sanitize "invalid bytes"

private def symbolicStringName : String := Moist.SMT.sanitize "invalid string"

/-- Force the recursive validators to reason about a model-provided sequence,
not merely reduce a ground literal. -/
private def invalidSymbolicBytes : SExpr :=
  SExpr.all
    [ .app "bytes_valid" [.sym symbolicBytesName]
    , SExpr.eq (SExpr.seqLen (.sym symbolicBytesName)) (.int 1)
    , SExpr.eq (SExpr.seqNth (.sym symbolicBytesName) (.int 0)) (.int 256)
    ]

private def invalidSymbolicString : SExpr :=
  SExpr.all
    [ .app "ustring_valid" [.sym symbolicStringName]
    , SExpr.eq (.app "seq.len" [.sym symbolicStringName]) (.int 1)
    , SExpr.eq (.app "seq.nth" [.sym symbolicStringName, .int 0])
        (.int 0xD800)
    ]

private def invalidNestedData : SExpr :=
  .app "data_valid" [.app "DB" [SExpr.seqUnit (.int 256)]]

private def invalidRuntimeConstructor : SExpr :=
  .app "val_valid" [.app "VConstr" [.int (-1), .app "VNil" []]]

private def aliasesCoincideInZ3 : SExpr :=
  SExpr.eq (SExpr.seqEmpty "Bytes") (SExpr.seqEmpty "UString")

/-- The open AST exposes raw `seq.extract`, whose negative-offset behavior is
different from the CEK byte-slice clamp.  The UPLC compiler never emits this
shape: it clamps both operands before constructing `seq.extract`. -/
private def unclampedNegativeExtract : SExpr :=
  SExpr.eq
    (SExpr.seqExtract (.bytes (ByteArray.mk #[1, 2, 3])) (.int (-1)) (.int 2))
    (.bytes (ByteArray.mk #[1, 2]))

private def hostileString : String :=
  "line\n\";(|\\λ𝄞" ++ String.singleton (Char.ofNat 0)

private def hostileStringRoundTrip : SExpr :=
  SExpr.eq (.str hostileString) (.str hostileString)

private def hostileDeclaration : SymDecl :=
  let declaration := symInt "x)\n(assert false) ; |\\ true"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.int 3)]

-- Z3 intentionally aliases these sorts; the production sort checker must
-- keep the CEK-level distinction even though the rendered formula is true.
example : expressionHasSort [] aliasesCoincideInZ3 .bool = false := by
  native_decide

example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty aliasesCoincideInZ3 = some false := by
  native_decide

-- Partial applications are excluded from caller-supplied declaration
-- assumptions.  Compiler-generated uses are admitted only behind proved
-- guards.
example : expressionTotalitySafe outOfBoundsNthMasked = false := by
  native_decide

example : expressionTotalitySafe divisionByZeroMasked = false := by
  native_decide

example : expressionTotalitySafe unclampedNegativeExtract = false := by
  native_decide

-- These are the exact strong-Boolean observations used by the compiler
-- proof, checked independently against the corresponding Z3 results below.
example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty wrongSelectorMasked = some false := by
  native_decide

example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty wrongSelectorOrMasked = some true := by
  native_decide

example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty wrongSelectorInactiveIte = some true := by
  native_decide

example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty outOfBoundsNthMasked = some false := by
  native_decide

example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty divisionByZeroMasked = some false := by
  native_decide

-- This deliberate mismatch is why raw sequence extraction is not a public
-- declaration expression.  The symbolic SliceByteString path inserts an
-- explicit zero clamp and is covered by the CEK differential suite.
example : Moist.SMT.Semantics.evalBool?
    Moist.SMT.Semantics.Model.empty unclampedNegativeExtract = some true := by
  native_decide

-- The hostile external name is encoded into the private simple-symbol
-- namespace; none of its delimiters reaches the rendered declaration.
example : declarationsRendererSafe [hostileDeclaration] = true := by
  native_decide

unsafe def main : IO Unit := do
  expectStatus "wrong-selector" "unsat" (solverScript [] wrongSelectorMasked)
  expectStatus "wrong-selector-or" "sat"
    (solverScript [] wrongSelectorOrMasked)
  expectStatus "wrong-selector-ite" "sat"
    (solverScript [] wrongSelectorInactiveIte)
  expectStatus "oob-nth" "unsat" (solverScript [] outOfBoundsNthMasked)
  expectStatus "div-zero" "unsat" (solverScript [] divisionByZeroMasked)
  expectStatus "invalid-byte" "sat" (solverScript [] invalidBytesRejected)
  expectStatus "surrogate" "sat" (solverScript [] surrogateStringRejected)
  expectStatus "symbolic-invalid-byte" "unsat"
    (solverScript [.declareConst symbolicBytesName .bytes] invalidSymbolicBytes)
  expectStatus "symbolic-surrogate" "unsat"
    (solverScript [.declareConst symbolicStringName .string] invalidSymbolicString)
  expectStatus "nested-invalid-byte" "unsat"
    (solverScript [] invalidNestedData)
  expectStatus "negative-runtime-tag" "unsat"
    (solverScript [] invalidRuntimeConstructor)
  expectStatus "sort-alias" "sat" (solverScript [] aliasesCoincideInZ3)
  expectStatus "negative-extract" "unsat"
    (solverScript [] unclampedNegativeExtract)
  expectStatus "hostile-string" "sat" (solverScript [] hostileStringRoundTrip)
  expectStatus "hostile-name" "sat"
    (scriptWith [hostileDeclaration] [.bool true])
  IO.println "adversarial renderer/prelude boundary checks passed"

end Test.SMT.RendererBoundaryQA

unsafe def main : IO Unit := Test.SMT.RendererBoundaryQA.main
