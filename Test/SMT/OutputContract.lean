import Test.SMT.BasicBuiltinDifferential
import Moist.SMT.Compiler.OutputAnalysis

/-!
# Generated-output contract regressions

The production constructors run the generated assertion checker and carry its
certificate.  These tests exercise fail-closed malformed scripts and the
complete ground/symbolic builtin differential corpus.
-/

namespace Test.SMT.OutputContract

open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness
open Moist.SMT.Compiler.OutputAnalysis
open Test.SMT.BasicBuiltinDifferential

private def checked? (declarations : List SymDecl)
    (expression : SExpr) : Bool :=
  (GeneratedOutputContract.check declarations
    (scriptWith declarations [expression])).isSome

private def scriptChecked? (declarations : List SymDecl)
    (commands : List Command) : Bool :=
  (GeneratedOutputContract.check declarations ⟨commands⟩).isSome

-- Raw commands outside the exact reviewed prelude cannot alter solver state.
example : scriptChecked? [] [.raw "(reset)", .assert (.bool true),
    .checkSatUsing z3QueryTactic, .getModel] = false := by
  native_decide

-- Solver tactic text is fixed rather than a caller-controlled raw fragment.
example : scriptChecked? [] [.assert (.bool true),
    .checkSatUsing "smt) (reset) (check-sat", .getModel] = false := by
  native_decide

-- A model request without the canonical preceding solver command is rejected.
example : scriptChecked? [] [.assert (.bool true), .getModel] = false := by
  native_decide

-- A correct final suffix does not excuse an earlier solver query.
example : scriptChecked? [] [.assert (.bool true),
    .checkSatUsing z3QueryTactic, .checkSatUsing z3QueryTactic,
    .getModel] = false := by
  native_decide

-- Nor may a script request a model before the one final solver query.
example : scriptChecked? [] [.assert (.bool true), .getModel,
    .checkSatUsing z3QueryTactic, .getModel] = false := by
  native_decide

-- The canonical control suffix remains accepted.
example : scriptChecked? [] [.assert (.bool true),
    .checkSatUsing z3QueryTactic, .getModel] = true := by
  native_decide

-- Generated declarations must correspond to the checked input environment.
example : scriptChecked? [] [.declareConst "$u$120" .int,
    .assert (.bool true), .checkSatUsing z3QueryTactic, .getModel] = false := by
  native_decide

def forbiddenCommandForms : List Command :=
  [ .comment "hidden"
  , .setLogic "ALL"
  , .declareFun "rogue" [] .bool
  , .defineFun "rogue" [] .bool (.bool true)
  , .checkSat
  , .getValue [.bool true]
  ]

-- Every low-level command constructor outside the reviewed production
-- vocabulary remains fail closed.
example : forbiddenCommandForms.all
    (fun command => !generatedCommandSafe [] command) = true := by
  native_decide

-- Renderer delimiter injection remains rejected when nested below an
-- otherwise recognized application head.
example : checked? []
    (.app "and" [.bool true, .sym "x) (assert false) ;"]) = false := by
  native_decide

-- Renderer-safe text is still rejected when its arity is wrong.
example : checked? [] (.app "+" [.int 1]) = false := by
  native_decide

-- Z3 aliases both sequences to `(Seq Int)`, but Lean and CEK distinguish
-- bytes from strings; cross-sort equality must stay rejected.
example : checked? []
    (SExpr.eq (.bytes ByteArray.empty) (.str "")) = false := by
  native_decide

-- Unknown helper names cannot silently acquire a sort.
example : checked? [] (.app "uplc_typo" [.int 1]) = false := by
  native_decide

-- SMT-LIB only permits Boolean assertions.
example : checked? [] (.int 1) = false := by
  native_decide

/- Fingerprints are only cache filters.  These expressions have the same
depth-two fingerprint, but the hidden leaf changes the application from a
well-sorted Boolean to an ill-sorted term.  The exact-identity gate must
reject the candidate instead of reusing the first analysis. -/
private def fingerprintCollisionBool : SExpr :=
  .app "not" [.app "not" [.app "not" [.bool true]]]

private def fingerprintCollisionInt : SExpr :=
  .app "not" [.app "not" [.app "not" [.int 0]]]

example : (expressionOutputFingerprint 2 fingerprintCollisionBool ==
    expressionOutputFingerprint 2 fingerprintCollisionInt) = true := by
  native_decide

example : expressionOutputEq fingerprintCollisionBool
    fingerprintCollisionInt = false := by
  native_decide

example : generatedAssertionsOutputSafe []
    ⟨[.assert fingerprintCollisionBool, .assert fingerprintCollisionInt]⟩ =
      false := by
  native_decide

-- Supported advanced helpers belong to the same checked grammar.
example : checked? []
    (SExpr.eq
      (.app "uplc_shiftByteString" [.bytes ByteArray.empty, .int 4])
      (.bytes ByteArray.empty)) = true := by
  native_decide

private def allEndpointOutputsAccepted (fuel : Nat) (test : Case) : Bool :=
  (BoolTrueQuery.compile? fuel test.declarations test.term).isSome &&
    (IntEqQuery.compile? fuel test.declarations test.term 0).isSome &&
    (ErrorQuery.compile? fuel test.declarations test.term).isSome

/-- Every ground success/error and symbolic success/type/domain-error case for
every certified builtin passes all three production output contracts. -/
def completeBuiltinCorpusAccepted : Bool :=
  allCases.all (allEndpointOutputsAccepted 120)

example : completeBuiltinCorpusAccepted = true := by
  native_decide

end Test.SMT.OutputContract
