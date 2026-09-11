import Moist.Onchain
import Moist.Cardano.V3
import Moist.Plutus.Eval
import Test.Framework

namespace Test.ConstitutionEncoding

open Moist.Cardano.V3
open Moist.Plutus (Data)
open Moist.Plutus.Term
open Moist.Onchain (PlutusData)
open Test.Framework

@[onchain] def makeConstitution (script : MaybeData ScriptHash) : Constitution := ⟨script⟩
@[onchain] def constitutionScript (constitution : Constitution) : MaybeData ScriptHash := constitution.script
@[onchain] def newConstitution (constitution : Constitution) : GovernanceAction :=
  .newConstitution .nothingData constitution

private def makeCompiled := compile! makeConstitution
private def projectCompiled := compile! constitutionScript
private def actionCompiled := compile! newConstitution

private def evaluateData (script : Term) (argument expected : Data) : IO Unit := do
  let term := Term.Apply script (.Constant (.Data argument, .AtomicType .TypeData))
  match ← Moist.Plutus.Eval.evalTerm term with
  | .ok result =>
    match result.term with
    | .Constant (.Data actual, _) =>
      unless actual == expected do throw (IO.userError s!"Expected {expected}, got {actual}")
    | _ => throw (IO.userError "Expected a Data result")
  | .error error => throw (IO.userError s!"Evaluation failed: {repr error}")

def tests : TestTree := suite "constitution_encoding" do
  test "native_and_compiled_upstream_layout" do
    for script in [MaybeData.nothingData, .justData "constitution".toUTF8] do
      let encodedScript := PlutusData.toData script
      let expected := Data.Constr 0 [encodedScript]
      let actual := PlutusData.toData (Constitution.mk script)
      unless actual == expected do throw (IO.userError "Constitution constructor wrapper missing")
      match PlutusData.fromData expected with
      | some (decoded : Constitution) =>
        unless PlutusData.toData decoded == expected do throw (IO.userError "Constitution roundtrip failed")
      | none => throw (IO.userError "Constitution decoding failed")
      evaluateData makeCompiled encodedScript expected
      evaluateData projectCompiled expected encodedScript
  test "new_constitution_action_nesting" do
    let constitution := Constitution.mk (.justData "guardrail".toUTF8)
    let encoded := Data.Constr 0 [.Constr 0 [.B "guardrail".toUTF8]]
    let expected := Data.Constr 5 [.Constr 1 [], encoded]
    unless PlutusData.toData (GovernanceAction.newConstitution .nothingData constitution) == expected do
      throw (IO.userError "NewConstitution action encoding mismatch")
    evaluateData actionCompiled encoded expected

end Test.ConstitutionEncoding
