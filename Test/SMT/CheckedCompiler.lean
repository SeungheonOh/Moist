import Test.SMT.SupportedQueries

/-!
# Proof-free compiler regressions

The public `Moist.SMT.Compiler` facade checks caller-controlled input and
constructs the canonical script once.  Generated-output validation remains an
explicit proof-boundary postcheck; these tests intentionally exercise only the
sharing-sensitive input-checked path.
-/

namespace Test.SMT.CheckedCompiler

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Test.SMT.SupportedQueries

private def acceptedByAllInputCheckedKinds (builtin : BuiltinFun) : Bool :=
  (Moist.SMT.Compiler.compileBoolTrueInputChecked?
      1 [] (.Builtin builtin)).isSome &&
    (Moist.SMT.Compiler.compileIntEqInputChecked?
      1 [] (.Builtin builtin) 0).isSome &&
    (Moist.SMT.Compiler.compileErrorInputChecked?
      1 [] (.Builtin builtin)).isSome

private def rejectedByAllInputCheckedKinds (builtin : BuiltinFun) : Bool :=
  !(Moist.SMT.Compiler.compileBoolTrueInputChecked?
      1 [] (.Builtin builtin)).isSome &&
    !(Moist.SMT.Compiler.compileIntEqInputChecked?
      1 [] (.Builtin builtin) 0).isSome &&
    !(Moist.SMT.Compiler.compileErrorInputChecked?
      1 [] (.Builtin builtin)).isSome

def all65CertifiedBuiltinsAccepted : Bool :=
  certifiedBuiltins.all acceptedByAllInputCheckedKinds

def all36UnsupportedBuiltinsRejected : Bool :=
  unsupportedBuiltins.all rejectedByAllInputCheckedKinds

example : certifiedBuiltins.length = 65 := by native_decide
example : unsupportedBuiltins.length = 36 := by native_decide
example : all65CertifiedBuiltinsAccepted = true := by native_decide
example : all36UnsupportedBuiltinsRejected = true := by native_decide

/- The three convenience wrappers return their exact canonical scripts, not
an independently reconstructed approximation.  `rfl` exercises the public
facade itself and requires no extensional equality instance for scripts. -/
example :
    Moist.SMT.Compiler.compileBoolTrueInputChecked? 3 [] .Error =
      some (scriptForBoolTrue 3 [] .Error) := by
  rfl

example :
    Moist.SMT.Compiler.compileIntEqInputChecked? 3 [] .Error (-7) =
      some (scriptForIntEq 3 [] .Error (.int (-7))) := by
  rfl

example :
    Moist.SMT.Compiler.compileErrorInputChecked? 3 [] .Error =
      some (scriptForError 3 [] .Error) := by
  rfl

end Test.SMT.CheckedCompiler

/--
info: 'Moist.SMT.UPLC.Soundness.CertifiedCompilation.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.CertifiedCompilation.compile_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.BoolTrueQuery.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.BoolTrueQuery.compile_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.IntEqQuery.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.IntEqQuery.compile_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.ErrorQuery.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.ErrorQuery.compile_map_script
