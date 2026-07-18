import Test.SMT.SupportedQueries

/-!
# Fully checked proof-free compiler regressions

The public `Moist.SMT.Compiler` facade checks caller-controlled input, builds
the canonical script once, and validates that exact generated output with the
sharing-aware analyzer.
-/

namespace Test.SMT.CheckedCompiler

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Test.SMT.SupportedQueries

private def acceptedByAllCheckedKinds (builtin : BuiltinFun) : Bool :=
  (Moist.SMT.Compiler.compileBoolTrue?
      1 [] (.Builtin builtin)).isSome &&
    (Moist.SMT.Compiler.compileIntEq?
      1 [] (.Builtin builtin) 0).isSome &&
    (Moist.SMT.Compiler.compileError?
      1 [] (.Builtin builtin)).isSome

private def rejectedByAllCheckedKinds (builtin : BuiltinFun) : Bool :=
  !(Moist.SMT.Compiler.compileBoolTrue?
      1 [] (.Builtin builtin)).isSome &&
    !(Moist.SMT.Compiler.compileIntEq?
      1 [] (.Builtin builtin) 0).isSome &&
    !(Moist.SMT.Compiler.compileError?
      1 [] (.Builtin builtin)).isSome

def all65CertifiedBuiltinsAccepted : Bool :=
  certifiedBuiltins.all acceptedByAllCheckedKinds

def all36UnsupportedBuiltinsRejected : Bool :=
  unsupportedBuiltins.all rejectedByAllCheckedKinds

example : certifiedBuiltins.length = 65 := by native_decide
example : unsupportedBuiltins.length = 36 := by native_decide
example : all65CertifiedBuiltinsAccepted = true := by native_decide
example : all36UnsupportedBuiltinsRejected = true := by native_decide

/- The convenience wrappers succeed on a simple term.  The kernel theorem
below fixes any returned value to the exact canonical script, without relying
on an extensional equality instance for scripts. -/
example : (Moist.SMT.Compiler.compileBoolTrue? 3 [] .Error).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileIntEq? 3 [] .Error (-7)).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileError? 3 [] .Error).isSome = true := by
  native_decide

example {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileBoolTrue? 3 [] .Error = some script) :
    script = scriptForBoolTrue 3 [] .Error := by
  exact (Moist.SMT.UPLC.Soundness.CheckedCompiler.compile_some h).2.1

example {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileIntEq? 3 [] .Error (-7) = some script) :
    script = scriptForIntEq 3 [] .Error (.int (-7)) := by
  exact (Moist.SMT.UPLC.Soundness.CheckedCompiler.compile_some h).2.1

example {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileError? 3 [] .Error = some script) :
    script = scriptForError 3 [] .Error := by
  exact (Moist.SMT.UPLC.Soundness.CheckedCompiler.compile_some h).2.1

/- The proof-free output gate rejects a malformed generated command stream
before any text is submitted to a solver. -/
example : Moist.SMT.Compiler.outputAccepted []
    ⟨[.raw "(reset)", .assert (.bool true),
      .checkSatUsing z3QueryTactic, .getModel]⟩ = false := by
  native_decide

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
