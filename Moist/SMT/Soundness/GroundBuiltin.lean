import Moist.SMT.Compiler.GroundBuiltin

/-!
# Ground-builtin adapter specification

These theorems pin every result of the executable ground-builtin adapter to
the canonical CEK evaluator.  They are kept out of the compiler module so a
proof-free compiler import does not pull in the soundness tree.
-/

namespace Moist.SMT.UPLC.Soundness.GroundBuiltin

open Moist.Plutus.Term (BuiltinFun Const)

/-- A folded constant is returned exactly when CEK returns that same
constant value. -/
theorem evaluateStackArguments_eq_value_iff
    (builtin : BuiltinFun) (arguments : List Const) (constant : Const) :
    Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments
        builtin arguments = .value constant ↔
      Moist.CEK.evalBuiltin builtin
        (arguments.map Moist.CEK.CekValue.VCon) =
          some (.VCon constant) := by
  unfold Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments
  cases hresult : Moist.CEK.evalBuiltin builtin
      (arguments.map Moist.CEK.CekValue.VCon) with
  | none => simp
  | some result =>
      cases result <;> simp

/-- A folded error is returned exactly when CEK reports failure. -/
theorem evaluateStackArguments_eq_error_iff
    (builtin : BuiltinFun) (arguments : List Const) :
    Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments
        builtin arguments = .error ↔
      Moist.CEK.evalBuiltin builtin
        (arguments.map Moist.CEK.CekValue.VCon) = none := by
  unfold Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments
  cases hresult : Moist.CEK.evalBuiltin builtin
      (arguments.map Moist.CEK.CekValue.VCon) with
  | none => simp
  | some result =>
      cases result <;> simp

/-- Deferral is possible exactly for a successful non-constant CEK result.
It is never conflated with a CEK error. -/
theorem evaluateStackArguments_eq_deferred_iff
    (builtin : BuiltinFun) (arguments : List Const) :
    Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments
        builtin arguments = .deferred ↔
      ∃ result,
        Moist.CEK.evalBuiltin builtin
            (arguments.map Moist.CEK.CekValue.VCon) = some result ∧
          ∀ constant, result ≠ .VCon constant := by
  unfold Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments
  cases hresult : Moist.CEK.evalBuiltin builtin
      (arguments.map Moist.CEK.CekValue.VCon) with
  | none => simp
  | some result =>
      cases result <;> simp_all

end Moist.SMT.UPLC.Soundness.GroundBuiltin
