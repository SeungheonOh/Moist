import Moist.SMT.UPLC
import Moist.SMT.Soundness.GroundBuiltin

/-!
# Ground-builtin portability boundary regressions

These checks make the CEK stack-order convention observable with a
noncommutative builtin, cover both value and error results, and exercise a
pass-through builtin whose result comes from an argument rather than
`evalBuiltinConst`.
-/

namespace Test.SMT.GroundBuiltinBoundary

open Moist.Plutus.Term
open Moist.SMT.Compiler.GroundBuiltin
open Moist.SMT.UPLC

example :
    evaluateStackArguments .SubtractInteger
        [.Integer 2, .Integer 7] =
      .value (.Integer 5) := by
  rfl

example :
    evaluateStackArguments .DivideInteger
        [.Integer 0, .Integer 7] = .error := by
  rfl

example :
    evaluateStackArguments .IfThenElse
        [.Integer 3, .Integer 8, .Bool true] =
      .value (.Integer 8) := by
  rfl

/-- The symbolic compiler consumes the same CEK-stack-order adapter without
adding a residual SMT branch to a fully static call. -/
example :
    evalBuiltinStatic? .SubtractInteger
        [.const (.integer (.int 2)), .const (.integer (.int 7))] =
      some [Outcome.ok (.bool true) (.const (.integer (.int 5)))] := by
  rfl

/- The proof contracts are intentionally outside the executable compiler
namespace and cover every builtin and literal argument list. -/
#check Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_value_iff
#check Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_error_iff
#check Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_deferred_iff

end Test.SMT.GroundBuiltinBoundary
