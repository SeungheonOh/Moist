import Moist.Verified.ApplicationPackingSoundness
import Moist.MIR.Optimize.Advanced

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

theorem finish_without_sharing_refines (expression : Expr) (options : Options)
    (builtinSharing : options.shareBuiltinStates = false)
    (constantPooling : options.poolConstants = false) :
    MIRCtxRefines expression (finish expression options) := by
  simp only [finish, builtinSharing, constantPooling, Bool.false_eq_true, if_false]
  split
  · exact packApplications_refines 3 expression
  · exact mirCtxRefines_refl expression

theorem finish_default_refines (expression : Expr) :
    MIRCtxRefines expression (finish expression) :=
  finish_without_sharing_refines expression {} rfl rfl

end Moist.Verified.MIR
