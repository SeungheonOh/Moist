import Moist.Verified.ApplicationPackingSoundness
import Moist.Verified.SharingSoundness
import Moist.Verified.PlacementSoundness
import Moist.MIR.Optimize.Advanced

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

/-- The final allocation stage refines its input for every option set. -/
theorem finish_refines (expression : Expr) (options : Options) :
    MIRCtxRefines expression (finish expression options) := by
  unfold finish
  dsimp only
  have packed : MIRCtxRefines expression
      (if options.packApplications then packApplications 3 expression else expression) := by
    split
    · exact packApplications_refines 3 expression
    · exact mirCtxRefines_refl expression
  have low : ∀ packed, MIRCtxRefines packed
      (if options.shareLow then shareLow options.lowSharing packed else packed) := by
    intro packed
    split
    · exact Placement.shareLow_refines _ packed
    · exact mirCtxRefines_refl packed
  have shared : ∀ low, MIRCtxRefines low
      (if options.shareBuiltinStates then
        hoistBuiltinStates (max 1 options.minimumBuiltinUses) low else low) := by
    intro low
    split
    · exact Sharing.hoistBuiltinStates_refines _ low
    · exact mirCtxRefines_refl low
  have pooled : ∀ shared, MIRCtxRefines shared
      (if options.poolConstants then poolConstants options.minimumConstantBytes shared
        else shared) := by
    intro shared
    split
    · exact Sharing.poolConstants_refines _ shared
    · exact mirCtxRefines_refl shared
  exact mirCtxRefines_trans (mirCtxRefines_trans (mirCtxRefines_trans packed (low _)) (shared _))
    (pooled _)

theorem finish_without_sharing_refines (expression : Expr) (options : Options)
    (_builtinSharing : options.shareBuiltinStates = false)
    (_constantPooling : options.poolConstants = false) :
    MIRCtxRefines expression (finish expression options) :=
  finish_refines expression options

theorem finish_default_refines (expression : Expr) :
    MIRCtxRefines expression (finish expression) :=
  finish_refines expression {}

end Moist.Verified.MIR
