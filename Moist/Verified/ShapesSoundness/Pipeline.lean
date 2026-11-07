import Moist.MIR.Optimize.Advanced
import Moist.Verified.ConstantFoldingSoundness
import Moist.Verified.ShapesSoundness.Simplify

/-! # The advanced simplification step

`Advanced.simplify` fuses list destructors, folds constants and data
constructors, and removes shape-checked dead code. Each stage refines its
input, so the composition does.
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

theorem simplify_refines (e : Expr) : MIRCtxRefines e (Advanced.simplify e) := by
  unfold Advanced.simplify
  exact mirCtxRefines_trans (fuseListDestructors_refines e)
    (mirCtxRefines_trans (constantFold_refines _)
      (mirCtxRefines_trans (foldDataConstructors_refines _) (shapeDCE_refines _)))

end Moist.Verified.MIR
