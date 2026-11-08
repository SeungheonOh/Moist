import Moist.MIR.Optimize.Advanced
import Moist.Verified.ConstantFoldingSoundness
import Moist.Verified.ShapesSoundness.Simplify
import Moist.Verified.TagChainsSoundness
import Moist.Verified.DataShapesSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # The advanced simplification step

`Advanced.simplify` fuses list destructors, folds constants and data
constructors, rewrites Data kind guards, binds the bytes of compared keys,
removes shape-checked dead code and compiles constructor-tag
test chains to integer cases. Each stage refines its input, so the
composition does.
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

theorem simplify_refines (e : Expr) : MIRCtxRefines e (Advanced.simplify e) := by
  unfold Advanced.simplify
  exact mirCtxRefines_trans (fuseListDestructors_refines e)
    (mirCtxRefines_trans (constantFold_refines _)
      (mirCtxRefines_trans (foldDataConstructors_refines _)
        (mirCtxRefines_trans (specializeDataChecks_refines _)
          (mirCtxRefines_trans (insertKeyBytes_refines _)
            (mirCtxRefines_trans (shapeDCE_refines _) (caseTagChains_refines _))))))

end Moist.Verified.MIR
