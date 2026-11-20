import Moist.MIR.Optimize.Advanced
import Moist.Verified.ConstantFoldingSoundness
import Moist.Verified.ShapesSoundness.Simplify
import Moist.Verified.TagChainsSoundness
import Moist.Verified.DataShapesSoundness
import Moist.Verified.KeyGuardsSoundness
import Moist.Verified.IntegerComparisonsSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # The advanced simplification step

`Advanced.simplify` fuses list destructors, folds constants and data
constructors, rewrites Data kind guards, binds the guards of compared keys,
removes shape-checked dead code, compiles constructor-tag test chains to
integer cases, and normalizes integer comparison thresholds. Each stage
refines its input, so the composition does.
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced

theorem simplify_refines (e : Expr) : MIRCtxRefines e (Advanced.simplify e) := by
  unfold Advanced.simplify
  exact mirCtxRefines_trans (fuseListDestructors_refines e)
    (mirCtxRefines_trans (constantFold_refines _)
      (mirCtxRefines_trans (foldDataConstructors_refines _)
        (mirCtxRefines_trans (specializeDataChecks_refines _)
          (mirCtxRefines_trans (insertKeyGuards_refines _)
            (mirCtxRefines_trans (shapeDCE_refines _)
              (mirCtxRefines_trans (caseTagChains_refines _) (normalizeIntegerComparisons_refines _)))))))

end Moist.Verified.MIR
