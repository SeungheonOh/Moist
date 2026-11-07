import Moist.Verified.CheckedBranchesSoundness.Lowering
import Moist.Verified.CheckedBranchesSoundness.Walk

/-! # Checked list branches

`optimizeCheckedBranches` first lowers fully forced delayed `chooseList`
calls to a `nullList` discriminator (`lowerDelayedListChoices_refines`), then
fuses head/tail projections of lists known to be non-empty inside the
selected branch of a list discriminator (`fuseCheckedListBranches_refines`).
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Head/tail fusion inside checked list branches refines its input. -/
theorem fuseCheckedListBranches_refines (e : Expr) : MIRCtxRefines e (fuseCheckedListBranches e) := by
  unfold fuseCheckedListBranches
  simp only
  split
  · exact mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_of_factRel (by assumption) (fun _ _ => trivial) (fun _ _ => trivial)
        (checkedBranchWalk_rel _ [] []).to_factRel)
  · exact Hygiene.uniqueOptimizationBinders_refines e

/-- The checked branch pass refines its input. -/
theorem optimizeCheckedBranches_refines (e : Expr) : MIRCtxRefines e (optimizeCheckedBranches e) :=
  mirCtxRefines_trans (lowerDelayedListChoices_refines e)
    (fuseCheckedListBranches_refines (lowerDelayedListChoices e))

end Moist.Verified.MIR
