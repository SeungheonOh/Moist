import Moist.Verified.KnownListsSoundness.Walk

variable [sv : Moist.CEK.SemVariant]

/-! # Known-list `case` fusion

`fuseKnownListCases` replaces `case (nullList l) [case l [C, …], E]` by
`case l [C, E]` when `l` is known to hold a list: by its producer, as the
tail bound by a `case` on a known list, or as a parameter of a recursive
function every call of which passes known lists at that position. The walk
refines its input (`knownListWalk_rel`), with the recursive argument facts
justified by the knot of `KnownListsSoundness/Knot.lean`.
-/

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Fusing `nullList` discriminators of known lists refines its input. -/
theorem fuseKnownListCases_refines (e : Expr) : MIRCtxRefines e (fuseKnownListCases e) := by
  unfold fuseKnownListCases
  simp only
  split
  · exact mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_of_factRel (by assumption) (fun _ _ => trivial) (fun _ _ => trivial)
        (Moist.Verified.KnownLists.knownListWalk_rel _ [] []).to_factRel)
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
