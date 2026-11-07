import Moist.Verified.SubstRefines
import Moist.Verified.StepWellFormed

/-! # Extended substitution refinement infrastructure

Utility lemmas for the inline soundness proof:

1. `obsRefinesK_compose_obsRefines_right` — compose step-indexed with
   unbounded ObsRefines on the RHS.
2. `obsRefines_of_shiftBisimState` — lift ShiftBisim to ObsRefines.
-/

namespace Moist.Verified.InlineSoundness.SubstRefinesExt

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun BuiltinType)
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.BetaValueRefines
open Moist.Verified.FundamentalRefines
open Moist.Verified.SubstRefines
open Moist.Verified.StepWellFormed

section Composition

/-- Compose step-indexed ObsRefinesK on the left with unbounded ObsRefines
    on the right.  ObsRefines (unbounded) doesn't consume any step budget,
    so the composition preserves the index `k`. -/
theorem obsRefinesK_compose_obsRefines_right {k : Nat} {s₁ s₂ s₃ : State}
    (h₁₂ : ObsRefinesK k s₁ s₂)
    (h₂₃ : ObsRefines s₂ s₃) :
    ObsRefinesK k s₁ s₃ := by
  constructor
  · intro v ⟨n, hn, hs⟩
    obtain ⟨v₂, hv₂⟩ := h₁₂.1 v ⟨n, hn, hs⟩
    exact h₂₃.halt ⟨v₂, hv₂⟩
  · intro n hn hs
    exact h₂₃.error (h₁₂.2 n hn hs)

end Composition

section ShiftBisimObsRefines

end ShiftBisimObsRefines

end Moist.Verified.InlineSoundness.SubstRefinesExt
