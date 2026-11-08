import Moist.Verified.StepWellFormed

variable [sv : Moist.CEK.SemVariant]

namespace Moist.Verified.InlineSoundness.SubstRefinesExt

open Moist.CEK
open Moist.Verified.Equivalence
open Moist.Verified.Contextual

/-- Compose step-indexed `ObsRefinesK` on the left with unbounded
    `ObsRefines` on the right; the index is preserved. -/
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

end Moist.Verified.InlineSoundness.SubstRefinesExt
