import Moist.Verified.Contextual

/-! # Congruence lemmas for `CtxRefines`

Every lemma has the shape `R a b → R (F a) (F b)` (or the pointwise list
version) for a term constructor `F`; all are instances of `ctxRefines_fill`.
The remaining `CtxEq` lemmas are kept only for existing imports. -/

namespace Moist.Verified.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence

--------------------------------------------------------------------------------
-- CtxEq (legacy two-sided relation)
--------------------------------------------------------------------------------

/-- Generic single-subterm congruence: `CtxEq` is preserved when wrapping both
    sides in any inner context. Proof: compose the outer test context with
    `inner`, then unfold via `fill_compose`. -/
private theorem ctxEq_extend
    {t₁ t₂ : Term} (h : CtxEq t₁ t₂) (inner : Context) :
    CtxEq (fill inner t₁) (fill inner t₂) := by
  intro C
  have h_filled := h (Context.compose C inner)
  rw [fill_compose, fill_compose] at h_filled
  exact h_filled

/-- Lambda congruence. -/
theorem ctxEq_lam {body₁ body₂ : Term} (name : Nat) (h : CtxEq body₁ body₂) :
    CtxEq (.Lam name body₁) (.Lam name body₂) := by
  have hwrap := ctxEq_extend h (.Lam name .Hole)
  simpa [fill] using hwrap

/-- Apply congruence. Chains the two single-hole swaps through `ctxEq_trans`. -/
theorem ctxEq_app {f₁ f₂ a₁ a₂ : Term}
    (hf : CtxEq f₁ f₂) (ha : CtxEq a₁ a₂) :
    CtxEq (.Apply f₁ a₁) (.Apply f₂ a₂) := by
  have hA : CtxEq (.Apply f₁ a₁) (.Apply f₂ a₁) := by
    have := ctxEq_extend hf (.AppLeft .Hole a₁)
    simpa [fill] using this
  have hB : CtxEq (.Apply f₂ a₁) (.Apply f₂ a₂) := by
    have := ctxEq_extend ha (.AppRight f₂ .Hole)
    simpa [fill] using this
  refine ctxEq_trans ?_ hA hB
  intro C hC1 hC2
  have d1 := (fill_closedAt_iff C (.Apply f₁ a₁) 0).mp hC1
  have d2 := (fill_closedAt_iff C (.Apply f₂ a₂) 0).mp hC2
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true] at d1 d2
  refine (fill_closedAt_iff C (.Apply f₂ a₁) 0).mpr ⟨d1.1, ?_⟩
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true]
  exact ⟨d2.2.1, d1.2.2⟩

--------------------------------------------------------------------------------
-- CONGRUENCE THEOREMS FOR CtxRefines
--------------------------------------------------------------------------------

/-- Generic one-hole congruence: `CtxRefines` is preserved by filling any
    context with both sides. -/
theorem ctxRefines_fill
    {t₁ t₂ : Term} (h : CtxRefines t₁ t₂) (inner : Context) :
    CtxRefines (fill inner t₁) (fill inner t₂) := by
  intro C
  have h_filled := h (Context.compose C inner)
  rw [fill_compose, fill_compose] at h_filled
  exact h_filled

/-- Lambda congruence for `CtxRefines`. -/
theorem ctxRefines_lam {body₁ body₂ : Term} (name : Nat) (h : CtxRefines body₁ body₂) :
    CtxRefines (.Lam name body₁) (.Lam name body₂) := by
  have hwrap := ctxRefines_fill h (.Lam name .Hole)
  simpa [fill] using hwrap

/-- Apply congruence for `CtxRefines`. -/
theorem ctxRefines_app {f₁ f₂ a₁ a₂ : Term}
    (hf : CtxRefines f₁ f₂) (ha : CtxRefines a₁ a₂) :
    CtxRefines (.Apply f₁ a₁) (.Apply f₂ a₂) := by
  have hA : CtxRefines (.Apply f₁ a₁) (.Apply f₂ a₁) := by
    have := ctxRefines_fill hf (.AppLeft .Hole a₁)
    simpa [fill] using this
  have hB : CtxRefines (.Apply f₂ a₁) (.Apply f₂ a₂) := by
    have := ctxRefines_fill ha (.AppRight f₂ .Hole)
    simpa [fill] using this
  exact ctxRefines_trans hA hB

end Moist.Verified.Contextual
