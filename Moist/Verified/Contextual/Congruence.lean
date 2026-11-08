import Moist.Verified.Contextual

variable [sv : Moist.CEK.SemVariant]

/-! # Congruence lemmas for `CtxRefines`

Every lemma has the shape `R a b → R (F a) (F b)` (or the pointwise list
version) for a term constructor `F`; all are instances of `ctxRefines_fill`. -/

namespace Moist.Verified.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence

--------------------------------------------------------------------------------
-- CtxEq (legacy two-sided relation)
--------------------------------------------------------------------------------

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
