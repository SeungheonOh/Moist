import Moist.Verified.Contextual

/-! # Congruence lemmas for `CtxEq` / `CtxRefines`

Every lemma in this file has the shape `R a b → R (F a) (F b)` (or the
pointwise list version thereof) for a term constructor `F`. They are pure
structural porters that plumb `ctxEq_extend` / `ctxRefines_extend` through
`Context.compose`, sometimes chaining via `ctxEq_trans` / `ctxRefines_trans`.

Pulled out of `Moist.Verified.Contextual` to keep the core module
focused on reflexivity / symmetry / transitivity / antisymmetry /
`fill_closedAt_iff` plumbing. -/

namespace Moist.Verified.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence

--------------------------------------------------------------------------------
-- CONGRUENCE THEOREMS FOR CtxEq
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

/-- Delay congruence. -/
theorem ctxEq_delay {body₁ body₂ : Term} (h : CtxEq body₁ body₂) :
    CtxEq (.Delay body₁) (.Delay body₂) := by
  have hwrap := ctxEq_extend h (.Delay .Hole)
  simpa [fill] using hwrap

/-- Force congruence. -/
theorem ctxEq_force {t₁ t₂ : Term} (h : CtxEq t₁ t₂) :
    CtxEq (.Force t₁) (.Force t₂) := by
  have hwrap := ctxEq_extend h (.Force .Hole)
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

/-- Constr congruence (single-element swap form). Swaps one field at a known
    position inside `pre ++ a :: post`. -/
theorem ctxEq_constr_one {tag : Nat} {a b : Term} {pre post : List Term}
    (hab : CtxEq a b) :
    CtxEq (.Constr tag (pre ++ a :: post)) (.Constr tag (pre ++ b :: post)) := by
  have hwrap := ctxEq_extend hab (.Constr tag pre .Hole post)
  simpa [fill] using hwrap

/-- Inductive worker for the Constr congruence: walks the field lists from left
    to right, swapping one element per step. -/
private theorem ctxEq_constr_swap_prefix {tag : Nat} {fs₁ fs₂ : List Term}
    (pre : List Term) (hrel : ListRel CtxEq fs₁ fs₂) :
    CtxEq (.Constr tag (pre ++ fs₁)) (.Constr tag (pre ++ fs₂)) := by
  induction fs₁ generalizing fs₂ pre with
  | nil =>
    cases fs₂ with
    | nil => exact ctxEq_refl _
    | cons => exact absurd hrel id
  | cons f₁ fs₁ ih =>
    cases fs₂ with
    | nil => exact absurd hrel id
    | cons f₂ fs₂ =>
      -- Step A: swap head f₁ → f₂ at slot |pre|
      have hA : CtxEq (.Constr tag (pre ++ f₁ :: fs₁)) (.Constr tag (pre ++ f₂ :: fs₁)) :=
        ctxEq_constr_one hrel.1
      -- Step B: shift the prefix one to the right and recurse on the tails
      have hB := ih (pre := pre ++ [f₂]) hrel.2
      have e1 : (pre ++ [f₂]) ++ fs₁ = pre ++ (f₂ :: fs₁) := by simp
      have e2 : (pre ++ [f₂]) ++ fs₂ = pre ++ (f₂ :: fs₂) := by simp
      rw [e1, e2] at hB
      refine ctxEq_trans ?_ hA hB
      intro C hC1 hC2
      have d1 := (fill_closedAt_iff C (.Constr tag (pre ++ f₁ :: fs₁)) 0).mp hC1
      have d2 := (fill_closedAt_iff C (.Constr tag (pre ++ f₂ :: fs₂)) 0).mp hC2
      simp only [Nat.zero_add, closedAt] at d1 d2
      have e1' := (closedAtList_append C.binders pre (f₁ :: fs₁)).mp d1.2
      have e2' := (closedAtList_append C.binders pre (f₂ :: fs₂)).mp d2.2
      simp only [closedAtList, Bool.and_eq_true] at e1' e2'
      refine (fill_closedAt_iff C (.Constr tag (pre ++ f₂ :: fs₁)) 0).mpr ⟨d1.1, ?_⟩
      simp only [Nat.zero_add, closedAt]
      refine (closedAtList_append C.binders pre (f₂ :: fs₁)).mpr ⟨e1'.1, ?_⟩
      simp only [closedAtList, Bool.and_eq_true]
      exact ⟨e2'.2.1, e1'.2.2⟩

/-- General Constr congruence in head-tail form, mirroring `compat_constr`. -/
theorem ctxEq_constr {tag : Nat} {m₁ m₂ : Term} {ms₁ ms₂ : List Term}
    (hm : CtxEq m₁ m₂) (hms : ListRel CtxEq ms₁ ms₂) :
    CtxEq (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  have hrel : ListRel CtxEq (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have := ctxEq_constr_swap_prefix (tag := tag) [] hrel
  simpa using this

/-- Case scrutinee-swap congruence: swap only the scrutinee, leave `alts` fixed. -/
theorem ctxEq_case_scrut {scrut₁ scrut₂ : Term} {alts : List Term}
    (hscrut : CtxEq scrut₁ scrut₂) :
    CtxEq (.Case scrut₁ alts) (.Case scrut₂ alts) := by
  have hwrap := ctxEq_extend hscrut (.Case .Hole alts)
  simpa [fill] using hwrap

/-- Case alt-swap congruence (single position): swaps one alt at slot `|pre|`. -/
theorem ctxEq_case_one_alt {scrut : Term} {a b : Term} {pre post : List Term}
    (hab : CtxEq a b) :
    CtxEq (.Case scrut (pre ++ a :: post)) (.Case scrut (pre ++ b :: post)) := by
  have hwrap := ctxEq_extend hab (.CaseAlt scrut pre .Hole post)
  simpa [fill] using hwrap

/-- Inductive worker for the Case alt-list pointwise congruence. -/
private theorem ctxEq_case_swap_prefix {scrut : Term} {as₁ as₂ : List Term}
    (pre : List Term) (hrel : ListRel CtxEq as₁ as₂) :
    CtxEq (.Case scrut (pre ++ as₁)) (.Case scrut (pre ++ as₂)) := by
  induction as₁ generalizing as₂ pre with
  | nil =>
    cases as₂ with
    | nil => exact ctxEq_refl _
    | cons => exact absurd hrel id
  | cons a₁ as₁ ih =>
    cases as₂ with
    | nil => exact absurd hrel id
    | cons a₂ as₂ =>
      have hA : CtxEq (.Case scrut (pre ++ a₁ :: as₁)) (.Case scrut (pre ++ a₂ :: as₁)) :=
        ctxEq_case_one_alt hrel.1
      have hB := ih (pre := pre ++ [a₂]) hrel.2
      have e1 : (pre ++ [a₂]) ++ as₁ = pre ++ (a₂ :: as₁) := by simp
      have e2 : (pre ++ [a₂]) ++ as₂ = pre ++ (a₂ :: as₂) := by simp
      rw [e1, e2] at hB
      refine ctxEq_trans ?_ hA hB
      intro C hC1 hC2
      have d1 := (fill_closedAt_iff C (.Case scrut (pre ++ a₁ :: as₁)) 0).mp hC1
      have d2 := (fill_closedAt_iff C (.Case scrut (pre ++ a₂ :: as₂)) 0).mp hC2
      simp only [Nat.zero_add, closedAt, Bool.and_eq_true] at d1 d2
      have e1' := (closedAtList_append C.binders pre (a₁ :: as₁)).mp d1.2.2
      have e2' := (closedAtList_append C.binders pre (a₂ :: as₂)).mp d2.2.2
      simp only [closedAtList, Bool.and_eq_true] at e1' e2'
      refine (fill_closedAt_iff C (.Case scrut (pre ++ a₂ :: as₁)) 0).mpr ⟨d1.1, ?_⟩
      simp only [Nat.zero_add, closedAt, Bool.and_eq_true]
      refine ⟨d1.2.1, ?_⟩
      refine (closedAtList_append C.binders pre (a₂ :: as₁)).mpr ⟨e1'.1, ?_⟩
      simp only [closedAtList, Bool.and_eq_true]
      exact ⟨e2'.2.1, e1'.2.2⟩

/-- General Case congruence: swap both the scrutinee and the alts pointwise. -/
theorem ctxEq_case {scrut₁ scrut₂ : Term} {alts₁ alts₂ : List Term}
    (hscrut : CtxEq scrut₁ scrut₂)
    (halts : ListRel CtxEq alts₁ alts₂) :
    CtxEq (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  have hA : CtxEq (.Case scrut₁ alts₁) (.Case scrut₂ alts₁) := ctxEq_case_scrut hscrut
  have hB : CtxEq (.Case scrut₂ alts₁) (.Case scrut₂ alts₂) := by
    have := ctxEq_case_swap_prefix (scrut := scrut₂) (pre := []) halts
    simpa using this
  refine ctxEq_trans ?_ hA hB
  intro C hC1 hC2
  have d1 := (fill_closedAt_iff C (.Case scrut₁ alts₁) 0).mp hC1
  have d2 := (fill_closedAt_iff C (.Case scrut₂ alts₂) 0).mp hC2
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true] at d1 d2
  refine (fill_closedAt_iff C (.Case scrut₂ alts₁) 0).mpr ⟨d1.1, ?_⟩
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true]
  exact ⟨d2.2.1, d1.2.2⟩

--------------------------------------------------------------------------------
-- CONGRUENCE THEOREMS FOR CtxRefines
--------------------------------------------------------------------------------

/-- Generic single-subterm extension for `CtxRefines`. Mirrors `ctxEq_extend`. -/
private theorem ctxRefines_extend
    {t₁ t₂ : Term} (h : CtxRefines t₁ t₂) (inner : Context) :
    CtxRefines (fill inner t₁) (fill inner t₂) := by
  intro C
  have h_filled := h (Context.compose C inner)
  rw [fill_compose, fill_compose] at h_filled
  exact h_filled

/-- Lambda congruence for `CtxRefines`. -/
theorem ctxRefines_lam {body₁ body₂ : Term} (name : Nat) (h : CtxRefines body₁ body₂) :
    CtxRefines (.Lam name body₁) (.Lam name body₂) := by
  have hwrap := ctxRefines_extend h (.Lam name .Hole)
  simpa [fill] using hwrap

/-- Delay congruence for `CtxRefines`. -/
theorem ctxRefines_delay {body₁ body₂ : Term} (h : CtxRefines body₁ body₂) :
    CtxRefines (.Delay body₁) (.Delay body₂) := by
  have hwrap := ctxRefines_extend h (.Delay .Hole)
  simpa [fill] using hwrap

/-- Force congruence for `CtxRefines`. -/
theorem ctxRefines_force {t₁ t₂ : Term} (h : CtxRefines t₁ t₂) :
    CtxRefines (.Force t₁) (.Force t₂) := by
  have hwrap := ctxRefines_extend h (.Force .Hole)
  simpa [fill] using hwrap

/-- Apply congruence for `CtxRefines`. -/
theorem ctxRefines_app {f₁ f₂ a₁ a₂ : Term}
    (hf : CtxRefines f₁ f₂) (ha : CtxRefines a₁ a₂) :
    CtxRefines (.Apply f₁ a₁) (.Apply f₂ a₂) := by
  have hA : CtxRefines (.Apply f₁ a₁) (.Apply f₂ a₁) := by
    have := ctxRefines_extend hf (.AppLeft .Hole a₁)
    simpa [fill] using this
  have hB : CtxRefines (.Apply f₂ a₁) (.Apply f₂ a₂) := by
    have := ctxRefines_extend ha (.AppRight f₂ .Hole)
    simpa [fill] using this
  exact ctxRefines_trans hA hB

/-- Constr single-position congruence for `CtxRefines`. -/
theorem ctxRefines_constr_one {tag : Nat} {a b : Term} {pre post : List Term}
    (hab : CtxRefines a b) :
    CtxRefines (.Constr tag (pre ++ a :: post)) (.Constr tag (pre ++ b :: post)) := by
  have hwrap := ctxRefines_extend hab (.Constr tag pre .Hole post)
  simpa [fill] using hwrap

/-- Inductive walker for the Constr congruence: swaps one field at a time. -/
private theorem ctxRefines_constr_swap_prefix {tag : Nat} {fs₁ fs₂ : List Term}
    (pre : List Term) (hrel : ListRel CtxRefines fs₁ fs₂) :
    CtxRefines (.Constr tag (pre ++ fs₁)) (.Constr tag (pre ++ fs₂)) := by
  induction fs₁ generalizing fs₂ pre with
  | nil =>
    cases fs₂ with
    | nil => exact ctxRefines_refl _
    | cons => exact absurd hrel id
  | cons f₁ fs₁ ih =>
    cases fs₂ with
    | nil => exact absurd hrel id
    | cons f₂ fs₂ =>
      have hA : CtxRefines (.Constr tag (pre ++ f₁ :: fs₁))
          (.Constr tag (pre ++ f₂ :: fs₁)) :=
        ctxRefines_constr_one hrel.1
      have hB := ih (pre := pre ++ [f₂]) hrel.2
      have e1 : (pre ++ [f₂]) ++ fs₁ = pre ++ (f₂ :: fs₁) := by simp
      have e2 : (pre ++ [f₂]) ++ fs₂ = pre ++ (f₂ :: fs₂) := by simp
      rw [e1, e2] at hB
      exact ctxRefines_trans hA hB

/-- General Constr congruence for `CtxRefines` in head-tail form. -/
theorem ctxRefines_constr {tag : Nat} {m₁ m₂ : Term} {ms₁ ms₂ : List Term}
    (hm : CtxRefines m₁ m₂) (hms : ListRel CtxRefines ms₁ ms₂) :
    CtxRefines (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  have hrel : ListRel CtxRefines (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have := ctxRefines_constr_swap_prefix (tag := tag) [] hrel
  simpa using this

/-- Case scrutinee-swap congruence for `CtxRefines`. -/
theorem ctxRefines_case_scrut {scrut₁ scrut₂ : Term} {alts : List Term}
    (hscrut : CtxRefines scrut₁ scrut₂) :
    CtxRefines (.Case scrut₁ alts) (.Case scrut₂ alts) := by
  have hwrap := ctxRefines_extend hscrut (.Case .Hole alts)
  simpa [fill] using hwrap

/-- Case alt-swap (single position) congruence for `CtxRefines`. -/
theorem ctxRefines_case_one_alt {scrut : Term} {a b : Term} {pre post : List Term}
    (hab : CtxRefines a b) :
    CtxRefines (.Case scrut (pre ++ a :: post)) (.Case scrut (pre ++ b :: post)) := by
  have hwrap := ctxRefines_extend hab (.CaseAlt scrut pre .Hole post)
  simpa [fill] using hwrap

/-- Inductive walker for the Case alt-list pointwise congruence. -/
private theorem ctxRefines_case_swap_prefix {scrut : Term} {as₁ as₂ : List Term}
    (pre : List Term) (hrel : ListRel CtxRefines as₁ as₂) :
    CtxRefines (.Case scrut (pre ++ as₁)) (.Case scrut (pre ++ as₂)) := by
  induction as₁ generalizing as₂ pre with
  | nil =>
    cases as₂ with
    | nil => exact ctxRefines_refl _
    | cons => exact absurd hrel id
  | cons a₁ as₁ ih =>
    cases as₂ with
    | nil => exact absurd hrel id
    | cons a₂ as₂ =>
      have hA : CtxRefines (.Case scrut (pre ++ a₁ :: as₁))
          (.Case scrut (pre ++ a₂ :: as₁)) :=
        ctxRefines_case_one_alt hrel.1
      have hB := ih (pre := pre ++ [a₂]) hrel.2
      have e1 : (pre ++ [a₂]) ++ as₁ = pre ++ (a₂ :: as₁) := by simp
      have e2 : (pre ++ [a₂]) ++ as₂ = pre ++ (a₂ :: as₂) := by simp
      rw [e1, e2] at hB
      exact ctxRefines_trans hA hB

/-- General Case congruence for `CtxRefines`: swap scrutinee and alts pointwise. -/
theorem ctxRefines_case {scrut₁ scrut₂ : Term} {alts₁ alts₂ : List Term}
    (hscrut : CtxRefines scrut₁ scrut₂)
    (halts : ListRel CtxRefines alts₁ alts₂) :
    CtxRefines (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  have hA : CtxRefines (.Case scrut₁ alts₁) (.Case scrut₂ alts₁) :=
    ctxRefines_case_scrut hscrut
  have hB : CtxRefines (.Case scrut₂ alts₁) (.Case scrut₂ alts₂) := by
    have := ctxRefines_case_swap_prefix (scrut := scrut₂) (pre := []) halts
    simpa using this
  exact ctxRefines_trans hA hB

end Moist.Verified.Contextual
