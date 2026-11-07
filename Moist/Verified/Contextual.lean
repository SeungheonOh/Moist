import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.Verified.Equivalence
import Moist.Verified.Definitions.Contextual

namespace Moist.Verified.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence

--------------------------------------------------------------------------------
-- Theorems.
--
-- Core definitions (`Context`, `fill`, `Context.binders`, `Context.closedAt`,
-- `Context.compose`, `CtxEq`, `ObsRefines`, `CtxRefines`) now live in
-- `Moist.Verified.Definitions.Contextual`. This file hosts the
-- theorems about them.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 4. CONTEXT COMPOSITION (plumbing for congruence theorems)
--
-- `Context.compose` itself is now defined in
-- `Moist.Verified.Definitions.Contextual`; theorems about it stay here.
--------------------------------------------------------------------------------

/-- The composition law: filling a composed context equals filling outer with the
    inner-filled term. -/
theorem fill_compose (outer inner : Context) (t : Term) :
    fill (Context.compose outer inner) t = fill outer (fill inner t) := by
  induction outer with
  | Hole => rfl
  | Lam x C ih => simp [Context.compose, fill, ih]
  | AppLeft C e ih => simp [Context.compose, fill, ih]
  | AppRight e C ih => simp [Context.compose, fill, ih]
  | Delay C ih => simp [Context.compose, fill, ih]
  | Force C ih => simp [Context.compose, fill, ih]
  | Constr tag lefts C rights ih => simp [Context.compose, fill, ih]
  | Case C alts ih => simp [Context.compose, fill, ih]
  | CaseAlt scrut lefts C rights ih => simp [Context.compose, fill, ih]

/-- `closedAtList` distributes over list concatenation. -/
theorem closedAtList_append (d : Nat) (xs ys : List Term) :
    closedAtList d (xs ++ ys) = true ↔
      closedAtList d xs = true ∧ closedAtList d ys = true := by
  induction xs with
  | nil => simp [closedAtList]
  | cons x xs ih =>
    simp only [List.cons_append, closedAtList, Bool.and_eq_true]
    constructor
    · rintro ⟨hx, hrest⟩
      have := ih.mp hrest
      exact ⟨⟨hx, this.1⟩, this.2⟩
    · rintro ⟨⟨hx, hxs⟩, hys⟩
      exact ⟨hx, ih.mpr ⟨hxs, hys⟩⟩

mutual
  /-- Monotonicity of `closedAt`: a term closed at depth `d` is also closed
      at any larger depth. Re-established for `Moist.Verified.closedAt`
      after its removal from the old Contextual chain (see PathA postmortem). -/
  theorem closedAt_mono {d d' : Nat} {t : Term} (h : closedAt d t = true) (hle : d ≤ d') :
      closedAt d' t = true := by
    cases t with
    | Var n =>
      simp only [closedAt] at h ⊢
      exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) hle)
    | Lam _ body =>
      simp only [closedAt] at h ⊢
      exact closedAt_mono h (by omega)
    | Apply f x =>
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono h.1 hle, closedAt_mono h.2 hle⟩
    | Force e =>
      simp only [closedAt] at h ⊢
      exact closedAt_mono h hle
    | Delay e =>
      simp only [closedAt] at h ⊢
      exact closedAt_mono h hle
    | Constr _ args =>
      simp only [closedAt] at h ⊢
      exact closedAtList_mono h hle
    | Case scrut alts =>
      simp only [closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono h.1 hle, closedAtList_mono h.2 hle⟩
    | Constant _ => simp [closedAt]
    | Builtin _ => simp [closedAt]
    | Error => simp [closedAt]
  termination_by sizeOf t

  /-- Monotonicity of `closedAtList`. -/
  theorem closedAtList_mono {d d' : Nat} {ts : List Term}
      (h : closedAtList d ts = true) (hle : d ≤ d') :
      closedAtList d' ts = true := by
    cases ts with
    | nil => simp [closedAtList]
    | cons t rest =>
      simp only [closedAtList, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_mono h.1 hle, closedAtList_mono h.2 hle⟩
  termination_by sizeOf ts
end

/-- `closedAtList` on a singleton unfolds to the element. -/
theorem closedAtList_singleton (d : Nat) (t : Term) :
    closedAtList d [t] = true ↔ closedAt d t = true := by
  simp [closedAtList]

/-- **Decomposition lemma**: closedness of `fill C t` at depth `d` is exactly
    closedness of `C` at `d` plus closedness of `t` at the shifted depth
    `d + C.binders`. This is the key lemma that lets us discharge the
    middle-term closedness side conditions in the transitivity calls of the
    congruence theorems below. -/
theorem fill_closedAt_iff (C : Context) (t : Term) :
    ∀ (d : Nat), closedAt d (fill C t) = true ↔
      C.closedAt d = true ∧ closedAt (d + C.binders) t = true := by
  induction C with
  | Hole =>
    intro d
    simp [fill, Context.closedAt, Context.binders]
  | Lam x C ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders]
    rw [ih (d + 1)]
    constructor
    · rintro ⟨hC, ht⟩
      have : (d + 1) + C.binders = d + (C.binders + 1) := by omega
      rw [this] at ht
      exact ⟨hC, ht⟩
    · rintro ⟨hC, ht⟩
      have : (d + 1) + C.binders = d + (C.binders + 1) := by omega
      rw [this]
      exact ⟨hC, ht⟩
  | AppLeft C e ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders, Bool.and_eq_true]
    rw [ih d]
    constructor
    · rintro ⟨⟨hC, ht⟩, he⟩
      exact ⟨⟨hC, he⟩, ht⟩
    · rintro ⟨⟨hC, he⟩, ht⟩
      exact ⟨⟨hC, ht⟩, he⟩
  | AppRight e C ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders, Bool.and_eq_true]
    rw [ih d]
    constructor
    · rintro ⟨he, hC, ht⟩
      exact ⟨⟨he, hC⟩, ht⟩
    · rintro ⟨⟨he, hC⟩, ht⟩
      exact ⟨he, hC, ht⟩
  | Delay C ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders]
    exact ih d
  | Force C ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders]
    exact ih d
  | Constr tag lefts C rights ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders, Bool.and_eq_true]
    constructor
    · intro hlist
      have h1 := (closedAtList_append d (lefts ++ [fill C t]) rights).mp hlist
      have h2 := (closedAtList_append d lefts [fill C t]).mp h1.1
      have h3 := (closedAtList_singleton d (fill C t)).mp h2.2
      have h4 := (ih d).mp h3
      exact ⟨⟨⟨h2.1, h4.1⟩, h1.2⟩, h4.2⟩
    · rintro ⟨⟨⟨hL, hC⟩, hR⟩, ht⟩
      have h3 := (ih d).mpr ⟨hC, ht⟩
      have h2 := (closedAtList_singleton d (fill C t)).mpr h3
      have h1 := (closedAtList_append d lefts [fill C t]).mpr ⟨hL, h2⟩
      exact (closedAtList_append d (lefts ++ [fill C t]) rights).mpr ⟨h1, hR⟩
  | Case C alts ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders, Bool.and_eq_true]
    rw [ih d]
    constructor
    · rintro ⟨⟨hC, ht⟩, hA⟩
      exact ⟨⟨hC, hA⟩, ht⟩
    · rintro ⟨⟨hC, hA⟩, ht⟩
      exact ⟨⟨hC, ht⟩, hA⟩
  | CaseAlt scrut lefts C rights ih =>
    intro d
    simp only [fill, closedAt, Context.closedAt, Context.binders, Bool.and_eq_true]
    constructor
    · rintro ⟨hs, hlist⟩
      have h1 := (closedAtList_append d (lefts ++ [fill C t]) rights).mp hlist
      have h2 := (closedAtList_append d lefts [fill C t]).mp h1.1
      have h3 := (closedAtList_singleton d (fill C t)).mp h2.2
      have h4 := (ih d).mp h3
      exact ⟨⟨⟨⟨hs, h2.1⟩, h4.1⟩, h1.2⟩, h4.2⟩
    · rintro ⟨⟨⟨⟨hs, hL⟩, hC⟩, hR⟩, ht⟩
      have h3 := (ih d).mpr ⟨hC, ht⟩
      have h2 := (closedAtList_singleton d (fill C t)).mpr h3
      have h1 := (closedAtList_append d lefts [fill C t]).mpr ⟨hL, h2⟩
      refine ⟨hs, ?_⟩
      exact (closedAtList_append d (lefts ++ [fill C t]) rights).mpr ⟨h1, hR⟩

--------------------------------------------------------------------------------
-- CONTEXTUAL REFINEMENT
--------------------------------------------------------------------------------

/-- Reflexivity: refinement is the identity implication on both halt and error. -/
theorem ctxRefines_refl (t : Term) : CtxRefines t t := by
  intro C hC
  exact ⟨hC, ObsRefines.mk (fun h => h) (fun h => h)⟩

/-- Transitivity of `CtxRefines`. Thanks to the bundled closedness
    preservation, this is a clean composition — no side conditions. -/
theorem ctxRefines_trans {t₁ t₂ t₃ : Term}
    (h12 : CtxRefines t₁ t₂) (h23 : CtxRefines t₂ t₃) : CtxRefines t₁ t₃ := by
  intro C hC1
  obtain ⟨hC2, ref12⟩ := h12 C hC1
  obtain ⟨hC3, ref23⟩ := h23 C hC2
  refine ⟨hC3, ?_⟩
  exact ObsRefines.mk
    (fun h_t1 => ref23.halt (ref12.halt h_t1))
    (fun h_t1 => ref23.error (ref12.error h_t1))

end Moist.Verified.Contextual
