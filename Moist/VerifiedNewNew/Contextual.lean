import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.VerifiedNewNew.Equivalence
import Moist.VerifiedNewNew.Definitions.Contextual

namespace Moist.VerifiedNewNew.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew (closedAt closedAtList)
open Moist.VerifiedNewNew.Equivalence

--------------------------------------------------------------------------------
-- Theorems.
--
-- Core definitions (`Context`, `fill`, `Context.binders`, `Context.closedAt`,
-- `Context.compose`, `CtxEq`, `ObsRefines`, `CtxRefines`) now live in
-- `Moist.VerifiedNewNew.Definitions.Contextual`. This file hosts the
-- theorems about them.
--------------------------------------------------------------------------------

/--
  Transitivity of guarded contextual equivalence. Needs an auxiliary closedness
  hypothesis on the intermediate term at every context, which caller-side
  helpers (`ctxEq_extend`) thread through naturally. The generic form takes
  it as a side condition; specialized congruence rules discharge it
  structurally.
-/
theorem ctxEq_trans {t₁ t₂ t₃ : Term}
    (h_closed_mid : ∀ C, closedAt 0 (fill C t₁) = true →
                          closedAt 0 (fill C t₃) = true →
                          closedAt 0 (fill C t₂) = true) :
    CtxEq t₁ t₂ → CtxEq t₂ t₃ → CtxEq t₁ t₃ := by
  intro h1 h2 C hC1 hC3
  have hC2 := h_closed_mid C hC1 hC3
  have eq12 := h1 C hC1 hC2
  have eq23 := h2 C hC2 hC3
  exact ObsEq.mk (Iff.trans eq12.halt eq23.halt) (Iff.trans eq12.error eq23.error)

/-- Reflexivity of `CtxEq`. -/
theorem ctxEq_refl (t : Term) : CtxEq t t := by
  intro C _ _
  exact ObsEq.mk Iff.rfl Iff.rfl

/-- Symmetry of `CtxEq`. -/
theorem ctxEq_symm {t₁ t₂ : Term} (h : CtxEq t₁ t₂) : CtxEq t₂ t₁ := by
  intro C hC2 hC1
  have obs := h C hC1 hC2
  exact ObsEq.mk obs.halt.symm obs.error.symm

--------------------------------------------------------------------------------
-- 4. CONTEXT COMPOSITION (plumbing for congruence theorems)
--
-- `Context.compose` itself is now defined in
-- `Moist.VerifiedNewNew.Definitions.Contextual`; theorems about it stay here.
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

/-- Number of binders is additive under composition (since the inner context's
    binders are nested below the outer's). -/
theorem Context.compose_binders (outer inner : Context) :
    (Context.compose outer inner).binders = outer.binders + inner.binders := by
  induction outer with
  | Hole => simp [Context.compose, Context.binders]
  | Lam x C ih =>
    simp [Context.compose, Context.binders, ih]; omega
  | AppLeft C e ih => simp [Context.compose, Context.binders, ih]
  | AppRight e C ih => simp [Context.compose, Context.binders, ih]
  | Delay C ih => simp [Context.compose, Context.binders, ih]
  | Force C ih => simp [Context.compose, Context.binders, ih]
  | Constr tag lefts C rights ih => simp [Context.compose, Context.binders, ih]
  | Case C alts ih => simp [Context.compose, Context.binders, ih]
  | CaseAlt scrut lefts C rights ih => simp [Context.compose, Context.binders, ih]

/-- Closedness of a composed context: the outer must be closed at `d`, and the
    inner must be closed at `d + outer.binders` (the depth at which it sits). -/
theorem Context.compose_closedAt {outer inner : Context} :
    ∀ {d : Nat}, outer.closedAt d = true →
      inner.closedAt (d + outer.binders) = true →
      (Context.compose outer inner).closedAt d = true := by
  induction outer with
  | Hole =>
    intro d _ hinner
    simpa [Context.compose, Context.binders] using hinner
  | Lam x C ih =>
    intro d houter hinner
    -- (.Lam x C).closedAt d = C.closedAt (d+1)
    -- (.Lam x C).binders = C.binders + 1
    -- need: (compose (.Lam x C) inner).closedAt d = (.Lam x (compose C inner)).closedAt d
    --     = (compose C inner).closedAt (d+1)
    have hC : C.closedAt (d + 1) = true := houter
    have hi : inner.closedAt ((d + 1) + C.binders) = true := by
      have : (d + 1) + C.binders = d + (C.binders + 1) := by omega
      rw [this]; exact hinner
    show (Context.compose C inner).closedAt (d + 1) = true
    exact ih hC hi
  | AppLeft C e ih =>
    intro d houter hinner
    simp [Context.closedAt, Context.compose, Context.binders] at houter hinner ⊢
    exact ⟨ih houter.1 hinner, houter.2⟩
  | AppRight e C ih =>
    intro d houter hinner
    simp [Context.closedAt, Context.compose, Context.binders] at houter hinner ⊢
    exact ⟨houter.1, ih houter.2 hinner⟩
  | Delay C ih =>
    intro d houter hinner
    show (Context.compose C inner).closedAt d = true
    exact ih houter hinner
  | Force C ih =>
    intro d houter hinner
    show (Context.compose C inner).closedAt d = true
    exact ih houter hinner
  | Constr tag lefts C rights ih =>
    intro d houter hinner
    simp [Context.closedAt, Context.compose, Context.binders] at houter hinner ⊢
    exact ⟨⟨houter.1.1, ih houter.1.2 hinner⟩, houter.2⟩
  | Case C alts ih =>
    intro d houter hinner
    simp [Context.closedAt, Context.compose, Context.binders] at houter hinner ⊢
    exact ⟨ih houter.1 hinner, houter.2⟩
  | CaseAlt scrut lefts C rights ih =>
    intro d houter hinner
    simp [Context.closedAt, Context.compose, Context.binders] at houter hinner ⊢
    exact ⟨⟨⟨houter.1.1.1, houter.1.1.2⟩, ih houter.1.2 hinner⟩, houter.2⟩

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
      at any larger depth. Re-established for `Moist.VerifiedNewNew.closedAt`
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
-- 5. CONGRUENCE THEOREMS FOR CtxEq
--
-- Moved to `Moist.VerifiedNewNew.Contextual.Congruence`. That module reopens
-- the `Moist.VerifiedNewNew.Contextual` namespace, so the names are accessed
-- as `Contextual.ctxEq_lam` etc. just like before.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 6. CONTEXTUAL REFINEMENT
--
-- One-directional sibling of `CtxEq`: `t₁ ⊑Ctx t₂` says that whenever `t₁`
-- converges in a closed context, so does `t₂`. The two relations are linked
-- by `ctxRefines_antisymm` (CtxRefines both ways ↔ CtxEq).
--
-- `ObsRefines` and `CtxRefines` themselves are defined in
-- `Moist.VerifiedNewNew.Definitions.Contextual`; theorems stay here.
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

/-- Equivalence subsumes refinement (forward direction). Requires an
    external proof that `CtxEq` preserves closedness in the forward
    direction, since `CtxEq` itself is closedness-agnostic. -/
theorem CtxEq.toCtxRefines {t₁ t₂ : Term} (h : CtxEq t₁ t₂)
    (h_close : ∀ C, closedAt 0 (fill C t₁) = true → closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ := by
  intro C hC1
  have hC2 := h_close C hC1
  have obs := h C hC1 hC2
  exact ⟨hC2, ObsRefines.mk obs.halt.mp obs.error.mp⟩

/-- Equivalence subsumes refinement (backward direction). Requires an
    external proof that `CtxEq` preserves closedness in the backward
    direction. -/
theorem CtxEq.toCtxRefines_symm {t₁ t₂ : Term} (h : CtxEq t₁ t₂)
    (h_close : ∀ C, closedAt 0 (fill C t₂) = true → closedAt 0 (fill C t₁) = true) :
    CtxRefines t₂ t₁ := by
  intro C hC2
  have hC1 := h_close C hC2
  have obs := h C hC1 hC2
  exact ⟨hC1, ObsRefines.mk obs.halt.mpr obs.error.mpr⟩

/-- Antisymmetry: bidirectional refinement gives equivalence. -/
theorem ctxRefines_antisymm {t₁ t₂ : Term} :
    CtxRefines t₁ t₂ → CtxRefines t₂ t₁ → CtxEq t₁ t₂ := by
  intro h12 h21 C hC1 hC2
  obtain ⟨_, ref12⟩ := h12 C hC1
  obtain ⟨_, ref21⟩ := h21 C hC2
  exact ObsEq.mk
    (Iff.intro ref12.halt ref21.halt)
    (Iff.intro ref12.error ref21.error)

--------------------------------------------------------------------------------
-- CONGRUENCE THEOREMS FOR CtxRefines
--
-- Moved to `Moist.VerifiedNewNew.Contextual.Congruence` (same file as the
-- `CtxEq` congruences).
--------------------------------------------------------------------------------

/-!
### Soundness

The open-context soundness theorem

```
theorem soundness {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ (C : Context),
      ObsEq (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂))
```

lives in `Moist.VerifiedNewNew.Contextual.Soundness` and bridges directly
from the semantic `OpenEq` into the new open-context `CtxEq` above. Import
that module to use it.
-/

end Moist.VerifiedNewNew.Contextual
