import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.VerifiedNewNew.Equivalence

namespace Moist.VerifiedNewNew.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew (closedAt closedAtList)
open Moist.VerifiedNewNew.Equivalence

--------------------------------------------------------------------------------
-- 1. SYNTACTIC CONTEXTS
--------------------------------------------------------------------------------

/--
  A program context: an AST with exactly one `Hole`.
  This mirrors the `Term` inductive type.
-/
inductive Context
  | Hole : Context
  | Lam : Nat → Context → Context
  | AppLeft : Context → Term → Context
  | AppRight : Term → Context → Context
  | Delay : Context → Context
  | Force : Context → Context
  | Constr : Nat → List Term → Context → List Term → Context
  | Case : Context → List Term → Context
  /-- Hole inside a single alt of a `Case`.
      `CaseAlt scrut lefts C rights` places the hole at slot `|lefts|` of
      `Case scrut (lefts ++ [HOLE] ++ rights)`. -/
  | CaseAlt : Term → List Term → Context → List Term → Context
  -- NOTE: No `Builtin` constructor: `Term.Builtin : BuiltinFun → Term` is nullary;
  -- builtin arguments are introduced via `Apply`, so the `AppLeft`/`AppRight` cases
  -- already cover holes inside builtin applications.

--------------------------------------------------------------------------------
-- 2. THE FILL OPERATOR (Capture-Permitting Substitution)
--------------------------------------------------------------------------------

/--
  Plugs a term into the context hole.
  Variable capture is strictly permitted to simulate adversarial environments.
-/
def fill : Context → Term → Term
  | .Hole, t => t
  | .Lam x C, t => .Lam x (fill C t)
  | .AppLeft C e, t => .Apply (fill C t) e
  | .AppRight e C, t => .Apply e (fill C t)
  | .Delay C, t => .Delay (fill C t)
  | .Force C, t => .Force (fill C t)
  | .Constr tag lefts C rights, t => .Constr tag (lefts ++ [fill C t] ++ rights)
  | .Case C alts, t => .Case (fill C t) alts
  | .CaseAlt scrut lefts C rights, t => .Case scrut (lefts ++ [fill C t] ++ rights)

--------------------------------------------------------------------------------
-- 3. CONTEXTUAL EQUIVALENCE & TRANSITIVITY
--------------------------------------------------------------------------------

/--
  Number of binders the context introduces above the hole.
  Used to relate the OpenEq depth at the hole to the OpenEq depth at the root.
-/
def Context.binders : Context → Nat
  | .Hole => 0
  | .Lam _ C => C.binders + 1
  | .AppLeft C _ | .AppRight _ C
  | .Delay C    | .Force C
  | .Constr _ _ C _ | .Case C _
  | .CaseAlt _ _ C _ => C.binders

/--
  `C.closedAt d` asserts that every non-hole sibling term embedded in `C` is
  closed at the depth at which it sits inside the context, when `C` itself is
  interpreted at root depth `d`. Lambdas in the context bump the depth by one
  for everything beneath them.
-/
def Context.closedAt : Nat → Context → Bool
  | _, .Hole => true
  | d, .Lam _ C => Context.closedAt (d + 1) C
  | d, .AppLeft C e => Context.closedAt d C && Moist.VerifiedNewNew.closedAt d e
  | d, .AppRight e C => Moist.VerifiedNewNew.closedAt d e && Context.closedAt d C
  | d, .Delay C => Context.closedAt d C
  | d, .Force C => Context.closedAt d C
  | d, .Constr _ lefts C rights =>
      Moist.VerifiedNewNew.closedAtList d lefts && Context.closedAt d C
        && Moist.VerifiedNewNew.closedAtList d rights
  | d, .Case C alts =>
      Context.closedAt d C && Moist.VerifiedNewNew.closedAtList d alts
  | d, .CaseAlt scrut lefts C rights =>
      Moist.VerifiedNewNew.closedAt d scrut
        && Moist.VerifiedNewNew.closedAtList d lefts && Context.closedAt d C
        && Moist.VerifiedNewNew.closedAtList d rights

-- The `fill_closedAt_iff` lemma proved further below discharges the
-- middle-term closedness side conditions on `ctxEq_trans` / `ctxRefines_trans`
-- at each congruence call site.

/--
  **Guarded** contextual equivalence: `t₁ ≈ t₂` iff for every context `C`
  that fully closes both `fill C t₁` and `fill C t₂` at depth 0, the empty-
  state CEK runs are observationally equivalent. The closedness premises
  ensure that during CEK evaluation we never reach the hole with missing
  bindings — the context supplies exactly the right number of binders,
  which lets us bake `ρ.length = d` into `EnvEqK`. Without this guard, we'd
  have to accept ghost `(none, none)` lookups and the soundness bridge
  would have no way to discharge the purity obligations that strict-error
  refinement demands.
-/
def CtxEq (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    closedAt 0 (fill C t₁) = true →
    closedAt 0 (fill C t₂) = true →
    ObsEq (.compute [] .nil (fill C t₁))
          (.compute [] .nil (fill C t₂))

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
--------------------------------------------------------------------------------

/-- Plug `inner` into the hole of `outer`. Standard context composition. -/
def Context.compose : Context → Context → Context
  | .Hole, inner => inner
  | .Lam x C, inner => .Lam x (Context.compose C inner)
  | .AppLeft C e, inner => .AppLeft (Context.compose C inner) e
  | .AppRight e C, inner => .AppRight e (Context.compose C inner)
  | .Delay C, inner => .Delay (Context.compose C inner)
  | .Force C, inner => .Force (Context.compose C inner)
  | .Constr tag lefts C rights, inner =>
      .Constr tag lefts (Context.compose C inner) rights
  | .Case C alts, inner => .Case (Context.compose C inner) alts
  | .CaseAlt scrut lefts C rights, inner =>
      .CaseAlt scrut lefts (Context.compose C inner) rights

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
-- 5. CONGRUENCE THEOREMS FOR CtxEq (port of compat_* from Equivalence)
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
-- 6. CONTEXTUAL REFINEMENT
--
-- One-directional sibling of `CtxEq`: `t₁ ⊑Ctx t₂` says that whenever `t₁`
-- converges in a closed context, so does `t₂`. The two relations are linked
-- by `ctxRefines_antisymm` (CtxRefines both ways ↔ CtxEq).
--------------------------------------------------------------------------------

/-- Observational refinement: `c₂` refines `c₁`'s halt AND error behavior.
    This prevents unsound transforms like `Let x = Error in 10 ⊑ 10`.
    Defined as a `structure` for the same reason `ObsEq` is — unambiguous
    destructuring/construction with `.halt`/`.error`/`ObsRefines.mk`. -/
structure ObsRefines (c₁ c₂ : State) : Prop where
  halt : (∃ v₁, Reaches c₁ (.halt v₁)) → (∃ v₂, Reaches c₂ (.halt v₂))
  error : Reaches c₁ .error → Reaches c₂ .error

/-- **Guarded** contextual refinement: `t₁ ⊑ t₂` iff for every closing context
    `C`, the empty-state CEK run of `fill C t₁` is halt/error-refined by that
    of `fill C t₂`. Same closedness guard as `CtxEq`. -/
def CtxRefines (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    closedAt 0 (fill C t₁) = true →
    closedAt 0 (fill C t₂) = true →
    ObsRefines (.compute [] .nil (fill C t₁))
               (.compute [] .nil (fill C t₂))

@[inherit_doc] scoped infix:50 " ⊑Ctx " => CtxRefines

/-- Reflexivity: refinement is the identity implication on both halt and error. -/
theorem ctxRefines_refl (t : Term) : CtxRefines t t := by
  intro C _ _
  exact ObsRefines.mk (fun h => h) (fun h => h)

/-- Transitivity: implication composition on both clauses. Needs the same
    middle-term closedness side condition as `ctxEq_trans`. -/
theorem ctxRefines_trans {t₁ t₂ t₃ : Term}
    (h_closed_mid : ∀ C, closedAt 0 (fill C t₁) = true →
                          closedAt 0 (fill C t₃) = true →
                          closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ → CtxRefines t₂ t₃ → CtxRefines t₁ t₃ := by
  intro h12 h23 C hC1 hC3
  have hC2 := h_closed_mid C hC1 hC3
  have ref12 := h12 C hC1 hC2
  have ref23 := h23 C hC2 hC3
  exact ObsRefines.mk
    (fun h_t1 => ref23.halt (ref12.halt h_t1))
    (fun h_t1 => ref23.error (ref12.error h_t1))

/-- Equivalence subsumes refinement (forward direction). -/
theorem CtxEq.toCtxRefines {t₁ t₂ : Term} (h : CtxEq t₁ t₂) :
    CtxRefines t₁ t₂ := by
  intro C hC1 hC2
  have obs := h C hC1 hC2
  exact ObsRefines.mk obs.halt.mp obs.error.mp

/-- Equivalence subsumes refinement (backward direction). -/
theorem CtxEq.toCtxRefines_symm {t₁ t₂ : Term} (h : CtxEq t₁ t₂) :
    CtxRefines t₂ t₁ := by
  intro C hC2 hC1
  have obs := h C hC1 hC2
  exact ObsRefines.mk obs.halt.mpr obs.error.mpr

/-- Antisymmetry: bidirectional refinement gives equivalence. -/
theorem ctxRefines_antisymm {t₁ t₂ : Term} :
    CtxRefines t₁ t₂ → CtxRefines t₂ t₁ → CtxEq t₁ t₂ := by
  intro h12 h21 C hC1 hC2
  have ref12 := h12 C hC1 hC2
  have ref21 := h21 C hC2 hC1
  exact ObsEq.mk
    (Iff.intro ref12.halt ref21.halt)
    (Iff.intro ref12.error ref21.error)

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
  refine ctxRefines_trans ?_ hA hB
  intro C hC1 hC2
  have d1 := (fill_closedAt_iff C (.Apply f₁ a₁) 0).mp hC1
  have d2 := (fill_closedAt_iff C (.Apply f₂ a₂) 0).mp hC2
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true] at d1 d2
  refine (fill_closedAt_iff C (.Apply f₂ a₁) 0).mpr ⟨d1.1, ?_⟩
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true]
  exact ⟨d2.2.1, d1.2.2⟩

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
      refine ctxRefines_trans ?_ hA hB
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
      refine ctxRefines_trans ?_ hA hB
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
  refine ctxRefines_trans ?_ hA hB
  intro C hC1 hC2
  have d1 := (fill_closedAt_iff C (.Case scrut₁ alts₁) 0).mp hC1
  have d2 := (fill_closedAt_iff C (.Case scrut₂ alts₂) 0).mp hC2
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true] at d1 d2
  refine (fill_closedAt_iff C (.Case scrut₂ alts₁) 0).mpr ⟨d1.1, ?_⟩
  simp only [Nat.zero_add, closedAt, Bool.and_eq_true]
  exact ⟨d2.2.1, d1.2.2⟩

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
