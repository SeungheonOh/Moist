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
  | .Constr _ _ C _ | .Case C _ => C.binders

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

/--
  Two terms are contextually equivalent if, when placed in any **closed** syntax
  tree and evaluated in the empty machine, their unbounded termination behavior
  matches.

  We restrict to closed contexts (`C.closedAt 0`) because the soundness bridge
  goes through `openEq_contextual_closure`, which requires the context's
  non-hole siblings to be reflexively open-equivalent at the appropriate depth
  — and that comes from `openEq_refl`, which needs `closedAt`.
-/
def CtxEq (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context), C.closedAt 0 = true →
    ObsEq (.compute [] .nil (fill C t₁))
          (.compute [] .nil (fill C t₂))

/--
  The Transitivity of Contextual Equivalence.
  Because it operates purely on syntax and logical bi-implication, this is a free theorem.
-/
theorem ctxEq_trans {t₁ t₂ t₃ : Term} :
  CtxEq t₁ t₂ → CtxEq t₂ t₃ → CtxEq t₁ t₃ := by
  intro h1 h2 C hC
  exact Iff.trans (h1 C hC) (h2 C hC)

/-- Reflexivity of `CtxEq`. Both sides are syntactically equal, so `Iff.rfl`. -/
theorem ctxEq_refl (t : Term) : CtxEq t t := fun _ _ => Iff.rfl

/-- Symmetry of `CtxEq`. -/
theorem ctxEq_symm {t₁ t₂ : Term} (h : CtxEq t₁ t₂) : CtxEq t₂ t₁ :=
  fun C hC => (h C hC).symm

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

--------------------------------------------------------------------------------
-- 5. CONGRUENCE THEOREMS FOR CtxEq (port of compat_* from Equivalence)
--------------------------------------------------------------------------------

/-- Generic single-subterm congruence: if the "extension" inner context is
    closed-at-depth-`outer.binders`, then `CtxEq` is preserved when wrapping
    both sides in that inner. -/
private theorem ctxEq_extend
    {t₁ t₂ : Term} (h : CtxEq t₁ t₂)
    (inner : Context)
    (h_inner_closed : ∀ {C : Context}, C.closedAt 0 = true →
      inner.closedAt C.binders = true) :
    CtxEq (fill inner t₁) (fill inner t₂) := by
  intro C hC
  have hC' : (Context.compose C inner).closedAt 0 = true :=
    Context.compose_closedAt hC (by simpa using h_inner_closed hC)
  have h_filled := h (Context.compose C inner) hC'
  rw [fill_compose, fill_compose] at h_filled
  exact h_filled

/-- Lambda congruence. The inner context `Lam x Hole` is always closed because
    `Hole` is trivially closed at any depth. -/
theorem ctxEq_lam {body₁ body₂ : Term} (name : Nat) (h : CtxEq body₁ body₂) :
    CtxEq (.Lam name body₁) (.Lam name body₂) := by
  have hwrap := ctxEq_extend h (.Lam name .Hole) (fun _ => by simp [Context.closedAt])
  simpa [fill] using hwrap

/-- Delay congruence. -/
theorem ctxEq_delay {body₁ body₂ : Term} (h : CtxEq body₁ body₂) :
    CtxEq (.Delay body₁) (.Delay body₂) := by
  have hwrap := ctxEq_extend h (.Delay .Hole) (fun _ => by simp [Context.closedAt])
  simpa [fill] using hwrap

/-- Force congruence. -/
theorem ctxEq_force {t₁ t₂ : Term} (h : CtxEq t₁ t₂) :
    CtxEq (.Force t₁) (.Force t₂) := by
  have hwrap := ctxEq_extend h (.Force .Hole) (fun _ => by simp [Context.closedAt])
  simpa [fill] using hwrap

-- Monotonicity of `closedAt`: a term closed at depth `d` is also closed at any
-- greater depth. Proven by mutual structural induction on terms / lists.
mutual
private theorem closedAt_mono {d d' : Nat} :
    ∀ {t : Term}, closedAt d t = true → d ≤ d' → closedAt d' t = true := by
  intro t h hle
  cases t with
  | Var n =>
    rw [closedAt.eq_1] at h ⊢
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true h) hle)
  | Lam _ body =>
    rw [closedAt.eq_2] at h ⊢
    exact closedAt_mono h (by omega)
  | Apply f x =>
    rw [closedAt.eq_3] at h ⊢
    have ⟨hf, hx⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono hf hle, closedAt_mono hx hle⟩
  | Force e =>
    rw [closedAt.eq_4] at h ⊢
    exact closedAt_mono h hle
  | Delay e =>
    rw [closedAt.eq_5] at h ⊢
    exact closedAt_mono h hle
  | Constr _ args =>
    rw [closedAt.eq_6] at h ⊢
    exact closedAtList_mono h hle
  | Case scrut alts =>
    rw [closedAt.eq_7] at h ⊢
    have ⟨hs, ha⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono hs hle, closedAtList_mono ha hle⟩
  | Constant _ => simp [closedAt]
  | Builtin _ => simp [closedAt]
  | Error => simp [closedAt]
private theorem closedAtList_mono {d d' : Nat} :
    ∀ {ts : List Term}, closedAtList d ts = true → d ≤ d' →
      closedAtList d' ts = true := by
  intro ts h hle
  cases ts with
  | nil => simp [closedAtList]
  | cons t rest =>
    rw [closedAtList.eq_2] at h ⊢
    have ⟨ht, hr⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨closedAt_mono ht hle, closedAtList_mono hr hle⟩
end

/--
  Apply congruence. The chain `Apply f₁ a₁ → Apply f₂ a₁ → Apply f₂ a₂` requires
  the intermediate sibling — `a₁` on the left swap, `f₂` on the right swap — to
  sit inside a context that is closed at depth 0. The cleanest sufficient
  condition is `closedAt 0` on those siblings (which by monotonicity holds at
  every depth).
-/
theorem ctxEq_app {f₁ f₂ a₁ a₂ : Term}
    (ha₁_closed : closedAt 0 a₁ = true)
    (hf₂_closed : closedAt 0 f₂ = true)
    (hf : CtxEq f₁ f₂) (ha : CtxEq a₁ a₂) :
    CtxEq (.Apply f₁ a₁) (.Apply f₂ a₂) := by
  -- Step A: swap f₁ → f₂ via inner = AppLeft Hole a₁
  have hA : CtxEq (.Apply f₁ a₁) (.Apply f₂ a₁) := by
    have := ctxEq_extend hf (.AppLeft .Hole a₁) (fun _ => by
      simp [Context.closedAt]; exact closedAt_mono ha₁_closed (Nat.zero_le _))
    simpa [fill] using this
  -- Step B: swap a₁ → a₂ via inner = AppRight f₂ Hole
  have hB : CtxEq (.Apply f₂ a₁) (.Apply f₂ a₂) := by
    have := ctxEq_extend ha (.AppRight f₂ .Hole) (fun _ => by
      simp [Context.closedAt]; exact closedAt_mono hf₂_closed (Nat.zero_le _))
    simpa [fill] using this
  exact ctxEq_trans hA hB

/-- Append preserves `closedAtList`. -/
private theorem closedAtList_append {d : Nat} :
    {l r : List Term} → closedAtList d l = true → closedAtList d r = true →
    closedAtList d (l ++ r) = true
  | [], _, _, hr => by simpa
  | x :: xs, r, hl, hr => by
    simp [closedAtList] at hl ⊢
    exact ⟨hl.1, closedAtList_append hl.2 hr⟩

/--
  Constr congruence (single-element swap form). Swaps one field at a known
  position; the remaining `pre`/`post` siblings must be `closedAt 0` so that the
  corresponding test context is closed.
-/
theorem ctxEq_constr_one {tag : Nat} {a b : Term} {pre post : List Term}
    (hpre : closedAtList 0 pre = true)
    (hpost : closedAtList 0 post = true)
    (hab : CtxEq a b) :
    CtxEq (.Constr tag (pre ++ a :: post)) (.Constr tag (pre ++ b :: post)) := by
  have hwrap := ctxEq_extend hab (.Constr tag pre .Hole post) (fun {C} _ => by
    simp [Context.closedAt]
    refine ⟨closedAtList_mono hpre (Nat.zero_le _), closedAtList_mono hpost (Nat.zero_le _)⟩)
  simpa [fill] using hwrap

/-- Inductive worker for the Constr congruence: walks the field lists from left
    to right, swapping one element per step. -/
private theorem ctxEq_constr_swap_prefix {tag : Nat} {fs₁ fs₂ : List Term}
    (pre : List Term) (hpre : closedAtList 0 pre = true)
    (hclo₁ : closedAtList 0 fs₁ = true)
    (hclo₂ : closedAtList 0 fs₂ = true)
    (hrel : ListRel CtxEq fs₁ fs₂) :
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
      simp [closedAtList] at hclo₁ hclo₂
      -- Step A: swap head f₁ → f₂ at slot |pre|
      have hA : CtxEq (.Constr tag (pre ++ f₁ :: fs₁)) (.Constr tag (pre ++ f₂ :: fs₁)) :=
        ctxEq_constr_one hpre hclo₁.2 hrel.1
      -- Step B: shift the prefix one to the right and recurse on the tails
      have hf₂_list : closedAtList 0 [f₂] = true := by
        simp [closedAtList]; exact hclo₂.1
      have hpre' : closedAtList 0 (pre ++ [f₂]) = true := closedAtList_append hpre hf₂_list
      have hB := ih (pre := pre ++ [f₂]) hpre' hclo₁.2 hclo₂.2 hrel.2
      have e1 : (pre ++ [f₂]) ++ fs₁ = pre ++ (f₂ :: fs₁) := by simp
      have e2 : (pre ++ [f₂]) ++ fs₂ = pre ++ (f₂ :: fs₂) := by simp
      rw [e1, e2] at hB
      exact ctxEq_trans hA hB

/-- General Constr congruence in head-tail form, mirroring `compat_constr`. -/
theorem ctxEq_constr {tag : Nat} {m₁ m₂ : Term} {ms₁ ms₂ : List Term}
    (hm₁_closed : closedAt 0 m₁ = true) (hm₂_closed : closedAt 0 m₂ = true)
    (hms₁_closed : closedAtList 0 ms₁ = true) (hms₂_closed : closedAtList 0 ms₂ = true)
    (hm : CtxEq m₁ m₂) (hms : ListRel CtxEq ms₁ ms₂) :
    CtxEq (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  have hclo₁ : closedAtList 0 (m₁ :: ms₁) = true := by
    simp [closedAtList]; exact ⟨hm₁_closed, hms₁_closed⟩
  have hclo₂ : closedAtList 0 (m₂ :: ms₂) = true := by
    simp [closedAtList]; exact ⟨hm₂_closed, hms₂_closed⟩
  have hrel : ListRel CtxEq (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have := ctxEq_constr_swap_prefix (tag := tag) [] (by simp [closedAtList])
    hclo₁ hclo₂ hrel
  simpa using this

/--
  Case congruence (scrutinee swap form), mirroring `compat_case` in
  `Equivalence.lean`. The `alts` list is identical on both sides; only the
  scrutinee is swapped via the inner context `Case Hole alts`. The `Context`
  inductive does not currently expose a `CaseAlt` constructor, so swapping an
  individual alt would require extending `Context` (and porting this through
  `binders`, `closedAt`, `compose`, and `openEq_contextual_closure`).
-/
theorem ctxEq_case {scrut₁ scrut₂ : Term} {alts : List Term}
    (halts_closed : closedAtList 0 alts = true)
    (hscrut : CtxEq scrut₁ scrut₂) :
    CtxEq (.Case scrut₁ alts) (.Case scrut₂ alts) := by
  have hwrap := ctxEq_extend hscrut (.Case .Hole alts) (fun _ => by
    simp [Context.closedAt]
    exact closedAtList_mono halts_closed (Nat.zero_le _))
  simpa [fill] using hwrap

-- ── Helper lemmas for the contextual closure ─────────────────────────────────

/-- Reflexive `ListRel` of `OpenEq` for any list of terms closed at depth `d`. -/
private theorem openEq_listRel_refl (d : Nat) :
    {ts : List Term} → closedAtList d ts = true →
    ListRel (fun t₁ t₂ => OpenEq d t₁ t₂) ts ts
  | [], _ => trivial
  | t :: rest, h => by
    simp [closedAtList] at h
    exact ⟨openEq_refl d t h.1, openEq_listRel_refl d h.2⟩

/-- Insert a "hole" position into a list surrounded by closed siblings. -/
private theorem openEq_listRel_around {d : Nat} {a b : Term} :
    {pre post : List Term} → closedAtList d pre = true → OpenEq d a b →
    closedAtList d post = true →
    ListRel (fun t₁ t₂ => OpenEq d t₁ t₂) (pre ++ a :: post) (pre ++ b :: post)
  | [], post, _, hab, hpost => ⟨hab, openEq_listRel_refl d hpost⟩
  | p :: ps, post, hpre, hab, hpost => by
    simp [closedAtList] at hpre
    refine ⟨openEq_refl d p hpre.1, ?_⟩
    exact openEq_listRel_around hpre.2 hab hpost

/-- Lifted `compat_constr` that does not require the head form `m :: ms`.
    Handles the empty-fields case via `openEq_refl`. -/
private theorem openEq_constr {d tag : Nat} :
    {fields₁ fields₂ : List Term} →
    ListRel (fun t₁ t₂ => OpenEq d t₁ t₂) fields₁ fields₂ →
    OpenEq d (.Constr tag fields₁) (.Constr tag fields₂)
  | [], [], _ => openEq_refl d (.Constr tag []) (by simp [closedAt, closedAtList])
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id
  | _ :: _, _ :: _, h => compat_constr h.1 h.2

/--
  The Fundamental Theorem of Logical Relations: OpenEq is a Congruence.

  Depth bookkeeping: a `Lam` in the context puts the hole one level deeper, so
  the depth at the hole is `d + C.binders`, where `d` is the depth at the root
  of the filled term.

  Closedness assumption: every non-hole sibling embedded in `C` must be closed
  at the depth where it sits (`C.closedAt d`). This lets each `compat_*` lemma
  produce its reflexive sibling instance via `openEq_refl`.
-/
theorem openEq_contextual_closure {t₁ t₂ : Term} (C : Context) :
    ∀ {d : Nat}, C.closedAt d = true → OpenEq (d + C.binders) t₁ t₂ →
      OpenEq d (fill C t₁) (fill C t₂) := by
  induction C with
  | Hole =>
    intro d _ h
    simpa [fill, Context.binders] using h
  | Lam x C ih =>
    intro d hC h
    have hCcl : C.closedAt (d + 1) = true := hC
    have hbody : OpenEq ((d + 1) + C.binders) t₁ t₂ := by
      have hEq : (d + 1) + C.binders = d + (.Lam x C : Context).binders := by
        show (d + 1) + C.binders = d + (C.binders + 1)
        omega
      rw [hEq]; exact h
    exact compat_lam (ih hCcl hbody)
  | AppLeft C e ih =>
    intro d hC h
    simp [Context.closedAt] at hC
    obtain ⟨hCcl, he⟩ := hC
    exact compat_app (ih hCcl h) (openEq_refl d e he)
  | AppRight e C ih =>
    intro d hC h
    simp [Context.closedAt] at hC
    obtain ⟨he, hCcl⟩ := hC
    exact compat_app (openEq_refl d e he) (ih hCcl h)
  | Delay C ih =>
    intro d hC h
    have hCcl : C.closedAt d = true := hC
    exact compat_delay (ih hCcl h)
  | Force C ih =>
    intro d hC h
    have hCcl : C.closedAt d = true := hC
    exact compat_force (ih hCcl h)
  | Constr tag lefts C rights ih =>
    intro d hC h
    simp [Context.closedAt] at hC
    obtain ⟨⟨hlefts, hCcl⟩, hrights⟩ := hC
    have hhole : OpenEq d (fill C t₁) (fill C t₂) := ih hCcl h
    apply openEq_constr (tag := tag)
    -- fill yields `lefts ++ [fill C t₁] ++ rights`; reassociate to
    -- `lefts ++ fill C t₁ :: rights` so `openEq_listRel_around` applies.
    show ListRel _ ((lefts ++ [fill C t₁]) ++ rights) ((lefts ++ [fill C t₂]) ++ rights)
    rw [List.append_assoc, List.append_assoc]
    show ListRel _ (lefts ++ fill C t₁ :: rights) (lefts ++ fill C t₂ :: rights)
    exact openEq_listRel_around hlefts hhole hrights
  | Case C alts ih =>
    intro d hC h
    simp [Context.closedAt] at hC
    obtain ⟨hCcl, halts⟩ := hC
    exact compat_case (openEq_listRel_refl d halts) (ih hCcl h)

-- ── Bridge lemmas: OpenEq 0 → ObsEq at empty env / empty stack ───────────────

/-- `EnvEqK _ 0` is vacuous: the body quantifies over `0 < n ≤ 0`, which is empty. -/
private theorem envEqK_zero {k : Nat} (ρ₁ ρ₂ : CekEnv) : EnvEqK k 0 ρ₁ ρ₂ := by
  intro n hn hn0
  exfalso; omega

/-- The empty stack is `StackRelK`-related to itself: `.ret [] v` always halts in
    one step, so `ObsEqK j (.ret [] v₁) (.ret [] v₂)` holds unconditionally. -/
private theorem stackRelK_nil {k : Nat} : StackRelK ValueEqK k [] [] := by
  intro j _ v₁ v₂ _
  refine ⟨?_, ?_⟩
  · rintro v ⟨_, _, _⟩
    exact ⟨v₂, 1, by simp [steps, step]⟩
  · rintro v ⟨_, _, _⟩
    exact ⟨v₁, 1, by simp [steps, step]⟩

/-- Depth weakening: `OpenEq 0` is the strongest (it quantifies unconditionally
    over env pairs since `EnvEqK _ 0` is vacuous), so it implies `OpenEq d` for
    any `d`. -/
private theorem openEq_weaken_zero {t₁ t₂ : Term} (h : OpenEq 0 t₁ t₂) :
    ∀ d, OpenEq d t₁ t₂ := by
  intro d k j hj ρ₁ ρ₂ _
  exact h k j hj ρ₁ ρ₂ (envEqK_zero ρ₁ ρ₂)

/--
  SOUNDNESS: If terms survive the CEK machine (OpenEq), they survive all closed
  syntax (CtxEq). Proof strategy:
    1. Weaken `OpenEq 0 t₁ t₂` to `OpenEq (0 + C.binders) t₁ t₂`.
    2. Apply `openEq_contextual_closure` to obtain `OpenEq 0 (fill C t₁) (fill C t₂)`.
    3. Instantiate at empty env (vacuous `EnvEqK`) and empty stack (`stackRelK_nil`).
    4. For each direction of `ObsEq`, choose `k = n` so the bound `n ≤ k` is `le_refl`.
-/
theorem soundness (t₁ t₂ : Term) : OpenEq 0 t₁ t₂ → CtxEq t₁ t₂ := by
  intro h_open C hC
  -- Step 1+2: lift to depth `C.binders`, then push the hole through `C`.
  have h_filled : OpenEq 0 (fill C t₁) (fill C t₂) :=
    openEq_contextual_closure C hC (openEq_weaken_zero h_open (0 + C.binders))
  -- Step 3+4: bridge `OpenEq 0` to `ObsEq` at empty env / empty stack.
  refine ⟨?_, ?_⟩
  · rintro ⟨v, n, hs⟩
    have hbeh : BehEqK ValueEqK n .nil .nil (fill C t₁) (fill C t₂) :=
      h_filled n n (Nat.le_refl _) .nil .nil (envEqK_zero .nil .nil)
    have hobs : ObsEqK n (.compute [] .nil (fill C t₁))
                          (.compute [] .nil (fill C t₂)) :=
      hbeh n (Nat.le_refl _) [] [] stackRelK_nil
    exact hobs.1 v ⟨n, Nat.le_refl _, hs⟩
  · rintro ⟨v, n, hs⟩
    have hbeh : BehEqK ValueEqK n .nil .nil (fill C t₁) (fill C t₂) :=
      h_filled n n (Nat.le_refl _) .nil .nil (envEqK_zero .nil .nil)
    have hobs : ObsEqK n (.compute [] .nil (fill C t₁))
                          (.compute [] .nil (fill C t₂)) :=
      hbeh n (Nat.le_refl _) [] [] stackRelK_nil
    exact hobs.2 v ⟨n, Nat.le_refl _, hs⟩

--------------------------------------------------------------------------------
-- 5. THE COMPLETENESS BRIDGE (Contextual → Biorthogonality)
--------------------------------------------------------------------------------

-- -- The Definability Tax: raw CEK states must be simulable by pure Plutus Core
-- -- syntax trees. We construct the reifications below; no axioms.

-- /-- Plug `inner` into the hole of `outer`. Standard context composition. -/
-- def Context.compose : Context → Context → Context
--   | .Hole, inner => inner
--   | .Lam x C, inner => .Lam x (Context.compose C inner)
--   | .AppLeft C e, inner => .AppLeft (Context.compose C inner) e
--   | .AppRight e C, inner => .AppRight e (Context.compose C inner)
--   | .Delay C, inner => .Delay (Context.compose C inner)
--   | .Force C, inner => .Force (Context.compose C inner)
--   | .Constr tag lefts C rights, inner =>
--       .Constr tag lefts (Context.compose C inner) rights
--   | .Case C alts, inner => .Case (Context.compose C inner) alts

-- /--
--   Reify a CEK environment as a closed program context.

--   `fill (env_to_context ρ) t` evaluates under the empty env the same way that
--   `compute [] ρ t` does: each value in `ρ` is read back to a term via
--   `readbackValue` and supplied through a β-redex. Recursion is structural on
--   the env; the head `v` becomes the innermost binding (`Var 1`) by composing
--   the recursive context for the tail with a fresh `(λ. _) (readback v)` wrapper
--   around the hole.

--   Although `readbackValue` is upstream-partial, this function recurses only on
--   the `CekEnv` spine — that recursion is structural, so the definition itself
--   is total.
-- -/
-- def env_to_context : CekEnv → Context
--   | .nil => .Hole
--   | .cons v rest =>
--       Context.compose (env_to_context rest)
--         (.AppLeft (.Lam 0 .Hole) (readbackValue v))

-- /-- Synthesizes a Context that mimics the continuation of a CEK stack. -/
-- axiom stack_to_context (π : Stack) : Context

-- /--
--   The Definability Lemma:
--   Plugging a term into the synthesized contexts is observationally equivalent
--   to directly evaluating it under the original CEK environment and stack.
-- -/
-- axiom definability_lemma (π : Stack) (ρ : CekEnv) (t : Term) :
--   ObsEq (.compute π ρ t)
--         (.compute [] .nil (fill (stack_to_context π) (fill (env_to_context ρ) t)))

-- /--
--   COMPLETENESS: If terms survive all syntax (CtxEq), they survive the CEK machine (OpenEq).
--   Proof strategy: Reify π and ρ into contexts, apply CtxEq, and un-reify via definability.
-- -/
-- theorem completeness (t₁ t₂ : Term) : CtxEq t₁ t₂ → OpenEq 0 t₁ t₂ := by
--   intro h_ctx
--   sorry

end Moist.VerifiedNewNew.Contextual
