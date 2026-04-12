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

/--
  Two terms are contextually equivalent if, when placed in **any** syntax tree
  and evaluated in the empty machine, their unbounded termination behavior
  matches. Contexts are unrestricted — no closedness side condition — because
  the soundness bridge (`Contextual.Soundness.soundness`) handles open contexts
  directly via the semantic `term_obsEq` chain.
-/
def CtxEq (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    ObsEq (.compute [] .nil (fill C t₁))
          (.compute [] .nil (fill C t₂))

/--
  The Transitivity of Contextual Equivalence.
  `ObsEq` is a conjunction of a halt-Iff and an error-Iff, so trans chains both.
-/
theorem ctxEq_trans {t₁ t₂ t₃ : Term} :
  CtxEq t₁ t₂ → CtxEq t₂ t₃ → CtxEq t₁ t₃ := by
  intro h1 h2 C
  exact ⟨Iff.trans (h1 C).1 (h2 C).1, Iff.trans (h1 C).2 (h2 C).2⟩

/-- Reflexivity of `CtxEq`. Both halt and error Iffs are `Iff.rfl`. -/
theorem ctxEq_refl (t : Term) : CtxEq t t := fun _ => ⟨Iff.rfl, Iff.rfl⟩

/-- Symmetry of `CtxEq`. -/
theorem ctxEq_symm {t₁ t₂ : Term} (h : CtxEq t₁ t₂) : CtxEq t₂ t₁ :=
  fun C => ⟨(h C).1.symm, (h C).2.symm⟩

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
  exact ctxEq_trans hA hB

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
      exact ctxEq_trans hA hB

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
      exact ctxEq_trans hA hB

/-- General Case congruence: swap both the scrutinee and the alts pointwise. -/
theorem ctxEq_case {scrut₁ scrut₂ : Term} {alts₁ alts₂ : List Term}
    (hscrut : CtxEq scrut₁ scrut₂)
    (halts : ListRel CtxEq alts₁ alts₂) :
    CtxEq (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  have hA : CtxEq (.Case scrut₁ alts₁) (.Case scrut₂ alts₁) := ctxEq_case_scrut hscrut
  have hB : CtxEq (.Case scrut₂ alts₁) (.Case scrut₂ alts₂) := by
    have := ctxEq_case_swap_prefix (scrut := scrut₂) (pre := []) halts
    simpa using this
  exact ctxEq_trans hA hB

--------------------------------------------------------------------------------
-- 6. CONTEXTUAL REFINEMENT
--
-- One-directional sibling of `CtxEq`: `t₁ ⊑Ctx t₂` says that whenever `t₁`
-- converges in a closed context, so does `t₂`. The two relations are linked
-- by `ctxRefines_antisymm` (CtxRefines both ways ↔ CtxEq).
--------------------------------------------------------------------------------

/-- Observational refinement: `c₂` refines `c₁`'s halt AND error behavior.
    This prevents unsound transforms like `Let x = Error in 10 ⊑ 10`. -/
def ObsRefines (c₁ c₂ : State) : Prop :=
  ((∃ v₁, Reaches c₁ (.halt v₁)) → (∃ v₂, Reaches c₂ (.halt v₂))) ∧
  (Reaches c₁ .error → Reaches c₂ .error)

/-- Contextual refinement: in any context, if `t₁` converges, so does `t₂`. -/
def CtxRefines (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    ObsRefines (.compute [] .nil (fill C t₁))
               (.compute [] .nil (fill C t₂))

@[inherit_doc] scoped infix:50 " ⊑Ctx " => CtxRefines

/-- Reflexivity: refinement is the identity implication on both halt and error. -/
theorem ctxRefines_refl (t : Term) : CtxRefines t t :=
  fun _ => ⟨fun h => h, fun h => h⟩

/-- Transitivity: implication composition on both clauses. -/
theorem ctxRefines_trans {t₁ t₂ t₃ : Term} :
    CtxRefines t₁ t₂ → CtxRefines t₂ t₃ → CtxRefines t₁ t₃ := by
  intro h12 h23 C
  exact ⟨fun h_t1 => (h23 C).1 ((h12 C).1 h_t1),
         fun h_t1 => (h23 C).2 ((h12 C).2 h_t1)⟩

/-- Equivalence subsumes refinement (forward direction). -/
theorem CtxEq.toCtxRefines {t₁ t₂ : Term} (h : CtxEq t₁ t₂) :
    CtxRefines t₁ t₂ :=
  fun C => ⟨(h C).1.mp, (h C).2.mp⟩

/-- Equivalence subsumes refinement (backward direction). -/
theorem CtxEq.toCtxRefines_symm {t₁ t₂ : Term} (h : CtxEq t₁ t₂) :
    CtxRefines t₂ t₁ :=
  fun C => ⟨(h C).1.mpr, (h C).2.mpr⟩

/-- Antisymmetry: bidirectional refinement gives equivalence. -/
theorem ctxRefines_antisymm {t₁ t₂ : Term} :
    CtxRefines t₁ t₂ → CtxRefines t₂ t₁ → CtxEq t₁ t₂ := by
  intro h12 h21 C
  exact ⟨⟨(h12 C).1, (h21 C).1⟩, ⟨(h12 C).2, (h21 C).2⟩⟩

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
