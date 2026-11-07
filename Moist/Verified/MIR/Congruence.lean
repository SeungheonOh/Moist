import Moist.Verified.MIR

/-! # MIR-level congruence lemmas for `MIRCtxEq` / `MIRCtxRefines`

Each lemma has the shape `R a b → R (F a) (F b)` (or the pointwise list
version) for a MIR constructor `F`. Every proof decomposes `lowerTotalExpr`
over the MIR constructor, then invokes the corresponding UPLC-level
`ctxEq_*` / `ctxRefines_*` congruence.

Split out of `Moist.Verified.MIR` so the main module can focus on
the lifting scaffolding (`MIRRefines → MIRCtxRefines`, reflexivity,
transitivity, the `toCtxEq` / `toCtxRefines` projections, and the
`MIRCtxEq ↔ MIRCtxRefines`-bidirectional bridge). -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.Verified (closedAt)
open Moist.Verified.Contextual
  (Context fill closedAt_mono fill_closedAt_iff ObsRefines
   CtxEq CtxRefines
   ctxEq_refl ctxEq_symm ctxEq_trans ctxRefines_refl ctxRefines_trans
   ctxEq_lam ctxEq_delay ctxEq_force ctxEq_app
   ctxEq_constr_one ctxEq_constr ctxEq_case_scrut ctxEq_case_one_alt ctxEq_case
   ctxRefines_lam ctxRefines_delay ctxRefines_force ctxRefines_app
   ctxRefines_constr_one ctxRefines_constr ctxRefines_case_scrut
   ctxRefines_case_one_alt ctxRefines_case)
open Moist.Verified.Equivalence (ObsEq ListRel)

--------------------------------------------------------------------------------
-- 6c. Unary / binary congruences for `MIRCtxEq`
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 6e. Constr / Case congruences for `MIRCtxEq`
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 7b. Unary / binary congruences for `MIRCtxRefines`
--------------------------------------------------------------------------------

/-- Force congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_force {t₁ t₂ : Expr} (h : MIRCtxRefines t₁ t₂) :
    MIRCtxRefines (.Force t₁) (.Force t₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_force, lowerTotalExpr_force]
    simp only [Option.isSome_map]
    exact h.toImp env
  · rw [lowerTotalExpr_force, lowerTotalExpr_force]
    cases hlow₁ : lowerTotalExpr env t₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr env t₂ with
      | none => simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxRefines_force (h.toCtxRefines hlow₁ hlow₂)

/-- Delay congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_delay {t₁ t₂ : Expr} (h : MIRCtxRefines t₁ t₂) :
    MIRCtxRefines (.Delay t₁) (.Delay t₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_delay, lowerTotalExpr_delay]
    simp only [Option.isSome_map]
    exact h.toImp env
  · rw [lowerTotalExpr_delay, lowerTotalExpr_delay]
    cases hlow₁ : lowerTotalExpr env t₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr env t₂ with
      | none => simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxRefines_delay (h.toCtxRefines hlow₁ hlow₂)

/-- Lambda congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_lam {x : VarId} {body₁ body₂ : Expr} (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Lam x body₁) (.Lam x body₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
    simp only [Option.isSome_map]
    exact h.toImp (x :: env)
  · rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
    cases hlow₁ : lowerTotalExpr (x :: env) body₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr (x :: env) body₂ with
      | none => simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxRefines_lam 0 (h.toCtxRefines hlow₁ hlow₂)

/-- Application congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_app {f₁ f₂ a₁ a₂ : Expr}
    (hf : MIRCtxRefines f₁ f₂) (ha : MIRCtxRefines a₁ a₂) :
    MIRCtxRefines (.App f₁ a₁) (.App f₂ a₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hlow_f₁ : lowerTotalExpr env f₁ with
    | none => simp
    | some t_f₁ =>
      have hsome_f₂ : (lowerTotalExpr env f₂).isSome :=
        hf.toImp env (by rw [hlow_f₁]; rfl)
      cases hlow_f₂ : lowerTotalExpr env f₂ with
      | none => rw [hlow_f₂] at hsome_f₂; exact absurd hsome_f₂ (by simp)
      | some t_f₂ =>
        cases hlow_a₁ : lowerTotalExpr env a₁ with
        | none => simp
        | some t_a₁ =>
          have hsome_a₂ : (lowerTotalExpr env a₂).isSome :=
            ha.toImp env (by rw [hlow_a₁]; rfl)
          cases hlow_a₂ : lowerTotalExpr env a₂ with
          | none => rw [hlow_a₂] at hsome_a₂; exact absurd hsome_a₂ (by simp)
          | some t_a₂ => simp
  · rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hlow_f₁ : lowerTotalExpr env f₁ with
    | none => simp
    | some tf₁ =>
      cases hlow_f₂ : lowerTotalExpr env f₂ with
      | none => simp
      | some tf₂ =>
        cases hlow_a₁ : lowerTotalExpr env a₁ with
        | none => simp
        | some ta₁ =>
          cases hlow_a₂ : lowerTotalExpr env a₂ with
          | none => simp
          | some ta₂ =>
            show CtxRefines (.Apply tf₁ ta₁) (.Apply tf₂ ta₂)
            exact ctxRefines_app (hf.toCtxRefines hlow_f₁ hlow_f₂)
                                 (ha.toCtxRefines hlow_a₁ hlow_a₂)

--------------------------------------------------------------------------------
-- 7d. Constr / Case congruences for `MIRCtxRefines`
--------------------------------------------------------------------------------

/-- Constr congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_constr {tag : Nat} {m₁ m₂ : Expr} {ms₁ ms₂ : List Expr}
    (hm : MIRCtxRefines m₁ m₂) (hms : ListRel MIRCtxRefines ms₁ ms₂) :
    MIRCtxRefines (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  intro env
  have hrel : ListRel MIRCtxRefines (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have hlist_imp := listRel_mirCtxRefines_isSome_imp hrel env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    simp only [Option.isSome_map]
    exact hlist_imp
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    cases hlow₁ : lowerTotalExprList env (m₁ :: ms₁) with
    | none => simp
    | some ts₁ =>
      cases hlow₂ : lowerTotalExprList env (m₂ :: ms₂) with
      | none => simp
      | some ts₂ =>
        show CtxRefines (.Constr tag ts₁) (.Constr tag ts₂)
        rw [lowerTotalExprList_cons] at hlow₁ hlow₂
        cases ht_m₁ : lowerTotalExpr env m₁ with
        | none => rw [ht_m₁] at hlow₁; simp at hlow₁
        | some t_m₁ =>
          cases ht_ms₁ : lowerTotalExprList env ms₁ with
          | none => rw [ht_m₁, ht_ms₁] at hlow₁; simp at hlow₁
          | some t_ms₁ =>
            cases ht_m₂ : lowerTotalExpr env m₂ with
            | none => rw [ht_m₂] at hlow₂; simp at hlow₂
            | some t_m₂ =>
              cases ht_ms₂ : lowerTotalExprList env ms₂ with
              | none => rw [ht_m₂, ht_ms₂] at hlow₂; simp at hlow₂
              | some t_ms₂ =>
                rw [ht_m₁, ht_ms₁] at hlow₁
                rw [ht_m₂, ht_ms₂] at hlow₂
                cases hlow₁; cases hlow₂
                exact ctxRefines_constr (hm.toCtxRefines ht_m₁ ht_m₂)
                  (listRel_mirCtxRefines_toListCtxRefines hms ht_ms₁ ht_ms₂)

/-- General Case congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_case {scrut₁ scrut₂ : Expr} {alts₁ alts₂ : List Expr}
    (hscrut : MIRCtxRefines scrut₁ scrut₂)
    (halts : ListRel MIRCtxRefines alts₁ alts₂) :
    MIRCtxRefines (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    have h_scrut_imp := hscrut.toImp env
    have h_alts_imp := listRel_mirCtxRefines_isSome_imp halts env
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some _ =>
      have : (lowerTotalExpr env scrut₂).isSome := h_scrut_imp (by rw [h_s₁]; rfl)
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => rw [h_s₂] at this; exact absurd this (by simp)
      | some _ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some _ =>
          have : (lowerTotalExprList env alts₂).isSome := h_alts_imp (by rw [h_a₁]; rfl)
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => rw [h_a₂] at this; exact absurd this (by simp)
          | some _ => simp
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some ts₁ =>
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => simp
      | some ts₂ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some t_a₁ =>
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => simp
          | some t_a₂ =>
            show CtxRefines (.Case ts₁ t_a₁) (.Case ts₂ t_a₂)
            have hlist_ctx : ListRel CtxRefines t_a₁ t_a₂ :=
              listRel_mirCtxRefines_toListCtxRefines halts h_a₁ h_a₂
            exact ctxRefines_case (hscrut.toCtxRefines h_s₁ h_s₂) hlist_ctx

/-! ### 7d. Fix-Lam congruence for `MIRCtxRefines`

The Fix-Lam case leverages the canonical form lemma
`lowerTotalExpr_fix_lam_with_fresh` to factor both sides through a common
fresh `s` variable, then applies UPLC-level congruences to lift through
the Z-combinator wrapper.
-/

/-- Fix-Lam congruence for `MIRCtxRefines`. The Z combinator expansion
    produces a fixed UPLC wrapper around the inner body lowering; the
    congruence follows by picking a common fresh variable and applying
    Apply/Lam congruences through the wrapper. -/
theorem mirCtxRefines_fix_lam {f x : VarId} {body₁ body₂ : Expr}
    (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Fix f (.Lam x body₁)) (.Fix f (.Lam x body₂)) := by
  intro env
  -- Canonical fresh `s` variable that avoids both expanded bodies
  let body₁' := Moist.MIR.expandFix body₁
  let body₂' := Moist.MIR.expandFix body₂
  let s_common : VarId :=
    ⟨max (Moist.MIR.maxUidExpr body₁') (Moist.MIR.maxUidExpr body₂') + 1, .gen, "s"⟩
  have hs₁ : (Moist.MIR.freeVars body₁').contains s_common = false :=
    Moist.MIR.maxUidExpr_fresh body₁' s_common (by simp [s_common]; omega)
  have hs₂ : (Moist.MIR.freeVars body₂').contains s_common = false :=
    Moist.MIR.maxUidExpr_fresh body₂' s_common (by simp [s_common]; omega)
  -- Both sides reduce to a map over `lowerTotal (x :: f :: s_common :: env) body_i'`
  have hlhs : lowerTotalExpr env (.Fix f (.Lam x body₁)) =
      (Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₁').map
        Moist.MIR.fixLamWrapUplc :=
    Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x body₁ s_common hs₁
  have hrhs : lowerTotalExpr env (.Fix f (.Lam x body₂)) =
      (Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₂').map
        Moist.MIR.fixLamWrapUplc :=
    Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x body₂ s_common hs₂
  -- Apply IH at the common env
  have ih := h (x :: f :: s_common :: env)
  refine ⟨?_, ?_⟩
  · -- isSome part (implication)
    rw [hlhs, hrhs]
    simp only [Option.isSome_map]
    exact ih.1
  · -- CtxRefines part
    rw [hlhs, hrhs]
    cases hb₁ : Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₁' with
    | none => simp
    | some t₁ =>
      cases hb₂ : Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₂' with
      | none => simp
      | some t₂ =>
        simp only [Option.map_some]
        have hlow₁ : lowerTotalExpr (x :: f :: s_common :: env) body₁ = some t₁ := hb₁
        have hlow₂ : lowerTotalExpr (x :: f :: s_common :: env) body₂ = some t₂ := hb₂
        have hctx : CtxRefines t₁ t₂ := h.toCtxRefines hlow₁ hlow₂
        show CtxRefines (Moist.MIR.fixLamWrapUplc t₁) (Moist.MIR.fixLamWrapUplc t₂)
        unfold Moist.MIR.fixLamWrapUplc
        have h_inner : CtxRefines
            (Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₁))
            (Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₂)) :=
          ctxRefines_lam 0 (ctxRefines_lam 0 hctx)
        have h_fixed_refl : CtxRefines
            (Moist.Plutus.Term.Term.Lam 0
              (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                (Moist.Plutus.Term.Term.Var 1)))
            (Moist.Plutus.Term.Term.Lam 0
              (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                (Moist.Plutus.Term.Term.Var 1))) :=
          ctxRefines_refl _
        have h_app_inner : CtxRefines
            ((Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₁)).Apply
              (Moist.Plutus.Term.Term.Lam 0
                (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                  (Moist.Plutus.Term.Term.Var 1))))
            ((Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₂)).Apply
              (Moist.Plutus.Term.Term.Lam 0
                (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                  (Moist.Plutus.Term.Term.Var 1)))) :=
          ctxRefines_app h_inner h_fixed_refl
        have h_lam_outer := ctxRefines_lam 0 h_app_inner
        have h_z_refl : CtxRefines
            (Moist.Plutus.Term.Term.Lam 0
              ((Moist.Plutus.Term.Term.Var 1).Apply (Moist.Plutus.Term.Term.Var 1)))
            (Moist.Plutus.Term.Term.Lam 0
              ((Moist.Plutus.Term.Term.Var 1).Apply (Moist.Plutus.Term.Term.Var 1))) :=
          ctxRefines_refl _
        exact ctxRefines_app h_z_refl h_lam_outer

/-! ## Let congruences -/

section LetCongruence

open Moist.MIR (lowerTotal lowerTotalLet)

--------------------------------------------------------------------------------
-- Let congruences: `lowerTotalExpr` decomposition on `.Let`
--------------------------------------------------------------------------------

/-- Unconditional decomposition: `lowerTotalExpr env (.Let binds body)` equals
    `lowerTotalLet env (expandFixBinds binds) (expandFix body)`. Holds for any
    binds/body, including those containing Fix nodes. The expansion happens
    inside `expandFix` on the Let constructor. -/
theorem lowerTotalExpr_let (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let binds body) =
      lowerTotalLet env (Moist.MIR.expandFixBinds binds) (Moist.MIR.expandFix body) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

--------------------------------------------------------------------------------
-- 3. Helpers for `lowerTotalLet` body swap
--
-- Given `MIRCtxRefines body₁ body₂`, swap the body inside any `.Let binds body_i`.
-- Proved via structural induction on `binds`, with `ctxRefines_app` /
-- `ctxRefines_lam` wrapping at each level. All helpers go through `expandFix`
-- internally so no fix-free precondition is needed.
--------------------------------------------------------------------------------

/-- Compile-preservation direction for body swap inside `lowerTotalLet`. The
    body is `expandFix`-ed internally so we can use `MIRCtxRefines body₁ body₂`
    directly. -/
private theorem lowerTotalLet_some_body_swap :
    ∀ (binds : List (VarId × Expr × Bool)) (env : List VarId)
      (body₁ body₂ : Expr),
      MIRCtxRefines body₁ body₂ →
      (lowerTotalLet env binds (Moist.MIR.expandFix body₁)).isSome →
      (lowerTotalLet env binds (Moist.MIR.expandFix body₂)).isSome
  | [], env, body₁, body₂, h, hsome => by
    -- lowerTotalLet env [] (expandFix body) = lowerTotal env (expandFix body)
    -- = lowerTotalExpr env body, by definition.
    simp only [lowerTotalLet] at hsome ⊢
    exact h.toImp env hsome
  | (x, rhs, er) :: rest, env, body₁, body₂, h, hsome => by
    simp only [lowerTotalLet, Option.bind_eq_bind] at hsome ⊢
    cases hrhs : lowerTotal env rhs with
    | none => rw [hrhs] at hsome; simp at hsome
    | some r =>
      rw [hrhs] at hsome
      simp only [Option.bind_some] at hsome
      cases hinner₁ :
          lowerTotalLet (x :: env) rest (Moist.MIR.expandFix body₁) with
      | none => rw [hinner₁] at hsome; simp at hsome
      | some inner₁ =>
        have hinner_some :
            (lowerTotalLet (x :: env) rest (Moist.MIR.expandFix body₁)).isSome := by
          rw [hinner₁]; rfl
        have hinner₂_some :=
          lowerTotalLet_some_body_swap rest (x :: env) body₁ body₂ h hinner_some
        cases hinner₂ :
            lowerTotalLet (x :: env) rest (Moist.MIR.expandFix body₂) with
        | none => rw [hinner₂] at hinner₂_some; exact absurd hinner₂_some (by simp)
        | some inner₂ => simp

/-- CtxRefines-preservation direction for body swap inside `lowerTotalLet`. -/
private theorem lowerTotalLet_ctxRefines_body_swap :
    ∀ (binds : List (VarId × Expr × Bool)) (env : List VarId)
      (body₁ body₂ : Expr),
      MIRCtxRefines body₁ body₂ →
      ∀ t₁ t₂,
        lowerTotalLet env binds (Moist.MIR.expandFix body₁) = some t₁ →
        lowerTotalLet env binds (Moist.MIR.expandFix body₂) = some t₂ →
        CtxRefines t₁ t₂
  | [], env, body₁, body₂, h, t₁, t₂, hlow₁, hlow₂ => by
    simp only [lowerTotalLet] at hlow₁ hlow₂
    -- hlow₁ : lowerTotal env (expandFix body₁) = some t₁
    -- = lowerTotalExpr env body₁ = some t₁ (definitionally)
    have ⟨_, hobs⟩ := h env
    show CtxRefines t₁ t₂
    have h₁ : lowerTotalExpr env body₁ = some t₁ := hlow₁
    have h₂ : lowerTotalExpr env body₂ = some t₂ := hlow₂
    rw [h₁, h₂] at hobs
    exact hobs
  | (x, rhs, er) :: rest, env, body₁, body₂, h, t₁, t₂, hlow₁, hlow₂ => by
    simp only [lowerTotalLet, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow₁ hlow₂
    obtain ⟨r₁, hr₁, inner₁, hinner₁, heq₁⟩ := hlow₁
    obtain ⟨r₂, hr₂, inner₂, hinner₂, heq₂⟩ := hlow₂
    have hreq : r₁ = r₂ := by rw [hr₁] at hr₂; injection hr₂
    subst hreq
    injection heq₁ with heq₁
    injection heq₂ with heq₂
    subst heq₁; subst heq₂
    have ih_inner :=
      lowerTotalLet_ctxRefines_body_swap rest (x :: env) body₁ body₂ h
        inner₁ inner₂ hinner₁ hinner₂
    exact ctxRefines_app (ctxRefines_lam 0 ih_inner) (ctxRefines_refl _)

/-- MIR-level body swap congruence for `.Let`. The lowering goes through
    `expandFix` internally. -/
theorem mirCtxRefines_let_body
    {binds : List (VarId × Expr × Bool)} {body₁ body₂ : Expr}
    (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Let binds body₁) (.Let binds body₂) := by
  intro env
  rw [lowerTotalExpr_let env binds body₁,
      lowerTotalExpr_let env binds body₂]
  refine ⟨?_, ?_⟩
  · exact lowerTotalLet_some_body_swap
      (Moist.MIR.expandFixBinds binds) env body₁ body₂ h
  · cases h₁ :
        lowerTotalLet env (Moist.MIR.expandFixBinds binds) (Moist.MIR.expandFix body₁) with
    | none => trivial
    | some t₁ =>
      cases h₂ :
          lowerTotalLet env (Moist.MIR.expandFixBinds binds) (Moist.MIR.expandFix body₂) with
      | none => trivial
      | some t₂ =>
        exact lowerTotalLet_ctxRefines_body_swap
          (Moist.MIR.expandFixBinds binds) env body₁ body₂ h t₁ t₂ h₁ h₂

--------------------------------------------------------------------------------
-- 4. MIR-level head-rhs congruence for `.Let`
--------------------------------------------------------------------------------

/-- MIR-level head-rhs swap congruence for `.Let`. The lowering goes through
    `expandFix` internally. -/
theorem mirCtxRefines_let_rhs_head
    {x : VarId} {rhs₁ rhs₂ : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : MIRCtxRefines rhs₁ rhs₂) :
    MIRCtxRefines (.Let ((x, rhs₁, er) :: rest) body)
                  (.Let ((x, rhs₂, er) :: rest) body) := by
  intro env
  rw [lowerTotalExpr_let env _ body,
      lowerTotalExpr_let env _ body]
  simp only [Moist.MIR.expandFixBinds, lowerTotalLet, Option.bind_eq_bind]
  refine ⟨?_, ?_⟩
  · intro hsome
    cases hrhs₁_low : lowerTotal env (Moist.MIR.expandFix rhs₁) with
    | none => rw [hrhs₁_low] at hsome; simp at hsome
    | some r₁ =>
      rw [hrhs₁_low] at hsome
      simp only [Option.bind_some] at hsome
      have hrhs₁_exp : (lowerTotalExpr env rhs₁).isSome := by
        show (lowerTotal env (Moist.MIR.expandFix rhs₁)).isSome
        rw [hrhs₁_low]; rfl
      have hrhs₂_exp : (lowerTotalExpr env rhs₂).isSome := h.toImp env hrhs₁_exp
      cases hrhs₂_low : lowerTotal env (Moist.MIR.expandFix rhs₂) with
      | none =>
        exfalso
        have heq : lowerTotal env (Moist.MIR.expandFix rhs₂) = lowerTotalExpr env rhs₂ := rfl
        rw [hrhs₂_low] at heq
        rw [← heq] at hrhs₂_exp
        exact absurd hrhs₂_exp (by simp)
      | some r₂ =>
        simp only [Option.bind_some]
        cases hinner :
            lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
        | none => rw [hinner] at hsome; simp at hsome
        | some inner => simp
  · cases hrhs₁_low : lowerTotal env (Moist.MIR.expandFix rhs₁) with
    | none => simp
    | some r₁ =>
      simp only [Option.bind_some]
      cases hrhs₂_low : lowerTotal env (Moist.MIR.expandFix rhs₂) with
      | none => simp
      | some r₂ =>
        simp only [Option.bind_some]
        cases hinner :
            lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
        | none => simp
        | some inner =>
          simp only [Option.bind_some]
          have hr_ref : CtxRefines r₁ r₂ := by
            have ⟨_, hobs⟩ := h env
            have h₁ : lowerTotalExpr env rhs₁ = some r₁ := hrhs₁_low
            have h₂ : lowerTotalExpr env rhs₂ = some r₂ := hrhs₂_low
            rw [h₁, h₂] at hobs
            exact hobs
          exact ctxRefines_app (ctxRefines_refl _) hr_ref

--------------------------------------------------------------------------------
-- 5. Empty let collapse
--------------------------------------------------------------------------------

/-- `lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body` definitionally
    via `lowerTotalExpr → lowerTotal ∘ expandFix → lowerTotal on .Let → lowerTotalLet`
    → nil case → `lowerTotal env (expandFix body)` = `lowerTotalExpr env body`. -/
theorem lowerTotalExpr_let_nil_eq (env : List VarId) (body : Expr) :
    lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
    Moist.MIR.lowerTotalLet]

/-- An empty `.Let [] body` is `MIRCtxRefines`-equivalent to `body`. -/
theorem mirCtxRefines_let_nil {body : Expr} :
    MIRCtxRefines (.Let [] body) body :=
  mirCtxRefines_of_lowerEq (lowerTotalExpr_let_nil_eq · body)

--------------------------------------------------------------------------------
-- Binds-list congruence for .Let
--
-- Given per-rhs `MIRCtxRefines` pairings between `binds₁` and `binds₂`
-- (matching names and `er` flags), swap the binds in a `.Let`. Proved by
-- induction on `binds₁`, using `mirCtxRefines_let_rhs_head` at each step to
-- swap the head rhs, then a body swap via `mirCtxRefines_let_body` applied
-- with a recursive inner-Let swap.
--------------------------------------------------------------------------------

/-- Per-binding rhs swap congruence for `.Let`. Pass-through proof using the
    head-rhs and body helpers. -/
theorem mirCtxRefines_let_binds_congr :
    ∀ (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr),
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                            MIRCtxRefines b₁.2.1 b₂.2.1) binds₁ binds₂ →
      MIRCtxRefines (.Let binds₁ body) (.Let binds₂ body)
  | [], [], _, _ => mirCtxRefines_refl _
  | [], _ :: _, _, hrel => absurd hrel id
  | _ :: _, [], _, hrel => absurd hrel id
  | (v₁, rhs₁, er₁) :: rest₁, (v₂, rhs₂, er₂) :: rest₂, body, hrel => by
    obtain ⟨⟨hname, her, hrhs_ref⟩, hrel_rest⟩ := hrel
    subst hname; subst her
    -- Step 1: swap head rhs from rhs₁ to rhs₂.
    have h_step1 : MIRCtxRefines (.Let ((v₁, rhs₁, er₁) :: rest₁) body)
                                  (.Let ((v₁, rhs₂, er₁) :: rest₁) body) :=
      mirCtxRefines_let_rhs_head hrhs_ref
    -- Step 2: swap body via inner Let-body swap.
    have hrest_ref : MIRCtxRefines (.Let rest₁ body) (.Let rest₂ body) :=
      mirCtxRefines_let_binds_congr rest₁ rest₂ body hrel_rest
    have h_single_swap :
        MIRCtxRefines (.Let [(v₁, rhs₂, er₁)] (.Let rest₁ body))
                      (.Let [(v₁, rhs₂, er₁)] (.Let rest₂ body)) :=
      mirCtxRefines_let_body hrest_ref
    -- Identical lowerings between the two forms.
    have hlow_eq : ∀ (rest_x : List (VarId × Expr × Bool)) env,
        lowerTotalExpr env (.Let ((v₁, rhs₂, er₁) :: rest_x) body) =
        lowerTotalExpr env (.Let [(v₁, rhs₂, er₁)] (.Let rest_x body)) := by
      intro rest_x env
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
        Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
    have hunroll := mirCtxRefines_of_lowerEq (hlow_eq rest₁)
    have hreroll := mirCtxRefines_of_lowerEq (fun env => (hlow_eq rest₂ env).symm)
    exact mirCtxRefines_trans h_step1
      (mirCtxRefines_trans hunroll
        (mirCtxRefines_trans h_single_swap hreroll))
termination_by binds₁ _ _ _ => List.length binds₁

end LetCongruence

end Moist.Verified.MIR
