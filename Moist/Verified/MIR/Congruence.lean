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

end Moist.Verified.MIR
