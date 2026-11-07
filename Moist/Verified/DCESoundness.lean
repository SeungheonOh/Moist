import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.DeadLet
import Moist.MIR.Optimize.DCE

/-! # Soundness of MIR Dead Code Elimination

Proves `MIRCtxRefines t (dce t).1` for every MIR expression `t`: the
optimized program refines the original one (halt-preserving,
error-preserving) under any closing context at every env.

## Proof structure

Structural induction on `t`. For leaf and structural-recursion cases we
compose the IH through the corresponding `mirCtxRefines_*` congruence.
The `.Fix` case dispatches on the body shape: `Fix (Lam x inner)` uses
`mirCtxRefines_fix_lam`; other Fix shapes are vacuous because the
expression can't be lowered (lowerTotalExpr returns `none`). The `.Let`
case uses:

  1. Recursively simplified every RHS and the body via per-rhs and body
     congruences.
  2. Removed dead pure bindings via `dead_let_mirRefines` + the
     `mirRefines_to_mirCtxRefines` bridge with a closedness-preservation
     witness derived from `closedAt_renameTerm_shiftRename_inv`.
  3. Collapsed an empty-binding `Let` into its body.
-/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId dce dceList dceBinds filterBindings
   isPure isPureBinds freeVars
   lowerTotalExpr lowerTotal lowerTotalLet
   lowerTotal_prepend_unused)
open Moist.Verified (closedAt)
open Moist.Verified.Contextual
  (Context fill ObsRefines CtxRefines
   closedAt_mono
   ctxRefines_refl ctxRefines_trans
   ctxRefines_lam ctxRefines_app
   fill_closedAt_iff)
open Moist.Verified.Equivalence (ListRel)

--------------------------------------------------------------------------------
-- 6. Dead let bridge: MIRCtxRefines for unused-pure let
--
-- Uses `dead_let_mirRefines` (which gives `MIRRefines`) + the
-- `mirRefines_to_mirCtxRefines` bridge. The required closedness preservation
-- uses `closedAt_shiftRename_unshift` to strip the extra
-- `Apply (Lam 0 body_shifted) rhs` wrapper.
--------------------------------------------------------------------------------

/-- The `er` flag in a let binding doesn't affect the lowering, so any
    let with arbitrary `er` is `MIRCtxRefines`-equivalent to the same let
    with `er := false`. -/
private theorem mirCtxRefines_let_er_normalize
    (x : VarId) (e body : Expr) (er : Bool) :
    MIRCtxRefines (.Let [(x, e, er)] body) (.Let [(x, e, false)] body) := by
  intro env
  -- Both sides have the same lowerTotalExpr because `expandFixBinds` and
  -- `lowerTotalLet` discard the `er` flag.
  have heq : lowerTotalExpr env (.Let [(x, e, er)] body) =
             lowerTotalExpr env (.Let [(x, e, false)] body) := by
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  rw [heq]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let [(x, e, false)] body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-- Dead-let elimination at `MIRCtxRefines` level. Uses
    `dead_let_mirRefines` + closedness preservation through the expanded
    body. -/
theorem dead_let_mirCtxRefines {x : VarId} {e body : Expr}
    (hunused : (freeVars body).contains x = false)
    (hsafe : Moist.MIR.isPure e = true) :
    MIRCtxRefines (.Let [(x, e, false)] body) body := by
  refine mirRefines_to_mirCtxRefines
    (Moist.Verified.DeadLet.dead_let_mirRefines hunused hsafe) ?_
  intro env k t₁ t₂ hlow₁ hlow₂ hclosed
  -- Unfold lowerTotalExpr on both sides through expandFix
  have hlet_eq : lowerTotalExpr env (.Let [(x, e, false)] body) =
      Moist.MIR.lowerTotal env
        (.Let [(x, Moist.MIR.expandFix e, false)] (Moist.MIR.expandFix body)) := by
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds]
  have hbody_eq : lowerTotalExpr env body = Moist.MIR.lowerTotal env (Moist.MIR.expandFix body) := by
    simp only [lowerTotalExpr]
  rw [hlet_eq] at hlow₁
  rw [hbody_eq] at hlow₂
  -- Unfold lowerTotalLet
  simp only [Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hlow₁
  obtain ⟨e_t, he_t, rest_t, hrest_t, heq⟩ := hlow₁
  injection heq with heq
  subst heq
  -- t₁ = .Apply (.Lam 0 rest_t) e_t
  have hunused' : (Moist.MIR.freeVars (Moist.MIR.expandFix body)).contains x = false :=
    Moist.MIR.expandFix_freeVars_not_contains body x hunused
  have hshift := lowerTotal_prepend_unused env x _ hunused' t₂ hlow₂
  rw [hrest_t] at hshift
  injection hshift with hshift
  subst hshift
  simp only [closedAt, Bool.and_eq_true] at hclosed
  exact Moist.Verified.closedAt_renameTerm_shiftRename_inv t₂ k 1 (by omega) (by omega) hclosed.1

--------------------------------------------------------------------------------
-- 8. filterBindings walk: simulates filterBindings via dead_let_mirCtxRefines
--------------------------------------------------------------------------------

/-- The filterBindings walk: right-recursively drops dead bindings from a
    `.Let`, proving that the result refines the original. -/
private theorem filterBindings_mirCtxRefines :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      MIRCtxRefines (.Let binds body)
        (match Moist.MIR.filterBindings binds body with
         | [] => body
         | s :: rest => .Let (s :: rest) body)
  | [], body => by
    simp only [Moist.MIR.filterBindings]
    exact mirCtxRefines_let_nil
  | (v, rhs, er) :: rest, body => by
    -- Recurse on rest
    have ih := filterBindings_mirCtxRefines rest body
    -- Step 1: unroll head: .Let ((v, rhs, er) :: rest) body ≈ .Let [(v, rhs, er)] (.Let rest body)
    have hunroll :
        MIRCtxRefines (.Let ((v, rhs, er) :: rest) body)
                      (.Let [(v, rhs, er)] (.Let rest body)) := by
      intro env
      have hlow_eq :
          lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
          lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) := by
        simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
          Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
      rw [hlow_eq]
      refine ⟨id, ?_⟩
      cases h : lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) with
      | none => trivial
      | some t => exact ctxRefines_refl t
    -- Step 2: swap inner body via IH; two sub-cases on filterBindings result
    cases hrest_filt_eq : Moist.MIR.filterBindings rest body with
    | nil =>
      have ih' : MIRCtxRefines (.Let rest body) body := by
        rw [hrest_filt_eq] at ih; exact ih
      have h_inner_swap :
          MIRCtxRefines (.Let [(v, rhs, er)] (.Let rest body))
                        (.Let [(v, rhs, er)] body) :=
        mirCtxRefines_let_body ih'
      simp only [Moist.MIR.filterBindings, hrest_filt_eq]
      cases hfree : (freeVars (Expr.Let [] body)).contains v with
      | true =>
        simp only [Bool.true_or, ↓reduceIte]
        exact mirCtxRefines_trans hunroll h_inner_swap
      | false =>
        cases hpure_check : isPure rhs with
        | true =>
          simp only [Bool.false_or, Bool.not_true]
          have hcond_v : (freeVars body).contains v = false := by
            have hh : (freeVars (Expr.Let [] body)).contains v = false := hfree
            show (freeVars body).contains v = false
            simp only [freeVars, Moist.MIR.freeVarsLet] at hh
            exact hh
          have h_er_norm :
              MIRCtxRefines (.Let [(v, rhs, er)] body) (.Let [(v, rhs, false)] body) :=
            mirCtxRefines_let_er_normalize v rhs body er
          have h_dead :
              MIRCtxRefines (.Let [(v, rhs, false)] body) body :=
            dead_let_mirCtxRefines hcond_v hpure_check
          exact mirCtxRefines_trans hunroll
            (mirCtxRefines_trans h_inner_swap
              (mirCtxRefines_trans h_er_norm h_dead))
        | false =>
          simp only [Bool.false_or, Bool.not_false, ↓reduceIte]
          exact mirCtxRefines_trans hunroll h_inner_swap
    | cons s' rest' =>
      have ih' : MIRCtxRefines (.Let rest body) (.Let (s' :: rest') body) := by
        rw [hrest_filt_eq] at ih; exact ih
      have h_inner_swap :
          MIRCtxRefines (.Let [(v, rhs, er)] (.Let rest body))
                        (.Let [(v, rhs, er)] (.Let (s' :: rest') body)) :=
        mirCtxRefines_let_body ih'
      have hreroll :
          MIRCtxRefines (.Let [(v, rhs, er)] (.Let (s' :: rest') body))
                        (.Let ((v, rhs, er) :: s' :: rest') body) := by
        intro env
        have hlow_eq :
            lowerTotalExpr env (.Let [(v, rhs, er)] (.Let (s' :: rest') body)) =
            lowerTotalExpr env (.Let ((v, rhs, er) :: s' :: rest') body) := by
          simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
            Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
        rw [hlow_eq]
        refine ⟨id, ?_⟩
        cases h : lowerTotalExpr env (.Let ((v, rhs, er) :: s' :: rest') body) with
        | none => trivial
        | some t => exact ctxRefines_refl t
      simp only [Moist.MIR.filterBindings, hrest_filt_eq]
      cases hfree : (freeVars (Expr.Let (s' :: rest') body)).contains v with
      | true =>
        simp only [Bool.true_or, ↓reduceIte]
        exact mirCtxRefines_trans hunroll
          (mirCtxRefines_trans h_inner_swap hreroll)
      | false =>
        cases hpure_check : isPure rhs with
        | true =>
          simp only [Bool.false_or, Bool.not_true]
          have h_er_norm :
              MIRCtxRefines (.Let [(v, rhs, er)] (.Let (s' :: rest') body))
                            (.Let [(v, rhs, false)] (.Let (s' :: rest') body)) :=
            mirCtxRefines_let_er_normalize v rhs (.Let (s' :: rest') body) er
          have h_dead :
              MIRCtxRefines (.Let [(v, rhs, false)] (.Let (s' :: rest') body))
                            (.Let (s' :: rest') body) :=
            dead_let_mirCtxRefines hfree hpure_check
          exact mirCtxRefines_trans hunroll
            (mirCtxRefines_trans h_inner_swap
              (mirCtxRefines_trans h_er_norm h_dead))
        | false =>
          simp only [Bool.false_or, Bool.not_false, ↓reduceIte]
          exact mirCtxRefines_trans hunroll
            (mirCtxRefines_trans h_inner_swap hreroll)
termination_by binds _ => List.length binds

--------------------------------------------------------------------------------
-- 11. Main theorem: dce soundness
--------------------------------------------------------------------------------

mutual

/-- `dce` is sound: it preserves `MIRCtxRefines`. No `fixCount` precondition;
    the Fix-Lam case is handled by `mirCtxRefines_fix_lam`, other Fix cases
    are vacuous (lowering fails). -/
theorem dce_refines : ∀ (t : Expr), MIRCtxRefines t (dce t).1
  | .Var _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Lit _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Builtin _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Error => by simp only [dce]; exact mirCtxRefines_refl _
  | .Lam x body => by
    simp only [dce]
    exact mirCtxRefines_lam (dce_refines body)
  | .Force inner => by
    simp only [dce]
    exact mirCtxRefines_force (dce_refines inner)
  | .Delay inner => by
    simp only [dce]
    exact mirCtxRefines_delay (dce_refines inner)
  | .App fn arg => by
    simp only [dce]
    exact mirCtxRefines_app (dce_refines fn) (dce_refines arg)
  | .Fix f body => by
    -- dce on .Fix recursively: (.Fix f (dce body).1, _)
    simp only [dce]
    -- Case on whether body is a Lam
    cases body with
    | Lam x inner =>
      -- dce (.Lam x inner) = (.Lam x (dce inner).1, _)
      simp only [dce]
      exact mirCtxRefines_fix_lam (dce_refines inner)
    | Var v => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Lit c => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Builtin b => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Error => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Fix _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | App _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Force _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Delay _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Constr _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Case _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Let _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
  | .Constr tag args => by
    simp only [dce]
    cases args with
    | nil =>
      simp only [dceList]
      exact mirCtxRefines_refl _
    | cons e rest =>
      simp only [dceList]
      exact mirCtxRefines_constr (dce_refines e) (dceList_listRel rest)
  | .Case scrut alts => by
    simp only [dce]
    cases alts with
    | nil =>
      simp only [dceList]
      exact mirCtxRefines_case (dce_refines scrut) True.intro
    | cons a rest =>
      simp only [dceList]
      exact mirCtxRefines_case
        (dce_refines scrut)
        ⟨dce_refines a, dceList_listRel rest⟩
  | .Let binds body => by
    -- Step 1: swap each rhs via dceBinds (binds congruence)
    have h_binds_swap :
        MIRCtxRefines (.Let binds body) (.Let (dceBinds binds).1 body) :=
      mirCtxRefines_let_binds_congr binds (dceBinds binds).1 body
        (dceBinds_listRel binds)
    -- Step 2: swap body via dce
    have h_body_swap :
        MIRCtxRefines (.Let (dceBinds binds).1 body)
                      (.Let (dceBinds binds).1 (dce body).1) :=
      mirCtxRefines_let_body (dce_refines body)
    -- Step 3: filterBindings walk
    have h_filter :
        MIRCtxRefines (.Let (dceBinds binds).1 (dce body).1)
          (match Moist.MIR.filterBindings (dceBinds binds).1 (dce body).1 with
           | [] => (dce body).1
           | s :: rest => .Let (s :: rest) (dce body).1) :=
      filterBindings_mirCtxRefines (dceBinds binds).1 (dce body).1
    -- Step 4: equate the filter result with `(dce (.Let binds body)).1`
    simp only [dce]
    cases hfilt : Moist.MIR.filterBindings (dceBinds binds).1 (dce body).1 with
    | nil =>
      have h_filter' :
          MIRCtxRefines (.Let (dceBinds binds).1 (dce body).1) (dce body).1 := by
        rw [hfilt] at h_filter; exact h_filter
      simp only
      exact mirCtxRefines_trans h_binds_swap (mirCtxRefines_trans h_body_swap h_filter')
    | cons s rest =>
      have h_filter' :
          MIRCtxRefines (.Let (dceBinds binds).1 (dce body).1)
                        (.Let (s :: rest) (dce body).1) := by
        rw [hfilt] at h_filter; exact h_filter
      simp only
      exact mirCtxRefines_trans h_binds_swap (mirCtxRefines_trans h_body_swap h_filter')
  termination_by t => sizeOf t

/-- List-level DCE soundness: every element pair is `MIRCtxRefines`. -/
theorem dceList_listRel : ∀ (ts : List Expr),
    ListRel MIRCtxRefines ts (dceList ts).1
  | [] => by simp only [dceList]; exact True.intro
  | e :: rest => by
    simp only [dceList]
    exact ⟨dce_refines e, dceList_listRel rest⟩
  termination_by ts => sizeOf ts

/-- Per-binding DCE soundness: each rhs's pair is `MIRCtxRefines`,
    names and `er` flags are preserved. -/
theorem dceBinds_listRel : ∀ (bs : List (VarId × Expr × Bool)),
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                          MIRCtxRefines b₁.2.1 b₂.2.1) bs (dceBinds bs).1
  | [] => by simp only [dceBinds]; exact True.intro
  | (v, rhs, er) :: rest => by
    simp only [dceBinds]
    refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
    · exact dce_refines rhs
    · exact dceBinds_listRel rest
  termination_by bs => sizeOf bs

end

end Moist.Verified.MIR
