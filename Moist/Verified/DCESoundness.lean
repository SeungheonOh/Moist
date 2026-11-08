import Moist.Verified.AdvancedTraversal
import Moist.Verified.DeadLet
import Moist.MIR.Optimize.DCE

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of MIR Dead Code Elimination

`dce` is the bottom-up traversal of the local rewrite `dceLocal`, which drops
dead pure bindings of one `Let` (`filterBindings`). Each dropped binding is
removed by `dead_let_mirCtxRefines`; `rewriteBottomUp_refines` lifts the
local step to the whole traversal.
-/

namespace Moist.Verified.MIR

open Moist.MIR
  (Expr VarId dce dceList dceBinds filterBindings isPure freeVars
   lowerTotalExpr lowerTotal_prepend_unused)
open Moist.MIR.Advanced (mapChildren rewriteBottomUp)
open Moist.Verified (closedAt)

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

omit sv in
private theorem let_cons_lowerEq (binding : VarId × Expr × Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let (binding :: rest) body) =
      lowerTotalExpr env (.Let [binding] (.Let rest body)) := by
  obtain ⟨v, rhs, er⟩ := binding
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
    Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]

/-- Dropping the bindings rejected by `filterBindings` is a refinement. -/
private theorem filterBindings_mirCtxRefines :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      MIRCtxRefines (.Let binds body) (.Let (filterBindings binds body) body)
  | [], _ => mirCtxRefines_refl _
  | (v, rhs, er) :: rest, body => by
    have step := mirCtxRefines_trans (mirCtxRefines_of_lowerEq (let_cons_lowerEq (v, rhs, er) rest body))
      (mirCtxRefines_let_body (filterBindings_mirCtxRefines rest body))
    simp only [filterBindings]
    split
    · exact mirCtxRefines_trans step
        (mirCtxRefines_of_lowerEq fun env => (let_cons_lowerEq _ _ body env).symm)
    · next keep =>
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true] at keep
      refine mirCtxRefines_trans step (mirCtxRefines_trans (mirCtxRefines_of_lowerEq fun env => ?_)
        (dead_let_mirCtxRefines keep.1 (by simpa using keep.2)))
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
        Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]

/-- One local DCE step: drop the dead pure bindings of a `Let`. -/
def dceLocal : Expr → Expr
  | .Let binds body =>
    match filterBindings binds body with
    | [] => body
    | binding :: rest => .Let (binding :: rest) body
  | expression => expression

theorem dceLocal_refines : ∀ expression, MIRCtxRefines expression (dceLocal expression)
  | .Let binds body => by
    have h := filterBindings_mirCtxRefines binds body
    simp only [dceLocal]
    split
    · next empty => rw [empty] at h; exact mirCtxRefines_trans h mirCtxRefines_let_nil
    · next binding rest surviving => rw [surviving] at h; exact h
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _ | .Force _
  | .Delay _ | .Constr _ _ | .Case _ _ => mirCtxRefines_refl _

omit sv in
private theorem dceList_fst : ∀ (expressions : List Expr),
    (dceList expressions).1 = expressions.map fun child => (dce child).1
  | [] => by simp [dceList]
  | child :: rest => by simp [dceList, dceList_fst rest]

omit sv in
private theorem dceBinds_fst : ∀ (bindings : List (VarId × Expr × Bool)),
    (dceBinds bindings).1 =
      bindings.map fun (binder, rhs, erased) => (binder, (dce rhs).1, erased)
  | [] => by simp [dceBinds]
  | (binder, rhs, erased) :: rest => by simp [dceBinds, dceBinds_fst rest]

omit sv in
/-- `dce` is one `dceLocal` step after recursing into every child. -/
theorem dce_eq_local (expression : Expr) :
    (dce expression).1 = dceLocal (mapChildren (fun child => (dce child).1) expression) := by
  cases expression with
  | Let binds body =>
    simp only [dce, mapChildren, dceLocal, dceBinds_fst]
    split <;> simp_all
  | Constr tag args => simp [dce, mapChildren, dceLocal, dceList_fst]
  | Case scrut alts => simp [dce, mapChildren, dceLocal, dceList_fst]
  | _ => simp [dce, mapChildren, dceLocal]

/-- `dce` is sound: the optimized program refines the original. -/
theorem dce_refines (t : Expr) : MIRCtxRefines t (dce t).1 := by
  rw [← rewriteBottomUp_unique dceLocal (fun expression => (dce expression).1) dce_eq_local t]
  exact rewriteBottomUp_refines dceLocal dceLocal_refines (fun _ _ => rfl) _ t

end Moist.Verified.MIR
