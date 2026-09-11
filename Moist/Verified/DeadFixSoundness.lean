import Moist.Verified.InlineSoundness
import Moist.Verified.AdvancedTraversal
import Moist.MIR.Optimize.Advanced.Allocations

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced
open Moist.Plutus.Term (Term)
open Moist.Verified.Contextual
open Moist.Verified.Equivalence

theorem mirCtxRefines_dead_application (binder : VarId) (body argument : Expr)
    (unused : (freeVars body).contains binder = false) (pure : isPure argument = true) :
    MIRCtxRefines (.App (.Lam binder body) argument) body :=
  mirCtxRefines_trans (mirCtxRefines_app_lam_to_let binder body argument)
    (dead_let_mirCtxRefines unused pure)

theorem mirCtxRefines_self_application (binder parameter : VarId) (body : Expr) :
    MIRCtxRefines (.App (.Lam binder (.App (.Var binder) (.Var binder))) (.Lam parameter body))
      (.App (.Lam parameter body) (.Lam parameter body)) := by
  intro environment
  simp only [lowerTotalExpr, expandFix, lowerTotal, Option.bind_eq_bind, envLookupT_cons_self]
  cases lowered : lowerTotal (parameter :: environment) (expandFix body) with
  | none => simp
  | some term =>
    simp only [Option.bind_some]
    refine ⟨fun _ => rfl, ?_⟩
    have closed := lowerTotal_closedAt (parameter :: environment) (expandFix body) term lowered
    have refines := InlineSoundness.SubstCommute.uplc_beta_multi_pure_openRefines
      (d := environment.length) (t_body := .Apply (.Var 1) (.Var 1)) (t_rhs := .Lam 0 term)
      (by simp [closedAt]) (by simpa [closedAt] using closed) ?_
    · simpa only [substTerm, if_pos rfl] using refines
    · intro runtime _ stack
      refine ⟨1, .VLam term runtime, rfl, ?_⟩
      intro fuel bound
      cases fuel with
      | zero => intro impossible; cases impossible
      | succ fuel =>
        have equal : fuel = 0 := by omega
        subst fuel
        intro impossible; cases impossible

private def fixUnroll (recursive parameter self argument binder : VarId) (body : Expr) : Expr :=
  .App (.Lam binder (.App (.Var binder) (.Var binder)))
    (.Lam self (.App (.Lam recursive (.Lam parameter body))
      (.Lam argument (.App (.App (.Var self) (.Var self)) (.Var argument)))))

private theorem fixUnroll_lower (environment : List VarId)
    (recursive parameter self argument binder : VarId) (body : Expr)
    (different : (argument == self) = false) :
    lowerTotalExpr environment (fixUnroll recursive parameter self argument binder body) =
      (lowerTotal (parameter :: recursive :: self :: environment) (expandFix body)).map fixLamWrapUplc := by
  simp only [fixUnroll, lowerTotalExpr, expandFix, lowerTotal, Option.bind_eq_bind,
    envLookupT_cons_self, envLookupT_cons_second _ _ environment different]
  cases lowerTotal (parameter :: recursive :: self :: environment) (expandFix body) <;> rfl

theorem eliminateDeadFix_local (recursive parameter : VarId) (body : Expr)
    (unused : (freeVars (.Lam parameter body)).contains recursive = false) :
    MIRCtxRefines (.Fix recursive (.Lam parameter body)) (.Lam parameter body) := by
  let freshStart := max (maxUidExpr (.Lam parameter body)) (maxUidExpr (expandFix body)) + 1
  let self : VarId := ⟨freshStart, .gen, "self"⟩
  let argument : VarId := ⟨freshStart + 1, .gen, "argument"⟩
  let binder : VarId := ⟨freshStart + 2, .gen, "binder"⟩
  have different : (argument == self) = false := by
    rw [VarId.beq_false_iff]
    exact .inr (by simp only [argument, self]; omega)
  have freshBody : (freeVars (.Lam parameter body)).contains self = false :=
    maxUidExpr_fresh _ self (by simp only [self, freshStart]; omega)
  have freshExpanded : (freeVars (expandFix body)).contains self = false :=
    maxUidExpr_fresh _ self (by simp only [self, freshStart]; omega)
  apply mirCtxRefines_trans (m₂ := fixUnroll recursive parameter self argument binder body)
  · apply mirCtxRefines_of_lowerEq
    intro environment
    rw [fixUnroll_lower environment recursive parameter self argument binder body different,
      lowerTotalExpr_fix_lam_with_fresh environment recursive parameter body self freshExpanded]
  · apply mirCtxRefines_trans (m₂ :=
        .App (.Lam binder (.App (.Var binder) (.Var binder))) (.Lam self (.Lam parameter body)))
    · apply mirCtxRefines_app (mirCtxRefines_refl _)
      apply mirCtxRefines_lam
      exact mirCtxRefines_dead_application recursive (.Lam parameter body) _ unused (by simp [isPure])
    · exact mirCtxRefines_trans (mirCtxRefines_self_application binder self (.Lam parameter body))
        (mirCtxRefines_dead_application self (.Lam parameter body) _ freshBody (by simp [isPure]))

theorem eliminateDeadFixRoot_refines (expression : Expr) :
    MIRCtxRefines expression (eliminateDeadFixRoot expression) := by
  unfold eliminateDeadFixRoot
  split
  · rename_i recursive parameter body
    dsimp only
    split
    · exact mirCtxRefines_refl _
    · rename_i unused
      exact eliminateDeadFix_local recursive parameter body (Bool.eq_false_iff.mpr unused)
  · exact mirCtxRefines_refl _

theorem eliminateDeadFix_refines (expression : Expr) :
    MIRCtxRefines expression (eliminateDeadFix expression) :=
  rewriteBottomUp_refines eliminateDeadFixRoot eliminateDeadFixRoot_refines
    (fun _ _ => rfl) (exprSize expression) expression

theorem eliminateDeadFix_recursive_eq (expression : Expr) :
    eliminateDeadFix expression = eliminateDeadFixRoot (mapChildren eliminateDeadFix expression) :=
  rewriteBottomUp_complete eliminateDeadFixRoot expression

end Moist.Verified.MIR
