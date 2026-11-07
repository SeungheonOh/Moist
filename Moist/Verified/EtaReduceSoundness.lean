import Moist.Verified.EtaReduce.Rule
import Moist.Verified.AdvancedTraversal
import Moist.MIR.Optimize.EtaReduce

/-! # Soundness of MIR eta reduction

`etaReduce` rewrites `λx. f x` to `f` bottom-up when `x` is not free in `f`
and `f` is a callable value. The local rule is `EtaReduce.eta_mirCtxRefines`
(proved with the eta logical relation, which relates the eta-expanded closure
to a builtin state as well as to a closure); the traversal composes it with
the MIR congruences. The mandatory lambda under `Fix` is never rewritten.
-/

namespace Moist.Verified.MIR

open Moist.MIR (Expr VarId etaReduce etaReduceFuel etaRule)
open Moist.Verified.EtaReduce (eta_mirCtxRefines)
open Moist.Verified.Equivalence (ListRel)

theorem etaRule_refines {expression reduced : Expr} (fired : etaRule expression = some reduced) :
    MIRCtxRefines expression reduced := by
  unfold etaRule at fired
  split at fired
  · split at fired
    · rename_i checked
      cases fired
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at checked
      exact eta_mirCtxRefines checked.1.1 checked.1.2 checked.2
    · cases fired
  · cases fired

private theorem bindings_fst (fuel : Nat) (binds : List (VarId × Expr × Bool)) :
    List.map Prod.fst (binds.map fun (v, rhs, er) =>
        let (rhs', changed) := etaReduceFuel fuel rhs
        ((v, rhs', er), changed)) =
      binds.map fun (v, rhs, er) => (v, (etaReduceFuel fuel rhs).1, er) := by
  induction binds with
  | nil => rfl
  | cons binding rest ih =>
    obtain ⟨v, rhs, er⟩ := binding
    simp only [List.map_cons, ih]

theorem etaReduceFuel_refines (fuel : Nat) (expression : Expr) :
    MIRCtxRefines expression (etaReduceFuel fuel expression).1 := by
  induction fuel generalizing expression with
  | zero => exact mirCtxRefines_refl expression
  | succ fuel ih =>
    have list : ∀ expressions : List Expr,
        ListRel MIRCtxRefines expressions
          (List.map Prod.fst (expressions.map (etaReduceFuel fuel))) := by
      intro expressions
      rw [List.map_map]
      exact listRel_map_refines _ ih expressions
    cases expression with
    | Var _ | Lit _ | Builtin _ | Error => exact mirCtxRefines_refl _
    | Lam x body =>
      have inner := mirCtxRefines_lam (x := x) (ih body)
      rcases reducedBody : etaReduceFuel fuel body with ⟨body', changed⟩
      rw [reducedBody] at inner
      simp only [etaReduceFuel, reducedBody]
      split
      · exact inner
      · rename_i reduced fired
        split
        · exact inner
        · exact mirCtxRefines_trans inner
            (mirCtxRefines_trans (etaRule_refines fired) (ih _))
    | Fix f body =>
      cases body with
      | Lam parameter inner =>
        simp only [etaReduceFuel]
        exact mirCtxRefines_fix_lam (ih inner)
      | Var _ | Lit _ | Builtin _ | Error | Fix _ _ | App _ _ | Force _ | Delay _
      | Constr _ _ | Case _ _ | Let _ _ =>
        exact mirCtxRefines_fix_nonlam_lhs (by intros; intro impossible; cases impossible)
    | App function argument =>
      simp only [etaReduceFuel]
      exact mirCtxRefines_app (ih function) (ih argument)
    | Force inner =>
      simp only [etaReduceFuel]
      exact mirCtxRefines_force (ih inner)
    | Delay inner =>
      simp only [etaReduceFuel]
      exact mirCtxRefines_delay (ih inner)
    | Constr tag fields =>
      simp only [etaReduceFuel]
      cases fields with
      | nil => exact mirCtxRefines_refl _
      | cons field rest =>
        have related := list (field :: rest)
        simp only [List.map_cons] at related ⊢
        exact mirCtxRefines_constr related.1 related.2
    | Case scrutinee alternatives =>
      simp only [etaReduceFuel]
      exact mirCtxRefines_case (ih scrutinee) (list alternatives)
    | Let bindings body =>
      simp only [etaReduceFuel]
      rw [bindings_fst]
      exact mirCtxRefines_trans
        (mirCtxRefines_let_binds_congr bindings _ body
          (bindings_map_refines (fun rhs => (etaReduceFuel fuel rhs).1) ih bindings))
        (mirCtxRefines_let_body (ih body))

/-- **Eta reduction is sound**: the result contextually refines the input. -/
theorem etaReduce_refines (e : Expr) : MIRCtxRefines e (etaReduce e).1 :=
  etaReduceFuel_refines _ e

/-! ## Fuel

Every recursive call of `etaReduceFuel` is on a strictly smaller expression,
so any fuel of at least `exprSize e` computes the same result as `etaReduce`. -/

open Moist.MIR (exprSize exprSizeList exprSizeBinds)

theorem etaRule_smaller {expression reduced : Expr} (fired : etaRule expression = some reduced) :
    exprSize reduced < exprSize expression := by
  unfold etaRule at fired
  split at fired
  · split at fired
    · cases fired; simp [exprSize]; omega
    · cases fired
  · cases fired

private theorem sizeList_map_le (transform : Expr → Expr)
    (smaller : ∀ expression, exprSize (transform expression) ≤ exprSize expression) :
    ∀ expressions : List Expr,
      exprSizeList (expressions.map transform) ≤ exprSizeList expressions
  | [] => by simp [exprSizeList]
  | expression :: rest => by
    have head := smaller expression
    have tail := sizeList_map_le transform smaller rest
    simp only [List.map_cons, exprSizeList]
    omega

private theorem sizeBinds_map_le (transform : Expr → Expr)
    (smaller : ∀ expression, exprSize (transform expression) ≤ exprSize expression) :
    ∀ bindings : List (VarId × Expr × Bool),
      exprSizeBinds (bindings.map fun (v, rhs, er) => (v, transform rhs, er)) ≤
        exprSizeBinds bindings
  | [] => by simp [exprSizeBinds]
  | (v, rhs, er) :: rest => by
    have head := smaller rhs
    have tail := sizeBinds_map_le transform smaller rest
    simp only [List.map_cons, exprSizeBinds] at tail ⊢
    omega

theorem etaReduceFuel_size (fuel : Nat) (expression : Expr) :
    exprSize (etaReduceFuel fuel expression).1 ≤ exprSize expression := by
  induction fuel generalizing expression with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    have list : ∀ expressions : List Expr,
        exprSizeList (List.map Prod.fst (expressions.map (etaReduceFuel fuel))) ≤
          exprSizeList expressions := by
      intro expressions
      rw [List.map_map]
      exact sizeList_map_le _ ih expressions
    cases expression with
    | Var _ | Lit _ | Builtin _ | Error => exact Nat.le_refl _
    | Lam x body =>
      have inner := ih body
      rcases reducedBody : etaReduceFuel fuel body with ⟨body', changed⟩
      rw [reducedBody] at inner
      simp only at inner
      simp only [etaReduceFuel, reducedBody]
      split
      · simp [exprSize]; omega
      · rename_i reduced fired
        have smaller := etaRule_smaller fired
        split
        · simp [exprSize]; omega
        · have again := ih reduced
          simp only [exprSize] at smaller ⊢
          omega
    | Fix f body =>
      have whole := ih body
      cases body
      case Lam parameter inner =>
        have := ih inner
        simp only [etaReduceFuel, exprSize]
        omega
      all_goals (simp only [etaReduceFuel, exprSize] at whole ⊢; omega)
    | App function argument =>
      have := ih function
      have := ih argument
      simp only [etaReduceFuel, exprSize]
      omega
    | Force inner =>
      have := ih inner
      simp only [etaReduceFuel, exprSize]
      omega
    | Delay inner =>
      have := ih inner
      simp only [etaReduceFuel, exprSize]
      omega
    | Constr tag fields =>
      have := list fields
      simp only [etaReduceFuel, exprSize]
      omega
    | Case scrutinee alternatives =>
      have := ih scrutinee
      have := list alternatives
      simp only [etaReduceFuel, exprSize]
      omega
    | Let bindings body =>
      have := ih body
      have := sizeBinds_map_le (fun rhs => (etaReduceFuel fuel rhs).1) ih bindings
      simp only [etaReduceFuel, exprSize]
      rw [bindings_fst]
      omega

private theorem exprSize_binding_le {binding : VarId × Expr × Bool}
    {bindings : List (VarId × Expr × Bool)} (member : binding ∈ bindings) :
    exprSize binding.2.1 ≤ exprSizeBinds bindings := by
  induction bindings with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨binder, rhs, erased⟩ := head
    simp only [List.mem_cons] at member
    cases member with
    | inl equal => subst binding; simp [exprSizeBinds]
    | inr member => have bound := ih member; simp only [exprSizeBinds]; omega

/-- Fuel beyond the expression size does not change the result. -/
theorem etaReduceFuel_irrel (left right : Nat) (expression : Expr)
    (leftBound : exprSize expression ≤ left) (rightBound : exprSize expression ≤ right) :
    etaReduceFuel left expression = etaReduceFuel right expression := by
  induction left generalizing right expression with
  | zero => have := exprSize_positive expression; omega
  | succ left ih =>
    cases right with
    | zero => have := exprSize_positive expression; omega
    | succ right =>
      have child : ∀ inner, exprSize inner < exprSize expression →
          etaReduceFuel left inner = etaReduceFuel right inner :=
        fun inner smaller => ih right inner (by omega) (by omega)
      have list : ∀ expressions : List Expr, exprSizeList expressions < exprSize expression →
          expressions.map (etaReduceFuel left) = expressions.map (etaReduceFuel right) := by
        intro expressions bound
        apply List.map_congr_left
        intro inner member
        exact child inner (by have := exprSize_member_le member; omega)
      cases expression with
      | Var _ | Lit _ | Builtin _ | Error => rfl
      | Lam x body =>
        have bodyEqual := child body (by simp [exprSize])
        have inner := etaReduceFuel_size right body
        simp only [etaReduceFuel, bodyEqual]
        rcases reducedBody : etaReduceFuel right body with ⟨body', changed⟩
        rw [reducedBody] at inner
        simp only at inner
        simp only
        cases fired : etaRule (.Lam x body') with
        | none => rfl
        | some reduced =>
          have smaller := etaRule_smaller fired
          simp only [exprSize] at smaller
          simp only
          split
          · rfl
          · rw [child reduced (by simp only [exprSize]; omega)]
      | Fix f body =>
        cases body
        case Lam parameter inner =>
          simp only [etaReduceFuel, child inner (by simp [exprSize]; omega)]
        all_goals
          simp only [etaReduceFuel]
          rw [child _ (by simp [exprSize])]
      | App function argument =>
        simp only [etaReduceFuel, child function (by simp [exprSize]; omega),
          child argument (by simp [exprSize]; omega)]
      | Force inner =>
        simp only [etaReduceFuel, child inner (by simp [exprSize])]
      | Delay inner =>
        simp only [etaReduceFuel, child inner (by simp [exprSize])]
      | Constr tag fields =>
        simp only [etaReduceFuel, list fields (by simp [exprSize])]
      | Case scrutinee alternatives =>
        simp only [etaReduceFuel, child scrutinee (by simp [exprSize]; omega),
          list alternatives (by simp [exprSize]; omega)]
      | Let bindings body =>
        have bindingsEqual :
            (bindings.map fun (v, rhs, er) =>
              let (rhs', changed) := etaReduceFuel left rhs
              ((v, rhs', er), changed)) =
            (bindings.map fun (v, rhs, er) =>
              let (rhs', changed) := etaReduceFuel right rhs
              ((v, rhs', er), changed)) := by
          apply List.map_congr_left
          intro binding member
          obtain ⟨v, rhs, er⟩ := binding
          have bound := exprSize_binding_le member
          simp only at bound
          have equal := child rhs (by simp only [exprSize]; omega)
          simp only [equal]
        simp only [etaReduceFuel, bindingsEqual, child body (by simp [exprSize]; omega)]

/-- `etaReduce` runs `etaReduceFuel` with enough fuel: any larger fuel agrees. -/
theorem etaReduce_eq_fuel (expression : Expr) (fuel : Nat)
    (bound : exprSize expression ≤ fuel) :
    etaReduce expression = etaReduceFuel fuel expression :=
  etaReduceFuel_irrel _ _ expression (Nat.le_refl _) bound

end Moist.Verified.MIR
