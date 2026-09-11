import Moist.MIR.Optimize.Advanced.Traversal
import Moist.Verified.DCESoundness

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced
open Moist.Verified.Equivalence

theorem exprSize_positive (expression : Expr) : 0 < exprSize expression := by
  cases expression <;> simp [exprSize] <;> omega

theorem exprSize_member_le {expression : Expr} {expressions : List Expr}
    (member : expression ∈ expressions) : exprSize expression ≤ exprSizeList expressions := by
  induction expressions with
  | nil => cases member
  | cons head tail inductionHypothesis =>
    simp only [List.mem_cons] at member
    cases member with
    | inl equal => subst expression; simp [exprSizeList]
    | inr member => have bound := inductionHypothesis member; simp only [exprSizeList]; omega

private theorem exprSize_binding_le {binding : VarId × Expr × Bool}
    {bindings : List (VarId × Expr × Bool)} (member : binding ∈ bindings) :
    exprSize binding.2.1 ≤ exprSizeBinds bindings := by
  induction bindings with
  | nil => cases member
  | cons head tail inductionHypothesis =>
    obtain ⟨binder, rhs, erased⟩ := head
    simp only [List.mem_cons] at member
    cases member with
    | inl equal => subst binding; simp [exprSizeBinds]
    | inr member => have bound := inductionHypothesis member; simp only [exprSizeBinds]; omega

theorem mapChildren_congr_size (left right : Expr → Expr) (expression : Expr)
    (agree : ∀ child, exprSize child < exprSize expression → left child = right child) :
    mapChildren left expression = mapChildren right expression := by
  cases expression with
  | Var _ | Lit _ | Builtin _ | Error => rfl
  | Lam binder body | Fix binder body | Force body | Delay body =>
    simp only [mapChildren]
    rw [agree body (by simp [exprSize])]
  | App function argument =>
    simp only [mapChildren]
    rw [agree function (by simp [exprSize]; omega), agree argument (by simp [exprSize]; omega)]
  | Constr tag fields =>
    simp only [mapChildren]
    congr 1
    apply List.map_congr_left
    intro field member
    exact agree field (by have bound := exprSize_member_le member; simp only [exprSize]; omega)
  | Case scrutinee alternatives =>
    simp only [mapChildren]
    congr 1
    · exact agree scrutinee (by simp [exprSize]; omega)
    · apply List.map_congr_left
      intro alternative member
      exact agree alternative (by have bound := exprSize_member_le member; simp only [exprSize]; omega)
  | Let bindings body =>
    simp only [mapChildren]
    congr 1
    · apply List.map_congr_left
      intro binding member
      obtain ⟨binder, rhs, erased⟩ := binding
      simp only
      rw [agree rhs (by have bound := exprSize_binding_le member; simp only [exprSize] at *; omega)]
    · exact agree body (by simp [exprSize]; omega)

theorem rewriteBottomUp_fuel_irrel (rewrite : Expr → Expr) (expression : Expr)
    (leftFuel rightFuel : Nat) (leftBound : exprSize expression ≤ leftFuel)
    (rightBound : exprSize expression ≤ rightFuel) :
    rewriteBottomUp rewrite leftFuel expression = rewriteBottomUp rewrite rightFuel expression := by
  cases leftFuel with
  | zero => have positive := exprSize_positive expression; omega
  | succ leftFuel =>
    cases rightFuel with
    | zero => have positive := exprSize_positive expression; omega
    | succ rightFuel =>
      simp only [rewriteBottomUp]
      congr 1
      apply mapChildren_congr_size
      intro child smaller
      exact rewriteBottomUp_fuel_irrel rewrite child leftFuel rightFuel (by omega) (by omega)
termination_by exprSize expression

theorem rewriteBottomUp_complete (rewrite : Expr → Expr) (expression : Expr) :
    rewriteBottomUp rewrite (exprSize expression) expression =
      rewrite (mapChildren (fun child => rewriteBottomUp rewrite (exprSize child) child) expression) := by
  cases sizeEqual : exprSize expression with
  | zero => have positive := exprSize_positive expression; omega
  | succ fuel =>
    simp only [rewriteBottomUp]
    congr 1
    apply mapChildren_congr_size
    intro child smaller
    exact rewriteBottomUp_fuel_irrel rewrite child fuel (exprSize child) (by omega) (Nat.le_refl _)

theorem rewriteBottomUp_unique (rewrite candidate : Expr → Expr)
    (equation : ∀ expression, candidate expression = rewrite (mapChildren candidate expression))
    (expression : Expr) :
    rewriteBottomUp rewrite (exprSize expression) expression = candidate expression := by
  rw [rewriteBottomUp_complete, equation expression]
  congr 1
  apply mapChildren_congr_size
  intro child smaller
  exact rewriteBottomUp_unique rewrite candidate equation child
termination_by exprSize expression

theorem fix_nonlam_refines {binder : VarId} {body target : Expr}
    (notLambda : ∀ parameter inner, body ≠ .Lam parameter inner) :
    MIRCtxRefines (.Fix binder body) target := by
  intro environment
  have failed : lowerTotalExpr environment (.Fix binder body) = none := by
    cases body <;> simp_all [lowerTotalExpr, expandFix, lowerTotal]
  simp [failed]

theorem listRel_map_refines (transform : Expr → Expr)
    (sound : ∀ expression, MIRCtxRefines expression (transform expression))
    (expressions : List Expr) : ListRel MIRCtxRefines expressions (expressions.map transform) := by
  induction expressions with
  | nil => trivial
  | cons expression rest inductionHypothesis => exact ⟨sound expression, inductionHypothesis⟩

theorem bindings_map_refines (transform : Expr → Expr)
    (sound : ∀ expression, MIRCtxRefines expression (transform expression))
    (bindings : List (VarId × Expr × Bool)) :
    ListRel (fun before after => before.1 = after.1 ∧ before.2.2 = after.2.2 ∧
      MIRCtxRefines before.2.1 after.2.1)
      bindings (bindings.map fun (binder, rhs, erased) => (binder, transform rhs, erased)) := by
  induction bindings with
  | nil => trivial
  | cons binding rest inductionHypothesis =>
    obtain ⟨binder, rhs, erased⟩ := binding
    exact ⟨⟨rfl, rfl, sound rhs⟩, inductionHypothesis⟩

theorem rewriteBottomUp_refines (rewrite : Expr → Expr)
    (localSound : ∀ expression, MIRCtxRefines expression (rewrite expression))
    (preservesLambda : ∀ binder body, rewrite (.Lam binder body) = .Lam binder body)
    (fuel : Nat) (expression : Expr) :
    MIRCtxRefines expression (rewriteBottomUp rewrite fuel expression) := by
  induction fuel using Nat.strongRecOn generalizing expression with
  | ind fuel inductionHypothesis =>
    cases fuel with
    | zero => exact mirCtxRefines_refl expression
    | succ fuel =>
      let transform := rewriteBottomUp rewrite fuel
      have childrenSound : ∀ child, MIRCtxRefines child (transform child) :=
        inductionHypothesis fuel (by omega)
      apply mirCtxRefines_trans (m₂ := mapChildren transform expression)
      · cases expression with
        | Var _ | Lit _ | Builtin _ | Error => exact mirCtxRefines_refl _
        | Lam binder body => exact mirCtxRefines_lam (childrenSound body)
        | Force body => exact mirCtxRefines_force (childrenSound body)
        | Delay body => exact mirCtxRefines_delay (childrenSound body)
        | App function argument => exact mirCtxRefines_app (childrenSound function) (childrenSound argument)
        | Constr tag fields =>
          cases fields with
          | nil => exact mirCtxRefines_refl _
          | cons field rest =>
            exact mirCtxRefines_constr (childrenSound field) (listRel_map_refines transform childrenSound rest)
        | Case scrutinee alternatives =>
          exact mirCtxRefines_case (childrenSound scrutinee)
            (listRel_map_refines transform childrenSound alternatives)
        | Let bindings body =>
          exact mirCtxRefines_trans
            (mirCtxRefines_let_binds_congr bindings _ body (bindings_map_refines transform childrenSound bindings))
            (mirCtxRefines_let_body (childrenSound body))
        | Fix binder body =>
          cases body with
          | Lam parameter body =>
            cases fuel with
            | zero => exact mirCtxRefines_refl _
            | succ remaining =>
              simp only [mapChildren, transform, rewriteBottomUp, preservesLambda]
              exact mirCtxRefines_fix_lam (inductionHypothesis remaining (by omega) body)
          | Var _ | Lit _ | Builtin _ | Error | Fix _ _ | App _ _ | Force _ | Delay _
          | Constr _ _ | Case _ _ | Let _ _ =>
            exact fix_nonlam_refines (by intros; intro impossible; cases impossible)
      · exact localSound _

end Moist.Verified.MIR
