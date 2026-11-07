import Moist.MIR.Optimize.Advanced.Facts
import Moist.MIR.Optimize.Advanced.Shapes
import Moist.MIR.Optimize.PreLower

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! Lower projections of positively known builtin pairs to native Case.
Projection-only bindings are unboxed once for their entire lexical scope.
Unknown source parameters never supply pair evidence. The producer remains
strict, and fresh component binders cannot capture deferred uses. Already-shared
projection functions are retained: expanding them adds component-binding cost.
Whole-pair unboxing requires a projection on the first evaluation frontier.
Component binders are numbered from a counter above every identifier of the
program, threaded through the walk in evaluation order. The walk is skipped
when the freshened program is not well scoped.
-/

def knownProduct (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  match resolveHead 64 environment expression with
  | .App (.Builtin .UnConstrData) _ | .App (.App (.Builtin .MkPairData) _) _ => true
  | _ => false

/-- Every occurrence of `binder` is the argument of a pair projection. -/
def projectionOnly (binder : VarId) (expression : Expr) : Bool :=
  match expression with
  | .App (.Force (.Force (.Builtin .FstPair))) (.Var _) => true
  | .App (.Force (.Force (.Builtin .SndPair))) (.Var _) => true
  | .Var other => binder != other
  | .Lam _ body => projectionOnly binder body
  | .Fix _ body => projectionOnly binder body
  | .Force body => projectionOnly binder body
  | .Delay body => projectionOnly binder body
  | .App function argument => projectionOnly binder function && projectionOnly binder argument
  | .Constr _ fields => fields.attach.all fun ⟨field, _⟩ => projectionOnly binder field
  | .Case scrutinee alternatives =>
    projectionOnly binder scrutinee &&
      alternatives.attach.all fun ⟨alternative, _⟩ => projectionOnly binder alternative
  | .Let bindings body =>
    (bindings.attach.all fun ⟨(_, rhs, _), _⟩ => projectionOnly binder rhs) &&
      projectionOnly binder body
  | .Lit _ | .Builtin _ | .Error => true
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption)
       simp only [exprSize] at *; omega)

def replaceProjections (binder first second : VarId) (expression : Expr) : Expr :=
  match expression with
  | .App (.Force (.Force (.Builtin .FstPair))) (.Var other) =>
    if binder == other then .Var first else expression
  | .App (.Force (.Force (.Builtin .SndPair))) (.Var other) =>
    if binder == other then .Var second else expression
  | .App function argument =>
    .App (replaceProjections binder first second function)
      (replaceProjections binder first second argument)
  | .Lam name body => .Lam name (replaceProjections binder first second body)
  | .Fix name body => .Fix name (replaceProjections binder first second body)
  | .Force body => .Force (replaceProjections binder first second body)
  | .Delay body => .Delay (replaceProjections binder first second body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ => replaceProjections binder first second field)
  | .Case scrutinee alternatives =>
    .Case (replaceProjections binder first second scrutinee)
      (alternatives.attach.map fun ⟨alternative, _⟩ =>
        replaceProjections binder first second alternative)
  | .Let bindings body =>
    .Let (bindings.attach.map fun ⟨(name, rhs, erased), _⟩ =>
        (name, replaceProjections binder first second rhs, erased))
      (replaceProjections binder first second body)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSizeBinds_mem_lt (by assumption)
       simp only [exprSize] at *; omega)

/-! ## Size of the replaced suffix -/

theorem productList_attach_map (children : List Expr) (transform : Expr → Expr) :
    (children.attach.map fun ⟨child, _⟩ => transform child) = children.map transform := by
  induction children with
  | nil => rfl
  | cons child rest inductionHypothesis =>
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem productBinds_attach_map (bindings : List (VarId × Expr × Bool)) (transform : Expr → Expr) :
    (bindings.attach.map fun ⟨(name, rhs, erased), _⟩ => (name, transform rhs, erased)) =
      bindings.map fun (name, rhs, erased) => (name, transform rhs, erased) := by
  induction bindings with
  | nil => rfl
  | cons binding rest inductionHypothesis =>
    obtain ⟨name, rhs, erased⟩ := binding
    simp only [List.attach_cons, List.map_cons, List.map_map]
    congr 1

theorem exprSizeList_map_le (children : List Expr) (transform : Expr → Expr)
    (bound : ∀ child ∈ children, exprSize (transform child) ≤ exprSize child) :
    exprSizeList (children.map transform) ≤ exprSizeList children := by
  induction children with
  | nil => simp [exprSizeList]
  | cons child rest inductionHypothesis =>
    simp only [List.map_cons, exprSizeList]
    have head := bound child (.head _)
    have tail := inductionHypothesis fun c hc => bound c (.tail _ hc)
    omega

theorem exprSizeBinds_map_le (bindings : List (VarId × Expr × Bool)) (transform : Expr → Expr)
    (bound : ∀ binding ∈ bindings, exprSize (transform binding.2.1) ≤ exprSize binding.2.1) :
    exprSizeBinds (bindings.map fun (name, rhs, erased) => (name, transform rhs, erased)) ≤
      exprSizeBinds bindings := by
  induction bindings with
  | nil => simp [exprSizeBinds]
  | cons binding rest inductionHypothesis =>
    obtain ⟨name, rhs, erased⟩ := binding
    have head := bound (name, rhs, erased) (.head _)
    have tail := inductionHypothesis fun c hc => bound c (.tail _ hc)
    simp only [List.map_cons, exprSizeBinds] at head tail ⊢
    omega

theorem exprSize_replaceProjections (binder first second : VarId) (expression : Expr) :
    exprSize (replaceProjections binder first second expression) ≤ exprSize expression := by
  unfold replaceProjections
  split
  · split <;> simp [exprSize]
  · split <;> simp [exprSize]
  · rename_i function argument _ _
    have := exprSize_replaceProjections binder first second function
    have := exprSize_replaceProjections binder first second argument
    simp only [exprSize]; omega
  · rename_i name body
    have := exprSize_replaceProjections binder first second body
    simp only [exprSize]; omega
  · rename_i name body
    have := exprSize_replaceProjections binder first second body
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceProjections binder first second body
    simp only [exprSize]; omega
  · rename_i body
    have := exprSize_replaceProjections binder first second body
    simp only [exprSize]; omega
  · rename_i tag fields
    have := exprSizeList_map_le fields (replaceProjections binder first second)
      fun child _ => exprSize_replaceProjections binder first second child
    rw [productList_attach_map]
    simp only [exprSize]; omega
  · rename_i scrutinee alternatives
    have := exprSize_replaceProjections binder first second scrutinee
    have := exprSizeList_map_le alternatives (replaceProjections binder first second)
      fun child _ => exprSize_replaceProjections binder first second child
    rw [productList_attach_map]
    simp only [exprSize]; omega
  · rename_i bindings body
    have := exprSize_replaceProjections binder first second body
    have := exprSizeBinds_map_le bindings (replaceProjections binder first second)
      fun binding _ => exprSize_replaceProjections binder first second binding.2.1
    rw [productBinds_attach_map]
    simp only [exprSize] at *; omega
  all_goals exact Nat.le_refl _
termination_by exprSize expression
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (subst_vars; have := exprSizeBinds_mem_lt (by assumption); simp only [exprSize] at *; omega)

/-! ## The walk

`productWalk environment expression next` returns the rewritten expression and
the next unused component identifier. -/

mutual
  def productWalk (environment : List (VarId × Expr)) (expression : Expr) (next : Nat) : Expr × Nat :=
    match expression with
    | .Let [] body => productWalk environment body next
    | .Let ((binder, rhs, erased) :: rest) body =>
      let rhs' := productWalk environment rhs next
      if knownProduct environment rhs'.1 && firstEvaluationUse binder (.Let rest body) &&
          projectionOnly binder (.Let rest body) then
        let first : VarId := { uid := rhs'.2, origin := .gen, hint := "first" }
        let second : VarId := { uid := rhs'.2 + 1, origin := .gen, hint := "second" }
        let suffix' := productWalk environment
          (replaceProjections binder first second (.Let rest body)) (rhs'.2 + 2)
        (.Case rhs'.1 [.Lam first (.Lam second suffix'.1)], suffix'.2)
      else
        let suffix' := productWalk ((binder, rhs'.1) :: environment) (.Let rest body) rhs'.2
        (.Let [(binder, rhs'.1, erased)] suffix'.1, suffix'.2)
    | .Lam binder body =>
      let body' := productWalk environment body next
      (.Lam binder body'.1, body'.2)
    | .Fix binder body =>
      let body' := productWalk environment body next
      (.Fix binder body'.1, body'.2)
    | .App function argument =>
      let function' := productWalk environment function next
      let argument' := productWalk environment argument function'.2
      let first : VarId := { uid := argument'.2, origin := .gen, hint := "first" }
      let second : VarId := { uid := argument'.2 + 1, origin := .gen, hint := "second" }
      match function'.1 with
      | .Force (.Force (.Builtin .FstPair)) =>
        if knownProduct environment argument'.1 then
          (.Case argument'.1 [.Lam first (.Lam second (.Var first))], argument'.2 + 2)
        else (.App function'.1 argument'.1, argument'.2)
      | .Force (.Force (.Builtin .SndPair)) =>
        if knownProduct environment argument'.1 then
          (.Case argument'.1 [.Lam first (.Lam second (.Var second))], argument'.2 + 2)
        else (.App function'.1 argument'.1, argument'.2)
      | _ => (.App function'.1 argument'.1, argument'.2)
    | .Force body =>
      let body' := productWalk environment body next
      (.Force body'.1, body'.2)
    | .Delay body =>
      let body' := productWalk environment body next
      (.Delay body'.1, body'.2)
    | .Constr tag fields =>
      let fields' := productWalkList environment fields next
      (.Constr tag fields'.1, fields'.2)
    | .Case scrutinee alternatives =>
      let scrutinee' := productWalk environment scrutinee next
      let alternatives' := productWalkList environment alternatives scrutinee'.2
      (.Case scrutinee'.1 alternatives'.1, alternatives'.2)
    | .Var _ | .Lit _ | .Builtin _ | .Error => (expression, next)
  termination_by 2 * exprSize expression
  decreasing_by
    all_goals first
      | (simp only [exprSize, exprSizeBinds]; omega)
      | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
      | (apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (exprSize_replaceProjections _ _ _ _))
         simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)

  def productWalkList (environment : List (VarId × Expr)) (expressions : List Expr) (next : Nat) :
      List Expr × Nat :=
    match expressions with
    | [] => ([], next)
    | expression :: rest =>
      let expression' := productWalk environment expression next
      let rest' := productWalkList environment rest expression'.2
      (expression'.1 :: rest'.1, rest'.2)
  termination_by 2 * exprSizeList expressions + 1
  decreasing_by
    all_goals (simp only [exprSizeList]; have := exprSize_pos expression; omega)
end

def destructureProducts (expression : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders expression
  preLowerInlineExpr
    (if wellScoped prepared then (productWalk [] prepared (maxUidExpr prepared + 1)).1 else prepared)

end Moist.MIR.Advanced
