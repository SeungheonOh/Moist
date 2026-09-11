import Moist.MIR.Optimize.Advanced.Facts
import Moist.MIR.Optimize.PreLower

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! Lower projections of positively known builtin pairs to native Case.
Projection-only bindings are unboxed once for their entire lexical scope.
Unknown source parameters never supply pair evidence. The producer remains
strict, and fresh component binders cannot capture deferred uses. Already-shared
projection functions are retained: expanding them adds component-binding cost.
Whole-pair unboxing requires a projection on the first evaluation frontier.
-/

private def knownProduct (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  match resolveHead 64 environment expression with
  | .App (.Builtin .UnConstrData) _ | .App (.App (.Builtin .MkPairData) _) _ => true
  | _ => false

private def projection (binder : VarId) : Expr → Option Bool
  | .App (.Force (.Force (.Builtin .FstPair))) (.Var other) =>
    if binder == other then some false else none
  | .App (.Force (.Force (.Builtin .SndPair))) (.Var other) =>
    if binder == other then some true else none
  | _ => none

private partial def projectionOnly (binder : VarId) (expression : Expr) : Bool :=
  if (projection binder expression).isSome then true else
  match expression with
  | .Var other => binder != other
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => projectionOnly binder body
  | .App function argument => projectionOnly binder function && projectionOnly binder argument
  | .Constr _ fields => fields.all (projectionOnly binder)
  | .Case scrutinee alternatives =>
    projectionOnly binder scrutinee && alternatives.all (projectionOnly binder)
  | .Let bindings body =>
    bindings.all (fun binding => projectionOnly binder binding.2.1) && projectionOnly binder body
  | _ => true

private partial def replaceProjections (binder first second : VarId) (expression : Expr) : Expr :=
  match projection binder expression with
  | some false => .Var first
  | some true => .Var second
  | none => mapChildren (replaceProjections binder first second) expression

private partial def productWalk (environment : List (VarId × Expr)) (expression : Expr) : FreshM Expr := do
  match expression with
  | .Let [] body => productWalk environment body
  | .Let ((binder, rhs, erased) :: rest) body =>
    let rhs' ← productWalk environment rhs
    let suffix := if rest.isEmpty then body else .Let rest body
    if knownProduct environment rhs' && firstEvaluationUse binder suffix && projectionOnly binder suffix then
      let first ← freshVar "first"
      let second ← freshVar "second"
      let suffix' ← productWalk environment (replaceProjections binder first second suffix)
      return .Case rhs' [.Lam first (.Lam second suffix')]
    else
      return .Let [(binder, rhs', erased)] (← productWalk ((binder, rhs') :: environment) suffix)
  | .Lam binder body => return .Lam binder (← productWalk environment body)
  | .Fix binder body => return .Fix binder (← productWalk environment body)
  | .App function argument =>
    let function' ← productWalk environment function
    let argument' ← productWalk environment argument
    let component := match function' with
      | .Force (.Force (.Builtin .FstPair)) => some false
      | .Force (.Force (.Builtin .SndPair)) => some true
      | _ => none
    match component with
    | some selected =>
      if knownProduct environment argument' then
        let first ← freshVar "first"
        let second ← freshVar "second"
        return .Case argument' [.Lam first (.Lam second (.Var (if selected then second else first)))]
      else return .App function' argument'
    | none => return .App function' argument'
  | .Force body => return .Force (← productWalk environment body)
  | .Delay body => return .Delay (← productWalk environment body)
  | .Constr tag fields => return .Constr tag (← fields.mapM (productWalk environment))
  | .Case scrutinee alternatives =>
    return .Case (← productWalk environment scrutinee) (← alternatives.mapM (productWalk environment))
  | _ => return expression

def destructureProducts (expression : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders expression
  preLowerInlineExpr (runFresh (productWalk [] prepared) (maxUidExpr prepared + 1))

end Moist.MIR.Advanced
