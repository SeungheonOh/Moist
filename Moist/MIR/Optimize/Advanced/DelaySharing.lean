import Moist.MIR.Optimize.Advanced.Traversal

namespace Moist.MIR.Advanced

/-! Delayed-value sharing.

In `let v = delay d`, when `d` is pure and every use of `v` is `force v`,
the binding becomes `let v = d` and each `force v` becomes `v`: the body is
evaluated once, eagerly. `onlyForced` also rejects any rebinding of `v`, so
`removeForces` never needs to reason about shadowing. Binders are made
unique first, so the rebinding guard does not cost any sharing.
-/

mutual
  /-- Every occurrence of `binder` is forced directly and `binder` is never rebound. -/
  def onlyForced (binder : VarId) : Expr → Bool
    | .Var other => binder != other
    | .Lit _ | .Builtin _ | .Error => true
    | .Lam other body | .Fix other body => binder != other && onlyForced binder body
    | .App function argument => onlyForced binder function && onlyForced binder argument
    | .Force (.Var _) => true
    | .Force inner => onlyForced binder inner
    | .Delay inner => onlyForced binder inner
    | .Constr _ fields => onlyForcedList binder fields
    | .Case scrutinee alternatives =>
      onlyForced binder scrutinee && onlyForcedList binder alternatives
    | .Let bindings body => onlyForcedBinds binder bindings && onlyForced binder body
  termination_by expression => sizeOf expression

  def onlyForcedList (binder : VarId) : List Expr → Bool
    | [] => true
    | expression :: rest => onlyForced binder expression && onlyForcedList binder rest
  termination_by expressions => sizeOf expressions

  def onlyForcedBinds (binder : VarId) : List (VarId × Expr × Bool) → Bool
    | [] => true
    | (other, rhs, _) :: rest =>
      binder != other && onlyForced binder rhs && onlyForcedBinds binder rest
  termination_by bindings => sizeOf bindings
end

mutual
  /-- Replace `force binder` by `binder`. -/
  def removeForces (binder : VarId) : Expr → Expr
    | .Force (.Var other) => if binder == other then .Var other else .Force (.Var other)
    | .Force inner => .Force (removeForces binder inner)
    | .Lam other body => .Lam other (removeForces binder body)
    | .Fix other body => .Fix other (removeForces binder body)
    | .App function argument => .App (removeForces binder function) (removeForces binder argument)
    | .Delay inner => .Delay (removeForces binder inner)
    | .Constr tag fields => .Constr tag (removeForcesList binder fields)
    | .Case scrutinee alternatives =>
      .Case (removeForces binder scrutinee) (removeForcesList binder alternatives)
    | .Let bindings body => .Let (removeForcesBinds binder bindings) (removeForces binder body)
    | expression => expression
  termination_by expression => sizeOf expression

  def removeForcesList (binder : VarId) : List Expr → List Expr
    | [] => []
    | expression :: rest => removeForces binder expression :: removeForcesList binder rest
  termination_by expressions => sizeOf expressions

  def removeForcesBinds (binder : VarId) : List (VarId × Expr × Bool) → List (VarId × Expr × Bool)
    | [] => []
    | (other, rhs, erased) :: rest =>
      (other, removeForces binder rhs, erased) :: removeForcesBinds binder rest
  termination_by bindings => sizeOf bindings
end

/-- Re-nest one binding in front of an already processed suffix, sharing it
    when it is a pure delay that is only ever forced. -/
def shareDelayBinding (binding : VarId × Expr × Bool) (suffix : Expr) : Expr :=
  match binding with
  | (binder, .Delay delayed, erased) =>
    if isPure delayed && onlyForced binder suffix then
      .Let [(binder, delayed, erased)] (removeForces binder suffix)
    else .Let [(binder, .Delay delayed, erased)] suffix
  | binding => .Let [binding] suffix

def shareDelaysLocal : Expr → Expr
  | .Let bindings body => bindings.foldr shareDelayBinding body
  | expression => expression

def shareDelaysCore (expression : Expr) : Expr :=
  rewriteBottomUp shareDelaysLocal (exprSize expression) expression

def shareDelayedValues (expression : Expr) : Expr :=
  shareDelaysCore (uniqueOptimizationBinders expression)

end Moist.MIR.Advanced
