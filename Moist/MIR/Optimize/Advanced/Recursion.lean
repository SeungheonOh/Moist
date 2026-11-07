import Moist.MIR.Optimize.Advanced.Traversal

namespace Moist.MIR.Advanced

/-! Static argument transformation for call-by-value Fix expressions.

Move an invariant leading parameter outside the recursive worker only when
every recursive occurrence is a direct application to that exact parameter.
At least one worker lambda remains, so creating a partial application cannot
evaluate the recursive body. Bare, aliased, changed and effectful arguments
are rejected. Hygiene is established before moving any binder, and the
check also rejects any worker that rebinds the recursive name or the
parameter.
-/

mutual
  /-- Every occurrence of `recursive` is the head of an application whose
      first argument is exactly `parameter`, and neither name is rebound. -/
  def invariantUses (recursive parameter : VarId) : Expr → Bool
    | .Var binder => binder != recursive
    | .Lit _ | .Builtin _ | .Error => true
    | .Lam binder body | .Fix binder body =>
      binder != recursive && binder != parameter && invariantUses recursive parameter body
    | .App (.Var binder) argument =>
      if binder == recursive then
        match argument with
        | .Var argument => argument == parameter
        | _ => false
      else invariantUses recursive parameter argument
    | .App function argument =>
      invariantUses recursive parameter function && invariantUses recursive parameter argument
    | .Force body | .Delay body => invariantUses recursive parameter body
    | .Constr _ arguments => invariantUsesList recursive parameter arguments
    | .Case scrutinee alternatives =>
      invariantUses recursive parameter scrutinee &&
        invariantUsesList recursive parameter alternatives
    | .Let bindings body => invariantUsesLet recursive parameter bindings body
  termination_by expression => sizeOf expression

  def invariantUsesList (recursive parameter : VarId) : List Expr → Bool
    | [] => true
    | expression :: rest =>
      invariantUses recursive parameter expression && invariantUsesList recursive parameter rest
  termination_by expressions => sizeOf expressions

  def invariantUsesLet (recursive parameter : VarId) :
      List (VarId × Expr × Bool) → Expr → Bool
    | [], body => invariantUses recursive parameter body
    | (binder, rhs, _) :: rest, body =>
      binder != recursive && binder != parameter && invariantUses recursive parameter rhs &&
        invariantUsesLet recursive parameter rest body
  termination_by bindings body => sizeOf bindings + sizeOf body
end

mutual
  /-- Drop the first argument of every application headed by `recursive`. -/
  def removeArgument (recursive : VarId) : Expr → Expr
    | .App (.Var binder) argument =>
      if binder == recursive then .Var binder
      else .App (.Var binder) (removeArgument recursive argument)
    | .App function argument =>
      .App (removeArgument recursive function) (removeArgument recursive argument)
    | .Lam binder body => .Lam binder (removeArgument recursive body)
    | .Fix binder body => .Fix binder (removeArgument recursive body)
    | .Force body => .Force (removeArgument recursive body)
    | .Delay body => .Delay (removeArgument recursive body)
    | .Constr tag arguments => .Constr tag (removeArgumentList recursive arguments)
    | .Case scrutinee alternatives =>
      .Case (removeArgument recursive scrutinee) (removeArgumentList recursive alternatives)
    | .Let bindings body =>
      .Let (removeArgumentBinds recursive bindings) (removeArgument recursive body)
    | expression => expression
  termination_by expression => sizeOf expression

  def removeArgumentList (recursive : VarId) : List Expr → List Expr
    | [] => []
    | expression :: rest =>
      removeArgument recursive expression :: removeArgumentList recursive rest
  termination_by expressions => sizeOf expressions

  def removeArgumentBinds (recursive : VarId) :
      List (VarId × Expr × Bool) → List (VarId × Expr × Bool)
    | [] => []
    | (binder, rhs, erased) :: rest =>
      (binder, removeArgument recursive rhs, erased) :: removeArgumentBinds recursive rest
  termination_by bindings => sizeOf bindings
end

/-- One root rewrite; `recurse` re-runs the pass on the shortened worker. -/
def staticArgumentsRoot (recurse : Expr → Expr) : Expr → Expr
  | .Fix recursive (.Lam parameter (.Lam next body)) =>
    let worker := Expr.Lam next body
    if parameter != recursive && (freeVars worker).contains recursive &&
        invariantUses recursive parameter worker then
      .Lam parameter (recurse (.Fix recursive (removeArgument recursive worker)))
    else .Fix recursive (.Lam parameter worker)
  | expression => expression

/-- Bottom-up traversal; every recursive call consumes one unit of fuel. -/
def staticArgumentsFuel : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    staticArgumentsRoot (staticArgumentsFuel fuel)
      (mapChildren (staticArgumentsFuel fuel) expression)

/-- The pass never grows an expression, so `exprSize` bounds the recursion depth. -/
def staticArgumentsCore (expression : Expr) : Expr :=
  staticArgumentsFuel (exprSize expression) expression

def staticArguments (expression : Expr) : Expr :=
  staticArgumentsCore (uniqueOptimizationBinders expression)

end Moist.MIR.Advanced
