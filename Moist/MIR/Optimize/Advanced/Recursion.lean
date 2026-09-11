import Moist.MIR.Optimize.Advanced.Traversal

namespace Moist.MIR.Advanced

/-! Static argument transformation for call-by-value Fix expressions.

Move an invariant leading parameter outside the recursive worker only when
every recursive occurrence is a direct application to that exact parameter.
At least one worker lambda remains, so creating a partial application cannot
evaluate the recursive body. Bare, aliased, changed and effectful arguments
are rejected. Hygiene is established before moving any binder.
-/

private partial def invariantUses (recursive parameter : VarId) (expression : Expr) : Bool :=
  match expression with
  | .Var binder => binder != recursive
  | .App _ _ =>
    let (function, arguments) := applicationSpine expression
    match function, arguments with
    | .Var binder, .Var argument :: rest =>
      if binder == recursive then
        argument == parameter && rest.all (invariantUses recursive parameter)
      else invariantUses recursive parameter function && arguments.all (invariantUses recursive parameter)
    | _, _ => invariantUses recursive parameter function && arguments.all (invariantUses recursive parameter)
  | .Lam _ body | .Fix _ body | .Delay body | .Force body => invariantUses recursive parameter body
  | .Let bindings body => bindings.all (fun entry => invariantUses recursive parameter entry.2.1) &&
      invariantUses recursive parameter body
  | .Constr _ arguments => arguments.all (invariantUses recursive parameter)
  | .Case scrutinee alternatives => invariantUses recursive parameter scrutinee &&
      alternatives.all (invariantUses recursive parameter)
  | _ => true

private partial def removeArgument (recursive : VarId) (expression : Expr) : Expr :=
  match expression with
  | .App _ _ =>
    let (function, arguments) := applicationSpine expression
    match function with
    | .Var binder =>
      if binder == recursive then
        (arguments.drop 1).map (removeArgument recursive) |>.foldl Expr.App function
      else (arguments.map (removeArgument recursive)).foldl Expr.App (removeArgument recursive function)
    | _ => (arguments.map (removeArgument recursive)).foldl Expr.App (removeArgument recursive function)
  | _ => mapChildren (removeArgument recursive) expression

private partial def staticArgumentsCore (expression : Expr) : Expr :=
  let result := mapChildren staticArgumentsCore expression
  match result with
  | .Fix recursive (.Lam parameter (.Lam next body)) =>
    let worker := Expr.Lam next body
    if (freeVars worker).contains recursive && invariantUses recursive parameter worker then
      .Lam parameter (staticArgumentsCore (.Fix recursive (removeArgument recursive worker)))
    else result
  | _ => result

def staticArguments (expression : Expr) : Expr :=
  staticArgumentsCore (uniqueOptimizationBinders expression)

end Moist.MIR.Advanced
