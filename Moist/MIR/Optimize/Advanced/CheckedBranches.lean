import Moist.MIR.Optimize.Advanced.Facts

namespace Moist.MIR.Advanced

/-! A successful list discriminator establishes facts for its selected branch.
Keep the discriminator, including validation of unknown runtime inputs, and
fuse adjacent head/tail projections only inside the nonempty branch. ChooseList
arguments are strict, so its fact applies only inside a literal delayed branch,
not to an arbitrary argument expression evaluated before the builtin runs.
Fully forced ChooseList calls with two literal delayed branches become a
NullList discriminator and Boolean Case. NullList still rejects non-lists; the
removed delay allocations cannot evaluate either branch. Freshened binders
make branch facts stable across captured lambdas and prevent shadowing leaks.
-/

private partial def checkedBranchWalk (environment : List (VarId × Expr))
    (nonemptyLists : List VarId) (expression : Expr) : Expr :=
  match expression with
  | .App (.App (.App selector (.Var listBinder)) empty) (.Delay nonempty) =>
    if resolveHead 64 environment selector == .Force (.Force (.Builtin .ChooseList)) then
      .App (.App (.App selector (.Var listBinder)) (checkedBranchWalk environment nonemptyLists empty))
        (.Delay (checkedBranchWalk environment (listBinder :: nonemptyLists) nonempty))
    else mapChildren (checkedBranchWalk environment nonemptyLists) expression
  | .Case (.App selector (.Var listBinder)) [nonempty, empty] =>
    if resolveHead 64 environment selector == .Force (.Builtin .NullList) then
      .Case (.App selector (.Var listBinder))
        [checkedBranchWalk environment (listBinder :: nonemptyLists) nonempty,
         checkedBranchWalk environment nonemptyLists empty]
    else mapChildren (checkedBranchWalk environment nonemptyLists) expression
  | .Let initialBindings initialBody =>
    let (bindings, body) := flattenBindings initialBindings initialBody
    match bindings with
    | (headBinder, headRhs, _) :: (tailBinder, tailRhs, _) :: remaining =>
      match resolveHead 64 environment headRhs, resolveHead 64 environment tailRhs with
      | .App (.Force (.Builtin .HeadList)) (.Var listBinder),
        .App (.Force (.Builtin .TailList)) (.Var other) =>
        if listBinder == other && nonemptyLists.contains listBinder then
          .Case (.Var listBinder) [.Lam headBinder (.Lam tailBinder
            (checkedBranchWalk ((tailBinder, tailRhs) :: (headBinder, headRhs) :: environment)
              nonemptyLists (.Let remaining body)))]
        else keepFirstChecked environment nonemptyLists bindings body
      | _, _ => keepFirstChecked environment nonemptyLists bindings body
    | _ => keepFirstChecked environment nonemptyLists bindings body
  | _ => mapChildren (checkedBranchWalk environment nonemptyLists) expression
where
  keepFirstChecked (environment : List (VarId × Expr)) (nonemptyLists : List VarId)
      (bindings : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
    match bindings with
    | [] => checkedBranchWalk environment nonemptyLists body
    | (binder, rhs, erased) :: rest =>
      let rhs' := checkedBranchWalk environment nonemptyLists rhs
      let facts := match rhs' with
        | .Var original => if nonemptyLists.contains original then binder :: nonemptyLists else nonemptyLists
        | _ => nonemptyLists
      .Let [(binder, rhs', erased)]
        (checkedBranchWalk ((binder, rhs') :: environment) facts (.Let rest body))

def fuseCheckedListBranches (expression : Expr) : Expr :=
  checkedBranchWalk [] [] (uniqueOptimizationBinders expression)

private partial def lowerDelayedChoicesWalk (environment : List (VarId × Expr))
    (expression : Expr) : Expr :=
  match expression with
  | .Force (.App (.App (.App selector input) (.Delay empty)) (.Delay nonempty)) =>
    if resolveHead 64 environment selector == .Force (.Force (.Builtin .ChooseList)) then
      .Case (.App (.Force (.Builtin .NullList)) (lowerDelayedChoicesWalk environment input))
        [lowerDelayedChoicesWalk environment nonempty, lowerDelayedChoicesWalk environment empty]
    else mapChildren (lowerDelayedChoicesWalk environment) expression
  | .Let [] body => lowerDelayedChoicesWalk environment body
  | .Let ((binder, rhs, erased) :: rest) body =>
    let rhs' := lowerDelayedChoicesWalk environment rhs
    .Let [(binder, rhs', erased)]
      (lowerDelayedChoicesWalk ((binder, rhs') :: environment) (.Let rest body))
  | _ => mapChildren (lowerDelayedChoicesWalk environment) expression

def lowerDelayedListChoices (expression : Expr) : Expr :=
  lowerDelayedChoicesWalk [] (uniqueOptimizationBinders expression)

def optimizeCheckedBranches (expression : Expr) : Expr :=
  fuseCheckedListBranches (lowerDelayedListChoices expression)

end Moist.MIR.Advanced
