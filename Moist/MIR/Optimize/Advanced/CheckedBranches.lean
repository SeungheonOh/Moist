import Moist.MIR.Optimize.Advanced.Shapes

namespace Moist.MIR.Advanced

/-! A successful list discriminator establishes facts for its selected branch.
Keep the discriminator, including validation of unknown runtime inputs, and
fuse adjacent head/tail projections only inside the nonempty branch. ChooseList
arguments are strict, so its fact applies only inside a literal delayed branch,
not to an arbitrary argument expression evaluated before the builtin runs.
Fully forced ChooseList calls with two literal delayed branches become a
NullList discriminator and Boolean Case. NullList still rejects non-lists; the
removed delay allocations cannot evaluate either branch. Both walks run on
well-scoped programs with unique binders, so branch facts are stable across
captured lambdas and no binder shadows a recorded name.
-/

/-- The list projected by a head binding followed by a tail binding, when it
    is known to be non-empty. -/
def headTailList (environment : List (VarId × Expr)) (nonemptyLists : List VarId)
    (headRhs tailRhs : Expr) : Option VarId :=
  match resolveHead 64 environment headRhs, resolveHead 64 environment tailRhs with
  | .App (.Force (.Builtin .HeadList)) (.Var listBinder),
    .App (.Force (.Builtin .TailList)) (.Var other) =>
    if listBinder == other && nonemptyLists.contains listBinder then some listBinder else none
  | _, _ => none

/-- A binder aliasing a non-empty list is non-empty. -/
def aliasFacts (nonemptyLists : List VarId) (binder : VarId) (rhs : Expr) : List VarId :=
  match rhs with
  | .Var original => if nonemptyLists.contains original then binder :: nonemptyLists else nonemptyLists
  | _ => nonemptyLists

set_option linter.unusedVariables false in
def checkedBranchWalk (environment : List (VarId × Expr)) (nonemptyLists : List VarId)
    (expression : Expr) : Expr :=
  match expression with
  | .App function argument =>
    match hf : function, ha : argument with
    | .App (.App selector (.Var listBinder)) empty, .Delay nonempty =>
      if resolveHead 64 environment selector == .Force (.Force (.Builtin .ChooseList)) then
        .App (.App (.App selector (.Var listBinder)) (checkedBranchWalk environment nonemptyLists empty))
          (.Delay (checkedBranchWalk environment (listBinder :: nonemptyLists) nonempty))
      else
        .App (checkedBranchWalk environment nonemptyLists function)
          (checkedBranchWalk environment nonemptyLists argument)
    | _, _ =>
      .App (checkedBranchWalk environment nonemptyLists function)
        (checkedBranchWalk environment nonemptyLists argument)
  | .Case scrutinee alternatives =>
    match hs : scrutinee, halts : alternatives with
    | .App selector (.Var listBinder), [nonempty, empty] =>
      if resolveHead 64 environment selector == .Force (.Builtin .NullList) then
        .Case (.App selector (.Var listBinder))
          [checkedBranchWalk environment (listBinder :: nonemptyLists) nonempty,
           checkedBranchWalk environment nonemptyLists empty]
      else
        .Case (checkedBranchWalk environment nonemptyLists scrutinee)
          (alternatives.attach.map fun ⟨alternative, _⟩ =>
            checkedBranchWalk environment nonemptyLists alternative)
    | _, _ =>
      .Case (checkedBranchWalk environment nonemptyLists scrutinee)
        (alternatives.attach.map fun ⟨alternative, _⟩ =>
          checkedBranchWalk environment nonemptyLists alternative)
  | .Let initialBindings initialBody =>
    match flattening : flattenBindings initialBindings initialBody with
    | ([], body) => checkedBranchWalk environment nonemptyLists body
    | ((binder, rhs, erased) :: rest, body) =>
      match rest with
      | (tailBinder, tailRhs, tailErased) :: remaining =>
        match headTailList environment nonemptyLists rhs tailRhs with
        | some listBinder =>
          .Case (.Var listBinder) [.Lam binder (.Lam tailBinder
            (checkedBranchWalk ((tailBinder, tailRhs) :: (binder, rhs) :: environment)
              nonemptyLists (.Let remaining body)))]
        | none =>
          let rhs' := checkedBranchWalk environment nonemptyLists rhs
          .Let [(binder, rhs', erased)]
            (checkedBranchWalk ((binder, rhs') :: environment) (aliasFacts nonemptyLists binder rhs')
              (.Let ((tailBinder, tailRhs, tailErased) :: remaining) body))
      | [] =>
        let rhs' := checkedBranchWalk environment nonemptyLists rhs
        .Let [(binder, rhs', erased)]
          (checkedBranchWalk ((binder, rhs') :: environment) (aliasFacts nonemptyLists binder rhs')
            (.Let [] body))
  | .Lam binder body => .Lam binder (checkedBranchWalk environment nonemptyLists body)
  | .Fix binder body => .Fix binder (checkedBranchWalk environment nonemptyLists body)
  | .Force body => .Force (checkedBranchWalk environment nonemptyLists body)
  | .Delay body => .Delay (checkedBranchWalk environment nonemptyLists body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ => checkedBranchWalk environment nonemptyLists field)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have bound := exprSize_flattenBindings initialBindings initialBody
       rw [flattening] at bound
       simp only [exprSize, exprSizeBinds] at bound ⊢
       have := exprSize_pos rhs
       have := exprSize_pos tailRhs
       omega)
    | (have bound := exprSize_flattenBindings initialBindings initialBody
       rw [flattening] at bound
       simp only [exprSize, exprSizeBinds] at bound ⊢
       have := exprSize_pos rhs
       omega)
    | (have bound := exprSize_flattenBindings initialBindings initialBody
       rw [flattening] at bound
       simp only [exprSize, exprSizeBinds] at bound ⊢
       omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

def fuseCheckedListBranches (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then checkedBranchWalk [] [] unique else unique

set_option linter.unusedVariables false in
def lowerDelayedChoicesWalk (environment : List (VarId × Expr)) (expression : Expr) : Expr :=
  match expression with
  | .Force body =>
    match hb : body with
    | .App (.App (.App selector input) (.Delay empty)) (.Delay nonempty) =>
      if resolveHead 64 environment selector == .Force (.Force (.Builtin .ChooseList)) then
        .Case (.App (.Force (.Builtin .NullList)) (lowerDelayedChoicesWalk environment input))
          [lowerDelayedChoicesWalk environment nonempty, lowerDelayedChoicesWalk environment empty]
      else .Force (lowerDelayedChoicesWalk environment body)
    | _ => .Force (lowerDelayedChoicesWalk environment body)
  | .Let [] body => lowerDelayedChoicesWalk environment body
  | .Let ((binder, rhs, erased) :: rest) body =>
    let rhs' := lowerDelayedChoicesWalk environment rhs
    .Let [(binder, rhs', erased)]
      (lowerDelayedChoicesWalk ((binder, rhs') :: environment) (.Let rest body))
  | .Lam binder body => .Lam binder (lowerDelayedChoicesWalk environment body)
  | .Fix binder body => .Fix binder (lowerDelayedChoicesWalk environment body)
  | .App function argument =>
    .App (lowerDelayedChoicesWalk environment function) (lowerDelayedChoicesWalk environment argument)
  | .Delay body => .Delay (lowerDelayedChoicesWalk environment body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ => lowerDelayedChoicesWalk environment field)
  | .Case scrutinee alternatives =>
    .Case (lowerDelayedChoicesWalk environment scrutinee)
      (alternatives.attach.map fun ⟨alternative, _⟩ => lowerDelayedChoicesWalk environment alternative)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

def lowerDelayedListChoices (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then lowerDelayedChoicesWalk [] unique else unique

def optimizeCheckedBranches (expression : Expr) : Expr :=
  fuseCheckedListBranches (lowerDelayedListChoices expression)

end Moist.MIR.Advanced
