import Moist.MIR.Optimize.Advanced.KnownLists
import Moist.MIR.Optimize.Advanced.Products

namespace Moist.MIR.Advanced

/-! # Entries of lists of data pairs

A name holds a list of data pairs when its binding is an `unMapData`
application or a pair-list literal (`knownPairDataList`), when it is the tail
bound by a `case` on such a list, or when it is a parameter of a recursive
function every call of which passes such a list at that position (the fixed
point of `KnownLists` with the pair-list test as its base).

The head bound by a `case` on a list of data pairs is a builtin pair. When
every occurrence of the head in the alternative is the argument of `fstPair`
or `sndPair`, the head is destructured once with native `case` and the
projections become its components:

```
case l [λh t. B, E]   ~>   case l [λh t. case h [λa b. B[fstPair h := a, sndPair h := b]], E]
```

The component binders are prepared by `prepareHeads`, which binds them to the
head, unused, right inside every candidate alternative; `pairListWalk` turns
those bindings into the destructuring when the list is known to hold data
pairs, and `preLowerInlineExpr` removes the bindings left unused elsewhere.
-/

/-- `expression` evaluates, when it halts, to a list of data pairs: a name of
    `lists`, or a known pair-data list. -/
def pairListKnown (environment : List (VarId × Expr)) (lists : List VarId) (expression : Expr) : Bool :=
  (match expression with
    | .Var binder => lists.contains binder
    | _ => false) ||
    knownPairDataList 64 environment expression

/-- Positions of a recursive function's parameters holding pair lists in every call. -/
def pairListPositions (environment : List (VarId × Expr)) (lists : List VarId) (recursive : VarId)
    (parameters : List VarId) (arguments : List Expr) (body : Expr) : List Nat :=
  if arguments.length < parameters.length then [] else
    let initial := (List.range parameters.length).filter fun position =>
      match arguments[position]? with
      | some argument => pairListKnown environment lists argument
      | none => false
    listPositions.stable lists recursive parameters body (initial.length + 1) initial

/-- Names bound by `environment` to known pair lists. -/
def environmentPairLists (environment : List (VarId × Expr)) (lists : List VarId) : List VarId :=
  environment.filterMap fun entry =>
    if pairListKnown environment lists (.Var entry.1) then some entry.1 else none

/-- Positions of a let-bound recursive function's parameters holding pair
    lists in every call. -/
def letFixPairPositions (environment : List (VarId × Expr)) (lists : List VarId) (binder recursive : VarId)
    (parameters : List VarId) (inner scope : Expr) : List Nat :=
  stable (parameters.length + 1) (List.range parameters.length)
where
  stable : Nat → List Nat → List Nat
    | 0, _ => []
    | fuel + 1, positions =>
      if positions.isEmpty then [] else
        let assumed := listedParameters parameters positions ++ lists
        let outer := environmentPairLists environment lists ++ lists
        let kept := positions.filter fun position =>
          listCallsOK recursive parameters.length [position] assumed inner &&
            listCallsOK binder parameters.length [position] outer scope
        if kept.length == positions.length then
          if listCallsOK recursive parameters.length positions assumed inner &&
              listCallsOK binder parameters.length positions outer scope then positions else []
        else stable fuel kept

/-- The facts recording the components of a destructured head. -/
def componentFacts (environment : List (VarId × Expr)) (head first second : VarId) :
    List (VarId × Expr) :=
  (second, sndApp head) :: (first, fstApp head) :: environment

/-- An alternative prepared by `prepareHeads`: the two component binders bound
    to the head, then a body using the head only in projections. -/
def preparedHead (environment : List (VarId × Expr)) (head : VarId) : Expr → Option (VarId × VarId × Expr)
  | .Let [(first, .Var head₁, _)] (.Let [(second, .Var head₂, _)] body) =>
    if head₁ == head && head₂ == head && !(second == first) && !(first == head) && !(second == head) &&
        decide (maxUidExpr body < first.uid) && decide (maxUidExpr body < second.uid) &&
        projectionOnly (componentFacts environment head first second) head body then
      some (first, second, body)
    else none
  | _ => none

set_option linter.unusedVariables false in
def pairListWalk (environment : List (VarId × Expr)) (lists : List VarId) (expression : Expr) : Expr :=
  match expression with
  | .App function argument =>
    match hfix : fixApplication (.App function argument) [] with
    | some (recursive, parameter, body, arguments) =>
      let parameters := parameter :: (lambdaChain body).1
      let inner := (lambdaChain body).2
      let positions := pairListPositions environment lists recursive parameters arguments inner
      let lists' := listedParameters parameters positions ++ lists
      applyAll (.Fix recursive (lambdaWrap parameters (pairListWalk environment lists' inner)))
        (arguments.attach.map fun ⟨argument, _⟩ => pairListWalk environment lists argument)
    | none =>
      .App (pairListWalk environment lists function) (pairListWalk environment lists argument)
  | .Case scrutinee alternatives =>
    match hs : scrutinee, halts : alternatives with
    | .Var listBinder, .Lam headBinder (.Lam tailBinder body) :: rest =>
      if pairListKnown environment lists (.Var listBinder) then
        let body' := pairListWalk environment (tailBinder :: lists) body
        let rest' := rest.attach.map fun ⟨alternative, _⟩ => pairListWalk environment lists alternative
        match preparedHead environment headBinder body' with
        | some (first, second, inner) =>
          .Case (.Var listBinder)
            (.Lam headBinder (.Lam tailBinder (.Case (.Var headBinder)
              [.Lam first (.Lam second (replaceProjections (componentFacts environment headBinder first second)
                headBinder first second inner))])) :: rest')
        | none => .Case (.Var listBinder) (.Lam headBinder (.Lam tailBinder body') :: rest')
      else
        .Case (pairListWalk environment lists scrutinee)
          (alternatives.attach.map fun ⟨alternative, _⟩ => pairListWalk environment lists alternative)
    | _, _ =>
      .Case (pairListWalk environment lists scrutinee)
        (alternatives.attach.map fun ⟨alternative, _⟩ => pairListWalk environment lists alternative)
  | .Let [] body => pairListWalk environment lists body
  | .Let ((binder, rhs, erased) :: rest) body =>
    match hr : rhs with
    | .Fix recursive (.Lam parameter fixBody) =>
      let parameters := parameter :: (lambdaChain fixBody).1
      let inner := (lambdaChain fixBody).2
      let positions := letFixPairPositions environment lists binder recursive parameters inner (.Let rest body)
      if positions.isEmpty then
        let rhs' := pairListWalk environment lists (.Fix recursive (.Lam parameter fixBody))
        .Let [(binder, rhs', erased)] (pairListWalk ((binder, rhs') :: environment) lists (.Let rest body))
      else
        let rhs' := Expr.Fix recursive (lambdaWrap parameters
          (pairListWalk environment (listedParameters parameters positions ++ lists) inner))
        .Let [(binder, rhs', erased)] (pairListWalk ((binder, rhs') :: environment) lists (.Let rest body))
    | other =>
      let rhs' := pairListWalk environment lists other
      .Let [(binder, rhs', erased)] (pairListWalk ((binder, rhs') :: environment) lists (.Let rest body))
  | .Lam binder body => .Lam binder (pairListWalk environment lists body)
  | .Fix binder body => .Fix binder (pairListWalk environment lists body)
  | .Force body => .Force (pairListWalk environment lists body)
  | .Delay body => .Delay (pairListWalk environment lists body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ => pairListWalk environment lists field)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (have := fixApplication_inner_size hfix
       simp only [exprSize] at *; omega)
    | (have bound := fixApplication_size _ _ hfix
       have := bound.2.2 _ (by assumption)
       simp only [exprSize, exprSizeList] at *; omega)
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)
    | (subst_vars; have := exprSize_lambdaChain fixBody; simp only [exprSize, exprSizeBinds] at *; omega)
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos other; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize, exprSizeList] at *; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

/-! ## Preparing the component binders -/

/-- Whether the head of a list `case` alternative is used, and only in
    projections (resolved through the let bindings of `environment`). -/
def headCandidate (environment : List (VarId × Expr)) (head : VarId) (body : Expr) : Bool :=
  (freeVars body).contains head && projectionOnly environment head body

mutual
/-- The walk returns the prepared expression and the next unused identifier;
    binders are numbered after the children, so those of an alternative exceed
    every identifier inside it. -/
def prepareWalk (environment : List (VarId × Expr)) (expression : Expr) (next : Nat) : Expr × Nat :=
  match expression with
  | .Case (.Var listBinder) (.Lam headBinder (.Lam tailBinder body) :: rest) =>
    let body' := prepareWalk environment body next
    let rest' := prepareList environment rest body'.2
    if headCandidate environment headBinder body'.1 then
      let first : VarId := { uid := rest'.2, origin := .gen, hint := "key" }
      let second : VarId := { uid := rest'.2 + 1, origin := .gen, hint := "value" }
      (.Case (.Var listBinder) (.Lam headBinder (.Lam tailBinder
        (.Let [(first, .Var headBinder, false)] (.Let [(second, .Var headBinder, false)] body'.1))) ::
          rest'.1), rest'.2 + 2)
    else (.Case (.Var listBinder) (.Lam headBinder (.Lam tailBinder body'.1) :: rest'.1), rest'.2)
  | .Case scrutinee alternatives =>
    let scrutinee' := prepareWalk environment scrutinee next
    let alternatives' := prepareList environment alternatives scrutinee'.2
    (.Case scrutinee'.1 alternatives'.1, alternatives'.2)
  | .Let [] body => prepareWalk environment body next
  | .Let ((binder, rhs, erased) :: rest) body =>
    let rhs' := prepareWalk environment rhs next
    let rest' := prepareWalk ((binder, rhs'.1) :: environment) (.Let rest body) rhs'.2
    (.Let [(binder, rhs'.1, erased)] rest'.1, rest'.2)
  | .Lam binder body =>
    let body' := prepareWalk environment body next
    (.Lam binder body'.1, body'.2)
  | .Fix binder body =>
    let body' := prepareWalk environment body next
    (.Fix binder body'.1, body'.2)
  | .App function argument =>
    let function' := prepareWalk environment function next
    let argument' := prepareWalk environment argument function'.2
    (.App function'.1 argument'.1, argument'.2)
  | .Force body =>
    let body' := prepareWalk environment body next
    (.Force body'.1, body'.2)
  | .Delay body =>
    let body' := prepareWalk environment body next
    (.Delay body'.1, body'.2)
  | .Constr tag fields =>
    let fields' := prepareList environment fields next
    (.Constr tag fields'.1, fields'.2)
  | .Var _ | .Lit _ | .Builtin _ | .Error => (expression, next)
termination_by 2 * exprSize expression
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)

def prepareList (environment : List (VarId × Expr)) (expressions : List Expr) (next : Nat) :
    List Expr × Nat :=
  match expressions with
  | [] => ([], next)
  | expression :: rest =>
    let expression' := prepareWalk environment expression next
    let rest' := prepareList environment rest expression'.2
    (expression'.1 :: rest'.1, rest'.2)
termination_by 2 * exprSizeList expressions + 1
decreasing_by
  all_goals (simp only [exprSizeList]; have := exprSize_pos expression; omega)
end

/-- Bind the component binders of the heads of list `case`s that are only
    projected. -/
def prepareHeads (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then (prepareWalk [] unique (maxUidExpr unique + 1)).1 else unique

def destructurePairEntries (expression : Expr) : Expr :=
  let prepared := prepareHeads expression
  preLowerInlineExpr (if wellScoped prepared then pairListWalk [] [] prepared else prepared)

end Moist.MIR.Advanced
