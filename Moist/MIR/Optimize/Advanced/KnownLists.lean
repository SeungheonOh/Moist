import Moist.MIR.Optimize.Advanced.CheckedBranches

namespace Moist.MIR.Advanced

/-! A `nullList` discriminator of a value known to be a builtin list selects
the same alternative as a list `case` on that value, so
`case (nullList l) [case l [C, …], E]` becomes `case l [C, E]`. The rewrite
is only sound for lists: a `case` on an integer, a Boolean or a constructor
value may select an alternative where `nullList` fails.

A name is known to hold a list when its binding produces one (`knownList`),
when it is the tail bound by a `case` on a known list, or when it is a
parameter of a recursive function every call of which passes a known list
at that position. The last fact is a greatest fixed point: positions whose
external argument is a known list are assumed to hold lists while the calls
inside the body are checked, and positions where some recursive call passes
anything else are dropped until the assumption is stable. The recursive
binder must not escape: every occurrence is the head of a call supplying at
least all parameters of the function, and the calls pass tail binders or
parameters known to be lists at the checked positions. Both walks run on well-scoped programs with unique
binders, so recorded names are never shadowed.
-/

/-- `expression` evaluates, when it halts, to a builtin list: by its producer
    or because it names a binder recorded in `lists`. -/
def knownListValue : Nat → List (VarId × Expr) → List VarId → Expr → Bool
  | 0, _, _, _ => false
  | fuel + 1, environment, lists, expression =>
    match expression with
    | .Var binder =>
      lists.contains binder ||
        (environment.find? (fun entry => entry.1 == binder)).any
          (fun entry => knownListValue fuel environment lists entry.2)
    | .Lit (.ConstList _, .TypeOperator (.TypeList _))
    | .Lit (.ConstDataList _, .TypeOperator (.TypeList _))
    | .Lit (.ConstPairDataList _, .TypeOperator (.TypeList _)) => true
    | .App function argument =>
      match resolveHead fuel environment function with
      | .Builtin .UnListData | .Builtin .UnMapData | .Force (.Builtin .TailList) => true
      | .Force (.Force (.Builtin .SndPair)) => constructorPair fuel environment argument
      | _ => false
    | _ => false

def listKnown (environment : List (VarId × Expr)) (lists : List VarId) (expression : Expr) : Bool :=
  knownListValue 64 environment lists expression

/-- An argument at a checked position names a known list. -/
def listArgument (lists : List VarId) (positions : List Nat) (position : Nat) (argument : Expr) : Bool :=
  !positions.contains position ||
    match argument with
    | .Var binder => lists.contains binder
    | _ => false

theorem expr_sizeOf_pos (expression : Expr) : 0 < sizeOf expression := by
  cases expression <;> simp <;> omega

set_option linter.unusedVariables false in
mutual
  /-- Every occurrence of `recursive` heads a call with `arity` arguments whose
      checked positions name known lists. -/
  def listCallsOK (recursive : VarId) (arity : Nat) (positions : List Nat) (lists : List VarId)
      (expression : Expr) : Bool :=
    match expression with
    | .Var binder => !(binder == recursive)
    | .Lit _ | .Builtin _ | .Error => true
    | .Lam _ body => listCallsOK recursive arity positions lists body
    | .Fix _ body => listCallsOK recursive arity positions lists body
    | .App function argument =>
      listCallSpine recursive arity positions lists arity function argument ||
        (listCallsOK recursive arity positions lists function &&
          listCallsOK recursive arity positions lists argument)
    | .Force body | .Delay body => listCallsOK recursive arity positions lists body
    | .Constr _ fields => listCallsOKList recursive arity positions lists fields
    | .Case scrutinee alternatives =>
      match hs : scrutinee, ha : alternatives with
      | .Var listBinder, .Lam headBinder (.Lam tailBinder body) :: rest =>
        if lists.contains listBinder then
          listCallsOK recursive arity positions (tailBinder :: lists) body &&
            listCallsOKList recursive arity positions lists rest
        else
          listCallsOK recursive arity positions lists (.Var listBinder) &&
            listCallsOKList recursive arity positions lists (.Lam headBinder (.Lam tailBinder body) :: rest)
      | _, _ =>
        listCallsOK recursive arity positions lists scrutinee &&
          listCallsOKList recursive arity positions lists alternatives
    | .Let bindings body =>
      listCallsOKBinds recursive arity positions lists bindings &&
        listCallsOK recursive arity positions lists body
  termination_by sizeOf expression
  decreasing_by all_goals (try subst_vars) <;> simp_wf <;> omega

  /-- `function argument` is `recursive` applied to its first `remaining`
      arguments, `argument` being the last of them. -/
  def listCallSpine (recursive : VarId) (arity : Nat) (positions : List Nat) (lists : List VarId)
      (remaining : Nat) (function argument : Expr) : Bool :=
    match remaining with
    | 0 => false
    | remaining + 1 =>
      listArgument lists positions remaining argument &&
        listCallsOK recursive arity positions lists argument &&
        listCallHead recursive arity positions lists remaining function
  termination_by sizeOf function + sizeOf argument
  decreasing_by all_goals simp_wf <;> first | omega | (have := expr_sizeOf_pos function; have := expr_sizeOf_pos argument; omega)

  /-- `expression` is `recursive` applied to its first `remaining` arguments. -/
  def listCallHead (recursive : VarId) (arity : Nat) (positions : List Nat) (lists : List VarId)
      (remaining : Nat) (expression : Expr) : Bool :=
    match remaining, expression with
    | 0, .Var binder => binder == recursive
    | remaining + 1, .App function argument =>
      listCallSpine recursive arity positions lists (remaining + 1) function argument
    | _, _ => false
  termination_by sizeOf expression

  def listCallsOKList (recursive : VarId) (arity : Nat) (positions : List Nat) (lists : List VarId)
      (expressions : List Expr) : Bool :=
    match expressions with
    | [] => true
    | expression :: rest =>
      listCallsOK recursive arity positions lists expression &&
        listCallsOKList recursive arity positions lists rest
  termination_by sizeOf expressions

  def listCallsOKBinds (recursive : VarId) (arity : Nat) (positions : List Nat) (lists : List VarId)
      (bindings : List (VarId × Expr × Bool)) : Bool :=
    match bindings with
    | [] => true
    | (_, rhs, _) :: rest =>
      listCallsOK recursive arity positions lists rhs &&
        listCallsOKBinds recursive arity positions lists rest
  termination_by sizeOf bindings
end

/-- Lambda parameters of a recursive body. -/
def lambdaChain : Expr → List VarId × Expr
  | .Lam binder body =>
    let (parameters, inner) := lambdaChain body
    (binder :: parameters, inner)
  | expression => ([], expression)

def lambdaWrap : List VarId → Expr → Expr
  | [], body => body
  | binder :: rest, body => .Lam binder (lambdaWrap rest body)

def listedParameters (parameters : List VarId) (positions : List Nat) : List VarId :=
  positions.filterMap fun position => parameters[position]?

/-- Positions of a recursive function's parameters holding lists in every call. -/
def listPositions (environment : List (VarId × Expr)) (lists : List VarId) (recursive : VarId)
    (parameters : List VarId) (arguments : List Expr) (body : Expr) : List Nat :=
  if arguments.length < parameters.length then [] else
    let initial := (List.range parameters.length).filter fun position =>
      match arguments[position]? with
      | some argument => listKnown environment lists argument
      | none => false
    stable (initial.length + 1) initial
where
  stable : Nat → List Nat → List Nat
    | 0, _ => []
    | fuel + 1, positions =>
      if positions.isEmpty then [] else
        let assumed := listedParameters parameters positions ++ lists
        let kept := positions.filter fun position =>
          listCallsOK recursive parameters.length [position] assumed body
        if kept.length == positions.length then
          if listCallsOK recursive parameters.length positions assumed body then positions else []
        else stable fuel kept

/-- Names bound by `environment` to known lists. -/
def environmentLists (environment : List (VarId × Expr)) (lists : List VarId) : List VarId :=
  environment.filterMap fun entry =>
    if listKnown environment lists (.Var entry.1) then some entry.1 else none

/-- Positions of a let-bound recursive function's parameters holding lists in
    every call: the calls in the scope of the binding and the recursive calls. -/
def letFixPositions (environment : List (VarId × Expr)) (lists : List VarId) (binder recursive : VarId)
    (parameters : List VarId) (inner scope : Expr) : List Nat :=
  stable (parameters.length + 1) (List.range parameters.length)
where
  stable : Nat → List Nat → List Nat
    | 0, _ => []
    | fuel + 1, positions =>
      if positions.isEmpty then [] else
        let assumed := listedParameters parameters positions ++ lists
        let outer := environmentLists environment lists ++ lists
        let kept := positions.filter fun position =>
          listCallsOK recursive parameters.length [position] assumed inner &&
            listCallsOK binder parameters.length [position] outer scope
        if kept.length == positions.length then
          if listCallsOK recursive parameters.length positions assumed inner &&
              listCallsOK binder parameters.length positions outer scope then positions else []
        else stable fuel kept

/-- A recursive function applied to at least one argument. -/
def fixApplication : Expr → List Expr → Option (VarId × VarId × Expr × List Expr)
  | .App function argument, arguments => fixApplication function (argument :: arguments)
  | .Fix recursive (.Lam parameter body), arguments =>
    if arguments.isEmpty then none else some (recursive, parameter, body, arguments)
  | _, _ => none

def applyAll : Expr → List Expr → Expr
  | function, [] => function
  | function, argument :: rest => applyAll (.App function argument) rest

theorem exprSizeList_mem_lt {child : Expr} {children : List Expr} (member : child ∈ children) :
    exprSize child < exprSizeList children + 1 := exprSize_lt_of_mem member

theorem fixApplication_size : ∀ (expression : Expr) (arguments : List Expr)
    {recursive parameter : VarId} {body : Expr} {result : List Expr},
    fixApplication expression arguments = some (recursive, parameter, body, result) →
      exprSize body + 2 ≤ exprSize expression ∧
        exprSizeList result ≤ exprSize expression + exprSizeList arguments ∧
        (∀ argument ∈ result, exprSize argument < exprSize expression + exprSizeList arguments)
  | .App function argument, arguments, recursive, parameter, body, result, h => by
    simp only [fixApplication] at h
    have ih := fixApplication_size function (argument :: arguments) h
    simp only [exprSize, exprSizeList] at ih ⊢
    refine ⟨by omega, by omega, fun a ha => ?_⟩
    have := ih.2.2 a ha
    omega
  | .Fix recursive' (.Lam parameter' body'), arguments, recursive, parameter, body, result, h => by
    simp only [fixApplication] at h
    split at h
    · cases h
    · cases h
      simp only [exprSize]
      refine ⟨by omega, by omega, fun a ha => ?_⟩
      have := exprSize_lt_of_mem ha
      have := exprSize_pos body'
      omega
  | .Var _, _, _, _, _, _, h | .Lit _, _, _, _, _, _, h | .Builtin _, _, _, _, _, _, h
  | .Error, _, _, _, _, _, h | .Lam _ _, _, _, _, _, _, h | .Force _, _, _, _, _, _, h
  | .Delay _, _, _, _, _, _, h | .Constr _ _, _, _, _, _, _, h | .Case _ _, _, _, _, _, _, h
  | .Let _ _, _, _, _, _, _, h => by simp [fixApplication] at h
  | .Fix _ (.Var _), _, _, _, _, _, h | .Fix _ (.Lit _), _, _, _, _, _, h
  | .Fix _ (.Builtin _), _, _, _, _, _, h | .Fix _ .Error, _, _, _, _, _, h
  | .Fix _ (.Fix _ _), _, _, _, _, _, h | .Fix _ (.App _ _), _, _, _, _, _, h
  | .Fix _ (.Force _), _, _, _, _, _, h | .Fix _ (.Delay _), _, _, _, _, _, h
  | .Fix _ (.Constr _ _), _, _, _, _, _, h | .Fix _ (.Case _ _), _, _, _, _, _, h
  | .Fix _ (.Let _ _), _, _, _, _, _, h => by simp [fixApplication] at h

theorem exprSize_lambdaChain : ∀ (expression : Expr), exprSize (lambdaChain expression).2 ≤ exprSize expression
  | .Lam binder body => by
    have := exprSize_lambdaChain body
    simp only [lambdaChain, exprSize]; omega
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _ | .Force _ | .Delay _
  | .Constr _ _ | .Case _ _ | .Let _ _ => by simp [lambdaChain]

theorem fixApplication_inner_size {expression : Expr} {recursive parameter : VarId} {body : Expr}
    {result : List Expr} (h : fixApplication expression [] = some (recursive, parameter, body, result)) :
    exprSize (lambdaChain body).2 < exprSize expression := by
  have := fixApplication_size expression [] h
  have := exprSize_lambdaChain body
  simp only [exprSizeList] at *
  omega

set_option linter.unusedVariables false in
def knownListWalk (environment : List (VarId × Expr)) (lists : List VarId) (expression : Expr) : Expr :=
  match expression with
  | .App function argument =>
    match hfix : fixApplication (.App function argument) [] with
    | some (recursive, parameter, body, arguments) =>
      let parameters := parameter :: (lambdaChain body).1
      let inner := (lambdaChain body).2
      let positions := listPositions environment lists recursive parameters arguments inner
      let lists' := listedParameters parameters positions ++ lists
      applyAll (.Fix recursive (lambdaWrap parameters (knownListWalk environment lists' inner)))
        (arguments.attach.map fun ⟨argument, _⟩ => knownListWalk environment lists argument)
    | none =>
      .App (knownListWalk environment lists function) (knownListWalk environment lists argument)
  | .Case scrutinee alternatives =>
    match hs : scrutinee, halts : alternatives with
    | .App selector (.Var listBinder), [nonempty, empty] =>
      if resolveHead 64 environment selector == .Force (.Builtin .NullList) &&
          listKnown environment lists (.Var listBinder) then
        match hn : nonempty with
        | .Case (.Var inner) (.Lam headBinder (.Lam tailBinder body) :: rest) =>
          if inner == listBinder && rest.length ≤ 1 then
            .Case (.Var listBinder)
              [.Lam headBinder (.Lam tailBinder (knownListWalk environment (tailBinder :: lists) body)),
               knownListWalk environment lists empty]
          else
            .Case (knownListWalk environment lists scrutinee)
              [knownListWalk environment lists nonempty, knownListWalk environment lists empty]
        | _ =>
          .Case (knownListWalk environment lists scrutinee)
            [knownListWalk environment lists nonempty, knownListWalk environment lists empty]
      else
        .Case (knownListWalk environment lists scrutinee)
          [knownListWalk environment lists nonempty, knownListWalk environment lists empty]
    | .Var listBinder, .Lam headBinder (.Lam tailBinder body) :: rest =>
      if listKnown environment lists (.Var listBinder) then
        .Case (.Var listBinder)
          (.Lam headBinder (.Lam tailBinder (knownListWalk environment (tailBinder :: lists) body)) ::
            rest.attach.map fun ⟨alternative, _⟩ => knownListWalk environment lists alternative)
      else
        .Case (knownListWalk environment lists scrutinee)
          (alternatives.attach.map fun ⟨alternative, _⟩ => knownListWalk environment lists alternative)
    | _, _ =>
      .Case (knownListWalk environment lists scrutinee)
        (alternatives.attach.map fun ⟨alternative, _⟩ => knownListWalk environment lists alternative)
  | .Let [] body => knownListWalk environment lists body
  | .Let ((binder, rhs, erased) :: rest) body =>
    match hr : rhs with
    | .Fix recursive (.Lam parameter fixBody) =>
      let parameters := parameter :: (lambdaChain fixBody).1
      let inner := (lambdaChain fixBody).2
      let positions := letFixPositions environment lists binder recursive parameters inner (.Let rest body)
      if positions.isEmpty then
        let rhs' := knownListWalk environment lists (.Fix recursive (.Lam parameter fixBody))
        .Let [(binder, rhs', erased)] (knownListWalk ((binder, rhs') :: environment) lists (.Let rest body))
      else
        let rhs' := Expr.Fix recursive (lambdaWrap parameters
          (knownListWalk environment (listedParameters parameters positions ++ lists) inner))
        .Let [(binder, rhs', erased)] (knownListWalk ((binder, rhs') :: environment) lists (.Let rest body))
    | other =>
      let rhs' := knownListWalk environment lists other
      .Let [(binder, rhs', erased)] (knownListWalk ((binder, rhs') :: environment) lists (.Let rest body))
  | .Lam binder body => .Lam binder (knownListWalk environment lists body)
  | .Fix binder body => .Fix binder (knownListWalk environment lists body)
  | .Force body => .Force (knownListWalk environment lists body)
  | .Delay body => .Delay (knownListWalk environment lists body)
  | .Constr tag fields =>
    .Constr tag (fields.attach.map fun ⟨field, _⟩ => knownListWalk environment lists field)
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

def fuseKnownListCases (expression : Expr) : Expr :=
  let unique := uniqueOptimizationBinders expression
  if wellScoped unique then knownListWalk [] [] unique else unique

end Moist.MIR.Advanced
