import Moist.MIR.Optimize.Advanced.Traversal
import Moist.MIR.Optimize.Advanced.Results

namespace Moist.MIR.Advanced

/-! Facts describe the shape of a value after successful evaluation, not the
totality of its producer. Only dominating bindings provide facts. Dead-binding
decisions use the prefix environment, preserving the validation establishing a
fact. Public scope-moving entry points establish unique lexical binders.
Checked conversion round trips retain their validating producers. Arithmetic
identities require runtime Integer evidence and retain effects of discarded
operands. Boolean branch facts are confined to the selected alternative.
-/

open Moist.Plutus.Term

private def knownBooleanLocal : Nat → List (VarId × Expr) → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, environment, expression =>
    match expression with
    | .Lit (.Bool _, _) => true
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any
        (fun entry => knownBooleanLocal fuel environment entry.2)
    | .App function _ =>
      let head := resolveHead fuel environment function
      (builtinProtocolAfterSuccess head).any fun (builtin, remaining) =>
        remaining.head == .argV && remaining.isFinal && booleanBuiltin builtin
    | .Case _ alternatives =>
      !alternatives.isEmpty && alternatives.all (knownBooleanLocal fuel environment)
    | _ => false

private def knownBoolean (fuel : Nat) (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  knownBooleanLocal fuel environment expression || knownBooleanResult fuel environment expression

private def constructorPair : Nat → List (VarId × Expr) → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, environment, expression =>
    match expression with
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any
        (fun entry => constructorPair fuel environment entry.2)
    | .App function _ =>
      match resolveHead fuel environment function with
      | .Builtin .UnConstrData => true
      | _ => false
    | _ => false

def knownList : Nat → List (VarId × Expr) → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, environment, expression =>
    match expression with
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any
        (fun entry => knownList fuel environment entry.2)
    | .Lit (.ConstList _, .TypeOperator (.TypeList _))
    | .Lit (.ConstDataList _, .TypeOperator (.TypeList _))
    | .Lit (.ConstPairDataList _, .TypeOperator (.TypeList _)) => true
    | .App function argument =>
      match resolveHead fuel environment function with
      | .Builtin .UnListData | .Force (.Builtin .TailList) => true
      | .Force (.Force (.Builtin .SndPair)) => constructorPair fuel environment argument
      | _ => false
    | _ => false

private partial def fuseListWalk (environment : List (VarId × Expr)) (expression : Expr) : Expr :=
  match expression with
  | .Let bindings body =>
    let (bindings, body) := flattenBindings bindings body
    match bindings with
    | (headBinder, headRhs, headErased) :: (tailBinder, tailRhs, tailErased) :: remaining =>
      match resolveHead 64 environment headRhs, resolveHead 64 environment tailRhs with
      | .App (.Force (.Builtin .HeadList)) (.Var listBinder),
        .App (.Force (.Builtin .TailList)) (.Var other) =>
        if listBinder == other && knownList 64 environment (.Var listBinder) then
          let suffix := fuseListWalk ((tailBinder, tailRhs) :: (headBinder, headRhs) :: environment)
            (.Let remaining body)
          .Case (.Var listBinder) [.Lam headBinder (.Lam tailBinder suffix), .Error]
        else
          .Let [(headBinder, fuseListWalk environment headRhs, headErased)]
            (fuseListWalk ((headBinder, headRhs) :: environment)
              (.Let ((tailBinder, tailRhs, tailErased) :: remaining) body))
      | _, _ =>
        .Let [(headBinder, fuseListWalk environment headRhs, headErased)]
          (fuseListWalk ((headBinder, headRhs) :: environment)
            (.Let ((tailBinder, tailRhs, tailErased) :: remaining) body))
    | [(binder, rhs, erased)] =>
      .Let [(binder, fuseListWalk environment rhs, erased)]
        (fuseListWalk ((binder, rhs) :: environment) body)
    | [] => fuseListWalk environment body
  | _ => mapChildren (fuseListWalk environment) expression

def fuseListDestructors (expression : Expr) : Expr :=
  fuseListWalk [] (uniqueOptimizationBinders expression)

private partial def replaceListProjections (listBinder headBinder tailBinder : VarId)
    (expression : Expr) : Expr :=
  match expression with
  | .App (.Force (.Builtin .HeadList)) (.Var binder) =>
    if binder == listBinder then .Var headBinder else expression
  | .App (.Force (.Builtin .TailList)) (.Var binder) =>
    if binder == listBinder then .Var tailBinder else expression
  | _ => mapChildren (replaceListProjections listBinder headBinder tailBinder) expression

private partial def listChoiceWalk (environment : List (VarId × Expr)) (expression : Expr) : Expr :=
  match expression with
  | .Let [] body => listChoiceWalk environment body
  | .Let ((binder, rhs, erased) :: rest) body =>
    let rhs' := listChoiceWalk environment rhs
    .Let [(binder, rhs', erased)] (listChoiceWalk ((binder, rhs') :: environment) (.Let rest body))
  | _ =>
    let result := mapChildren (listChoiceWalk environment) expression
    match result with
    | .Case (.App function (.Var listBinder)) [nonempty, empty] =>
      if resolveHead 64 environment function == .Force (.Builtin .NullList) &&
          knownList 64 environment (.Var listBinder) then
        let headBinder : VarId := { uid := maxUidExpr result + 1, origin := .gen, hint := "head" }
        let tailBinder : VarId := { uid := maxUidExpr result + 2, origin := .gen, hint := "tail" }
        .Case (.Var listBinder)
          [.Lam headBinder (.Lam tailBinder (replaceListProjections listBinder headBinder tailBinder nonempty)), empty]
      else result
    | _ => result

def fuseListChoices (expression : Expr) : Expr :=
  uniqueOptimizationBinders (listChoiceWalk [] (uniqueOptimizationBinders expression))

private def knownInteger : Nat → List (VarId × Expr) → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, environment, expression =>
    match expression with
    | .Lit (.Integer _, _) => true
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any
        (fun entry => knownInteger fuel environment entry.2)
    | .App function argument =>
      let head := resolveHead fuel environment function
      match head with
      | .Force (.Force (.Builtin .FstPair)) => constructorPair fuel environment argument
      | _ =>
        (builtinProtocolAfterSuccess head).any fun (builtin, remaining) =>
          remaining.head == .argV && remaining.isFinal &&
          match builtin with
          | .AddInteger | .SubtractInteger | .MultiplyInteger | .DivideInteger
          | .QuotientInteger | .RemainderInteger | .ModInteger | .UnIData
          | .LengthOfByteString | .IndexByteString => true
          | _ => false
    | _ => false

private partial def totalWithFacts (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  isPure expression ||
    match expression with
    | .App function argument =>
      match resolveHead 64 environment function with
      | .App (.Builtin builtin) first =>
        let integerOperation := match builtin with
          | .AddInteger | .SubtractInteger | .MultiplyInteger | .EqualsInteger
          | .LessThanInteger | .LessThanEqualsInteger => true
          | _ => false
        integerOperation && knownInteger 64 environment first && knownInteger 64 environment argument &&
          totalWithFacts environment first && totalWithFacts environment argument
      | .Force (.Force (.Builtin builtin)) =>
        (builtin == .FstPair || builtin == .SndPair) && constructorPair 64 environment argument &&
          totalWithFacts environment argument
      | _ => false
    | _ => false

private def delayBody : Expr → Option Expr
  | .Delay body => some body
  | _ => none

private def checkedRoundTrip (environment : List (VarId × Expr)) : Expr → Option Expr
  | .App (.Builtin outer) (.Var checked) =>
    match resolveHead 64 environment (.Var checked) with
    | .App (.Builtin inner) (.Var original) =>
      let inverse := match outer, inner with
        | .IData, .UnIData | .UnIData, .IData
        | .BData, .UnBData | .UnBData, .BData
        | .ListData, .UnListData | .MapData, .UnMapData => true
        | _, _ => false
      if inverse then some (.Var original) else none
    | _ => none
  | _ => none

private def integerConstant (value : Int) : Expr :=
  .Lit (.Integer value, .AtomicType .TypeInteger)

private def isIntegerLiteral (expression : Expr) (value : Int) : Bool :=
  match expression with
  | .Lit (.Integer actual, .AtomicType .TypeInteger) => actual == value
  | _ => false

private def retainEvaluation (environment : List (VarId × Expr))
    (expression result : Expr) : Expr :=
  if totalWithFacts environment expression then result
  else
    let unused : VarId := {
      uid := max (maxUidExpr expression) (maxUidExpr result) + 1
      origin := .gen
      hint := "evaluated" }
    .Let [(unused, expression, false)] result

private def integerIdentity (environment : List (VarId × Expr)) : Expr → Option Expr
  | .App (.App (.Builtin builtin) first) second => do
    if !knownInteger 64 environment first || !knownInteger 64 environment second then none
    else
      match builtin with
      | .AddInteger =>
        if isIntegerLiteral first 0 then some second
        else if isIntegerLiteral second 0 then some first else none
      | .SubtractInteger =>
        if isIntegerLiteral second 0 then some first
        else match first, second with
          | .Var left, .Var right => if left == right then some (integerConstant 0) else none
          | _, _ => none
      | .MultiplyInteger =>
        if isIntegerLiteral first 1 then some second
        else if isIntegerLiteral second 1 then some first
        else if isIntegerLiteral first 0 then
          some (retainEvaluation environment second (integerConstant 0))
        else if isIntegerLiteral second 0 then
          some (retainEvaluation environment first (integerConstant 0))
        else none
      | .DivideInteger | .QuotientInteger =>
        if isIntegerLiteral second 1 then some first else none
      | .RemainderInteger | .ModInteger =>
        if isIntegerLiteral second 1 then
          some (retainEvaluation environment first (integerConstant 0))
        else none
      | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger =>
        match first, second with
        | .Var left, .Var right =>
          if left == right then
            some (.Lit (.Bool (builtin != .LessThanInteger), .AtomicType .TypeBool))
          else none
        | _, _ => none
      | _ => none
  | _ => none

private partial def simplifyWithFacts (useShapes : Bool) (expression : Expr) : Expr :=
  uniqueOptimizationBinders (go [] (uniqueOptimizationBinders expression))
where
  go (environment : List (VarId × Expr)) (expression : Expr) : Expr :=
    match expression with
    | .Case (.Var binder) [first, second] =>
      if useShapes && knownBoolean 64 environment (.Var binder) then
        match resolveHead 64 environment (.Var binder) with
        | .Lit (.Bool value, .AtomicType .TypeBool) =>
          go environment (if value then second else first)
        | _ =>
          let first' := go ((binder, .Lit (.Bool false, .AtomicType .TypeBool)) :: environment) first
          let second' := go ((binder, .Lit (.Bool true, .AtomicType .TypeBool)) :: environment) second
          if alphaEq first' second' then first' else .Case (.Var binder) [first', second']
      else mapChildren (go environment) expression
    | .Let bindings body =>
      let (bindings', environment') := bindings.foldl (init := ([], environment))
        fun (processed, available) (binder, rhs, erased) =>
          let rhs' := go available rhs
          let total := useShapes && totalWithFacts available rhs'
          (processed ++ [((binder, rhs', erased), total)], (binder, rhs') :: available)
      let body' := go environment' body
      let retained := bindings'.foldr (fun (binding, total) suffix =>
        if total && !(freeVars (.Let suffix body')).contains binding.1 then suffix
        else binding :: suffix) []
      if retained.isEmpty then body' else .Let retained body'
    | _ =>
      let result := mapChildren (go environment) expression
      let result := if useShapes then
        (checkedRoundTrip environment result).getD result else result
      let result := if useShapes then
        (integerIdentity environment result).getD result else result
      match result with
      | .App (.App (.App (.Force (.Builtin .IfThenElse)) condition) whenTrue) whenFalse =>
        if knownBoolean 64 environment condition && isPure whenTrue && isPure whenFalse then
          .Case condition [whenFalse, whenTrue]
        else result
      | .Force (.Case scrutinee alternatives) =>
        if knownBoolean 64 environment scrutinee then
          match alternatives.mapM delayBody with
          | some bodies => .Case scrutinee bodies
          | none => result
        else result
      | .Case scrutinee [first, second] =>
        if useShapes && alphaEq first second && knownBoolean 64 environment scrutinee then
          if totalWithFacts environment scrutinee then first
          else
            let unused : VarId := { uid := maxUidExpr result + 1, origin := .gen, hint := "checked" }
            .Let [(unused, scrutinee, false)] first
        else result
      | _ => result

def simplifyChoices (expression : Expr) : Expr := simplifyWithFacts false expression

def shapeDCE (expression : Expr) : Expr := simplifyWithFacts true expression

end Moist.MIR.Advanced
