import Moist.MIR.Optimize.Purity
import Moist.MIR.AlphaRename
import Moist.MIR.LowerTotal

namespace Moist.MIR

open Moist.CEK (ExpectedArgs expectedArgs)

def builtinRemainder : Expr → Option ExpectedArgs
  | .Builtin builtin => some (expectedArgs builtin)
  | .Force expression => do
    let remaining ← builtinRemainder expression
    if remaining.head == .argQ then remaining.tail else none
  | .App function argument => do
    let remaining ← builtinRemainder function
    if remaining.head == .argV && isPure argument then remaining.tail else none
  | _ => none

def isCallableValue : Expr → Bool
  | .Lam _ _ => true
  | expression => (builtinRemainder expression).any (·.head == .argV)

mutual
  def freshenBinders (environment : List (VarId × VarId)) : Expr → FreshM Expr
    | .Var identifier => pure (.Var (substLookup environment identifier))
    | .Lam identifier body => do
      let fresh ← freshVar identifier.hint
      return .Lam fresh (← freshenBinders ((identifier, fresh) :: environment) body)
    | .Fix identifier body => do
      let fresh ← freshVar identifier.hint
      return .Fix fresh (← freshenBinders ((identifier, fresh) :: environment) body)
    | .App function argument =>
      return .App (← freshenBinders environment function) (← freshenBinders environment argument)
    | .Force expression => return .Force (← freshenBinders environment expression)
    | .Delay expression => return .Delay (← freshenBinders environment expression)
    | .Constr tag arguments => return .Constr tag (← freshenList environment arguments)
    | .Case scrutinee alternatives =>
      return .Case (← freshenBinders environment scrutinee) (← freshenList environment alternatives)
    | .Let bindings body => do
      let (bindings', environment') ← freshenBindings environment bindings
      return .Let bindings' (← freshenBinders environment' body)
    | expression => pure expression

  def freshenList (environment : List (VarId × VarId)) : List Expr → FreshM (List Expr)
    | [] => pure []
    | expression :: rest =>
      return (← freshenBinders environment expression) :: (← freshenList environment rest)

  def freshenBindings (environment : List (VarId × VarId)) :
      List (VarId × Expr × Bool) → FreshM (List (VarId × Expr × Bool) × List (VarId × VarId))
    | [] => pure ([], environment)
    | (identifier, expression, erased) :: rest => do
      let expression' ← freshenBinders environment expression
      let fresh ← freshVar identifier.hint
      let (rest', environment') ← freshenBindings ((identifier, fresh) :: environment) rest
      return ((fresh, expression', erased) :: rest', environment')
end

def uniqueOptimizationBinders (expression : Expr) : Expr :=
  if wellScoped expression then expression
  else runFresh (freshenBinders [] expression) (maxUidExpr expression + 1)

def reserveFreshFor (expression : Expr) : FreshM Unit :=
  modify fun state => { next := max state.next (maxUidExpr expression + 1) }

private def availableHead : Nat → List (Expr × VarId) → Expr → Expr
  | 0, _, expression => expression
  | fuel + 1, seen, expression =>
    match expression with
    | .Var identifier =>
      match seen.find? (fun entry => entry.2 == identifier) with
      | some (rhs, _) => availableHead fuel seen rhs
      | none => expression
    | .App function argument => .App (availableHead fuel seen function) argument
    | .Force inner => .Force (availableHead fuel seen inner)
    | _ => expression

private def builtinHead : Expr → Option Moist.Plutus.Term.BuiltinFun
  | .Builtin builtin => some builtin
  | .App function _ => builtinHead function
  | .Force expression => builtinHead expression
  | _ => none

def isRepeatable (seen : List (Expr × VarId)) (expression : Expr) : Bool :=
  go (exprSize expression + seen.length + 1) expression
where
  go : Nat → Expr → Bool
    | 0, _ => false
    | fuel + 1, expression =>
      match expression with
      | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Delay _ => true
      | .Fix _ (.Lam _ _) => true
      | .Constr _ fields => fields.all (go fuel)
      | .Let bindings body => bindings.all (fun binding => go fuel binding.2.1) && go fuel body
      | .Force inner =>
        match availableHead fuel seen inner with
        | .Delay body => go fuel body
        | head => isPure (.Force head)
      | .App function argument =>
        go fuel argument &&
          match availableHead fuel seen function with
          | .Lam _ body => isPure body
          | head => (builtinRemainder head).any (·.head == .argV) &&
            builtinHead head != some .Trace
      | _ => false

mutual
  def firstEvaluationUse (identifier : VarId) : Expr → Bool
    | .Var other => identifier == other
    | .App function argument =>
      firstEvaluationUse identifier function ||
        (isPure function && firstEvaluationUse identifier argument)
    | .Force expression => firstEvaluationUse identifier expression
    | .Case scrutinee _ => firstEvaluationUse identifier scrutinee
    | .Constr _ arguments => firstEvaluationUseList identifier arguments
    | .Let bindings body => firstEvaluationUseBindings identifier bindings body
    | _ => false
  termination_by expression => sizeOf expression

  def firstEvaluationUseList (identifier : VarId) : List Expr → Bool
    | [] => false
    | expression :: rest => firstEvaluationUse identifier expression ||
      (isPure expression && firstEvaluationUseList identifier rest)
  termination_by expressions => sizeOf expressions

  def firstEvaluationUseBindings (identifier : VarId) : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => firstEvaluationUse identifier body
    | (binder, expression, _) :: rest, body =>
      firstEvaluationUse identifier expression ||
        (binder != identifier && isPure expression && firstEvaluationUseBindings identifier rest body)
  termination_by bindings body => sizeOf bindings + sizeOf body
end

end Moist.MIR
