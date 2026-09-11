import Moist.MIR.Optimize.Advanced.Traversal
import Moist.Plutus.Encode

namespace Moist.MIR.Advanced

/-! Allocation transformations preserve effect order rather than exact budgets.
Packing requires total arguments. Hoisted builtin states must be closed and
unsaturated with a valid argument protocol. Constant sharing includes literal
types in equality. Final sharing/packing must not be followed by inlining or
case reduction, which can undo their intended representation.
-/

open Moist.Plutus.Term

def packApplicationsFuel (minimum : Nat) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression =>
    match expression with
    | .App _ _ =>
      let (function, arguments) := applicationSpine expression
      let function' := packApplicationsFuel minimum fuel function
      let arguments' := arguments.map (packApplicationsFuel minimum fuel)
      if arguments'.length >= minimum && arguments'.all isPure then
        .Case (.Constr 0 arguments') [function']
      else arguments'.foldl Expr.App function'
    | _ => mapChildren (packApplicationsFuel minimum fuel) expression

def packApplications (minimum : Nat := 3) (expression : Expr) : Expr :=
  packApplicationsFuel minimum (exprSize expression) expression

private def children : Expr → List Expr
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => [body]
  | .App function argument => [function, argument]
  | .Constr _ fields => fields
  | .Case scrutinee alternatives => scrutinee :: alternatives
  | .Let bindings body => bindings.map (·.2.1) ++ [body]
  | _ => []

private partial def onlyForced (binder : VarId) (expression : Expr) : Bool :=
  match expression with
  | .Force (.Var _) => true
  | .Var other => binder != other
  | _ => (children expression).all (onlyForced binder)

private partial def removeForces (binder : VarId) (expression : Expr) : Expr :=
  match expression with
  | .Force (.Var other) => if binder == other then .Var other else expression
  | _ => mapChildren (removeForces binder) expression

private partial def shareDelaysCore (expression : Expr) : Expr :=
  let result := mapChildren shareDelaysCore expression
  match result with
  | .Let bindings body =>
    bindings.foldr (fun (binder, rhs, erased) suffix =>
      match rhs with
      | .Delay delayed =>
        if isPure delayed && onlyForced binder suffix then
          .Let [(binder, delayed, erased)] (removeForces binder suffix)
        else .Let [(binder, rhs, erased)] suffix
      | _ => .Let [(binder, rhs, erased)] suffix) body
  | _ => result

def shareDelayedValues (expression : Expr) : Expr :=
  shareDelaysCore (uniqueOptimizationBinders expression)

def eliminateDeadFixRoot (expression : Expr) : Expr :=
  match expression with
  | .Fix binder (.Lam parameter body) =>
    let lambda := Expr.Lam parameter body
    if (freeVars lambda).contains binder then expression else lambda
  | _ => expression

def eliminateDeadFix (expression : Expr) : Expr :=
  rewriteBottomUp eliminateDeadFixRoot (exprSize expression) expression

private partial def collectMatches (predicate : Expr → Bool) (expression : Expr) : List Expr :=
  if predicate expression then [expression]
  else (children expression).flatMap (collectMatches predicate)

private partial def replaceMatches (replacements : List (Expr × VarId)) (expression : Expr) : Expr :=
  match replacements.find? (fun entry => alphaEq entry.1 expression) with
  | some (_, binder) => .Var binder
  | none => mapChildren (replaceMatches replacements) expression

private def shareClosed (predicate : Expr → Bool) (minimumUses : Nat) (expression : Expr) : Expr :=
  let occurrences := collectMatches predicate expression
  let unique := occurrences.foldl (fun result candidate =>
    if result.any (alphaEq candidate) then result else result ++ [candidate]) []
  let selected := unique.filter (fun candidate =>
    (occurrences.filter (alphaEq candidate)).length >= minimumUses)
  let start := maxUidExpr expression + 1
  let replacements := selected.zipIdx |>.map fun (candidate, index) =>
    (candidate, { uid := start + index, origin := .gen, hint := "shared" : VarId })
  if replacements.isEmpty then expression
  else .Let (replacements.map fun (rhs, binder) => (binder, rhs, false))
    (replaceMatches replacements expression)

def hoistBuiltinStates (minimumUses : Nat := 2) (expression : Expr) : Expr :=
  shareClosed (fun candidate =>
    !candidate.isAtom && (freeVars candidate).data.isEmpty &&
    (builtinRemainder candidate).isSome) minimumUses expression

def poolConstants (minimumBytes : Nat := 32) (expression : Expr) : Expr :=
  shareClosed (fun candidate =>
    match candidate with
    | .Lit literal =>
      (Moist.Plutus.Encode.encode_program
        (.Program (.Version 1 1 0) (.Constant literal))).toByteList.length >= minimumBytes
    | _ => false) 2 expression

end Moist.MIR.Advanced
