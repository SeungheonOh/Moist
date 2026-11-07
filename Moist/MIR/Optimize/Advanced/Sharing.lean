import Moist.MIR.Optimize.Advanced.Allocations
import Moist.Plutus.Encode

namespace Moist.MIR.Advanced

/-! Sharing of closed subterms through top-level bindings.

`shareClosed predicate minimumUses` binds every distinct (up to `alphaEq`)
subterm accepted by `predicate` that occurs at least `minimumUses` times in a
fresh top-level variable and replaces its occurrences by that variable. The
search stops at the first accepted subterm on each path. Hoisting evaluates
each shared term once, before the body, so accepted terms must be closed and
always return a value: unsaturated builtin states (`hoistBuiltinStates`) and
literals (`poolConstants`).
-/

open Moist.Plutus.Term

mutual
  def collectMatches (predicate : Expr → Bool) (expression : Expr) : List Expr :=
    if predicate expression then [expression]
    else
      match expression with
      | .Lam _ body => collectMatches predicate body
      | .Fix _ body => collectMatches predicate body
      | .Force inner => collectMatches predicate inner
      | .Delay inner => collectMatches predicate inner
      | .App function argument =>
        collectMatches predicate function ++ collectMatches predicate argument
      | .Constr _ fields => collectMatchesList predicate fields
      | .Case scrutinee alternatives =>
        collectMatches predicate scrutinee ++ collectMatchesList predicate alternatives
      | .Let bindings body =>
        collectMatchesBinds predicate bindings ++ collectMatches predicate body
      | _ => []
  termination_by sizeOf expression

  def collectMatchesList (predicate : Expr → Bool) : List Expr → List Expr
    | [] => []
    | expression :: rest =>
      collectMatches predicate expression ++ collectMatchesList predicate rest
  termination_by expressions => sizeOf expressions

  def collectMatchesBinds (predicate : Expr → Bool) : List (VarId × Expr × Bool) → List Expr
    | [] => []
    | (_, rhs, _) :: rest => collectMatches predicate rhs ++ collectMatchesBinds predicate rest
  termination_by bindings => sizeOf bindings
end

mutual
  def replaceMatches (replacements : List (Expr × VarId)) (expression : Expr) : Expr :=
    match replacements.find? (fun entry => alphaEq entry.1 expression) with
    | some (_, binder) => .Var binder
    | none =>
      match expression with
      | .Lam binder body => .Lam binder (replaceMatches replacements body)
      | .Fix binder body => .Fix binder (replaceMatches replacements body)
      | .App function argument =>
        .App (replaceMatches replacements function) (replaceMatches replacements argument)
      | .Force inner => .Force (replaceMatches replacements inner)
      | .Delay inner => .Delay (replaceMatches replacements inner)
      | .Constr tag fields => .Constr tag (replaceMatchesList replacements fields)
      | .Case scrutinee alternatives =>
        .Case (replaceMatches replacements scrutinee) (replaceMatchesList replacements alternatives)
      | .Let bindings body =>
        .Let (replaceMatchesBinds replacements bindings) (replaceMatches replacements body)
      | other => other
  termination_by sizeOf expression

  def replaceMatchesList (replacements : List (Expr × VarId)) : List Expr → List Expr
    | [] => []
    | expression :: rest =>
      replaceMatches replacements expression :: replaceMatchesList replacements rest
  termination_by expressions => sizeOf expressions

  def replaceMatchesBinds (replacements : List (Expr × VarId)) :
      List (VarId × Expr × Bool) → List (VarId × Expr × Bool)
    | [] => []
    | (binder, rhs, erased) :: rest =>
      (binder, replaceMatches replacements rhs, erased) :: replaceMatchesBinds replacements rest
  termination_by bindings => sizeOf bindings
end

def shareClosed (predicate : Expr → Bool) (minimumUses : Nat) (expression : Expr) : Expr :=
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
