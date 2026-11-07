import Moist.MIR.Optimize.Advanced.Traversal
import Moist.MIR.Optimize.Advanced.DelaySharing
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

def eliminateDeadFixRoot (expression : Expr) : Expr :=
  match expression with
  | .Fix binder (.Lam parameter body) =>
    let lambda := Expr.Lam parameter body
    if (freeVars lambda).contains binder then expression else lambda
  | _ => expression

def eliminateDeadFix (expression : Expr) : Expr :=
  rewriteBottomUp eliminateDeadFixRoot (exprSize expression) expression

end Moist.MIR.Advanced
