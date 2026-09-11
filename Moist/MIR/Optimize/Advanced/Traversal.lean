import Moist.MIR.Optimize.Safety

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

def applicationSpine (expression : Expr) : Expr × List Expr :=
  go expression []
where
  go : Expr → List Expr → Expr × List Expr
    | .App function argument, arguments => go function (argument :: arguments)
    | function, arguments => (function, arguments)

partial def flattenBindings (bindings : List (VarId × Expr × Bool))
    (body : Expr) : List (VarId × Expr × Bool) × Expr :=
  match body with
  | .Let more suffix => flattenBindings (bindings ++ more) suffix
  | _ => (bindings, body)

def mapChildren (transform : Expr → Expr) : Expr → Expr
  | .Lam binder body => .Lam binder (transform body)
  | .Fix binder body => .Fix binder (transform body)
  | .App function argument => .App (transform function) (transform argument)
  | .Force expression => .Force (transform expression)
  | .Delay expression => .Delay (transform expression)
  | .Constr tag fields => .Constr tag (fields.map transform)
  | .Case scrutinee alternatives => .Case (transform scrutinee) (alternatives.map transform)
  | .Let bindings body =>
    .Let (bindings.map fun (binder, rhs, erased) => (binder, transform rhs, erased)) (transform body)
  | expression => expression

def rewriteBottomUp (rewrite : Expr → Expr) : Nat → Expr → Expr
  | 0, expression => expression
  | fuel + 1, expression => rewrite (mapChildren (rewriteBottomUp rewrite fuel) expression)

end Moist.MIR.Advanced
