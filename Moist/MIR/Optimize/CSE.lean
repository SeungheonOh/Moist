import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Common Sub-Expression Elimination (CSE)

Eliminates redundant computations by detecting structurally identical
let-binding RHS expressions and reusing the first binding's result for
all subsequent duplicates.

## Why This Is Always Safe in Plutus

Plutus has no mutable state. If `App f x` succeeds for binding `a`,
computing `App f x` again for binding `b` in the same scope would
produce the identical result. If `App f x` errors, sequential
evaluation guarantees we never reach `b`, so replacing `b` with `a`
does not change the error semantics.

## Algorithm

1. Walk `Let binds body` left-to-right maintaining a map of previously
   seen RHS expressions to their binding variables: `List (Expr x VarId)`.
2. For each binding `(v, rhs)`:
   - Search the map for an entry where `exprStructEq rhs seenRhs`.
   - If found as `w`: rename all free occurrences of `v` to `w` in all
     subsequent bindings and in the body (using `rename`). Drop this
     binding entirely.
   - If not found: add `(rhs, v)` to the map and keep the binding.
3. Recurse into sub-expressions (Lam body, Fix body, Let inner, Case
   alternatives, etc.).

## Structural Equality vs Alpha-Equivalence

`exprStructEq` compares two expression trees for **exact** structural
equality: same VarIds, same literal values, same constructors. This is
deliberately NOT alpha-equivalence because CSE operates on bindings
in the same scope where variables have fixed names. Alpha-equivalence
would be unsound here (two lambdas binding different variables in the
same scope are semantically different if those variables are referenced
from the outside).

## Examples

```
-- Duplicate application eliminated
let a = App (Var f) (Var x) in
let b = App (Var f) (Var x) in
App (Var a) (Var b)
  ==>
let a = App (Var f) (Var x) in
App (Var a) (Var a)

-- Different applications kept
let a = App (Var f) (Var x) in
let b = App (Var f) (Var y) in
App (Var a) (Var b)
  ==> (unchanged, x /= y)

-- Nested CSE: inner let also gets optimized
let outer = Lit 1 in
Lam z (
  let a = App (Var f) (Var z) in
  let b = App (Var f) (Var z) in
  App (Var a) (Var b)
)
  ==>
let outer = Lit 1 in
Lam z (
  let a = App (Var f) (Var z) in
  App (Var a) (Var a)
)

-- Chain of duplicates: all collapse to the first
let a = Force (Var x) in
let b = Force (Var x) in
let c = Force (Var x) in
Constr 0 [Var a, Var b, Var c]
  ==>
let a = Force (Var x) in
Constr 0 [Var a, Var a, Var a]
```
-/

/-! ## Structural Equality

Exact structural comparison of two expression trees. Two expressions
are structurally equal iff they have identical constructors, identical
VarIds (not just alpha-equivalent), identical literals, and recursively
equal sub-expressions.

```
exprStructEq (Var x) (Var x)                     = true
exprStructEq (Var x) (Var y)                      = false  (different VarId)
exprStructEq (Lam x (Var x)) (Lam y (Var y))     = false  (different binder names)
exprStructEq (App (Var f) (Var x)) (App (Var f) (Var x))  = true
exprStructEq (Lit (Integer 1, t)) (Lit (Integer 1, t))    = true
```
-/

mutual
  partial def exprStructEq : Expr → Expr → Bool
    | .Var a, .Var b => a == b
    | .Lit a, .Lit b => litEq a b
    | .Builtin a, .Builtin b => a == b
    | .Error, .Error => true
    | .Lam x1 body1, .Lam x2 body2 =>
      x1 == x2 && exprStructEq body1 body2
    | .Fix f1 body1, .Fix f2 body2 =>
      f1 == f2 && exprStructEq body1 body2
    | .App f1 x1, .App f2 x2 =>
      exprStructEq f1 f2 && exprStructEq x1 x2
    | .Force e1, .Force e2 => exprStructEq e1 e2
    | .Delay e1, .Delay e2 => exprStructEq e1 e2
    | .Constr t1 args1, .Constr t2 args2 =>
      t1 == t2 && exprStructEqList args1 args2
    | .Case s1 alts1, .Case s2 alts2 =>
      exprStructEq s1 s2 && exprStructEqList alts1 alts2
    | .Let binds1 body1, .Let binds2 body2 =>
      exprStructEqBinds binds1 binds2 && exprStructEq body1 body2
    | _, _ => false

  partial def exprStructEqList : List Expr → List Expr → Bool
    | [], [] => true
    | a :: as_, b :: bs => exprStructEq a b && exprStructEqList as_ bs
    | _, _ => false

  partial def exprStructEqBinds : List (VarId × Expr) → List (VarId × Expr) → Bool
    | [], [] => true
    | (x, rhs1) :: rest1, (y, rhs2) :: rest2 =>
      x == y && exprStructEq rhs1 rhs2 && exprStructEqBinds rest1 rest2
    | _, _ => false
end

/-- Look up an expression in the seen-map by structural equality.
Returns the variable of the first matching entry, if any.

```
lookupStructEq [(App f x, v1), (Lit 1, v2)] (Lit 1) = some v2
lookupStructEq [(App f x, v1)] (App f y)             = none
```
-/
partial def lookupStructEq (seen : List (Expr × VarId)) (target : Expr)
    : Option VarId :=
  match seen with
  | [] => none
  | (expr, var) :: rest =>
    if exprStructEq expr target then some var
    else lookupStructEq rest target

/-! ## CSE Pass

`cse` performs common sub-expression elimination over the expression tree.
Returns the transformed expression paired with a flag indicating whether
any elimination was performed.

The pass walks into all sub-expressions (Lam bodies, Fix bodies, Let
bindings and bodies, Case alternatives, etc.) and at each `Let` block
scans bindings left-to-right for duplicates.

See the module-level documentation for the full algorithm description
and examples.
-/

mutual
  partial def cse : Expr → Expr × Bool
    | .Let binds body =>
      let (binds', changed1) := cseBindingsRHS binds
      let (body', changed2) := cse body
      let (resultExpr, changed3) := cseLetBindings binds' body'
      (resultExpr, changed1 || changed2 || changed3)

    | .Lam x body =>
      let (body', changed) := cse body
      (.Lam x body', changed)

    | .Fix f body =>
      let (body', changed) := cse body
      (.Fix f body', changed)

    | .App f x =>
      let (f', changed1) := cse f
      let (x', changed2) := cse x
      (.App f' x', changed1 || changed2)

    | .Force e =>
      let (e', changed) := cse e
      (.Force e', changed)

    | .Delay e =>
      let (e', changed) := cse e
      (.Delay e', changed)

    | .Constr tag args =>
      let (args', changed) := cseList args
      (.Constr tag args', changed)

    | .Case scrut alts =>
      let (scrut', changed1) := cse scrut
      let (alts', changed2) := cseList alts
      (.Case scrut' alts', changed1 || changed2)

    | e => (e, false)

  partial def cseList (es : List Expr) : List Expr × Bool :=
    go es [] false
  where
    go : List Expr → List Expr → Bool → List Expr × Bool
      | [], acc, changed => (acc.reverse, changed)
      | e :: rest, acc, changed =>
        let (e', c) := cse e
        go rest (e' :: acc) (changed || c)

  partial def cseBindingsRHS (binds : List (VarId × Expr))
      : List (VarId × Expr) × Bool :=
    go binds [] false
  where
    go : List (VarId × Expr) → List (VarId × Expr) → Bool
        → List (VarId × Expr) × Bool
      | [], acc, changed => (acc.reverse, changed)
      | (v, rhs) :: rest, acc, changed =>
        let (rhs', c) := cse rhs
        go rest ((v, rhs') :: acc) (changed || c)

  partial def cseLetBindings (binds : List (VarId × Expr)) (body : Expr)
      : Expr × Bool :=
    go binds [] [] body false
  where
    go : List (VarId × Expr) → List (Expr × VarId) → List (VarId × Expr)
        → Expr → Bool → Expr × Bool
      | [], _, acc, body, changed =>
        match acc.reverse with
        | [] => (body, changed)
        | kept => (.Let kept body, changed)
      | (v, rhs) :: rest, seen, acc, body, changed =>
        match lookupStructEq seen rhs with
        | some w =>
          let rest' := rest.map fun (y, e) => (y, rename v w e)
          let body' := rename v w body
          go rest' seen acc body' true
        | none =>
          go rest ((rhs, v) :: seen) ((v, rhs) :: acc) body changed
end

end Moist.MIR
