import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Common Sub-Expression Elimination (CSE)

Eliminates redundant computations by detecting structurally identical
let-binding RHS expressions and reusing the first binding's result for
all subsequent duplicates.

## Why This Is Always Safe in Plutus

Plutus has no mutable state. If `App f x` succeeds for binding `a`,
computing `App f x` again for binding `b` would produce the identical
result. If `App f x` errors, sequential evaluation guarantees we never
reach `b`, so replacing `b` with `a` does not change the error
semantics.

## Scope-Aware Deduplication

The seen map of known bindings is propagated across scope boundaries:
from outer Let blocks into nested Let blocks, case alternatives, lambda
bodies, fix bodies, and delay bodies. This allows a binding inside a
case alternative to be deduplicated against a binding from an enclosing
scope.

This is safe because outer bindings are always evaluated before inner
scopes are entered. If an outer binding succeeded, any duplicate inner
binding would also succeed with the identical result (no mutable state).

When entering a Lam or Fix scope, entries in the seen map are filtered
to remove any whose RHS mentions the new binder (the RHS would refer to
a different binding in the new scope) or whose mapped variable equals
the binder (would be shadowed).

## Algorithm

1. Walk the expression tree carrying a `seen` map of previously computed
   RHS expressions to their binding variables: `List (Expr × VarId)`.
2. At each `Let binds body`, process bindings left-to-right:
   a. CSE the RHS with the current seen map (outer + previous bindings).
   b. Check if the CSE'd RHS matches any entry in the seen map.
   c. If found as `w`: rename all free occurrences of `v` to `w` in
      subsequent bindings and in the body. Drop this binding.
   d. If not found: add `(rhs, v)` to the seen map and keep the binding.
3. After all bindings, CSE the body with the full accumulated seen map.
4. When entering Lam/Fix, filter the seen map for the new binder.
5. Pass the seen map unchanged through Case, Delay, App, Force, Constr.

## Examples

```
-- Duplicate application eliminated
let a = App (Var f) (Var x) in
let b = App (Var f) (Var x) in
App (Var a) (Var b)
  ==>
let a = App (Var f) (Var x) in
App (Var a) (Var a)

-- Cross-scope dedup: inner case alt reuses outer binding
let a = unConstrData ctx in
let tag = fstPair (sndPair a) in
Case (equalsInteger tag 0) [
  ...,
  let a' = unConstrData ctx in    -- matches a from outer scope!
  let flds = sndPair a' in        -- matches sndPair a after rename
  unListData (headList flds)
]
  ==>
let a = unConstrData ctx in
let flds = sndPair a in
let tag = fstPair flds in
Case (equalsInteger tag 0) [
  ...,
  unListData (headList flds)       -- a' and inner flds eliminated
]

-- Cross-scope through nested Let blocks
let a = App (Var f) (Var x) in
  let b = App (Var f) (Var x) in  -- matches a from outer Let
  App (Var a) (Var b)
  ==>
let a = App (Var f) (Var x) in
App (Var a) (Var a)
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

  partial def exprStructEqBinds : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Bool
    | [], [] => true
    | (x, rhs1, _) :: rest1, (y, rhs2, _) :: rest2 =>
      x == y && exprStructEq rhs1 rhs2 && exprStructEqBinds rest1 rest2
    | _, _ => false
end

/-- Look up an expression in the seen-map by alpha-equivalence.
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
    if alphaEq expr target then some var
    else lookupStructEq rest target

/-! ## Seen Map Filtering

When entering a new binder scope (Lam x or Fix f), entries in the seen
map may become invalid:

1. An entry whose mapped variable equals the binder would be shadowed.
2. An entry whose RHS contains the binder as a free variable would refer
   to a different binding in the new scope.

Both cases are removed to prevent incorrect deduplication.
-/

/-- Filter the seen map when entering a Lam/Fix scope with binder `v`.
Removes entries where `v` is the mapped variable (shadowed) or appears
free in the RHS expression (would refer to a different binding). -/
private def filterSeen (binder : VarId) (seen : List (Expr × VarId))
    : List (Expr × VarId) :=
  seen.filter fun (rhs, v) => v != binder && !(freeVars rhs).contains binder

/-! ## CSE Pass

`cse` performs scope-aware common sub-expression elimination over the
expression tree. The `seen` parameter carries bindings from enclosing
scopes. Returns the transformed expression paired with a flag indicating
whether any elimination was performed.

At each `Let` block, bindings are processed left-to-right: the RHS is
first CSE'd (exposing nested optimization opportunities), then checked
against the accumulated seen map. The body is processed last with the
full seen map, enabling cross-scope deduplication into case alternatives,
lambda bodies, and other nested expressions.
-/

mutual
  partial def cse (seen : List (Expr × VarId)) : Expr → Expr × Bool
    | .Let binds body =>
      cseLetBlock seen binds body

    | .Lam x body =>
      let seen' := filterSeen x seen
      let (body', changed) := cse seen' body
      (.Lam x body', changed)

    | .Fix f body =>
      let seen' := filterSeen f seen
      let (body', changed) := cse seen' body
      (.Fix f body', changed)

    | .App f x =>
      let (f', c1) := cse seen f
      let (x', c2) := cse seen x
      (.App f' x', c1 || c2)

    | .Force e =>
      let (e', c) := cse seen e
      (.Force e', c)

    | .Delay e =>
      let (e', c) := cse seen e
      (.Delay e', c)

    | .Constr tag args =>
      let (args', c) := cseList seen args
      (.Constr tag args', c)

    | .Case scrut alts =>
      let (scrut', c1) := cse seen scrut
      let (alts', c2) := cseList seen alts
      (.Case scrut' alts', c1 || c2)

    | e => (e, false)

  partial def cseList (seen : List (Expr × VarId)) (es : List Expr)
      : List Expr × Bool :=
    go es [] false
  where
    go : List Expr → List Expr → Bool → List Expr × Bool
      | [], acc, changed => (acc.reverse, changed)
      | e :: rest, acc, changed =>
        let (e', c) := cse seen e
        go rest (e' :: acc) (changed || c)

  /-- Process a Let block with scope-aware deduplication.

  Walks bindings left-to-right. For each binding:
  1. CSE the RHS with the current seen map (outer + previous bindings).
  2. Check if the CSE'd RHS matches any entry in the seen map.
  3. If duplicate found: rename the binding variable to the earlier one,
     drop the binding.
  4. If new: add to the seen map, keep the binding.

  After all bindings, CSE the body with the full accumulated seen map.
  This allows nested expressions (e.g. inside case alternatives) to
  deduplicate against bindings from enclosing let blocks. -/
  partial def cseLetBlock (outerSeen : List (Expr × VarId))
      (binds : List (VarId × Expr × Bool)) (body : Expr) : Expr × Bool :=
    go binds outerSeen [] body false
  where
    go : List (VarId × Expr × Bool) → List (Expr × VarId)
        → List (VarId × Expr × Bool) → Expr → Bool → Expr × Bool
      | [], seen, acc, body, changed =>
        let (body', bodyChanged) := cse seen body
        match acc.reverse with
        | [] => (body', changed || bodyChanged)
        | kept => (.Let kept body', changed || bodyChanged)
      | (v, rhs, er) :: rest, seen, acc, body, changed =>
        -- CSE nested expressions within the RHS
        let (rhs', rhsChanged) := cse seen rhs
        -- Check if the processed RHS matches something already seen
        match lookupStructEq seen rhs' with
        | some w =>
          let rest' := rest.map fun (y, e, er2) => (y, rename v w e, er2)
          let body' := rename v w body
          go rest' seen acc body' true
        | none =>
          go rest ((rhs', v) :: seen) ((v, rhs', er) :: acc) body (changed || rhsChanged)
end

end Moist.MIR
