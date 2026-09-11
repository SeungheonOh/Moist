import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Safety

namespace Moist.MIR

/-! # Common Sub-Expression Elimination

CSE reuses an earlier, dominating let-bound result when the expressions are
alpha-equivalent and reevaluation cannot emit observable trace messages.
Potential failure does not by itself prohibit reuse: a failed first
evaluation prevents reaching the duplicate. Trace, however, is observable
despite the absence of mutable state.

isRepeatable follows available function/thunk aliases conservatively.
Known nonlogging builtin calls and safe allocations remain eligible;
unknown calls, unknown forces, and potentially logging computations do not.

The seen map flows into nested scopes but never out of conditional or
deferred scopes. Entries are invalidated when their result or a free
dependency is rebound. Public traversal first establishes globally unique
binders, so replacement and later scope movement cannot capture variables.
The explicit seen argument is an internal environment of dominating bindings.

For example, repeated addInteger applications may share their result;
repeated calls to an unknown f must remain separate because f may trace.
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
  partial def cse (seen : List (Expr × VarId)) (expression : Expr) : Expr × Bool :=
    match uniqueOptimizationBinders expression with
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
        match if isRepeatable seen rhs' then lookupStructEq seen rhs' else none with
        | some w =>
          let rest' := rest.map fun (y, e, er2) => (y, rename v w e, er2)
          let body' := rename v w body
          go rest' seen acc body' true
        | none =>
          let available := filterSeen v seen
          let available := if (freeVars rhs').contains v then available else (rhs', v) :: available
          go rest available ((v, rhs', er) :: acc) body (changed || rhsChanged)
end

end Moist.MIR
