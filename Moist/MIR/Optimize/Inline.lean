import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Inlining Pass

Replaces variable references with their definitions when profitable,
reducing indirection and enabling further optimizations such as constant
folding and dead-code elimination.

## Inlining Decision Table

For each `let v = rhs in body` binding the pass inspects the RHS kind,
the number of free occurrences of `v` in `body`, and whether those
occurrences fall under a `Fix` node.

| RHS kind             | Occurrences | Under Fix? | Decision                        |
|----------------------|-------------|------------|---------------------------------|
| Atom (Var/Lit/Builtin) | any       | --         | ALWAYS inline (atoms are free)  |
| Value, size <= 5     | any         | --         | Inline (small, cheap to dup)    |
| Value, large         | 0           | --         | Keep (DCE handles dead code)    |
| Value, large         | 1           | no         | Inline (single use, no dup)     |
| Value, large         | 1           | yes        | Keep (recursion = unbounded)    |
| Value, large         | >= 2        | --         | Keep (avoids code bloat)        |
| Non-value            | 0           | --         | Keep (DCE handles dead code)    |
| Non-value            | 1           | no         | Inline (single evaluation)      |
| Non-value            | 1           | yes        | Keep (recursion duplicates it)  |
| Non-value            | >= 2        | --         | Keep (avoids re-evaluation)     |

## Fix Boundary Rule

When a binding's only occurrence is inside a `Fix f body` node, the
recursive function `f` could evaluate the inlined expression an unbounded
number of times. For non-value RHS expressions this changes semantics
(duplicates an effectful computation); for large value expressions it
causes unbounded code growth after unrolling. We therefore refuse to
inline across a Fix boundary even for single-use bindings.

## Beta Reduction

The pass also performs beta reduction on `App (Lam x body) arg` where
`arg` is atomic, replacing it with `subst x arg body`. This handles
the common case introduced by ANF normalization.

## Examples

```
-- Atom inlining: always inline regardless of occurrence count
let a = Var x in App (Var a) (Var a)
  ==> App (Var x) (Var x)

-- Small value inlining: Lam of size <= 5 is inlined even if used twice
let f = Lam y (Var y) in App (Var f) (App (Var f) (Var z))
  ==> App (Lam y (Var y)) (App (Lam y (Var y)) (Var z))

-- Single-use large value: inlined when NOT under Fix
let g = Lam x (App (Var x) (App (Var x) (Var x))) in App (Var g) (Var z)
  ==> App (Lam x (App (Var x) (App (Var x) (Var x)))) (Var z)

-- Single-use under Fix: NOT inlined
let g = Lam x (Var x) in Fix f (App (Var g) (Var f))
  ==> let g = Lam x (Var x) in Fix f (App (Var g) (Var f))
  (kept because the single use is under Fix)

-- Dead binding: kept for DCE to handle
let unused = App (Var f) (Var x) in Var y
  ==> let unused = App (Var f) (Var x) in Var y

-- Non-value single use not under Fix: inlined
let r = App (Var f) (Var x) in App (Var g) (Var r)
  ==> App (Var g) (App (Var f) (Var x))

-- Beta reduction on atomic argument
App (Lam x (App (Var x) (Var x))) (Var z)
  ==> App (Var z) (Var z)
```
-/

/-- Maximum AST node count for a value expression to be inlined unconditionally
(regardless of occurrence count). Atoms always have size 1, so this threshold
only matters for compound values like lambdas and delays. -/
def inlineThreshold : Nat := 5

/-! ## Fix Boundary Detection

`occursUnderFixAux` returns `true` when variable `v` has at least one free
occurrence that is nested inside the body of a `Fix` node in `e`.

We track an `underFix : Bool` flag that flips to `true` once we enter
a `Fix` body. Binder shadowing is respected: if the Fix or a Lam/Let
re-binds `v`, deeper occurrences do not count.

```
occursUnderFix v (Fix f (App (Var v) (Var f)))  = true
occursUnderFix v (App (Var v) (Fix f (Var f)))  = false  (v is outside Fix)
occursUnderFix v (Fix v body)                   = false  (v is rebound)
```
-/

mutual
  partial def occursUnderFixAux (v : VarId) (underFix : Bool) : Expr → Bool
    | .Var x => underFix && x == v
    | .Lit _ | .Builtin _ | .Error => false
    | .Lam x body =>
      if x == v then false
      else occursUnderFixAux v underFix body
    | .Fix f body =>
      if f == v then false
      else occursUnderFixAux v true body
    | .App f x =>
      occursUnderFixAux v underFix f || occursUnderFixAux v underFix x
    | .Force e => occursUnderFixAux v underFix e
    | .Delay e => occursUnderFixAux v underFix e
    | .Constr _ args => args.any (occursUnderFixAux v underFix)
    | .Case scrut alts =>
      occursUnderFixAux v underFix scrut || alts.any (occursUnderFixAux v underFix)
    | .Let binds body => occursUnderFixLetAux v underFix binds body

  partial def occursUnderFixLetAux (v : VarId) (underFix : Bool)
      : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => occursUnderFixAux v underFix body
    | (x, rhs, _) :: rest, body =>
      occursUnderFixAux v underFix rhs ||
      (if x == v then false else occursUnderFixLetAux v underFix rest body)
end

/-- Return `true` when variable `v` has at least one free occurrence nested
inside a `Fix` body in expression `e`. See `occursUnderFixAux` for details. -/
def occursUnderFix (v : VarId) (e : Expr) : Bool :=
  occursUnderFixAux v false e

/-! ## Inlining Decision -/

/-- Determine whether to inline a `let v = rhs in ...` binding given the
occurrence count and Fix boundary status. Returns `true` when inlining
is profitable.

See the module-level decision table for the full specification. -/
def shouldInline (rhs : Expr) (occurrences : Nat) (underFix : Bool) : Bool :=
  if rhs.isAtom then
    true
  else if rhs.isValue then
    if exprSize rhs <= inlineThreshold then
      true
    else if occurrences == 1 && !underFix then
      true
    else
      false
  else
    occurrences == 1 && !underFix

/-! ## Inline Pass

`inlinePass` performs one round of inlining over the expression tree.
Returns the transformed expression paired with a flag indicating whether
any inlining was performed (useful for fixed-point iteration).

The pass walks the tree bottom-up: it first recurses into sub-expressions,
then processes `Let` bindings left-to-right, and finally attempts beta
reduction on `App` nodes.

See the module-level documentation for the full decision table and examples.
-/

mutual
  partial def inlinePass : Expr → FreshM (Expr × Bool)
    | .Let binds body => do
      let (binds', changed1) ← inlineBindings binds
      let (body', changed2) ← inlinePass body
      let (resultExpr, changed3) ← inlineLetBindings binds' body'
      pure (resultExpr, changed1 || changed2 || changed3)

    | .Lam x body => do
      let (body', changed) ← inlinePass body
      pure (.Lam x body', changed)

    | .Fix f body => do
      let (body', changed) ← inlinePass body
      pure (.Fix f body', changed)

    | .App f x => do
      let (f', changed1) ← inlinePass f
      let (x', changed2) ← inlinePass x
      let (result, changed3) ← betaReduce f' x'
      pure (result, changed1 || changed2 || changed3)

    | .Force e => do
      let (e', changed) ← inlinePass e
      pure (.Force e', changed)

    | .Delay e => do
      let (e', changed) ← inlinePass e
      pure (.Delay e', changed)

    | .Constr tag args => do
      let (args', changed) ← inlinePassList args
      pure (.Constr tag args', changed)

    | .Case scrut alts => do
      let (scrut', changed1) ← inlinePass scrut
      let (alts', changed2) ← inlinePassList alts
      pure (.Case scrut' alts', changed1 || changed2)

    | e => pure (e, false)

  partial def inlinePassList (es : List Expr) : FreshM (List Expr × Bool) := do
    let mut result : List Expr := []
    let mut changed := false
    for e in es do
      let (e', c) ← inlinePass e
      result := result ++ [e']
      changed := changed || c
    pure (result, changed)

  partial def inlineBindings (binds : List (VarId × Expr × Bool))
      : FreshM (List (VarId × Expr × Bool) × Bool) := do
    let mut result : List (VarId × Expr × Bool) := []
    let mut changed := false
    for (v, rhs, er) in binds do
      let (rhs', c) ← inlinePass rhs
      result := result ++ [(v, rhs', er)]
      changed := changed || c
    pure (result, changed)

  partial def inlineLetBindings (binds : List (VarId × Expr × Bool)) (body : Expr)
      : FreshM (Expr × Bool) :=
    go binds [] body false
  where
    go : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Bool
        → FreshM (Expr × Bool)
      | [], acc, body, changed =>
        match acc.reverse with
        | [] => pure (body, changed)
        | kept => pure (.Let kept body, changed)
      | (v, rhs, er) :: rest, acc, body, changed => do
        let occ := countOccurrences v body +
          rest.foldl (fun n (_, e, _) => n + countOccurrences v e) 0
        let underFix := occursUnderFix v body ||
          rest.any (fun (_, e, _) => occursUnderFix v e)
        if shouldInline rhs occ underFix then do
          let body' ← subst v rhs body
          let rest' ← rest.mapM fun (w, e, er2) => do
            let e' ← subst v rhs e
            pure (w, e', er2)
          go rest' acc body' true
        else
          go rest ((v, rhs, er) :: acc) body changed

  partial def betaReduce (f : Expr) (x : Expr) : FreshM (Expr × Bool) :=
    match f with
    | .Lam param body =>
      if x.isAtom then do
        let result ← subst param x body
        pure (result, true)
      else
        pure (.App f x, false)
    | _ => pure (.App f x, false)
end

end Moist.MIR
