import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Case Merge

Merges multiple `Case` expressions on the same scrutinee variable into a
single `Case`. This eliminates redundant pattern match/destructure operations
that arise from accessing multiple fields of the same value.

## The Problem

After ANF, accessing two fields from the same value produces two let-bound cases:

```
Let [
  (t1, Case (Var x) [Lam a0 (Lam a1 (Lam a2 (Lam a3 (Var a1))))]),
  (t2, Case (Var x) [Lam b0 (Lam b1 (Lam b2 (Lam b3 (Var b3))))])
] (App (App (Builtin addInteger) (Var t1)) (Var t2))
```

The field variables are lambda-bound inside each case's alternative and not
visible to the other case. CSE cannot help because the two cases have different
bodies.

## The Transformation

1. **Absorb continuation into the first case.** Split the let bindings at the
   first case on `x`. Everything after it moves into each alternative's body,
   where field variables are in scope.

2. **Case-of-known-constructor.** Inside branch `i`, we know `x` has constructor
   tag `i` with specific field variables. Any subsequent `Case (Var x)` resolves
   to alternative `i` with field substitution — all other alternatives are dead
   code and discarded.

## Result

```
Case (Var x) [
  Lam a0 (Lam a1 (Lam a2 (Lam a3
    (App (App (Builtin addInteger) (Var a1)) (Var a3)))))
]
```

One destructure instead of two. Subsequent inlining and DCE clean up the rest.
-/

/-! ## Helpers -/

/-- Peel leading lambda binders from an expression.
Returns the list of bound variables and the inner body.

```
peelLambdas (Lam a (Lam b (Var a))) = ([a, b], Var a)
peelLambdas (Var x)                  = ([], Var x)
``` -/
private def peelLambdas : Expr → List VarId × Expr
  | .Lam v body =>
    let (vs, inner) := peelLambdas body
    (v :: vs, inner)
  | e => ([], e)

/-- Wrap an expression in lambdas (inverse of peelLambdas). -/
private def wrapLambdas : List VarId → Expr → Expr
  | [], e => e
  | v :: vs, e => .Lam v (wrapLambdas vs e)

/-- Map a function over a list with its index. -/
private def mapWithIndex (f : Nat → α → β) (l : List α) : List β :=
  go l 0 []
where
  go : List α → Nat → List β → List β
    | [], _, acc => acc.reverse
    | x :: xs, i, acc => go xs (i + 1) (f i x :: acc)

/-! ## Simultaneous Rename

Renames multiple variables simultaneously to avoid interference when
substituting field variables from an outer case into an inner case body.
Sequential renaming `g0→f0` then `g1→f1` can fail if `f0 == g1` (the
first rename introduces a variable that the second then incorrectly renames).
Simultaneous rename does a single lookup per variable occurrence. -/

mutual
  partial def renameMany (pairs : List (VarId × VarId)) : Expr → Expr
    | .Var x =>
      match pairs.find? (fun (old, _) => old == x) with
      | some (_, new_) => .Var new_
      | none => .Var x
    | .Lit c => .Lit c
    | .Builtin b => .Builtin b
    | .Error => .Error
    | .Lam x body =>
      let pairs' := pairs.filter (fun (old, _) => old != x)
      .Lam x (if pairs'.isEmpty then body else renameMany pairs' body)
    | .Fix f body =>
      let pairs' := pairs.filter (fun (old, _) => old != f)
      .Fix f (if pairs'.isEmpty then body else renameMany pairs' body)
    | .App f x => .App (renameMany pairs f) (renameMany pairs x)
    | .Force e => .Force (renameMany pairs e)
    | .Delay e => .Delay (renameMany pairs e)
    | .Constr tag args => .Constr tag (args.map (renameMany pairs))
    | .Case scrut alts => .Case (renameMany pairs scrut) (alts.map (renameMany pairs))
    | .Let binds body => renameManyLet pairs binds [] body

  partial def renameManyLet (pairs : List (VarId × VarId))
      : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Expr
    | [], acc, body => .Let acc.reverse (renameMany pairs body)
    | (x, rhs, er) :: rest, acc, body =>
      let rhs' := renameMany pairs rhs
      let pairs' := pairs.filter (fun (old, _) => old != x)
      if pairs'.isEmpty then
        .Let (acc.reverse ++ [(x, rhs', er)] ++ rest) body
      else
        renameManyLet pairs' rest ((x, rhs', er) :: acc) body
end

/-! ## Case Merge Pass -/

/-- Known constructor info: maps a scrutinee variable to its known constructor
tag and field variables. Populated when we enter a case branch. -/
private abbrev KnownCtors := List (VarId × Nat × List VarId)

private def lookupKnown (env : KnownCtors) (x : VarId) : Option (Nat × List VarId) :=
  match env with
  | [] => none
  | (v, tag, fields) :: rest => if v == x then some (tag, fields) else lookupKnown rest x

/-- Check if a scrutinee variable appears as a Case scrutinee in a later binding,
respecting shadowing (stops if the scrutinee is rebound). -/
private def hasDuplicateCase (scrutinee : VarId) : List (VarId × Expr × Bool) → Bool
  | [] => false
  | (v, rhs, _) :: rest =>
    if v == scrutinee then false  -- shadowed, stop
    else match rhs with
      | .Case (.Var x) _ => x == scrutinee || hasDuplicateCase scrutinee rest
      | _ => hasDuplicateCase scrutinee rest

/-- Find the first case binding whose scrutinee has a duplicate case later in the
same let block.

Returns `(beforeBinds, resultVar, scrutineeVar, alts, afterBinds)`. -/
private def findFirstMergeableCase (binds : List (VarId × Expr × Bool))
    : Option (List (VarId × Expr × Bool) × VarId × VarId × List Expr × List (VarId × Expr × Bool)) :=
  go binds []
where
  go : List (VarId × Expr × Bool) → List (VarId × Expr × Bool)
    → Option (List (VarId × Expr × Bool) × VarId × VarId × List Expr × List (VarId × Expr × Bool))
    | [], _ => none
    | (v, .Case (.Var x) alts, _) :: rest, acc =>
      if hasDuplicateCase x rest then
        some (acc.reverse, v, x, alts, rest)
      else
        go rest ((v, .Case (.Var x) alts, false) :: acc)
    | bind :: rest, acc =>
      go rest (bind :: acc)

mutual
  /-- Main case merge traversal. Carries `knownCtors` environment that records
  which scrutinee variables have a known constructor tag and field bindings
  (because we are inside one of their case branches). -/
  partial def caseMerge (env : KnownCtors) : Expr → Expr × Bool
    | .Let binds body =>
      -- First, recurse into binding RHS values (may resolve nested known cases)
      let (binds1, changed1) := caseMergeBinds env binds
      -- Look for the first let-bound case whose scrutinee has a duplicate later
      match findFirstMergeableCase binds1 with
      | some (beforeBinds, t1, x, alts, afterBinds) =>
        -- Build merged alternatives: absorb afterBinds + body into each branch
        let newAlts := mapWithIndex (fun i alt =>
          let (fields, altBody) := peelLambdas alt
          -- Inside branch i: x is known as (Constr i fields)
          let innerEnv := (x, i, fields) :: env
          -- Rebuild the continuation: let t1 = altBody in <afterBinds> in body
          let innerExpr := Expr.Let ((t1, altBody, false) :: afterBinds) body
          -- Recurse — this resolves subsequent cases on x via case-of-known-ctor
          let (resolved, _) := caseMerge innerEnv innerExpr
          wrapLambdas fields resolved) alts
        let caseExpr := Expr.Case (.Var x) newAlts
        let result := match beforeBinds with
          | [] => caseExpr
          | _ => .Let beforeBinds caseExpr
        (result, true)
      | none =>
        -- No mergeable cases, recurse into the body
        let (body', changed2) := caseMerge env body
        (.Let binds1 body', changed1 || changed2)

    | .Case (.Var x) alts =>
      -- Case-of-known-constructor: resolve if x has a known tag
      match lookupKnown env x with
      | some (tag, fields) =>
        match alts[tag]? with
        | some alt =>
          let (params, altBody) := peelLambdas alt
          -- Substitute field params with known field variables
          let pairs := params.zip fields
          let resolved := if pairs.isEmpty then altBody else renameMany pairs altBody
          -- Recurse in case of further opportunities
          let (result, _) := caseMerge env resolved
          (result, true)
        | none => (.Error, true)
      | none =>
        let (alts', changed) := caseMergeList env alts
        (.Case (.Var x) alts', changed)

    | .Case scrut alts =>
      let (scrut', c1) := caseMerge env scrut
      let (alts', c2) := caseMergeList env alts
      (.Case scrut' alts', c1 || c2)

    | .Lam x body =>
      let (body', changed) := caseMerge env body
      (.Lam x body', changed)

    | .Fix f body =>
      let (body', changed) := caseMerge env body
      (.Fix f body', changed)

    | .App f x =>
      let (f', c1) := caseMerge env f
      let (x', c2) := caseMerge env x
      (.App f' x', c1 || c2)

    | .Force e =>
      let (e', changed) := caseMerge env e
      (.Force e', changed)

    | .Delay e =>
      let (e', changed) := caseMerge env e
      (.Delay e', changed)

    | .Constr tag args =>
      let (args', changed) := caseMergeList env args
      (.Constr tag args', changed)

    | e => (e, false)

  partial def caseMergeList (env : KnownCtors) (es : List Expr) : List Expr × Bool :=
    go es [] false
  where
    go : List Expr → List Expr → Bool → List Expr × Bool
      | [], acc, changed => (acc.reverse, changed)
      | e :: rest, acc, changed =>
        let (e', c) := caseMerge env e
        go rest (e' :: acc) (changed || c)

  partial def caseMergeBinds (env : KnownCtors) (binds : List (VarId × Expr × Bool))
      : List (VarId × Expr × Bool) × Bool :=
    go binds [] false
  where
    go : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Bool
        → List (VarId × Expr × Bool) × Bool
      | [], acc, changed => (acc.reverse, changed)
      | (v, rhs, er) :: rest, acc, changed =>
        let (rhs', c) := caseMerge env rhs
        go rest ((v, rhs', er) :: acc) (changed || c)
end

/-- Run the case merge optimization pass.
Returns the transformed expression paired with a flag indicating whether
any merge was performed. -/
def caseMergePass (e : Expr) : Expr × Bool :=
  caseMerge [] e

end Moist.MIR
