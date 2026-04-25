import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity
import Moist.MIR.Canonicalize

namespace Moist.MIR

/-! # Inlining Pass

Replaces variable references with their definitions when profitable,
reducing indirection and enabling further optimizations such as constant
folding and dead-code elimination.

## Inlining Decision Table

For each `let v = rhs in body` binding the pass inspects the RHS kind,
the number of free occurrences of `v` in `body`, and whether those
occurrences fall under a `Fix` node.

| RHS kind               | Occurrences | Position   | Decision                        |
|------------------------|-------------|------------|---------------------------------|
| Atom (Var/Lit/Builtin) | any         | --         | ALWAYS inline (atoms are free)  |
| Value/pure, size <= 5  | any         | --         | Inline (small, cheap to dup)    |
| Value/pure, large      | 0           | --         | Keep (DCE handles dead code)    |
| Value/pure, large      | 1           | not in Fix | Inline (single use, no dup)     |
| Value/pure, large      | 1           | in Fix     | Keep (recursion = unbounded)    |
| Value/pure, large      | >= 2        | --         | Keep (avoids code bloat)        |
| Impure non-value       | 0           | --         | Keep (DCE handles dead code)    |
| Impure non-value       | 1           | strict     | Inline (single evaluation)      |
| Impure non-value       | 1           | deferred   | Keep (see below)                |
| Impure non-value       | >= 2        | --         | Keep (avoids re-evaluation)     |

## Deferred Position Rule

Under strict evaluation, a let binding `let v = rhs in body` always
evaluates `rhs` before `body`. Inlining `v` moves the evaluation of
`rhs` to wherever `v` appears in `body`. For non-value expressions
(which have evaluation effects — they may error), this is only safe
when the occurrence is in **strict position**: it will definitely be
evaluated, exactly once, in the same evaluation context.

Deferred positions where inlining non-values is unsafe:
- **Lam body**: evaluation moves from once-at-binding to per-call.
- **Fix body**: evaluation could happen an unbounded number of times.
- **Delay body**: evaluation moves from eager to lazy (only on Force).
- **Case alternative**: evaluation conditional on branch selection.

For **value** RHS expressions (Lam, Delay, Fix), only the Fix boundary
matters (to prevent unbounded code growth from recursion). Values have
no evaluation effects, so moving them into Lam/Delay/Case is safe.

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

-- Non-value single use in strict position: inlined
let r = App (Var f) (Var x) in App (Var g) (Var r)
  ==> App (Var g) (App (Var f) (Var x))

-- Non-value single use in Case alternative: NOT inlined (deferred position)
let r = App (Var f) (Var x) in Case (Var s) [Var r, Var y]
  ==> let r = App (Var f) (Var x) in Case (Var s) [Var r, Var y]
  (kept because the single use is in a Case branch — evaluation is conditional)

-- Non-value single use in Lam body: NOT inlined (deferred position)
let r = App (Var f) (Var x) in Lam y (Var r)
  ==> let r = App (Var f) (Var x) in Lam y (Var r)
  (kept because the single use is inside a lambda — changes eval from once to per-call)

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
  def occursUnderFixAux (v : VarId) (underFix : Bool) : Expr → Bool
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
    | .Constr _ args => occursUnderFixListAux v underFix args
    | .Case scrut alts =>
      occursUnderFixAux v underFix scrut || occursUnderFixListAux v underFix alts
    | .Let binds body => occursUnderFixLetAux v underFix binds body
  termination_by e => sizeOf e

  def occursUnderFixListAux (v : VarId) (underFix : Bool) : List Expr → Bool
    | [] => false
    | e :: rest =>
      occursUnderFixAux v underFix e || occursUnderFixListAux v underFix rest
  termination_by es => sizeOf es

  def occursUnderFixLetAux (v : VarId) (underFix : Bool)
      : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => occursUnderFixAux v underFix body
    | (x, rhs, _) :: rest, body =>
      occursUnderFixAux v underFix rhs ||
      (if x == v then false else occursUnderFixLetAux v underFix rest body)
  termination_by binds body => sizeOf binds + sizeOf body
end

/-- Return `true` when variable `v` has at least one free occurrence nested
inside a `Fix` body in expression `e`. See `occursUnderFixAux` for details. -/
def occursUnderFix (v : VarId) (e : Expr) : Bool :=
  occursUnderFixAux v false e

/-! ## Inlining Decision -/

/-- Determine whether to inline a `let v = rhs in ...` binding given the
occurrence count, Fix boundary status (for values), and deferred position
status (for impure non-values). Returns `true` when inlining is profitable
and semantics-preserving.

- `underFix`: the variable occurs inside a `Fix` body (used for values and
  pure non-values to prevent unbounded code growth from recursion).
- `inDeferred`: the variable occurs inside a Lam/Fix/Delay body or Case
  alternative (used for impure non-values to prevent moving effectful
  computations into positions where evaluation is not guaranteed).

Pure non-values (e.g. partial application of a total builtin like
`addInteger x`) follow the value rules: they have no evaluation effects,
so moving them into Lam/Delay/Case is safe. Only Fix matters (code bloat).

See the module-level decision table for the full specification. -/
def shouldInline (rhs : Expr) (occurrences : Nat) (underFix : Bool)
    (inDeferred : Bool) : Bool :=
  if rhs.isAtom then
    true
  else if rhs.isValue || isPure rhs then
    if exprSize rhs <= inlineThreshold then
      true
    else if occurrences == 1 && !underFix then
      true
    else
      false
  else
    occurrences == 1 && !inDeferred

/-! ## Inline Pass

`inlinePass` performs one round of inlining over the expression tree.
Returns the transformed expression paired with a flag indicating whether
any inlining was performed (useful for fixed-point iteration).

The pass walks the tree bottom-up: it first recurses into sub-expressions,
then processes `Let` bindings left-to-right, and finally attempts beta
reduction on `App` nodes.

See the module-level documentation for the full decision table and examples.
-/

/-! ## Beta Reduction -/

/-- Beta-reduce `App f x`: when `f` is `Lam param body` and `x` is atomic,
    substitute `x` for `param` in `body`. Atom restriction prevents
    duplicating or re-evaluating non-atomic arguments. -/
def betaReduce (f : Expr) (x : Expr) : FreshM (Expr × Bool) :=
  match f with
  | .Lam param body =>
    if x.isAtom then do
      let result ← subst param x body
      pure (result, true)
    else
      pure (.App f x, false)
  | _ => pure (.App f x, false)

/-! ## Length-Preserving Substitution on Bindings

`substInBindings v repl binds` applies `subst v repl` to each binding's
RHS (preserving names and `er` flags) and returns a subtype that carries
a proof of length preservation. The length proof is needed by `inlineLetGo`
below: after deciding to inline a binding `(v, rhs, er)`, we recurse on
the remaining bindings with `rhs` substituted into each RHS — the
recursion's termination measure (first argument's list length) must
decrease, which requires `rest'.length = rest.length`. -/
def substInBindings (v : VarId) (repl : Expr)
    : (binds : List (VarId × Expr × Bool)) →
      FreshM { result : List (VarId × Expr × Bool) // result.length = binds.length }
  | [] => pure ⟨[], rfl⟩
  | (w, e, er) :: rest => do
    let e' ← subst v repl e
    let ⟨rest', hlen⟩ ← substInBindings v repl rest
    pure ⟨(w, e', er) :: rest', by simp [List.length, hlen]⟩

/-! ## Inline Let Bindings (Decision Loop) -/

/-- Process let-bindings left-to-right, inlining or keeping each one
    according to `shouldInline`. Terminates structurally on the first
    argument (list length strictly decreases on each recursive call,
    using the subtype length proof from `substInBindings`). -/
def inlineLetGo : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Bool
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
    let inDeferred := occursInDeferred v body ||
      rest.any (fun (_, e, _) => occursInDeferred v e)
    if shouldInline rhs occ underFix inDeferred then do
      let body' ← subst v rhs body
      let ⟨rest', hlen⟩ ← substInBindings v rhs rest
      have : rest'.length < ((v, rhs, er) :: rest).length := by
        simp only [List.length_cons, hlen]; omega
      inlineLetGo rest' acc body' true
    else
      inlineLetGo rest ((v, rhs, er) :: acc) body changed
termination_by binds => binds.length

/-- Walk a list of bindings left-to-right, either inlining (substituting
    the RHS into the body and remaining bindings) or keeping the binding.
    Returns the resulting expression and a flag. -/
def inlineLetBindings (binds : List (VarId × Expr × Bool)) (body : Expr)
    : FreshM (Expr × Bool) :=
  inlineLetGo binds [] body false

mutual
  def inlinePass : Expr → FreshM (Expr × Bool)
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
  termination_by e => sizeOf e

  def inlinePassList : List Expr → FreshM (List Expr × Bool)
    | [] => pure ([], false)
    | e :: rest => do
      let (e', c1) ← inlinePass e
      let (rest', c2) ← inlinePassList rest
      pure (e' :: rest', c1 || c2)
  termination_by es => sizeOf es

  def inlineBindings : List (VarId × Expr × Bool) → FreshM (List (VarId × Expr × Bool) × Bool)
    | [] => pure ([], false)
    | (v, rhs, er) :: rest => do
      let (rhs', c1) ← inlinePass rhs
      let (rest', c2) ← inlineBindings rest
      pure ((v, rhs', er) :: rest', c1 || c2)
  termination_by bs => sizeOf bs
end

def inlinePassWithCanon (e : Expr) : FreshM (Expr × Bool) :=
  inlinePass (canonicalize e)

end Moist.MIR
