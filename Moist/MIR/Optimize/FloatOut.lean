import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity

namespace Moist.MIR

/-! # Let-Binding Float-Out

Moves let bindings outward past Lam/Fix boundaries so that pure
bindings are evaluated once at the definition site rather than
once per call at each application site.

## Motivation

Consider:

```
Lam x →
  Let a = <pure expr not mentioning x>
  Let b = App (Var a) (Var x)
  ...
```

Every time this lambda is applied, `a` is recomputed even though its value
never depends on `x`. By floating `a` outside the lambda we get:

```
Let a = <pure expr not mentioning x>
Lam x →
  Let b = App (Var a) (Var x)
  ...
```

Now `a` is computed once and shared across all calls.

## Algorithm

The pass works **bottom-up**: sub-expressions are processed first so that
deeply nested bindings bubble outward one level at a time across repeated
applications of the pass.

At each `Lam x body` or `Fix f body` node whose body is a
`Let binds innerBody`:

1. **Partition** bindings into a *float set* and a *stay set*.
2. A binding `(v, rhs)` **floats** when ALL of the following hold:
   - `isPure rhs` -- impure bindings must stay in place.
   - The Lam/Fix binder (`x` or `f`) is NOT in `freeVars rhs`.
   - None of the *stay* variables encountered so far appear in
     `freeVars rhs` (sequential scoping rule).
3. Otherwise the binding **stays**.
4. Reconstruct the expression:
   - Wrap the Lam/Fix with the floated bindings on the outside.
   - Keep the stayed bindings inside the Lam/Fix body.
   - If one of the two sets is empty, skip the corresponding Let wrapper.

### What we do NOT float out of

- **Delay** -- floating would change lazy evaluation to eager evaluation,
  altering semantics.
- **Case alternatives** -- floating would cause unconditional evaluation of
  bindings that should only run in one branch.

### Sequential scoping

Bindings in a Let block are scoped left-to-right: a later binding may
reference an earlier one. We process bindings in order and maintain a
set of "stay" variable names. If a binding's RHS mentions any stay
variable, the binding itself must stay (even if it is otherwise pure
and independent of the Lam binder), because its dependency is trapped
inside the Lam/Fix.

## Examples

### Binding floats out of a lambda

```
Lam x →                          Let a = Lit 1
  Let a = Lit 1                   Lam x →
      b = App (Var a) (Var x)       Let b = App (Var a) (Var x)
  in body                           in body
```

`a = Lit 1` is pure and does not mention `x`, so it floats.
`b = App (Var a) (Var x)` mentions `x`, so it stays.

### Binding stays because it depends on the lambda parameter

```
Lam x →
  Let c = App (Var x) (Var x)     -- c mentions x → stays
  in body
```

No transformation is applied.

### Binding stays because of sequential scoping dependency

```
Lam x →
  Let a = App (Var x) (Var x)    -- a mentions x → stays
      b = Lam y (Var a)          -- b is pure, doesn't mention x,
                                 -- BUT depends on stay-var a → stays
  in body
```

Even though `b` is pure and doesn't mention `x`, it references `a`
which is in the stay set, so `b` must also stay.

### Nested lambdas: bindings float to different levels

After two applications of floatOut:

```
Lam x →                          Let a = Lit 1
  Lam y →                        Lam x →
    Let a = Lit 1                   Let b = Lam z (Var x)
        b = Lam z (Var x)          Lam y →
        c = App (Var y) (Var b)       Let c = App (Var y) (Var b)
    in body                           in body
```

- `a` mentions neither `x` nor `y` -- floats out of both lambdas.
- `b` mentions `x` but not `y` -- floats out of the inner lambda only.
- `c` mentions `y` -- stays in the innermost scope.
-/

/-! ## Internal helpers -/

/-- Partition let bindings into (float, stay) relative to the given binder.

A binding floats when:
1. Its RHS is pure.
2. The binder `v` is not free in the RHS.
3. No previously-stayed variable is free in the RHS.

Bindings are processed left-to-right to respect sequential scoping. -/
private def partitionBindings (binder : VarId) (binds : List (VarId × Expr))
    : List (VarId × Expr) × List (VarId × Expr) :=
  let (floatRev, stayRev, _) := binds.foldl (init := ([], [], VarSet.empty))
    fun (floatAcc, stayAcc, stayVars) (x, rhs) =>
      let rhsFV := freeVars rhs
      if isPure rhs && !rhsFV.contains binder && !stayVars.data.any (rhsFV.contains ·) then
        ((x, rhs) :: floatAcc, stayAcc, stayVars)
      else
        (floatAcc, (x, rhs) :: stayAcc, stayVars.insert x)
  (floatRev.reverse, stayRev.reverse)

/-- Wrap an expression in a Let block, or return it unchanged when the
binding list is empty. -/
private def mkLet (binds : List (VarId × Expr)) (body : Expr) : Expr :=
  match binds with
  | [] => body
  | _ => .Let binds body

/-! ## Core pass -/

/-- Bottom-up let-float-out pass. Returns the transformed expression
together with a flag indicating whether any binding was moved.

See the module-level documentation for a full description of the algorithm,
invariants, and worked examples. -/
partial def floatOut : Expr → Expr × Bool :=
  go
where
  /-- Process a list of expressions, collecting the changed flag. -/
  goList (es : List Expr) : List Expr × Bool :=
    let results := es.map go
    let es'     := results.map Prod.fst
    let changed := results.any Prod.snd
    (es', changed)

  /-- Process let bindings (RHS only). -/
  goBinds (binds : List (VarId × Expr)) : List (VarId × Expr) × Bool :=
    let results := binds.map fun (v, rhs) =>
      let (rhs', c) := go rhs
      ((v, rhs'), c)
    let binds'  := results.map Prod.fst
    let changed := results.any Prod.snd
    (binds', changed)

  /-- Try to float bindings out of a Lam or Fix node.
  `binder` is the variable bound by the Lam/Fix.
  `mkWrapper` reconstructs the Lam/Fix given a new body. -/
  tryFloat (binder : VarId) (mkWrapper : Expr → Expr) (body : Expr) : Expr × Bool :=
    let (body', bodyChanged) := go body
    match body' with
    | .Let binds innerBody =>
      let (floatBinds, stayBinds) := partitionBindings binder binds
      if floatBinds.isEmpty then
        (mkWrapper body', bodyChanged)
      else
        let inner := mkWrapper (mkLet stayBinds innerBody)
        (mkLet floatBinds inner, true)
    | _ => (mkWrapper body', bodyChanged)

  /-- Main recursive traversal. -/
  go : Expr → Expr × Bool
    | .Var v        => (.Var v, false)
    | .Lit c        => (.Lit c, false)
    | .Builtin b    => (.Builtin b, false)
    | .Error        => (.Error, false)

    | .Lam x body   => tryFloat x (.Lam x) body
    | .Fix f body   => tryFloat f (.Fix f) body

    | .App f x =>
      let (f', c1) := go f
      let (x', c2) := go x
      (.App f' x', c1 || c2)

    | .Force e =>
      let (e', c) := go e
      (.Force e', c)

    -- Do NOT recurse into Delay bodies for floating; still process
    -- sub-expressions so deeper lambdas benefit.
    | .Delay e =>
      let (e', c) := go e
      (.Delay e', c)

    | .Constr tag args =>
      let (args', c) := goList args
      (.Constr tag args', c)

    -- Do NOT float out of Case alternatives; still recurse into them.
    | .Case scrut alts =>
      let (scrut', c1) := go scrut
      let (alts', c2)  := goList alts
      (.Case scrut' alts', c1 || c2)

    | .Let binds body =>
      let (binds', c1) := goBinds binds
      let (body', c2)  := go body
      (.Let binds' body', c1 || c2)

end Moist.MIR
