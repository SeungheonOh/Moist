import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Force-Delay Cancellation

In Plutus, `Force (Delay e)` evaluates to `e` -- the force eliminates the
delay. This pass removes the redundant indirection to save execution cost.

## Patterns

### Pattern 1 -- Direct cancellation

```
Force (Delay e)  ==>  e
```

Rare after ANF conversion (ANF names intermediates), but can appear after
inlining.

### Pattern 2 -- Through a let binding (common in ANF)

```
let v = Delay e
in ... Force (Var v) ...
```

When **every** free occurrence of `v` appears as the immediate argument of
`Force`, we can replace each `Force (Var v)` with `e` and mark the binding
for removal (it becomes dead code that DCE will clean up).

If `v` is also used outside `Force` position (e.g. passed as an argument),
the `Delay` wrapper is semantically necessary and we leave the binding
alone.

## `allUsesAreForce`

To decide whether the through-let optimization is safe we traverse the
expression checking that every free occurrence of `v` sits directly inside
`Force`:

```
allUsesAreForce v (Force (Var w))        | w == v  = true   -- valid use
allUsesAreForce v (Var w)                | w == v  = false  -- bare use
allUsesAreForce v (Lam w body)           | w == v  = true   -- shadowed
allUsesAreForce v (Fix w body)           | w == v  = true   -- shadowed
allUsesAreForce v (Let binds body)                 = ... (with shadowing)
allUsesAreForce v <other>                          = recurse children
```

## Examples

```
-- Direct cancellation
Force (Delay (Var x))
  ==>  Var x

-- Through-let, all uses are Force
let v = Delay (Var x)
in Force (Var v)
  ==>  let v = Delay (Var x)
       in Var x
-- (the dead binding is left for DCE)

-- Through-let, mixed uses -- no change
let v = Delay (Var x)
in App (Var v) (Force (Var v))
  ==>  unchanged  (Var v in App position is not under Force)
```
-/

/-! ## Checking that all uses of a variable are under Force -/

mutual
  /-- Return `true` when every free occurrence of `v` in `e` appears as the
  immediate argument of `Force`. A bare `Var v` outside `Force` makes the
  result `false`. Shadowed scopes are safe (the inner binder hides `v`). -/
  partial def allUsesAreForce (v : VarId) : Expr → Bool
    | .Force (.Var _) => true
      -- Either w == v (a valid Force-use) or w != v (v does not occur here).
      -- Both are fine; no deeper structure to check inside a Var.
    | .Force inner => allUsesAreForce v inner
    | .Var w => !(w == v)
      -- A bare occurrence of v outside Force position.
    | .Lit _ | .Builtin _ | .Error => true
    | .Lam x body => if x == v then true else allUsesAreForce v body
    | .Fix f body => if f == v then true else allUsesAreForce v body
    | .App fn arg => allUsesAreForce v fn && allUsesAreForce v arg
    | .Delay inner => allUsesAreForce v inner
    | .Constr _ args => args.all (allUsesAreForce v)
    | .Case scrut alts =>
      allUsesAreForce v scrut && alts.all (allUsesAreForce v)
    | .Let binds body => allUsesAreForceLet v binds body

  /-- Thread `allUsesAreForce` through a let-binding list, respecting
  shadowing: once a binding rebinds `v`, subsequent bindings and the body
  are safe regardless. -/
  partial def allUsesAreForceLet (v : VarId)
      : List (VarId × Expr) → Expr → Bool
    | [], body => allUsesAreForce v body
    | (x, rhs) :: rest, body =>
      allUsesAreForce v rhs &&
        (if x == v then true else allUsesAreForceLet v rest body)
end

/-! ## Replacing `Force (Var v)` with a substitute expression -/

mutual
  /-- Replace every `Force (Var v)` with `repl` inside `e`. Does not descend
  past binders that shadow `v`. -/
  partial def replaceForceVar (v : VarId) (repl : Expr) : Expr → Expr
    | .Force (.Var w) =>
      if w == v then repl else .Force (.Var w)
    | .Force inner => .Force (replaceForceVar v repl inner)
    | .Var w => .Var w
    | .Lit c => .Lit c
    | .Builtin b => .Builtin b
    | .Error => .Error
    | .Lam x body =>
      if x == v then .Lam x body
      else .Lam x (replaceForceVar v repl body)
    | .Fix f body =>
      if f == v then .Fix f body
      else .Fix f (replaceForceVar v repl body)
    | .App fn arg =>
      .App (replaceForceVar v repl fn) (replaceForceVar v repl arg)
    | .Delay inner => .Delay (replaceForceVar v repl inner)
    | .Constr tag args => .Constr tag (args.map (replaceForceVar v repl))
    | .Case scrut alts =>
      .Case (replaceForceVar v repl scrut) (alts.map (replaceForceVar v repl))
    | .Let binds body => replaceForceVarLet v repl binds [] body

  /-- Thread `replaceForceVar` through a let-binding list, stopping at
  binders that shadow `v`. -/
  partial def replaceForceVarLet (v : VarId) (repl : Expr)
      : List (VarId × Expr) → List (VarId × Expr) → Expr → Expr
    | [], acc, body =>
      .Let acc.reverse (replaceForceVar v repl body)
    | (x, rhs) :: rest, acc, body =>
      let rhs' := replaceForceVar v repl rhs
      if x == v then
        .Let (acc.reverse ++ [(x, rhs')] ++ rest) body
      else
        replaceForceVarLet v repl rest ((x, rhs') :: acc) body
end

/-! ## Main pass -/

/-- Eliminate `Force`/`Delay` pairs from `e`.

Returns `(e', changed)` where `changed` is `true` when at least one
cancellation was performed. Handles both direct `Force (Delay e)` and
the through-let pattern where a `Delay` binding is only used under
`Force`. See the module documentation for the full algorithm and
examples. -/
partial def forceDelay (e : Expr) : Expr × Bool :=
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => (e, false)

  | .Lam x body =>
    let (body', ch) := forceDelay body
    (.Lam x body', ch)

  | .Fix f body =>
    let (body', ch) := forceDelay body
    (.Fix f body', ch)

  | .App fn arg =>
    let (fn', ch1) := forceDelay fn
    let (arg', ch2) := forceDelay arg
    (.App fn' arg', ch1 || ch2)

  | .Delay inner =>
    let (inner', ch) := forceDelay inner
    (.Delay inner', ch)

  | .Constr tag args =>
    let results := args.map forceDelay
    let args' := results.map Prod.fst
    let ch := results.any Prod.snd
    (.Constr tag args', ch)

  | .Case scrut alts =>
    let (scrut', ch1) := forceDelay scrut
    let results := alts.map forceDelay
    let alts' := results.map Prod.fst
    let ch2 := results.any Prod.snd
    (.Case scrut' alts', ch1 || ch2)

  -- Pattern 1: direct Force (Delay e) cancellation
  | .Force (.Delay inner) =>
    let (inner', _) := forceDelay inner
    (inner', true)

  | .Force inner =>
    let (inner', ch) := forceDelay inner
    -- After recursion the inner expression may now be a Delay
    match inner' with
    | .Delay e => (e, true)
    | _ => (.Force inner', ch)

  | .Let binds body =>
    -- Step 1: recursively simplify all RHSs and the body
    let (binds', rhsChanged) := binds.foldl (init := ([], false))
      fun (acc, ch) (v, rhs) =>
        let (rhs', ch') := forceDelay rhs
        (acc ++ [(v, rhs')], ch || ch')
    let (body', bodyChanged) := forceDelay body
    -- Step 2: for each binding of the form v = Delay e, check whether all
    -- uses of v in subsequent bindings and the body are under Force.
    let (finalBinds, finalBody, patternChanged) :=
      processDelayBindings binds' body'
    let anyChanged := rhsChanged || bodyChanged || patternChanged
    (.Let finalBinds finalBody, anyChanged)
where
  /-- Walk bindings left-to-right. For each `v = Delay e` where all
  subsequent uses of `v` are under `Force`, replace `Force (Var v)` with
  `e` in the remaining bindings and body. The now-dead `v = Delay e`
  binding is kept (DCE handles removal). -/
  processDelayBindings (binds : List (VarId × Expr)) (body : Expr)
      : List (VarId × Expr) × Expr × Bool :=
    go binds [] body false
  go : List (VarId × Expr) → List (VarId × Expr) → Expr → Bool
      → List (VarId × Expr) × Expr × Bool
    | [], acc, body, ch => (acc.reverse, body, ch)
    | (v, rhs) :: rest, acc, body, ch =>
      match rhs with
      | .Delay inner =>
        -- Check all uses of v in subsequent bindings and body
        let restExpr := if rest.isEmpty then body else .Let rest body
        if allUsesAreForce v restExpr then
          -- Replace Force (Var v) -> inner in subsequent bindings and body
          let rest' := rest.map fun (w, r) => (w, replaceForceVar v inner r)
          let body' := replaceForceVar v inner body
          go rest' ((v, rhs) :: acc) body' true
        else
          go rest ((v, rhs) :: acc) body ch
      | _ => go rest ((v, rhs) :: acc) body ch

end Moist.MIR
