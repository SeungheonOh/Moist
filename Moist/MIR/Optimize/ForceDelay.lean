import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Safety

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

/-- `true` exactly when `e` is the variable `v`. -/
def isVarOf (v : VarId) : Expr → Bool
  | .Var w => w == v
  | _ => false

mutual
  /-- Return `true` when every free occurrence of `v` in `e` appears as the
  immediate argument of `Force`. A bare `Var v` outside `Force` makes the
  result `false`. Shadowed scopes are safe (the inner binder hides `v`). -/
  def allUsesAreForce (v : VarId) : Expr → Bool
    | .Force inner => isVarOf v inner || allUsesAreForce v inner
    | .Var w => !(w == v)
    | .Lit _ | .Builtin _ | .Error => true
    | .Lam x body => if x == v then true else allUsesAreForce v body
    | .Fix f body => if f == v then true else allUsesAreForce v body
    | .App fn arg => allUsesAreForce v fn && allUsesAreForce v arg
    | .Delay inner => allUsesAreForce v inner
    | .Constr _ args => allUsesAreForceList v args
    | .Case scrut alts => allUsesAreForce v scrut && allUsesAreForceList v alts
    | .Let binds body => allUsesAreForceLet v binds body
  termination_by e => sizeOf e

  def allUsesAreForceList (v : VarId) : List Expr → Bool
    | [] => true
    | e :: rest => allUsesAreForce v e && allUsesAreForceList v rest
  termination_by es => sizeOf es

  /-- Thread `allUsesAreForce` through a let-binding list, respecting
  shadowing: once a binding rebinds `v`, subsequent bindings and the body
  are safe regardless. -/
  def allUsesAreForceLet (v : VarId) : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => allUsesAreForce v body
    | (x, rhs, _) :: rest, body =>
      allUsesAreForce v rhs && (if x == v then true else allUsesAreForceLet v rest body)
  termination_by binds body => sizeOf binds + sizeOf body
end

/-! ## Binder hygiene check -/

mutual
  /-- `true` when no binder (Lam, Fix or Let) anywhere in `e` belongs to
  `avoid`. -/
  def bindersAvoid (avoid : VarSet) : Expr → Bool
    | .Var _ | .Lit _ | .Builtin _ | .Error => true
    | .Lam x body => !avoid.contains x && bindersAvoid avoid body
    | .Fix f body => !avoid.contains f && bindersAvoid avoid body
    | .App fn arg => bindersAvoid avoid fn && bindersAvoid avoid arg
    | .Force inner => bindersAvoid avoid inner
    | .Delay inner => bindersAvoid avoid inner
    | .Constr _ args => bindersAvoidList avoid args
    | .Case scrut alts => bindersAvoid avoid scrut && bindersAvoidList avoid alts
    | .Let binds body => bindersAvoidLet avoid binds body
  termination_by e => sizeOf e

  def bindersAvoidList (avoid : VarSet) : List Expr → Bool
    | [] => true
    | e :: rest => bindersAvoid avoid e && bindersAvoidList avoid rest
  termination_by es => sizeOf es

  def bindersAvoidLet (avoid : VarSet) : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => bindersAvoid avoid body
    | (x, rhs, _) :: rest, body =>
      !avoid.contains x && bindersAvoid avoid rhs && bindersAvoidLet avoid rest body
  termination_by binds body => sizeOf binds + sizeOf body
end

/-! ## Replacing `Force (Var v)` with a substitute expression -/

mutual
  /-- Replace every `Force (Var v)` with `repl` inside `e`. Does not descend
  past binders that shadow `v`. -/
  def replaceForceVar (v : VarId) (repl : Expr) : Expr → Expr
    | .Force inner =>
      if isVarOf v inner then repl else .Force (replaceForceVar v repl inner)
    | .Var w => .Var w
    | .Lit c => .Lit c
    | .Builtin b => .Builtin b
    | .Error => .Error
    | .Lam x body =>
      if x == v then .Lam x body else .Lam x (replaceForceVar v repl body)
    | .Fix f body =>
      if f == v then .Fix f body else .Fix f (replaceForceVar v repl body)
    | .App fn arg => .App (replaceForceVar v repl fn) (replaceForceVar v repl arg)
    | .Delay inner => .Delay (replaceForceVar v repl inner)
    | .Constr tag args => .Constr tag (replaceForceVarList v repl args)
    | .Case scrut alts =>
      .Case (replaceForceVar v repl scrut) (replaceForceVarList v repl alts)
    | .Let binds body =>
      let result := replaceForceVarLet v repl binds body
      .Let result.1 result.2
  termination_by e => sizeOf e

  def replaceForceVarList (v : VarId) (repl : Expr) : List Expr → List Expr
    | [] => []
    | e :: rest => replaceForceVar v repl e :: replaceForceVarList v repl rest
  termination_by es => sizeOf es

  /-- Thread `replaceForceVar` through a let-binding list, stopping at
  binders that shadow `v`. -/
  def replaceForceVarLet (v : VarId) (repl : Expr) :
      List (VarId × Expr × Bool) → Expr → List (VarId × Expr × Bool) × Expr
    | [], body => ([], replaceForceVar v repl body)
    | (x, rhs, er) :: rest, body =>
      let rhs' := replaceForceVar v repl rhs
      if x == v then ((x, rhs', er) :: rest, body)
      else
        let result := replaceForceVarLet v repl rest body
        ((x, rhs', er) :: result.1, result.2)
  termination_by binds body => sizeOf binds + sizeOf body
end

/-! ## Main pass -/

/-- Walk bindings left-to-right. For each `v = Delay e` where all subsequent
uses of `v` are under `Force`, replace `Force (Var v)` with `e` in the
remaining bindings and body. The now-dead `v = Delay e` binding is kept (DCE
handles removal). The replacement moves `e` under the binders of the
remaining scope, so it is only done when none of them rebinds `v` or a free
variable of `e`, and `e` does not mention `v` itself. -/
def processDelayBindings.go :
    List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Bool →
      List (VarId × Expr × Bool) × Expr × Bool
  | [], acc, body, ch => (acc.reverse, body, ch)
  | (v, rhs, er) :: rest, acc, body, ch =>
    match rhs with
    | .Delay inner =>
      let restExpr := if rest.isEmpty then body else .Let rest body
      if countOccurrences v restExpr > 0 && allUsesAreForce v restExpr &&
          !(freeVars inner).contains v &&
          bindersAvoid ((freeVars inner).insert v) restExpr then
        let rest' := rest.map fun (w, r, er2) => (w, replaceForceVar v inner r, er2)
        let body' := replaceForceVar v inner body
        processDelayBindings.go rest' ((v, rhs, er) :: acc) body' true
      else
        processDelayBindings.go rest ((v, rhs, er) :: acc) body ch
    | _ => processDelayBindings.go rest ((v, rhs, er) :: acc) body ch
  termination_by binds => binds.length

def processDelayBindings (binds : List (VarId × Expr × Bool)) (body : Expr) :
    List (VarId × Expr × Bool) × Expr × Bool :=
  processDelayBindings.go binds [] body false

mutual
  /-- Force/delay cancellation on an expression whose binders are already
  unique. -/
  def forceDelayCore : Expr → Expr × Bool
    | .Var x => (.Var x, false)
    | .Lit c => (.Lit c, false)
    | .Builtin b => (.Builtin b, false)
    | .Error => (.Error, false)
    | .Lam x body =>
      let result := forceDelayCore body
      (.Lam x result.1, result.2)
    | .Fix f body =>
      let result := forceDelayCore body
      (.Fix f result.1, result.2)
    | .App fn arg =>
      let fnResult := forceDelayCore fn
      let argResult := forceDelayCore arg
      (.App fnResult.1 argResult.1, fnResult.2 || argResult.2)
    | .Delay inner =>
      let result := forceDelayCore inner
      (.Delay result.1, result.2)
    | .Constr tag args =>
      let result := forceDelayList args
      (.Constr tag result.1, result.2)
    | .Case scrut alts =>
      let scrutResult := forceDelayCore scrut
      let altsResult := forceDelayList alts
      (.Case scrutResult.1 altsResult.1, scrutResult.2 || altsResult.2)
    | .Force inner =>
      let result := forceDelayCore inner
      -- Covers `Force (Delay e)` directly and a `Delay` exposed by recursion.
      match result.1 with
      | .Delay e => (e, true)
      | inner' => (.Force inner', result.2)
    | .Let binds body =>
      let bindsResult := forceDelayBinds binds
      let bodyResult := forceDelayCore body
      let processed := processDelayBindings bindsResult.1 bodyResult.1
      (.Let processed.1 processed.2.1, bindsResult.2 || bodyResult.2 || processed.2.2)
  termination_by e => sizeOf e

  def forceDelayList : List Expr → List Expr × Bool
    | [] => ([], false)
    | e :: rest =>
      let head := forceDelayCore e
      let tail := forceDelayList rest
      (head.1 :: tail.1, head.2 || tail.2)
  termination_by es => sizeOf es

  def forceDelayBinds : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) × Bool
    | [] => ([], false)
    | (v, rhs, er) :: rest =>
      let head := forceDelayCore rhs
      let tail := forceDelayBinds rest
      ((v, head.1, er) :: tail.1, head.2 || tail.2)
  termination_by binds => sizeOf binds
end

/-- Eliminate `Force`/`Delay` pairs from `e`.

Returns `(e', changed)` where `changed` is `true` when at least one
cancellation was performed. Handles both direct `Force (Delay e)` and
the through-let pattern where a `Delay` binding is only used under
`Force`. See the module documentation for the full algorithm and
examples. -/
def forceDelay (e : Expr) : Expr × Bool :=
  forceDelayCore (uniqueOptimizationBinders e)

end Moist.MIR
