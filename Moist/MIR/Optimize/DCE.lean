import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity

namespace Moist.MIR

/-! # Dead Code Elimination

Remove `Let` bindings whose bound variable is never referenced in the body,
provided the right-hand side is pure (cannot error or diverge).

## Why purity matters

Removing an impure unused binding would change program semantics. Consider:

```
let a = error in x
```

Evaluating this program raises an error. If we dropped the binding we would
get `x`, which succeeds -- a visible change in behavior. Therefore we only
eliminate a binding when `isPure rhs` holds.

## Algorithm

Bindings are scanned **right-to-left** using a *needed set* that starts as
`freeVars body`. This single-pass approach naturally handles transitive dead
code: if binding `b` references `a`, and `b` is dead, then `a`'s free
variables are never added to the needed set, so `a` is also recognized as
dead without requiring an additional iteration.

1. Recursively simplify every sub-expression (bottom-up).
2. At each `Let binds body`:
   - Initialize `needed := freeVars body`.
   - Walk `binds` right-to-left. For each `(v, rhs)`:
     - If `v ∈ needed`: keep the binding, add `freeVars rhs` to `needed`.
     - If `v ∉ needed` and `isPure rhs`: discard the binding (dead + safe).
     - If `v ∉ needed` and `¬ isPure rhs`: keep the binding (side effect).
   - If every binding was discarded, return just the body.
   - Otherwise rebuild `Let` with the surviving bindings.

## Examples

```
-- Pure unused binding is removed
let a = 42 in x
  ==>  x

-- Impure unused binding is kept (application may error)
let a = f x in y
  ==>  let a = f x in y

-- Error binding is kept (Error is impure)
let a = error in x
  ==>  let a = error in x

-- Transitive dead code in one pass (right-to-left needed set)
let a = 42
let b = Lam x (Var a)   -- pure, unused
in z
  ==>  z
-- b is dead and pure, so removed; its freeVars (including a) are never
-- added to the needed set, so a is also dead and pure, and removed.
```
-/

/-- Scan bindings right-to-left, collecting those that are needed (or impure)
and tracking whether any were eliminated. Returns `(surviving, eliminated)`
where `eliminated` is `true` when at least one binding was dropped. -/
private partial def filterBindings
    : List (VarId × Expr) → VarSet → List (VarId × Expr) → Bool
    → List (VarId × Expr) × Bool
  | [], _, acc, elim => (acc, elim)
  | (v, rhs) :: rest, needed, acc, elim =>
    if needed.contains v then
      filterBindings rest (needed.union (freeVars rhs)) ((v, rhs) :: acc) elim
    else if isPure rhs then
      filterBindings rest needed acc true
    else
      filterBindings rest needed ((v, rhs) :: acc) elim

/-- Eliminate unused pure `Let` bindings from `e`.

Returns `(e', changed)` where `changed` is `true` when at least one
binding was removed. See the module documentation for the full algorithm
and examples. -/
partial def dce (e : Expr) : Expr × Bool :=
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => (e, false)

  | .Lam x body =>
    let (body', ch) := dce body
    (.Lam x body', ch)

  | .Fix f body =>
    let (body', ch) := dce body
    (.Fix f body', ch)

  | .App fn arg =>
    let (fn', ch1) := dce fn
    let (arg', ch2) := dce arg
    (.App fn' arg', ch1 || ch2)

  | .Force inner =>
    let (inner', ch) := dce inner
    (.Force inner', ch)

  | .Delay inner =>
    let (inner', ch) := dce inner
    (.Delay inner', ch)

  | .Constr tag args =>
    let results := args.map dce
    let args' := results.map Prod.fst
    let ch := results.any Prod.snd
    (.Constr tag args', ch)

  | .Case scrut alts =>
    let (scrut', ch1) := dce scrut
    let results := alts.map dce
    let alts' := results.map Prod.fst
    let ch2 := results.any Prod.snd
    (.Case scrut' alts', ch1 || ch2)

  | .Let binds body =>
    -- Step 1: recursively simplify all RHSs and the body
    let (binds', rhsChanged) := binds.foldl (init := ([], false))
      fun (acc, ch) (v, rhs) =>
        let (rhs', ch') := dce rhs
        (acc ++ [(v, rhs')], ch || ch')
    let (body', bodyChanged) := dce body
    -- Step 2: right-to-left scan with needed set.
    -- We reverse the list, call filterBindings (which walks left-to-right
    -- on the reversed list, effectively right-to-left on the original),
    -- and the accumulator naturally ends up in the correct order.
    let needed := freeVars body'
    let (surviving, eliminated) := filterBindings binds'.reverse needed [] false
    let anyChanged := rhsChanged || bodyChanged || eliminated
    match surviving with
    | [] => (body', true)
    | _ => (.Let surviving body', anyChanged)

end Moist.MIR
