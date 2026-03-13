import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Beta Reduction Pass

Reduces immediately-applied lambdas (`App (Lam x body) arg`) to
`Let [(x, arg)] body`, enabling subsequent ANF normalization and CSE.

## Motivation

Structure projection translation generates per-field destructure chains
wrapped in lambdas:

```
addInteger ((λself. let pair = unConstrData self ... in f0) x)
           ((λself. let pair = unConstrData self ... in f3) x)
```

Each lambda traps its let-bindings in a separate scope, preventing CSE
from detecting the duplicate `unConstrData x`. Beta reduction flattens
these into lets:

```
addInteger (let pair = unConstrData x ... in f0)
           (let pair = unConstrData x ... in f3)
```

A subsequent ANF pass then floats the lets to a shared scope where CSE
can eliminate the duplicates.

## Algorithm

Bottom-up traversal. At each `App (Lam x body) arg`:
- If `arg` is atomic (Var/Lit/Builtin): substitute directly.
- Otherwise: rewrite to `Let [(x, arg)] body`.

Recurses into sub-expressions first so that nested beta-redexes are
reduced inside-out.
-/

mutual
  partial def betaReducePass : Expr → FreshM (Expr × Bool)
    | .App f x => do
      let (f', c1) ← betaReducePass f
      let (x', c2) ← betaReducePass x
      match f' with
      | .Lam param body =>
        if x'.isAtom then
          let result ← subst param x' body
          pure (result, true)
        else
          pure (.Let [(param, x', false)] body, true)
      | _ => pure (.App f' x', c1 || c2)

    | .Lam x body => do
      let (body', c) ← betaReducePass body
      pure (.Lam x body', c)

    | .Fix f body => do
      let (body', c) ← betaReducePass body
      pure (.Fix f body', c)

    | .Force e => do
      let (e', c) ← betaReducePass e
      pure (.Force e', c)

    | .Delay e => do
      let (e', c) ← betaReducePass e
      pure (.Delay e', c)

    | .Constr tag args => do
      let (args', c) ← betaReducePassList args
      pure (.Constr tag args', c)

    | .Case scrut alts => do
      let (scrut', c1) ← betaReducePass scrut
      let (alts', c2) ← betaReducePassList alts
      pure (.Case scrut' alts', c1 || c2)

    | .Let binds body => do
      let (binds', c1) ← betaReducePassBinds binds
      let (body', c2) ← betaReducePass body
      pure (.Let binds' body', c1 || c2)

    | e => pure (e, false)

  partial def betaReducePassList (es : List Expr) : FreshM (List Expr × Bool) := do
    let mut result : List Expr := []
    let mut changed := false
    for e in es do
      let (e', c) ← betaReducePass e
      result := result ++ [e']
      changed := changed || c
    pure (result, changed)

  partial def betaReducePassBinds (binds : List (VarId × Expr × Bool))
      : FreshM (List (VarId × Expr × Bool) × Bool) := do
    let mut result : List (VarId × Expr × Bool) := []
    let mut changed := false
    for (v, rhs, er) in binds do
      let (rhs', c) ← betaReducePass rhs
      result := result ++ [(v, rhs', er)]
      changed := changed || c
    pure (result, changed)
end

end Moist.MIR
