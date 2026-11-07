import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Safety

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

Binders are made unique once at the root (`uniqueOptimizationBinders`) and
the fresh-name counter is moved above every uid of the prepared term, so the
substitutions performed during the walk only draw names that do not occur in
the term. Subterms of a well-scoped term are well scoped, so freshening again
at inner nodes would be the identity.
-/

/-- Contract `App f x` when `f` is a lambda: substitute an atomic argument,
    otherwise bind it with a strict let. -/
def betaContract (f x : Expr) (changed : Bool) : FreshM (Expr × Bool) :=
  match f with
  | .Lam param body =>
    if x.isAtom then do
      let result ← subst param x body
      pure (result, true)
    else
      pure (.Let [(param, x, false)] body, true)
  | _ => pure (.App f x, changed)

mutual
  def betaReduceCore : Expr → FreshM (Expr × Bool)
    | .App f x => do
      let (f', c1) ← betaReduceCore f
      let (x', c2) ← betaReduceCore x
      betaContract f' x' (c1 || c2)
    | .Lam x body => do
      let (body', c) ← betaReduceCore body
      pure (.Lam x body', c)
    | .Fix f body => do
      let (body', c) ← betaReduceCore body
      pure (.Fix f body', c)
    | .Force e => do
      let (e', c) ← betaReduceCore e
      pure (.Force e', c)
    | .Delay e => do
      let (e', c) ← betaReduceCore e
      pure (.Delay e', c)
    | .Constr tag args => do
      let (args', c) ← betaReduceCoreList args
      pure (.Constr tag args', c)
    | .Case scrut alts => do
      let (scrut', c1) ← betaReduceCore scrut
      let (alts', c2) ← betaReduceCoreList alts
      pure (.Case scrut' alts', c1 || c2)
    | .Let binds body => do
      let (binds', c1) ← betaReduceCoreBinds binds
      let (body', c2) ← betaReduceCore body
      pure (.Let binds' body', c1 || c2)
    | e => pure (e, false)
  termination_by e => sizeOf e

  def betaReduceCoreList : List Expr → FreshM (List Expr × Bool)
    | [] => pure ([], false)
    | e :: rest => do
      let (e', c1) ← betaReduceCore e
      let (rest', c2) ← betaReduceCoreList rest
      pure (e' :: rest', c1 || c2)
  termination_by es => sizeOf es

  def betaReduceCoreBinds : List (VarId × Expr × Bool) → FreshM (List (VarId × Expr × Bool) × Bool)
    | [] => pure ([], false)
    | (v, rhs, er) :: rest => do
      let (rhs', c1) ← betaReduceCore rhs
      let (rest', c2) ← betaReduceCoreBinds rest
      pure ((v, rhs', er) :: rest', c1 || c2)
  termination_by binds => sizeOf binds
end

def betaReducePass (expression : Expr) : FreshM (Expr × Bool) := do
  let prepared := uniqueOptimizationBinders expression
  reserveFreshFor prepared
  betaReduceCore prepared

end Moist.MIR
