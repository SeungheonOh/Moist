import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity

namespace Moist.MIR

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! # MIR → UPLC Lowering

Translates MIR expressions to UPLC Terms (de Bruijn indexed).
Fix nodes are lowered via the Z combinator.

## Let Inlining

During lowering, single-use and dead let bindings are optimized:
- **Atom RHS** (Var, Lit, Builtin): always substituted, avoiding a
  redundant lambda-application wrapper.
- **Single-use**: always substituted. Safe in Plutus/UPLC where
  the only effects are error/trace (no mutable state).
- **Zero-use, pure RHS**: binding is dropped entirely.
- **Otherwise**: lowered as `(λ. body') rhs'` (standard encoding).

## Error Reporting

Returns `Except String Term` so that unbound variable errors
include the variable name.
-/

abbrev LowerM := ExceptT String FreshM

private def liftFresh (m : FreshM α) : LowerM α := ExceptT.lift m

private def envLookup (env : List VarId) (v : VarId) : Option Nat :=
  go env 0
where
  go : List VarId → Nat → Option Nat
    | [], _ => none
    | x :: xs, n => if x == v then some n else go xs (n + 1)

/-- Count occurrences of `x` in the remaining bindings and body. -/
private def countInRestAndBody (x : VarId) (rest : List (VarId × Expr)) (body : Expr) : Nat :=
  match rest with
  | [] => countOccurrences x body
  | _ => countOccurrences x (.Let rest body)

/-- Flatten degenerate empty-binding Lets that may arise from substitution. -/
private def flattenLet : Expr → Expr
  | .Let [] body => flattenLet body
  | e => e

partial def lower (env : List VarId) (e : Expr) : LowerM Term := do
  match e with
  | .Var x =>
    match envLookup env x with
    | some idx => pure (.Var (idx + 1))
    | none => ExceptT.mk (pure (.error s!"unbound variable: {x}"))

  | .Lit (c, ty) => pure (.Constant (c, ty))

  | .Builtin b => pure (.Builtin b)

  | .Error => pure .Error

  | .Lam x body => do
    let body' ← lower (x :: env) body
    pure (.Lam 0 body')

  | .App f x => do
    let f' ← lower env f
    let x' ← lower env x
    pure (.Apply f' x')

  | .Force e => do
    let e' ← lower env e
    pure (.Force e')

  | .Delay e => do
    let e' ← lower env e
    pure (.Delay e')

  | .Constr tag args => do
    let args' ← args.mapM (lower env)
    pure (.Constr tag args')

  | .Case scrut alts => do
    let scrut' ← lower env scrut
    let alts' ← alts.mapM (lower env)
    pure (.Case scrut' alts')

  | .Let binds body => lowerLet env binds body

  | .Fix f body => lowerFix env f body

where
  lowerLet (env : List VarId) : List (VarId × Expr) → Expr → LowerM Term
    | [], body => lower env body
    | (x, rhs) :: rest, body => do
      let uses := countInRestAndBody x rest body
      -- Atom RHS: always substitute (trivially cheap, no effects)
      if rhs.isAtom then
        let restBody ← liftFresh (subst x rhs (.Let rest body))
        lower env (flattenLet restBody)
      -- Zero uses, pure RHS: drop dead binding
      else if uses == 0 && isPure rhs then
        lowerLet env rest body
      -- Single use: always substitute. UPLC has no mutable state,
      -- so reordering across other bindings is safe.
      else if uses == 1 then
        let restBody ← liftFresh (subst x rhs (.Let rest body))
        lower env (flattenLet restBody)
      -- General case: (λ. rest') rhs'
      else do
        let rhs' ← lower env rhs
        let rest' ← lowerLet (x :: env) rest body
        pure (.Apply (.Lam 0 rest') rhs')

  lowerFix (env : List VarId) (f : VarId) (body : Expr) : LowerM Term := do
    match body with
    | .Lam x e =>
      -- Z combinator (CBV-safe):
      -- (λs. λx. e'[f := λv. s s v]) (λs. λx. e'[f := λv. s s v])
      let s ← liftFresh (freshVar "s")
      let v ← liftFresh (freshVar "v")
      let selfApp := Expr.Lam v (.App (.App (.Var s) (.Var s)) (.Var v))
      let e' ← liftFresh (subst f selfApp e)
      let inner := Expr.Lam s (.Lam x e')
      let innerTerm ← lower env inner
      pure (.Apply innerTerm innerTerm)
    | _ =>
      ExceptT.mk (pure (.error s!"Fix body must be a Lam, got: {repr body}"))

def lowerExpr (e : Expr) (freshStart : Nat := 10000) : Except String Term :=
  (ExceptT.run (lower [] e) |>.run ⟨freshStart⟩).1

end Moist.MIR
