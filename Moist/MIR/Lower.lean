import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! # MIR → UPLC Lowering

Translates MIR expressions to UPLC Terms (de Bruijn indexed).

This is a clean structural translation — no inlining or substitution
is performed here. Pre-lowering optimization (atom/single-use inlining,
dead binding elimination) is handled by `preLowerInline` before this pass.

## Let Encoding

Each `let v = rhs in body` is lowered to `(λ. body') rhs'`.

## Fix Encoding

Fix nodes are lowered via the Z combinator (CBV-safe):
`Fix f (Lam x e)` → `(λs. λx. e'[f := λv. s s v]) (λs. λx. e'[f := λv. s s v])`
-/

abbrev LowerM := ExceptT String FreshM

private def liftFresh (m : FreshM α) : LowerM α := ExceptT.lift m

private def envLookup (env : List VarId) (v : VarId) : Option Nat :=
  go env 0
where
  go : List VarId → Nat → Option Nat
    | [], _ => none
    | x :: xs, n => if x == v then some n else go xs (n + 1)

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
