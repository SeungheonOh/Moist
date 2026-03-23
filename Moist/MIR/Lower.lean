import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.Plutus.Convert
import PlutusCore.UPLC.Term

namespace Moist.MIR

open PlutusCore.UPLC.Term (Term)
open Moist.Plutus.Convert (convertConst convertBuiltinFun)

/-! # MIR → UPLC Lowering

Translates MIR expressions to sc-fvt UPLC Terms (named variables).

This is a clean structural translation — no inlining or substitution
is performed here. Pre-lowering optimization (atom/single-use inlining,
dead binding elimination) is handled by `preLowerInline` before this pass.

## Let Encoding

Each `let v = rhs in body` is lowered to `(λname. body') rhs'`.

## Fix Encoding

Fix nodes are lowered via the Z combinator (CBV-safe):
`Fix f (Lam x e)` → `(λs. λx. e'[f := λv. s s v]) (λs. λx. e'[f := λv. s s v])`
-/

abbrev LowerM := ExceptT String FreshM

private def liftFresh (m : FreshM α) : LowerM α := ExceptT.lift m

/-- Convert a VarId to a unique string name for UPLC. -/
private def varName (v : VarId) : String := toString v

private def envLookup (env : List VarId) (v : VarId) : Bool :=
  env.any (· == v)

partial def lower (env : List VarId) (e : Expr) : LowerM Term := do
  match e with
  | .Var x =>
    if envLookup env x then
      pure (.Var (varName x))
    else
      ExceptT.mk (pure (.error s!"unbound variable: {x}"))

  | .Lit (c, _ty) => pure (.Const (convertConst c))

  | .Builtin b => pure (.Builtin (convertBuiltinFun b))

  | .Error => pure .Error

  | .Lam x body => do
    let body' ← lower (x :: env) body
    pure (.Lam (varName x) body')

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
    let alts' ← alts.mapM (lowerCaseAlt env)
    pure (.Case scrut' alts')

  | .Let binds body => lowerLet env binds body

  | .Fix f body => lowerFix env f body

where
  /-- Lower a Case alternative. If the branch is `Lam v body` where `v` is not free
      in `body`, strip the Lam — this happens for 0-field constructors (e.g. Bool SOP). -/
  lowerCaseAlt (env : List VarId) (alt : Expr) : LowerM Term :=
    match alt with
    | .Lam v body =>
      if (freeVars body).contains v then
        lower env alt  -- v is used: keep the Lam
      else
        lower env body -- v is unused: strip the Lam (0-field constructor)
    | _ => lower env alt

  lowerLet (env : List VarId) : List (VarId × Expr × Bool) → Expr → LowerM Term
    | [], body => lower env body
    | (x, rhs, _) :: rest, body => do
      let rhs' ← lower env rhs
      let rest' ← lowerLet (x :: env) rest body
      pure (.Apply (.Lam (varName x) rest') rhs')

  lowerFix (env : List VarId) (f : VarId) (body : Expr) : LowerM Term := do
    match body with
    | .Lam x e =>
      -- Z combinator (CBV-safe), let-shared to avoid duplicating the functional:
      -- (λz. z z) (λs. λx. e'[f := λv. s s v])
      let s ← liftFresh (freshVar "s")
      let v ← liftFresh (freshVar "v")
      let selfApp := Expr.Lam v (.App (.App (.Var s) (.Var s)) (.Var v))
      let e' ← liftFresh (subst f selfApp e)
      let inner := Expr.Lam s (.Lam x e')
      let innerTerm ← lower env inner
      -- (λz. z z) innerTerm — the functional appears only once
      let zName := "z"
      let omega := Term.Lam zName (.Apply (.Var zName) (.Var zName))
      pure (.Apply omega innerTerm)
    | _ =>
      ExceptT.mk (pure (.error s!"Fix body must be a Lam, got: {repr body}"))

def lowerExpr (e : Expr) (freshStart : Nat := 10000) : Except String Term :=
  (ExceptT.run (lower [] e) |>.run ⟨freshStart⟩).1

end Moist.MIR
