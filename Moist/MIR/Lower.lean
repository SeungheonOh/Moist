import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.LowerTotal

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

Fix nodes are lowered via the Z combinator (CBV-safe), let-shared so the
functional appears once:
`Fix f (Lam x e)` → `(λz. z z) (λs. λx. e'[f := s s])`.

The body is lowered under `x :: f :: x :: env`: the third slot stands for
`s` and is never reached by a lookup because `x` shadows it. The recursive
reference `f` (index 2) is then replaced by the self application `s s` with
UPLC substitution, which also closes the gap left by `f`. A recursive call
`f a` therefore becomes `[[s s] a]`.

Inside the functional `s` is always bound to the functional itself, so `s s`
halts in four steps, without effects, with the closure of `λx. e'`. Moving it
before the argument of a call is therefore unobservable
(`Moist.Verified.FixLowering`).
-/

abbrev LowerM := ExceptT String FreshM

/-- `s s` under the binder `x`, with `s` at index 2 once `f` is removed. -/
def fixSelfCall : Term := .Apply (.Var 2) (.Var 2)

/-- Z-combinator wrapper around the lowered body of `Fix f (Lam x body)`;
    the body is lowered under `x :: f :: s :: env`. -/
def fixLamWrap (body : Term) : Term :=
  .Apply (.Lam 0 (.Apply (.Var 1) (.Var 1)))
    (.Lam 0 (.Lam 0 (Moist.Verified.substTerm 2 fixSelfCall body)))

mutual
  def lower (env : List VarId) (e : Expr) : Except String Term :=
    match e with
    | .Var x =>
      match envLookupT env x with
      | some idx => .ok (.Var (idx + 1))
      | none => .error s!"unbound variable: {x}"
    | .Lit (c, ty) => .ok (.Constant (c, ty))
    | .Builtin b => .ok (.Builtin b)
    | .Error => .ok .Error
    | .Lam x body => do
      let body' ← lower (x :: env) body
      pure (.Lam 0 body')
    | .App f x => do
      let f' ← lower env f
      let x' ← lower env x
      pure (.Apply f' x')
    | .Force inner => do
      let inner' ← lower env inner
      pure (.Force inner')
    | .Delay inner => do
      let inner' ← lower env inner
      pure (.Delay inner')
    | .Constr tag args => do
      let args' ← lowerList env args
      pure (.Constr tag args')
    | .Case scrut alts => do
      let scrut' ← lower env scrut
      let alts' ← lowerList env alts
      pure (.Case scrut' alts')
    | .Let binds body => lowerLet env binds body
    | .Fix f (.Lam x body) => do
      let body' ← lower (x :: f :: x :: env) body
      pure (fixLamWrap body')
    | .Fix _ body => .error s!"Fix body must be a Lam, got: {repr body}"
  termination_by sizeOf e

  def lowerList (env : List VarId) (es : List Expr) : Except String (List Term) :=
    match es with
    | [] => .ok []
    | e :: rest => do
      let t ← lower env e
      let ts ← lowerList env rest
      pure (t :: ts)
  termination_by sizeOf es

  def lowerLet (env : List VarId) (binds : List (VarId × Expr × Bool)) (body : Expr) :
      Except String Term :=
    match binds with
    | [] => lower env body
    | (x, rhs, _) :: rest => do
      let rhs' ← lower env rhs
      let rest' ← lowerLet (x :: env) rest body
      pure (.Apply (.Lam 0 rest') rhs')
  termination_by sizeOf binds + sizeOf body
end

/-- Lower a closed MIR expression. `freshStart` is accepted for compatibility;
    lowering no longer generates names. -/
def lowerExpr (e : Expr) (_freshStart : Nat := 10000) : Except String Term :=
  lower [] e

end Moist.MIR
