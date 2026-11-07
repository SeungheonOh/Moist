import Moist.MIR.LowerTotal
import Moist.Verified.Definitions.MIR

/-! # Prop-valued alpha-equivalence for MIR expressions

`AlphaEq env1 env2 e1 e2` holds when `e1` and `e2` are structurally
identical modulo bound-variable names, with `env1` and `env2` tracking
bound-variable scopes (each binder pushes the chosen name).

The bridge theorem `alphaEq_lowerTotal_eq` shows alpha-equivalent
expressions have identical `lowerTotal` outputs: since `lowerTotal`
maps named variables to de Bruijn indices via `envLookupT`, two
expressions with the same de Bruijn structure lower identically.
-/

namespace Moist.Verified.MIR.AlphaEq

open Moist.MIR
open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! ## Inductive definitions -/

mutual

inductive AlphaEq : List VarId → List VarId → Expr → Expr → Prop where
  | var {env1 env2 : List VarId} {x y : VarId} :
      envLookupT env1 x = envLookupT env2 y →
      AlphaEq env1 env2 (.Var x) (.Var y)
  | lit {env1 env2 : List VarId} {c : Const × BuiltinType} :
      AlphaEq env1 env2 (.Lit c) (.Lit c)
  | builtin {env1 env2 : List VarId} {b : BuiltinFun} :
      AlphaEq env1 env2 (.Builtin b) (.Builtin b)
  | error {env1 env2 : List VarId} :
      AlphaEq env1 env2 .Error .Error
  | lam {env1 env2 : List VarId} {x y : VarId} {body1 body2 : Expr} :
      AlphaEq (x :: env1) (y :: env2) body1 body2 →
      AlphaEq env1 env2 (.Lam x body1) (.Lam y body2)
  | fix {env1 env2 : List VarId} {f g : VarId} {body1 body2 : Expr} :
      AlphaEq (f :: env1) (g :: env2) body1 body2 →
      AlphaEq env1 env2 (.Fix f body1) (.Fix g body2)
  | app {env1 env2 : List VarId} {f1 f2 a1 a2 : Expr} :
      AlphaEq env1 env2 f1 f2 → AlphaEq env1 env2 a1 a2 →
      AlphaEq env1 env2 (.App f1 a1) (.App f2 a2)
  | force {env1 env2 : List VarId} {e1 e2 : Expr} :
      AlphaEq env1 env2 e1 e2 →
      AlphaEq env1 env2 (.Force e1) (.Force e2)
  | delay {env1 env2 : List VarId} {e1 e2 : Expr} :
      AlphaEq env1 env2 e1 e2 →
      AlphaEq env1 env2 (.Delay e1) (.Delay e2)
  | constr {env1 env2 : List VarId} {tag : Nat}
      {args1 args2 : List Expr} :
      AlphaEqList env1 env2 args1 args2 →
      AlphaEq env1 env2 (.Constr tag args1) (.Constr tag args2)
  | case_ {env1 env2 : List VarId} {scrut1 scrut2 : Expr}
      {alts1 alts2 : List Expr} :
      AlphaEq env1 env2 scrut1 scrut2 →
      AlphaEqList env1 env2 alts1 alts2 →
      AlphaEq env1 env2 (.Case scrut1 alts1) (.Case scrut2 alts2)
  | let_ {env1 env2 : List VarId}
      {binds1 binds2 : List (VarId × Expr × Bool)}
      {body1 body2 : Expr} :
      AlphaEqBinds env1 env2 binds1 binds2 body1 body2 →
      AlphaEq env1 env2 (.Let binds1 body1) (.Let binds2 body2)

inductive AlphaEqList : List VarId → List VarId → List Expr → List Expr → Prop where
  | nil {env1 env2 : List VarId} :
      AlphaEqList env1 env2 [] []
  | cons {env1 env2 : List VarId} {e1 e2 : Expr} {es1 es2 : List Expr} :
      AlphaEq env1 env2 e1 e2 → AlphaEqList env1 env2 es1 es2 →
      AlphaEqList env1 env2 (e1 :: es1) (e2 :: es2)

inductive AlphaEqBinds : List VarId → List VarId →
    List (VarId × Expr × Bool) → List (VarId × Expr × Bool) →
    Expr → Expr → Prop where
  | nil {env1 env2 : List VarId} {body1 body2 : Expr} :
      AlphaEq env1 env2 body1 body2 →
      AlphaEqBinds env1 env2 [] [] body1 body2
  | cons {env1 env2 : List VarId} {x y : VarId} {rhs1 rhs2 : Expr}
      {er : Bool}
      {rest1 rest2 : List (VarId × Expr × Bool)}
      {body1 body2 : Expr} :
      AlphaEq env1 env2 rhs1 rhs2 →
      AlphaEqBinds (x :: env1) (y :: env2) rest1 rest2 body1 body2 →
      AlphaEqBinds env1 env2
        ((x, rhs1, er) :: rest1) ((y, rhs2, er) :: rest2) body1 body2

end

/-! ## Bridge theorem: AlphaEq → identical lowering -/

/-! ## Reflexivity -/

/-! ## Environment agreement -/

end Moist.Verified.MIR.AlphaEq
