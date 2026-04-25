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

mutual

theorem alphaEq_lowerTotal_eq {env1 env2 : List VarId} {e1 e2 : Expr}
    (h : AlphaEq env1 env2 e1 e2) :
    lowerTotal env1 e1 = lowerTotal env2 e2 := by
  match h with
  | .var hlook =>
    simp only [lowerTotal.eq_1, hlook]
  | .lit (c := c) =>
    obtain ⟨cv, ty⟩ := c
    simp only [lowerTotal.eq_2]
  | .builtin =>
    simp only [lowerTotal.eq_3]
  | .error =>
    simp only [lowerTotal.eq_4]
  | .lam hbody =>
    simp only [lowerTotal.eq_5, alphaEq_lowerTotal_eq hbody]
  | .fix _ =>
    simp only [lowerTotal.eq_12]
  | .app hf ha =>
    simp only [lowerTotal.eq_6, alphaEq_lowerTotal_eq hf, alphaEq_lowerTotal_eq ha]
  | .force he =>
    simp only [lowerTotal.eq_7, alphaEq_lowerTotal_eq he]
  | .delay he =>
    simp only [lowerTotal.eq_8, alphaEq_lowerTotal_eq he]
  | .constr hargs =>
    simp only [lowerTotal.eq_9, alphaEqList_lowerTotalList_eq hargs]
  | .case_ hscrut halts =>
    simp only [lowerTotal.eq_10, alphaEq_lowerTotal_eq hscrut,
      alphaEqList_lowerTotalList_eq halts]
  | .let_ hbinds =>
    simp only [lowerTotal.eq_11]
    exact alphaEqBinds_lowerTotalLet_eq hbinds
  termination_by sizeOf e1

theorem alphaEqList_lowerTotalList_eq {env1 env2 : List VarId}
    {es1 es2 : List Expr}
    (h : AlphaEqList env1 env2 es1 es2) :
    lowerTotalList env1 es1 = lowerTotalList env2 es2 := by
  match h with
  | .nil =>
    simp only [lowerTotalList.eq_1]
  | .cons he hes =>
    simp only [lowerTotalList.eq_2, alphaEq_lowerTotal_eq he,
      alphaEqList_lowerTotalList_eq hes]
  termination_by sizeOf es1

theorem alphaEqBinds_lowerTotalLet_eq {env1 env2 : List VarId}
    {binds1 binds2 : List (VarId × Expr × Bool)}
    {body1 body2 : Expr}
    (h : AlphaEqBinds env1 env2 binds1 binds2 body1 body2) :
    lowerTotalLet env1 binds1 body1 = lowerTotalLet env2 binds2 body2 := by
  match h with
  | .nil hbody =>
    simp only [lowerTotalLet.eq_1]
    exact alphaEq_lowerTotal_eq hbody
  | .cons hrhs hrest =>
    simp only [lowerTotalLet.eq_2, alphaEq_lowerTotal_eq hrhs,
      alphaEqBinds_lowerTotalLet_eq hrest]
  termination_by sizeOf binds1 + sizeOf body1

end

/-! ## Reflexivity -/

mutual

theorem AlphaEq.refl (env : List VarId) (e : Expr) :
    AlphaEq env env e e := by
  match e with
  | .Var x => exact .var rfl
  | .Lit _ => exact .lit
  | .Builtin _ => exact .builtin
  | .Error => exact .error
  | .Lam x body => exact .lam (AlphaEq.refl (x :: env) body)
  | .Fix f body => exact .fix (AlphaEq.refl (f :: env) body)
  | .App f a => exact .app (AlphaEq.refl env f) (AlphaEq.refl env a)
  | .Force e => exact .force (AlphaEq.refl env e)
  | .Delay e => exact .delay (AlphaEq.refl env e)
  | .Constr tag args => exact .constr (AlphaEqList.refl env args)
  | .Case scrut alts =>
    exact .case_ (AlphaEq.refl env scrut) (AlphaEqList.refl env alts)
  | .Let binds body => exact .let_ (AlphaEqBinds.refl env binds body)
  termination_by sizeOf e

theorem AlphaEqList.refl (env : List VarId) (es : List Expr) :
    AlphaEqList env env es es := by
  match es with
  | [] => exact .nil
  | e :: rest => exact .cons (AlphaEq.refl env e) (AlphaEqList.refl env rest)
  termination_by sizeOf es

theorem AlphaEqBinds.refl (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    AlphaEqBinds env env binds binds body body := by
  match binds with
  | [] => exact .nil (AlphaEq.refl env body)
  | (x, rhs, er) :: rest =>
    exact .cons (AlphaEq.refl env rhs) (AlphaEqBinds.refl (x :: env) rest body)
  termination_by sizeOf binds + sizeOf body

end

/-! ## Environment agreement -/

mutual

theorem AlphaEq.env_agree {env1 env2 : List VarId}
    (hagree : ∀ v, envLookupT env1 v = envLookupT env2 v)
    (e : Expr) :
    AlphaEq env1 env2 e e := by
  match e with
  | .Var x => exact .var (hagree x)
  | .Lit _ => exact .lit
  | .Builtin _ => exact .builtin
  | .Error => exact .error
  | .Lam x body =>
    exact .lam (AlphaEq.env_agree (envLookupT_agree_cons x env1 env2 hagree) body)
  | .Fix f body =>
    exact .fix (AlphaEq.env_agree (envLookupT_agree_cons f env1 env2 hagree) body)
  | .App f a =>
    exact .app (AlphaEq.env_agree hagree f) (AlphaEq.env_agree hagree a)
  | .Force e => exact .force (AlphaEq.env_agree hagree e)
  | .Delay e => exact .delay (AlphaEq.env_agree hagree e)
  | .Constr tag args => exact .constr (AlphaEqList.env_agree hagree args)
  | .Case scrut alts =>
    exact .case_ (AlphaEq.env_agree hagree scrut)
      (AlphaEqList.env_agree hagree alts)
  | .Let binds body => exact .let_ (AlphaEqBinds.env_agree hagree binds body)
  termination_by sizeOf e

theorem AlphaEqList.env_agree {env1 env2 : List VarId}
    (hagree : ∀ v, envLookupT env1 v = envLookupT env2 v)
    (es : List Expr) :
    AlphaEqList env1 env2 es es := by
  match es with
  | [] => exact .nil
  | e :: rest =>
    exact .cons (AlphaEq.env_agree hagree e) (AlphaEqList.env_agree hagree rest)
  termination_by sizeOf es

theorem AlphaEqBinds.env_agree {env1 env2 : List VarId}
    (hagree : ∀ v, envLookupT env1 v = envLookupT env2 v)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    AlphaEqBinds env1 env2 binds binds body body := by
  match binds with
  | [] => exact .nil (AlphaEq.env_agree hagree body)
  | (x, rhs, er) :: rest =>
    exact .cons (AlphaEq.env_agree hagree rhs)
      (AlphaEqBinds.env_agree (envLookupT_agree_cons x env1 env2 hagree) rest body)
  termination_by sizeOf binds + sizeOf body

end

end Moist.Verified.MIR.AlphaEq
