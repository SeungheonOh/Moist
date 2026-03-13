import Moist.Plutus.Term

namespace Moist.MIR

open Moist.Plutus.Term

/-! # MIR Core Types

The Mid-level Intermediate Representation for Moist.
Named variables (VarId), expression type, predicates, and fresh variable supply.
-/

structure VarId where
  uid  : Nat
  hint : String := ""
deriving Repr, Inhabited

instance : BEq VarId where
  beq a b := a.uid == b.uid

instance : Hashable VarId where
  hash v := hash v.uid

/-- Strip Lean hygiene suffixes from a variable hint.
    `"a._@.Module._hyg.53"` → `"a"`, `"x._@.Foo._hyg.8.152"` → `"x"` -/
private def sanitizeHint (s : String) : String :=
  -- Drop everything from "._@." onward (Lean hygiene marker)
  match s.splitOn "._@." with
  | base :: _ => if base.isEmpty then "v" else base
  | [] => s

instance : ToString VarId where
  toString v :=
    let h := sanitizeHint v.hint
    if h.isEmpty then s!"v{v.uid}" else s!"{h}_{v.uid}"

inductive Expr
  | Var     : VarId → Expr
  | Lit     : Const × BuiltinType → Expr
  | Builtin : BuiltinFun → Expr
  | Let     : List (VarId × Expr × Bool) → Expr → Expr
  | Fix     : VarId → Expr → Expr
  | Lam     : VarId → Expr → Expr
  | App     : Expr → Expr → Expr
  | Force   : Expr → Expr
  | Delay   : Expr → Expr
  | Constr  : Nat → List Expr → Expr
  | Case    : Expr → List Expr → Expr
  | Error   : Expr
deriving Repr

private def beqExpr : Expr → Expr → Bool
  | .Var a, .Var b => a == b
  | .Lit (c1, t1), .Lit (c2, t2) => c1 == c2 && t1 == t2
  | .Builtin a, .Builtin b => a == b
  | .Let bs1 body1, .Let bs2 body2 =>
    beqBinds bs1 bs2 && beqExpr body1 body2
  | .Fix v1 e1, .Fix v2 e2 => v1 == v2 && beqExpr e1 e2
  | .Lam v1 e1, .Lam v2 e2 => v1 == v2 && beqExpr e1 e2
  | .App f1 a1, .App f2 a2 => beqExpr f1 f2 && beqExpr a1 a2
  | .Force e1, .Force e2 => beqExpr e1 e2
  | .Delay e1, .Delay e2 => beqExpr e1 e2
  | .Constr t1 es1, .Constr t2 es2 =>
    t1 == t2 && beqExprs es1 es2
  | .Case s1 alts1, .Case s2 alts2 =>
    beqExpr s1 s2 && beqExprs alts1 alts2
  | .Error, .Error => true
  | _, _ => false
where
  beqExprs : List Expr → List Expr → Bool
    | [], [] => true
    | a :: as, b :: bs => beqExpr a b && beqExprs as bs
    | _, _ => false
  beqBinds : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Bool
    | [], [] => true
    | (v1, e1, s1) :: as, (v2, e2, s2) :: bs =>
      v1 == v2 && s1 == s2 && beqExpr e1 e2 && beqBinds as bs
    | _, _ => false

instance : BEq Expr where beq := beqExpr

instance : Inhabited Expr where
  default := .Error


/-! ## Alpha Equivalence -/

/-- Alpha-equivalence check. Two expressions are alpha-equivalent when they
differ only in the choice of bound variable names. We maintain a pair of
mappings (left-VarId → depth, right-VarId → depth) to align binders. -/
private abbrev AlphaEnv := List (Nat × Nat)

private def alphaLookup (env : AlphaEnv) (uid : Nat) : Option Nat :=
  match env with
  | [] => none
  | (k, d) :: rest => if k == uid then some d else alphaLookup rest uid

mutual
  private partial def alphaEqCore (envL envR : AlphaEnv) (depth : Nat) : Expr → Expr → Bool
    | .Var a, .Var b =>
      match alphaLookup envL a.uid, alphaLookup envR b.uid with
      | some da, some db => da == db
      | none, none => a == b  -- both free
      | _, _ => false
    | .Lit (c1, t1), .Lit (c2, t2) => c1 == c2 && t1 == t2
    | .Builtin a, .Builtin b => a == b
    | .App f1 a1, .App f2 a2 =>
      alphaEqCore envL envR depth f1 f2 && alphaEqCore envL envR depth a1 a2
    | .Force e1, .Force e2 => alphaEqCore envL envR depth e1 e2
    | .Delay e1, .Delay e2 => alphaEqCore envL envR depth e1 e2
    | .Lam v1 e1, .Lam v2 e2 =>
      alphaEqCore ((v1.uid, depth) :: envL) ((v2.uid, depth) :: envR) (depth + 1) e1 e2
    | .Fix v1 e1, .Fix v2 e2 =>
      alphaEqCore ((v1.uid, depth) :: envL) ((v2.uid, depth) :: envR) (depth + 1) e1 e2
    | .Let bs1 body1, .Let bs2 body2 =>
      alphaEqBinds envL envR depth bs1 bs2 body1 body2
    | .Constr t1 es1, .Constr t2 es2 =>
      t1 == t2 && alphaEqList envL envR depth es1 es2
    | .Case s1 alts1, .Case s2 alts2 =>
      alphaEqCore envL envR depth s1 s2 && alphaEqList envL envR depth alts1 alts2
    | .Error, .Error => true
    | _, _ => false

  private partial def alphaEqList (eL eR : AlphaEnv) (d : Nat) : List Expr → List Expr → Bool
    | [], [] => true
    | a :: as, b :: bs => alphaEqCore eL eR d a b && alphaEqList eL eR d as bs
    | _, _ => false

  private partial def alphaEqBinds (eL eR : AlphaEnv) (d : Nat)
      : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → Expr → Bool
    | [], [], body1, body2 => alphaEqCore eL eR d body1 body2
    | (v1, rhs1, s1) :: rest1, (v2, rhs2, s2) :: rest2, body1, body2 =>
      s1 == s2 && alphaEqCore eL eR d rhs1 rhs2 &&
      alphaEqBinds ((v1.uid, d) :: eL) ((v2.uid, d) :: eR) (d + 1) rest1 rest2 body1 body2
    | _, _, _, _ => false
end

def Expr.alphaEq (a b : Expr) : Bool :=
  alphaEqCore [] [] 0 a b

def Expr.isAtom : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ => true
  | _ => false

def Expr.isValue : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ => true
  | .Lam _ _ | .Delay _ | .Fix _ _ => true
  | _ => false

/-! ## Fresh Variable Supply -/

structure FreshState where
  next : Nat := 0

abbrev FreshM := StateM FreshState

def freshVar (hint : String := "") : FreshM VarId := do
  let s ← get
  set { s with next := s.next + 1 }
  pure ⟨s.next, hint⟩

def runFresh (m : FreshM α) (start : Nat := 0) : α :=
  (m.run ⟨start⟩).1

end Moist.MIR
