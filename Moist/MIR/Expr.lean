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

instance : ToString VarId where
  toString v := if v.hint.isEmpty then s!"v{v.uid}" else s!"{v.hint}_{v.uid}"

inductive Expr
  | Var     : VarId → Expr
  | Lit     : Const × BuiltinType → Expr
  | Builtin : BuiltinFun → Expr
  | Let     : List (VarId × Expr) → Expr → Expr
  | Fix     : VarId → Expr → Expr
  | Lam     : VarId → Expr → Expr
  | App     : Expr → Expr → Expr
  | Force   : Expr → Expr
  | Delay   : Expr → Expr
  | Constr  : Nat → List Expr → Expr
  | Case    : Expr → List Expr → Expr
  | Error   : Expr
deriving Repr

instance : Inhabited Expr where
  default := .Error

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
