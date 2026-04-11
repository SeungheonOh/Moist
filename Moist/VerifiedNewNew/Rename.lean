import Moist.Plutus.Term

/-! # Variable Renaming and ClosedAt (vendored into VerifiedNewNew)

Re-defines the UPLC term renaming infrastructure and `closedAt` predicate
directly in the `VerifiedNewNew` namespace, avoiding cross-imports from
`Moist.Verified`. These are small, self-contained definitions.
-/

namespace Moist.VerifiedNewNew

open Moist.Plutus.Term

/-! ## liftRename -/

def liftRename (σ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => σ (n + 1) + 1

theorem liftRename_id : liftRename id = id := by
  funext n; cases n with
  | zero => rfl
  | succ m => cases m with | zero => rfl | succ k => simp [liftRename, id]

/-! ## renameTerm -/

mutual
  def renameTerm (σ : Nat → Nat) : Term → Term
    | .Var n => .Var (σ n)
    | .Lam name body => .Lam name (renameTerm (liftRename σ) body)
    | .Apply f x => .Apply (renameTerm σ f) (renameTerm σ x)
    | .Force e => .Force (renameTerm σ e)
    | .Delay e => .Delay (renameTerm σ e)
    | .Constr tag args => .Constr tag (renameTermList σ args)
    | .Case scrut alts => .Case (renameTerm σ scrut) (renameTermList σ alts)
    | .Constant c => .Constant c
    | .Builtin b => .Builtin b
    | .Error => .Error

  def renameTermList (σ : Nat → Nat) : List Term → List Term
    | [] => []
    | t :: ts => renameTerm σ t :: renameTermList σ ts
end

/-! ## shiftRename -/

def shiftRename (c : Nat) (n : Nat) : Nat :=
  if n ≥ c then n + 1 else n

@[simp] theorem shiftRename_ge {c n : Nat} (h : n ≥ c) : shiftRename c n = n + 1 := by
  simp [shiftRename, h]

@[simp] theorem shiftRename_lt {c n : Nat} (h : n < c) : shiftRename c n = n := by
  simp [shiftRename, Nat.not_le.mpr h]

theorem liftRename_shiftRename {c : Nat} (hc : c ≥ 1) :
    liftRename (shiftRename c) = shiftRename (c + 1) := by
  funext n; cases n with
  | zero => simp [liftRename, shiftRename]
  | succ m => cases m with
    | zero =>
      simp only [liftRename]
      have : ¬(0 + 1 ≥ c + 1) := by omega
      simp [shiftRename, this]
    | succ k =>
      simp only [liftRename, shiftRename]
      split <;> split <;> omega

/-! ## closedAt -/

mutual
  def closedAt (d : Nat) (t : Term) : Bool := match t with
    | .Var n => decide (n ≤ d)
    | .Lam _ body => closedAt (d + 1) body
    | .Apply f x => closedAt d f && closedAt d x
    | .Force e | .Delay e => closedAt d e
    | .Constr _ args => closedAtList d args
    | .Case scrut alts => closedAt d scrut && closedAtList d alts
    | .Constant _ | .Builtin _ | .Error => true
  termination_by sizeOf t

  def closedAtList (d : Nat) (ts : List Term) : Bool := match ts with
    | [] => true
    | t :: rest => closedAt d t && closedAtList d rest
  termination_by sizeOf ts
end


end Moist.VerifiedNewNew
