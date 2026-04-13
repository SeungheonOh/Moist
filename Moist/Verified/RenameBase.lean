import Moist.Plutus.Term

namespace Moist.Verified

open Moist.Plutus.Term

/-! # Variable Renaming for UPLC Terms (base definitions)

A renaming `σ : Nat → Nat` maps variable indices to variable indices.
`renameTerm σ t` applies the renaming to every `Var` node in `t`,
adjusting under binders via `liftRename`.

The key identity is `renameTerm id t = t`: the identity renaming
is a no-op. This lets the generalized bisimulation (parameterized
by `σ`) recover the original same-term bisimulation as the `σ = id`
special case.
-/

/-! ## liftRename: adjust a renaming under a binder

The CEK machine uses 1-based de Bruijn indices:
- Position 0 is always unused (`lookup _ 0 = none`)
- Position 1 is the most recently bound variable
- Position `n + 1` is the previous binding

When going under a `Lam`, the new binder occupies position 1,
and all previous positions shift up by 1. `liftRename σ` preserves
position 1 (the new binder) and shifts the rest through `σ`:

    liftRename σ 0       = 0        (invalid position, preserved)
    liftRename σ 1       = 1        (the new lambda binding)
    liftRename σ (n + 1) = σ n + 1  (outer variables shifted through σ)
-/
def liftRename (σ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => σ (n + 1) + 1

theorem liftRename_id : liftRename id = id := by
  funext n; cases n with
  | zero => rfl
  | succ m => cases m with
    | zero => rfl
    | succ k => simp [liftRename, id]

/-! ## renameTerm: apply a renaming to a UPLC term -/

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

/-! ## renameTerm id = id -/

mutual
  theorem renameTerm_id (t : Term) : renameTerm id t = t := by
    cases t with
    | Var n => simp [renameTerm]
    | Lam name body =>
      simp only [renameTerm]; rw [liftRename_id]; exact congrArg _ (renameTerm_id body)
    | Apply f x =>
      simp only [renameTerm]; rw [renameTerm_id f, renameTerm_id x]
    | Force e => simp only [renameTerm]; exact congrArg _ (renameTerm_id e)
    | Delay e => simp only [renameTerm]; exact congrArg _ (renameTerm_id e)
    | Constr tag args =>
      simp only [renameTerm]; exact congrArg _ (renameTermList_id args)
    | Case scrut alts =>
      simp only [renameTerm]; rw [renameTerm_id scrut, renameTermList_id alts]
    | Constant _ => rfl
    | Builtin _ => rfl
    | Error => rfl
  termination_by sizeOf t

  theorem renameTermList_id (ts : List Term) : renameTermList id ts = ts := by
    cases ts with
    | nil => rfl
    | cons t rest =>
      simp only [renameTermList]; rw [renameTerm_id t, renameTermList_id rest]
  termination_by sizeOf ts
end

/-! ## renameTermList structural lemmas -/

theorem renameTermList_length (σ : Nat → Nat) (ts : List Term) :
    (renameTermList σ ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons _ _ ih => simp [renameTermList, ih]

theorem renameTermList_getElem (σ : Nat → Nat) (ts : List Term) (i : Nat)
    (hi : i < ts.length) :
    (renameTermList σ ts)[i]'(by rw [renameTermList_length]; exact hi) =
    renameTerm σ (ts[i]) := by
  induction ts generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    cases i with
    | zero => simp [renameTermList]
    | succ j =>
      simp only [renameTermList, List.getElem_cons_succ]
      exact ih j (by simp at hi; omega)

/-! ## shiftRename: insert a gap at a cutoff position -/

/-- `shiftRename c n` inserts a gap at position `c`: indices ≥ c are
    incremented by 1, indices below `c` are unchanged. For the dead-let
    use case, `shiftRename 1` maps every 1-based variable index `n` to
    `n + 1`, which is the effect of prepending an unused binding. -/
def shiftRename (c : Nat) (n : Nat) : Nat :=
  if n ≥ c then n + 1 else n

@[simp] theorem shiftRename_ge {c n : Nat} (h : n ≥ c) : shiftRename c n = n + 1 := by
  simp [shiftRename, h]

@[simp] theorem shiftRename_lt {c n : Nat} (h : n < c) : shiftRename c n = n := by
  simp [shiftRename, Nat.not_le.mpr h]

/-- liftRename of shiftRename c equals shiftRename (c + 1) when c ≥ 1.
    Under a binder, the gap position shifts up by 1. -/
theorem liftRename_shiftRename {c : Nat} (hc : c ≥ 1) :
    liftRename (shiftRename c) = shiftRename (c + 1) := by
  funext n; cases n with
  | zero => simp [liftRename, shiftRename]
  | succ m => cases m with
    | zero =>
      simp only [liftRename, shiftRename]
      have : ¬ (c ≤ 0) := by omega
      simp [this]
    | succ k =>
      simp only [liftRename, shiftRename]
      split <;> split <;> omega

/-! ## substTerm: total UPLC-level substitution (open semantics)

`substTerm pos replacement t` substitutes the variable at de Bruijn position
`pos` in `t` with `replacement`, AND decrements variables at positions
`> pos` (because the binder at `pos` is being removed by the substitution).

When the substitution descends under a binder, `pos` increments by 1
(because the new binder occupies position 1, shifting our target up) and
`replacement` is shifted by `shiftRename 1` to track the new binding.

This is the standard "open substitution" used in β-reduction:
`(λ x. body) v` β-reduces to `body[x := v]` where the `x` binder is gone
and references to outer binders shift down.
-/

mutual
  /-- Total UPLC substitution with open semantics. -/
  def substTerm (pos : Nat) (replacement : Term) : Term → Term
    | .Var n =>
      if n = pos then replacement
      else if n > pos then .Var (n - 1)
      else .Var n
    | .Lam name body =>
      .Lam name (substTerm (pos + 1) (renameTerm (shiftRename 1) replacement) body)
    | .Apply f a => .Apply (substTerm pos replacement f) (substTerm pos replacement a)
    | .Force e => .Force (substTerm pos replacement e)
    | .Delay e => .Delay (substTerm pos replacement e)
    | .Constr tag args => .Constr tag (substTermList pos replacement args)
    | .Case scrut alts =>
      .Case (substTerm pos replacement scrut) (substTermList pos replacement alts)
    | .Constant c => .Constant c
    | .Builtin b => .Builtin b
    | .Error => .Error
  termination_by t => sizeOf t

  def substTermList (pos : Nat) (replacement : Term) : List Term → List Term
    | [] => []
    | t :: ts => substTerm pos replacement t :: substTermList pos replacement ts
  termination_by ts => sizeOf ts
end

/-- `substTermList` preserves length. -/
theorem substTermList_length (pos : Nat) (replacement : Term) (ts : List Term) :
    (substTermList pos replacement ts).length = ts.length := by
  induction ts with
  | nil => simp [substTermList]
  | cons _ _ ih => simp [substTermList, ih]

end Moist.Verified
