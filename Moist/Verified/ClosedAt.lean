import Moist.Plutus.Term
import Moist.Verified.RenameBase

/-! # `closedAt` for UPLC terms (Verified copy)

Self-contained Boolean `closedAt` predicate used throughout the
`Verified` tower. Lives in its own file so `Contextual.lean`,
`Equivalence.lean`, etc. can import it without dragging in heavier
semantic machinery. -/

namespace Moist.Verified

open Moist.Plutus.Term

mutual
  /-- `closedAt d t` — every `.Var n` node in `t` satisfies `n ≤ d`. -/
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

/-! ## Section 4b. Closedness under `shiftRename`

The forward direction: `closedAt k t → closedAt (k+1) (renameTerm (shiftRename 1) t)`.
and its inverse. -/

mutual

theorem closedAt_renameTerm_shiftRename :
    ∀ (t : Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAt k t = true →
      closedAt (k + 1) (renameTerm (shiftRename c) t) = true
  | .Var n, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    by_cases hn : n ≥ c
    · rw [shiftRename_ge hn]; omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [shiftRename_lt hn']; omega
  | .Lam _ body, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    have hlift : liftRename (shiftRename c) =
        shiftRename (c + 1) :=
      liftRename_shiftRename hc1
    rw [hlift]
    exact closedAt_renameTerm_shiftRename body (k + 1) (c + 1) (by omega) (by omega) h
  | .Apply f x, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename f k c hc1 hck h.1,
           closedAt_renameTerm_shiftRename x k c hc1 hck h.2⟩
  | .Force e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename e k c hc1 hck h
  | .Delay e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename e k c hc1 hck h
  | .Constr _ args, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList_shiftRename args k c hc1 hck h
  | .Case scrut alts, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename scrut k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename alts k c hc1 hck h.2⟩
  | .Constant _, _, _, _, _, _ => by simp [closedAt, renameTerm]
  | .Builtin _, _, _, _, _, _ => by simp [closedAt, renameTerm]
  | .Error, _, _, _, _, _ => by simp [closedAt, renameTerm]
termination_by t _ _ _ _ _ => sizeOf t

theorem closedAtList_renameTermList_shiftRename :
    ∀ (ts : List Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAtList k ts = true →
      closedAtList (k + 1)
        (renameTermList (shiftRename c) ts) = true
  | [], _, _, _, _, _ => by simp [closedAtList, renameTermList]
  | t :: rest, k, c, hc1, hck, h => by
    simp only [closedAtList, renameTermList,
               Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename t k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename rest k c hc1 hck h.2⟩
termination_by ts _ _ _ _ _ => sizeOf ts

end

mutual

/-- Inverse direction: `closedAt (k+1) (shiftRename c applied) → closedAt k t`. -/
theorem closedAt_renameTerm_shiftRename_inv :
    ∀ (t : Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAt (k + 1) (renameTerm (shiftRename c) t) = true →
      closedAt k t = true
  | .Var n, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    by_cases hn : n ≥ c
    · rw [shiftRename_ge hn] at h; omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [shiftRename_lt hn'] at h; omega
  | .Lam _ body, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    have hlift : liftRename (shiftRename c) =
        shiftRename (c + 1) :=
      liftRename_shiftRename hc1
    rw [hlift] at h
    exact closedAt_renameTerm_shiftRename_inv body (k + 1) (c + 1) (by omega) (by omega) h
  | .Apply f x, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv f k c hc1 hck h.1,
           closedAt_renameTerm_shiftRename_inv x k c hc1 hck h.2⟩
  | .Force e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename_inv e k c hc1 hck h
  | .Delay e, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_renameTerm_shiftRename_inv e k c hc1 hck h
  | .Constr _ args, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList_shiftRename_inv args k c hc1 hck h
  | .Case scrut alts, k, c, hc1, hck, h => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv scrut k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename_inv alts k c hc1 hck h.2⟩
  | .Constant _, _, _, _, _, _ => by simp [closedAt]
  | .Builtin _, _, _, _, _, _ => by simp [closedAt]
  | .Error, _, _, _, _, _ => by simp [closedAt]
termination_by t _ _ _ _ _ => sizeOf t

theorem closedAtList_renameTermList_shiftRename_inv :
    ∀ (ts : List Term) (k c : Nat), 1 ≤ c → c ≤ k + 1 →
      closedAtList (k + 1)
        (renameTermList (shiftRename c) ts) = true →
      closedAtList k ts = true
  | [], _, _, _, _, _ => by simp [closedAtList]
  | t :: rest, k, c, hc1, hck, h => by
    simp only [closedAtList, renameTermList,
               Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_renameTerm_shiftRename_inv t k c hc1 hck h.1,
           closedAtList_renameTermList_shiftRename_inv rest k c hc1 hck h.2⟩
termination_by ts _ _ _ _ _ => sizeOf ts

end

end Moist.Verified
