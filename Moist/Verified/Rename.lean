import Moist.Verified.RenameBase
import Moist.Verified.ClosedAt

namespace Moist.Verified

open Moist.Plutus.Term

/-! # Variable Renaming for UPLC Terms (closedAt-dependent theorems)

This module re-exports the core renaming definitions from `RenameBase`
and adds theorems that depend on `closedAt` from `ClosedAt.lean`.
-/

/-! ## closedAt is preserved by renamings that respect the bound -/

mutual
  theorem closedAt_rename {d d' : Nat} {σ : Nat → Nat}
      (hσ : ∀ n, n ≤ d → σ n ≤ d')
      {t : Term} (h : closedAt d t = true) :
      closedAt d' (renameTerm σ t) = true := by
    cases t with
    | Var n =>
      simp only [renameTerm, closedAt]
      have hle := of_decide_eq_true (by rw [closedAt.eq_1] at h; exact h)
      exact decide_eq_true (hσ n hle)
    | Lam name body =>
      simp only [renameTerm, closedAt]
      rw [closedAt.eq_2] at h
      exact closedAt_rename (σ := liftRename σ) (d := d + 1) (d' := d' + 1)
        (fun n hle => by
          cases n with
          | zero => simp [liftRename]
          | succ m => cases m with
            | zero => simp [liftRename]
            | succ k =>
              simp only [liftRename]
              have := hσ (k + 1) (by omega)
              omega) h
    | Apply f x =>
      have ⟨hf, hx⟩ := closedAt_apply h
      show closedAt d' (.Apply (renameTerm σ f) (renameTerm σ x)) = true
      rw [closedAt.eq_3, Bool.and_eq_true]
      exact ⟨closedAt_rename hσ hf, closedAt_rename hσ hx⟩
    | Force e =>
      simp only [renameTerm, closedAt]
      exact closedAt_rename hσ (by rw [closedAt.eq_4] at h; exact h)
    | Delay e =>
      simp only [renameTerm, closedAt]
      exact closedAt_rename hσ (by rw [closedAt.eq_5] at h; exact h)
    | Constr tag args =>
      simp only [renameTerm, closedAt]
      exact closedAtList_rename hσ (by rw [closedAt.eq_6] at h; exact h)
    | Case scrut alts =>
      have ⟨hs, ha⟩ := closedAt_case h
      show closedAt d' (.Case (renameTerm σ scrut) (renameTermList σ alts)) = true
      rw [closedAt.eq_7, Bool.and_eq_true]
      exact ⟨closedAt_rename hσ hs, closedAtList_rename hσ ha⟩
    | Constant _ => simp [renameTerm, closedAt]
    | Builtin _ => simp [renameTerm, closedAt]
    | Error => simp [renameTerm, closedAt]
  termination_by sizeOf t

  theorem closedAtList_rename {d d' : Nat} {σ : Nat → Nat}
      (hσ : ∀ n, n ≤ d → σ n ≤ d')
      {ts : List Term} (h : closedAtList d ts = true) :
      closedAtList d' (renameTermList σ ts) = true := by
    cases ts with
    | nil => simp [renameTermList, closedAtList]
    | cons t rest =>
      have ⟨ht, hr⟩ := closedAt_constr_cons h
      show closedAtList d' (renameTerm σ t :: renameTermList σ rest) = true
      rw [closedAtList.eq_2, Bool.and_eq_true]
      exact ⟨closedAt_rename hσ ht, closedAtList_rename hσ hr⟩
  termination_by sizeOf ts
end

end Moist.Verified
