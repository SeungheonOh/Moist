import Moist.Verified.SmallStep.StackDischarge
import Moist.Verified.ClosedAt
import Moist.Verified.RenameBase

/-! # de Bruijn substitution metatheory for the discharge/β bridge

Reusable equational lemmas about `renameTerm`/`substTerm` (from
`Moist.Verified.RenameBase`) relative to `closedAt`, leading to the
substitution-swap lemma used by the β step of the forward simulation.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK (CekValue CekEnv)
open Moist.Verified (closedAt closedAtList substTerm substTermList renameTerm renameTermList
  liftRename shiftRename)

/-! ## Renaming / substituting a closed term is a no-op -/

mutual
  /-- A renaming that fixes all indices `≤ d` leaves a `closedAt d` term unchanged. -/
  theorem renameTerm_id_closed : ∀ {d : Nat} {σ : Nat → Nat}, (∀ n, n ≤ d → σ n = n) →
      ∀ {t : Term}, closedAt d t = true → renameTerm σ t = t
    | d, σ, hσ, .Var n, ht => by
      simp only [closedAt] at ht
      simp only [renameTerm, hσ n (of_decide_eq_true ht)]
    | d, σ, hσ, .Lam name body, ht => by
      simp only [closedAt] at ht
      have hσ' : ∀ n, n ≤ d + 1 → liftRename σ n = n := by
        intro n hn
        match n with
        | 0 => rfl
        | 1 => rfl
        | m + 2 => simp only [liftRename]; rw [hσ (m + 1) (by omega)]
      simp only [renameTerm]; rw [renameTerm_id_closed hσ' ht]
    | d, σ, hσ, .Apply f x, ht => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [renameTerm]; rw [renameTerm_id_closed hσ ht.1, renameTerm_id_closed hσ ht.2]
    | d, σ, hσ, .Force e, ht => by
      simp only [closedAt] at ht
      simp only [renameTerm]; rw [renameTerm_id_closed hσ ht]
    | d, σ, hσ, .Delay e, ht => by
      simp only [closedAt] at ht
      simp only [renameTerm]; rw [renameTerm_id_closed hσ ht]
    | d, σ, hσ, .Constr tag args, ht => by
      simp only [closedAt] at ht
      simp only [renameTerm]; rw [renameTermList_id_closed hσ ht]
    | d, σ, hσ, .Case scrut alts, ht => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [renameTerm]
      rw [renameTerm_id_closed hσ ht.1, renameTermList_id_closed hσ ht.2]
    | _, _, _, .Constant _, _ => by simp only [renameTerm]
    | _, _, _, .Builtin _, _ => by simp only [renameTerm]
    | _, _, _, .Error, _ => by simp only [renameTerm]
  termination_by _ _ _ t _ => sizeOf t

  theorem renameTermList_id_closed : ∀ {d : Nat} {σ : Nat → Nat}, (∀ n, n ≤ d → σ n = n) →
      ∀ {ts : List Term}, closedAtList d ts = true → renameTermList σ ts = ts
    | _, _, _, [], _ => by simp only [renameTermList]
    | d, σ, hσ, t :: ts, ht => by
      simp only [closedAtList, Bool.and_eq_true] at ht
      simp only [renameTermList]
      rw [renameTerm_id_closed hσ ht.1, renameTermList_id_closed hσ ht.2]
  termination_by _ _ _ ts _ => sizeOf ts
end

mutual
  /-- Substituting at a position above the closedness bound is a no-op. -/
  theorem substTerm_id_closed : ∀ {d : Nat} {t : Term}, closedAt d t = true →
      ∀ {pos : Nat} {r : Term}, pos > d → substTerm pos r t = t
    | d, .Var n, ht, pos, r, hpos => by
      simp only [closedAt] at ht
      have hn : n ≤ d := of_decide_eq_true ht
      simp only [substTerm]
      rw [if_neg (by omega), if_neg (by omega)]
    | d, .Lam name body, ht, pos, r, hpos => by
      simp only [closedAt] at ht
      simp only [substTerm]
      rw [substTerm_id_closed ht (by omega : pos + 1 > d + 1)]
    | d, .Apply f x, ht, pos, r, hpos => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [substTerm]
      rw [substTerm_id_closed ht.1 hpos, substTerm_id_closed ht.2 hpos]
    | d, .Force e, ht, pos, r, hpos => by
      simp only [closedAt] at ht
      simp only [substTerm]; rw [substTerm_id_closed ht hpos]
    | d, .Delay e, ht, pos, r, hpos => by
      simp only [closedAt] at ht
      simp only [substTerm]; rw [substTerm_id_closed ht hpos]
    | d, .Constr tag args, ht, pos, r, hpos => by
      simp only [closedAt] at ht
      simp only [substTerm]; rw [substTermList_id_closed ht hpos]
    | d, .Case scrut alts, ht, pos, r, hpos => by
      simp only [closedAt, Bool.and_eq_true] at ht
      simp only [substTerm]
      rw [substTerm_id_closed ht.1 hpos, substTermList_id_closed ht.2 hpos]
    | _, .Constant _, _, _, _, _ => by simp only [substTerm]
    | _, .Builtin _, _, _, _, _ => by simp only [substTerm]
    | _, .Error, _, _, _, _ => by simp only [substTerm]
  termination_by _ t _ => sizeOf t

  theorem substTermList_id_closed : ∀ {d : Nat} {ts : List Term}, closedAtList d ts = true →
      ∀ {pos : Nat} {r : Term}, pos > d → substTermList pos r ts = ts
    | _, [], _, _, _, _ => by simp only [substTermList]
    | d, t :: ts, ht, pos, r, hpos => by
      simp only [closedAtList, Bool.and_eq_true] at ht
      simp only [substTermList]
      rw [substTerm_id_closed ht.1 hpos, substTermList_id_closed ht.2 hpos]
  termination_by _ ts _ => sizeOf ts
end

/-- A closed term is unaffected by any substitution (`pos ≥ 1`). -/
theorem substTerm_closed {t : Term} (ht : closedAt 0 t = true) (pos : Nat) (r : Term)
    (hpos : pos ≥ 1) : substTerm pos r t = t :=
  substTerm_id_closed ht (by omega)

/-- A closed term is unaffected by the `shiftRename 1` shift. -/
theorem renameTerm_shift_closed {r : Term} (hr : closedAt 0 r = true) :
    renameTerm (shiftRename 1) r = r :=
  renameTerm_id_closed (fun n hn => by
    have : n = 0 := by omega
    subst this; simp [shiftRename]) hr

/-! ## Substitution swap (for the β step)

`substTerm` unfolded on a variable. -/

theorem substTerm_var (pos : Nat) (r : Term) (n : Nat) :
    substTerm pos r (.Var n)
      = if n = pos then r else if n > pos then .Var (n - 1) else .Var n := by
  simp only [substTerm]

mutual
  /-- Swapping two substitutions of closed terms at adjacent positions.
      The key algebraic fact behind the β step of the forward simulation:
      iterated environment discharge commutes with the β substitution. -/
  theorem subst_swap_closed {r s : Term} (hr : closedAt 0 r = true) (hs : closedAt 0 s = true) :
      ∀ (p : Nat), p ≥ 1 → ∀ (t : Term),
        substTerm p r (substTerm (p + 1) s t) = substTerm p s (substTerm p r t)
    | p, hp, .Var n => by
      by_cases h1 : n = p + 1
      · subst h1
        rw [show substTerm (p + 1) s (Term.Var (p + 1)) = s by rw [substTerm_var, if_pos rfl],
            substTerm_closed hs p r (by omega),
            show substTerm p r (Term.Var (p + 1)) = Term.Var (p + 1 - 1) by
              rw [substTerm_var, if_neg (by omega), if_pos (by omega)],
            show substTerm p s (Term.Var (p + 1 - 1)) = s by
              rw [substTerm_var, if_pos (by omega)]]
      · by_cases h3 : n > p + 1
        · rw [show substTerm (p + 1) s (Term.Var n) = Term.Var (n - 1) by
                rw [substTerm_var, if_neg h1, if_pos h3],
              show substTerm p r (Term.Var (n - 1)) = Term.Var (n - 1 - 1) by
                rw [substTerm_var, if_neg (by omega), if_pos (by omega)],
              show substTerm p r (Term.Var n) = Term.Var (n - 1) by
                rw [substTerm_var, if_neg (by omega), if_pos (by omega)],
              show substTerm p s (Term.Var (n - 1)) = Term.Var (n - 1 - 1) by
                rw [substTerm_var, if_neg (by omega), if_pos (by omega)]]
        · by_cases h2 : n = p
          · rw [show substTerm (p + 1) s (Term.Var n) = Term.Var n by
                  rw [substTerm_var, if_neg (by omega), if_neg (by omega)],
                show substTerm p r (Term.Var n) = r by rw [substTerm_var, if_pos h2],
                substTerm_closed hr p s (by omega)]
          · rw [show substTerm (p + 1) s (Term.Var n) = Term.Var n by
                  rw [substTerm_var, if_neg h1, if_neg (by omega)],
                show substTerm p r (Term.Var n) = Term.Var n by
                  rw [substTerm_var, if_neg h2, if_neg (by omega)],
                show substTerm p s (Term.Var n) = Term.Var n by
                  rw [substTerm_var, if_neg h2, if_neg (by omega)]]
    | p, hp, .Lam name body => by
      simp only [substTerm, renameTerm_shift_closed hr, renameTerm_shift_closed hs]
      exact congrArg (Term.Lam name) (subst_swap_closed hr hs (p + 1) (by omega) body)
    | p, hp, .Apply f x => by
      simp only [substTerm]
      rw [subst_swap_closed hr hs p hp f, subst_swap_closed hr hs p hp x]
    | p, hp, .Force e => by
      simp only [substTerm]; rw [subst_swap_closed hr hs p hp e]
    | p, hp, .Delay e => by
      simp only [substTerm]; rw [subst_swap_closed hr hs p hp e]
    | p, hp, .Constr tag args => by
      simp only [substTerm]; rw [substList_swap_closed hr hs p hp args]
    | p, hp, .Case scrut alts => by
      simp only [substTerm]
      rw [subst_swap_closed hr hs p hp scrut, substList_swap_closed hr hs p hp alts]
    | _, _, .Constant _ => by simp only [substTerm]
    | _, _, .Builtin _ => by simp only [substTerm]
    | _, _, .Error => by simp only [substTerm]
  termination_by _ _ t => sizeOf t

  theorem substList_swap_closed {r s : Term} (hr : closedAt 0 r = true) (hs : closedAt 0 s = true) :
      ∀ (p : Nat), p ≥ 1 → ∀ (ts : List Term),
        substTermList p r (substTermList (p + 1) s ts) = substTermList p s (substTermList p r ts)
    | _, _, [] => by simp only [substTermList]
    | p, hp, t :: ts => by
      simp only [substTermList]
      rw [subst_swap_closed hr hs p hp t, substList_swap_closed hr hs p hp ts]
  termination_by _ _ ts => sizeOf ts
end

/-! ## β-step discharge commutation -/

/-- Every value bound in the environment discharges to a closed term. -/
def EnvDischargeClosed : CekEnv → Prop
  | .nil => True
  | .cons v rest => closedAt 0 (discharge v) = true ∧ EnvDischargeClosed rest

/-- The β substitution (at position 1) commutes with discharging an
    environment under one preserved binder. -/
theorem dischargeEnv_subst_comm {r : Term} (hr : closedAt 0 r = true) :
    ∀ (ρ : CekEnv), EnvDischargeClosed ρ → ∀ (body : Term),
      substTerm 1 r (dischargeEnv ρ 1 body) = dischargeEnv ρ 0 (substTerm 1 r body)
  | .nil, _, body => by simp only [dischargeEnv]
  | .cons v rest, hρ, body => by
    simp only [dischargeEnv]
    rw [dischargeEnv_subst_comm hr rest hρ.2 (substTerm (1 + 1) (discharge v) body)]
    congr 1
    exact subst_swap_closed hr hρ.1 1 (by omega) body

/-- The β step at the discharge level: substituting the discharged argument into
    the discharged lambda body equals discharging the extended environment. -/
theorem beta_discharge {vx : CekValue} {ρ : CekEnv} {body : Term}
    (hvx : closedAt 0 (discharge vx) = true) (hρ : EnvDischargeClosed ρ) :
    substTerm 1 (discharge vx) (dischargeEnv ρ 1 body) = dischargeEnv (ρ.extend vx) 0 body := by
  rw [dischargeEnv_subst_comm hvx ρ hρ body]
  simp only [CekEnv.extend, dischargeEnv]

end Moist.Verified.SmallStep
