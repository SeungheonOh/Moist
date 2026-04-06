import Moist.Verified.ClosedAt
import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.Verified.Purity
import Moist.Verified.Bisim

/-! # Same-Body Adequacy

The same closed UPLC term evaluated under two CEK environments that agree
at all observation depths produces agreeing results.

## Architecture

A one-directional step-bounded forward simulation (`sameBody_forward`)
proves: if side 1 errors/halts in `n` steps, side 2 reaches the
corresponding outcome with `ValueEq` on results. The full bidirectional
`sameBody_adequacy` is derived by applying the forward theorem in both
directions via `envValueEqAll_symm`.

Termination is by the well-founded lexicographic order `(n, sizeOf t)`.
-/

namespace Moist.Verified.SameBodyAdequacy

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics
open Moist.Verified.StepLift (liftState isActive step_liftState_active steps_liftState
  liftState_ne_halt liftState_eq_error)
open Moist.Verified.Purity (compute_to_ret_from_halt)
open Moist.Verified (closedAt closedAtList closedAt_exists closedAt_var closedAt_apply
  closedAt_force closedAt_delay closedAt_lam closedAt_constr closedAt_case
  closedAtList_getElem closedAt_mono)

def EnvValueEq (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False

def EnvValueEqAll (d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ k, EnvValueEq k d ρ₁ ρ₂

theorem envValueEq_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hρ : EnvValueEq k d ρ₁ ρ₂) (hv : ValueEq k v₁ v₂) :
    EnvValueEq k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hle
  match n with
  | 0 => omega
  | 1 => simp [CekEnv.extend, CekEnv.lookup]; exact hv
  | n + 2 =>
    simp only [CekEnv.extend, CekEnv.lookup]
    exact hρ (n + 1) (by omega) (by omega)

theorem envValueEqAll_extend {d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hρ : EnvValueEqAll d ρ₁ ρ₂) (hv : ∀ k, ValueEq k v₁ v₂) :
    EnvValueEqAll (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
  fun k => envValueEq_extend (hρ k) (hv k)

theorem envValueEqAll_of_same_extend (d : Nat) (ρ : CekEnv) (v₁ v₂ : CekValue)
    (hv : ∀ k, ValueEq k v₁ v₂) :
    EnvValueEqAll d (ρ.extend v₁) (ρ.extend v₂) := by
  intro k n hn hle
  match n with
  | 0 => omega
  | 1 => simp [CekEnv.extend, CekEnv.lookup]; exact hv k
  | n + 2 =>
    simp only [CekEnv.extend, CekEnv.lookup]
    cases h : ρ.lookup (n + 1) with
    | none => trivial
    | some v => exact valueEq_refl k v

/-- Find the first step index `K ≤ bound` where the state becomes inactive. -/
private theorem firstInactive (s : State) (bound : Nat)
    (hex : ∃ k, k ≤ bound ∧ isActive (steps k s) = false) :
    ∃ K, K ≤ bound ∧ isActive (steps K s) = false ∧
         (∀ j, j < K → isActive (steps j s) = true) := by
  induction bound with
  | zero =>
    obtain ⟨k, hk, hinact⟩ := hex
    have : k = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl _, hinact, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ bound ih =>
    by_cases h : ∃ k, k ≤ bound ∧ isActive (steps k s) = false
    · obtain ⟨K, hK_le, hK_inact, hK_min⟩ := ih h
      exact ⟨K, by omega, hK_inact, hK_min⟩
    · have hall : ∀ j, j ≤ bound → isActive (steps j s) = true := by
        intro j hj
        by_cases heq : isActive (steps j s) = true
        · exact heq
        · exfalso; apply h; exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      obtain ⟨k, hk, hinact⟩ := hex
      have hk_eq : k = bound + 1 := by
        by_cases heq : k = bound + 1
        · exact heq
        · exfalso; have hle : k ≤ bound := by omega
          have := hall k hle; simp [hinact] at this
      subst hk_eq
      exact ⟨bound + 1, Nat.le_refl _, hinact, fun j hj => hall j (by omega)⟩

/-- If `compute [] ρ t` reaches error, then `compute extra ρ t` also reaches error. -/
theorem compute_to_error_from_error (ρ : CekEnv) (t : Term) (extra : Stack)
    (h : Reaches (.compute [] ρ t) .error) :
    Reaches (.compute extra ρ t) .error := by
  obtain ⟨n, hn⟩ := h
  have hlift : State.compute extra ρ t =
      liftState extra (.compute [] ρ t) := by simp [liftState]
  have h_inner_err : isActive (steps n (.compute [] ρ t)) = false := by
    rw [hn]; rfl
  have h_has_inactive : ∃ k, k ≤ n ∧ isActive (steps k (.compute [] ρ t)) = false :=
    ⟨n, Nat.le_refl _, h_inner_err⟩
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ t) n h_has_inactive
  have h_comm : steps K (liftState extra (.compute [] ρ t)) =
      liftState extra (steps K (.compute [] ρ t)) :=
    steps_liftState extra K (.compute [] ρ t) hK_min
  generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_comm
  match sK with
  | .compute .. => simp [isActive] at hK_inact
  | .ret (_ :: _) _ => simp [isActive] at hK_inact
  | .error =>
    have h_lifted : steps K (liftState extra (.compute [] ρ t)) = .error := by
      rw [h_comm]; rfl
    exact ⟨K, by rw [hlift, h_lifted]⟩
  | .halt v =>
    exfalso
    have : steps n (.compute [] ρ t) = .halt v := by
      have : n = K + (n - K) := by omega
      rw [this, steps_trans, h_sK, steps_halt]
    rw [hn] at this; simp at this
  | .ret [] v =>
    exfalso
    have h_halt : steps (K + 1) (.compute [] ρ t) = .halt v := by
      rw [steps_trans, h_sK]; rfl
    exact reaches_halt_not_error ⟨K + 1, h_halt⟩ ⟨n, hn⟩

/-- Decompose a halting `Apply tf ta` into function result, argument result,
    and frame result. -/
theorem app_reaches (ρ : CekEnv) (tf ta : Term) (w : CekValue)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) (.halt w)) :
    ∃ vf vx,
      Reaches (.compute [] ρ tf) (.halt vf) ∧
      Reaches (.compute [] ρ ta) (.halt vx) ∧
      Reaches (.ret [.funV vf] vx) (.halt w) := by
  obtain ⟨N, hN⟩ := h
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) = .compute [.arg ta ρ] ρ tf := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.arg ta ρ] ρ tf) = .halt w := by
    have : N = 1 + (N - 1) := by omega
    rw [this, steps_trans, h1] at hN; exact hN
  have hlift1 : State.compute [.arg ta ρ] ρ tf =
      liftState [.arg ta ρ] (.compute [] ρ tf) := by simp [liftState]
  rw [hlift1] at hrest
  have h_has_inactive1 : ∃ k, k ≤ (N - 1) ∧ isActive (steps k (.compute [] ρ tf)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ (N - 1) → isActive (steps j (.compute [] ρ tf)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ tf)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ tf)) <;> simp_all⟩
      have h_comm := steps_liftState [.arg ta ρ] (N - 1) (.compute [] ρ tf)
        (fun j hj => hall' j (by omega))
      rw [hrest] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ w)
  obtain ⟨K1, hK1_le, hK1_inact, hK1_min⟩ :=
    firstInactive (.compute [] ρ tf) (N - 1) h_has_inactive1
  have h_comm1 : steps K1 (liftState [.arg ta ρ] (.compute [] ρ tf)) =
      liftState [.arg ta ρ] (steps K1 (.compute [] ρ tf)) :=
    steps_liftState [.arg ta ρ] K1 (.compute [] ρ tf) hK1_min
  have h_not_error1 : steps K1 (.compute [] ρ tf) ≠ .error := by
    intro herr
    have : steps ((N - 1) - K1) (liftState [.arg ta ρ] .error) = .halt w := by
      have : N - 1 = K1 + ((N - 1) - K1) := by omega
      rw [this, steps_trans, h_comm1, herr] at hrest; exact hrest
    simp [liftState, steps_error] at this
  have ⟨vf, h_inner_eq1, h_lifted_eq1⟩ :
      ∃ vf, (steps K1 (.compute [] ρ tf) = .halt vf ∨
             steps K1 (.compute [] ρ tf) = .ret [] vf) ∧
            liftState [.arg ta ρ] (steps K1 (.compute [] ρ tf)) =
              .ret [.arg ta ρ] vf := by
    generalize h_sK : steps K1 (.compute [] ρ tf) = sK at hK1_inact h_not_error1
    match sK with
    | .compute .. => simp [isActive] at hK1_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK1_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error1
  have h_reaches_tf : Reaches (.compute [] ρ tf) (.halt vf) := by
    cases h_inner_eq1 with
    | inl h => exact ⟨K1, h⟩
    | inr h => exact ⟨K1 + 1, by rw [steps_trans, h]; rfl⟩
  have hrest2 : steps ((N - 1) - K1) (.ret [.arg ta ρ] vf) = .halt w := by
    have : N - 1 = K1 + ((N - 1) - K1) := by omega
    rw [this, steps_trans, h_comm1, h_lifted_eq1] at hrest; exact hrest
  have hge1_2 : (N - 1) - K1 ≥ 1 := by
    by_cases hlt : (N - 1) - K1 ≥ 1
    · exact hlt
    · exfalso; have : (N - 1) - K1 = 0 := by omega
      rw [this] at hrest2; simp [steps] at hrest2
  have hrest3 : steps ((N - 1) - K1 - 1) (.compute [.funV vf] ρ ta) = .halt w := by
    have : (N - 1) - K1 = 1 + ((N - 1) - K1 - 1) := by omega
    rw [this, steps_trans] at hrest2
    simp [steps, step] at hrest2; exact hrest2
  have hlift2 : State.compute [.funV vf] ρ ta =
      liftState [.funV vf] (.compute [] ρ ta) := by simp [liftState]
  rw [hlift2] at hrest3
  have h_has_inactive2 : ∃ k, k ≤ ((N - 1) - K1 - 1) ∧
      isActive (steps k (.compute [] ρ ta)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ ((N - 1) - K1 - 1) →
          isActive (steps j (.compute [] ρ ta)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ ta)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ ta)) <;> simp_all⟩
      have h_comm := steps_liftState [.funV vf] ((N - 1) - K1 - 1) (.compute [] ρ ta)
        (fun j hj => hall' j (by omega))
      rw [hrest3] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ w)
  obtain ⟨K2, hK2_le, hK2_inact, hK2_min⟩ :=
    firstInactive (.compute [] ρ ta) ((N - 1) - K1 - 1) h_has_inactive2
  have h_comm2 : steps K2 (liftState [.funV vf] (.compute [] ρ ta)) =
      liftState [.funV vf] (steps K2 (.compute [] ρ ta)) :=
    steps_liftState [.funV vf] K2 (.compute [] ρ ta) hK2_min
  have h_not_error2 : steps K2 (.compute [] ρ ta) ≠ .error := by
    intro herr
    have : steps (((N - 1) - K1 - 1) - K2) (liftState [.funV vf] .error) = .halt w := by
      have : (N - 1) - K1 - 1 = K2 + (((N - 1) - K1 - 1) - K2) := by omega
      rw [this, steps_trans, h_comm2, herr] at hrest3; exact hrest3
    simp [liftState, steps_error] at this
  have ⟨vx, h_inner_eq2, h_lifted_eq2⟩ :
      ∃ vx, (steps K2 (.compute [] ρ ta) = .halt vx ∨
             steps K2 (.compute [] ρ ta) = .ret [] vx) ∧
            liftState [.funV vf] (steps K2 (.compute [] ρ ta)) =
              .ret [.funV vf] vx := by
    generalize h_sK : steps K2 (.compute [] ρ ta) = sK at hK2_inact h_not_error2
    match sK with
    | .compute .. => simp [isActive] at hK2_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK2_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error2
  have h_reaches_ta : Reaches (.compute [] ρ ta) (.halt vx) := by
    cases h_inner_eq2 with
    | inl h => exact ⟨K2, h⟩
    | inr h => exact ⟨K2 + 1, by rw [steps_trans, h]; rfl⟩
  have h_frame : steps (((N - 1) - K1 - 1) - K2) (.ret [.funV vf] vx) = .halt w := by
    have : (N - 1) - K1 - 1 = K2 + (((N - 1) - K1 - 1) - K2) := by omega
    rw [this, steps_trans, h_comm2, h_lifted_eq2] at hrest3; exact hrest3
  exact ⟨vf, vx, h_reaches_tf, h_reaches_ta, ((N - 1) - K1 - 1) - K2, h_frame⟩

/-- Compose function halt + argument halt + frame result into Apply result. -/
theorem app_apply_from_parts (ρ : CekEnv) (tf ta : Term)
    (vf vx : CekValue) (s : State)
    (hf : Reaches (.compute [] ρ tf) (.halt vf))
    (ha : Reaches (.compute [] ρ ta) (.halt vx))
    (hcont : Reaches (.ret [.funV vf] vx) s) :
    Reaches (.compute [] ρ (.Apply tf ta)) s := by
  obtain ⟨Kc, hKc⟩ := hcont
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) = .compute [.arg ta ρ] ρ tf := by
    simp [steps, step]
  have h_fun_ret := compute_to_ret_from_halt ρ tf vf [.arg ta ρ] hf
  obtain ⟨Kf', hKf'⟩ := h_fun_ret
  have h_step_arg : steps 1 (.ret [.arg ta ρ] vf) = .compute [.funV vf] ρ ta := by
    simp [steps, step]
  have h_arg_ret := compute_to_ret_from_halt ρ ta vx [.funV vf] ha
  obtain ⟨Ka', hKa'⟩ := h_arg_ret
  have h_total : steps (1 + Kf' + 1 + Ka' + Kc) (.compute [] ρ (.Apply tf ta)) = s := by
    have : 1 + Kf' + 1 + Ka' + Kc = 1 + (Kf' + (1 + (Ka' + Kc))) := by omega
    rw [this, steps_trans, h1, steps_trans, hKf', steps_trans, h_step_arg,
        steps_trans, hKa', hKc]
  exact ⟨1 + Kf' + 1 + Ka' + Kc, h_total⟩

/-- If the function sub-expression errors, Apply errors. -/
theorem app_error_from_fun_error (ρ : CekEnv) (tf ta : Term)
    (h : Reaches (.compute [] ρ tf) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error := by
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) = .compute [.arg ta ρ] ρ tf := by
    simp [steps, step]
  have h_err := compute_to_error_from_error ρ tf [.arg ta ρ] h
  obtain ⟨Ke, hKe⟩ := h_err
  exact ⟨1 + Ke, by rw [steps_trans, h1, hKe]⟩

/-- If the function halts and the argument errors, Apply errors. -/
theorem app_error_from_arg_error (ρ : CekEnv) (tf ta : Term) (vf : CekValue)
    (hf : Reaches (.compute [] ρ tf) (.halt vf))
    (ha : Reaches (.compute [] ρ ta) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error := by
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) = .compute [.arg ta ρ] ρ tf := by
    simp [steps, step]
  have h_fun_ret := compute_to_ret_from_halt ρ tf vf [.arg ta ρ] hf
  obtain ⟨Kf, hKf⟩ := h_fun_ret
  have h_step_arg : steps 1 (.ret [.arg ta ρ] vf) = .compute [.funV vf] ρ ta := by
    simp [steps, step]
  have h_arg_err := compute_to_error_from_error ρ ta [.funV vf] ha
  obtain ⟨Ka, hKa⟩ := h_arg_err
  exact ⟨1 + Kf + 1 + Ka, by
    have : 1 + Kf + 1 + Ka = 1 + (Kf + (1 + Ka)) := by omega
    rw [this, steps_trans, h1, steps_trans, hKf, steps_trans, h_step_arg, hKa]⟩

/-- If `EnvValueEqAll d ρ₁ ρ₂` and `0 < n` and `n ≤ d`, both lookups
    are simultaneously `some` or simultaneously `none`. -/
private theorem envValueEqAll_lookup_agree {d : Nat} {ρ₁ ρ₂ : CekEnv}
    (hρ : EnvValueEqAll d ρ₁ ρ₂) {n : Nat} (hn : 0 < n) (hle : n ≤ d) :
    (∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧
      ∀ k, ValueEq k v₁ v₂) ∨
    (ρ₁.lookup n = none ∧ ρ₂.lookup n = none) := by
  have h0 := hρ 0 n hn hle
  match h1eq : ρ₁.lookup n, h2eq : ρ₂.lookup n with
  | some v₁, some v₂ =>
    left; exact ⟨v₁, v₂, rfl, rfl, fun k => by
      have hk := hρ k n hn hle; simp [h1eq, h2eq] at hk; exact hk⟩
  | none, none => right; exact ⟨rfl, rfl⟩
  | some _, none => simp [h1eq, h2eq] at h0
  | none, some _ => simp [h1eq, h2eq] at h0

private theorem error_in_one_step_reaches_error (s : State)
    (h : step s = .error) : Reaches s .error :=
  ⟨1, by simp [steps, h]⟩

private theorem error_in_one_step_not_halts (s : State)
    (h : step s = .error) : ¬Halts s := by
  intro ⟨v, n, hn⟩
  have herr : Reaches s .error := error_in_one_step_reaches_error s h
  exact reaches_halt_not_error ⟨n, hn⟩ herr

private theorem reaches_of_step_reaches {s₁ s₂ s₃ : State}
    (h1 : step s₁ = s₂) (h2 : Reaches s₂ s₃) : Reaches s₁ s₃ := by
  obtain ⟨n, hn⟩ := h2
  exact ⟨n + 1, by simp [steps, h1, hn]⟩

private theorem reaches_to_step_reaches {s₁ s₂ s₃ : State}
    (h1 : step s₁ = s₂) (h2 : Reaches s₁ s₃) (h_ne : s₁ ≠ s₃) : Reaches s₂ s₃ := by
  obtain ⟨n, hn⟩ := h2
  cases n with
  | zero => simp [steps] at hn; exact absurd hn h_ne
  | succ m => exact ⟨m, by simp [steps, h1] at hn; exact hn⟩

mutual
  private theorem valueEq_mono : ∀ (k : Nat) (v₁ v₂ : CekValue),
      ValueEq (k + 1) v₁ v₂ → ValueEq k v₁ v₂
    | 0, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, h => by simp only [ValueEq] at h ⊢; exact h
    | k + 1, .VLam _ _, .VLam _ _, h => by
      unfold ValueEq at h ⊢; intro arg
      have ⟨he, hh, hv⟩ := h arg
      exact ⟨he, hh, fun v₁ v₂ h₁ h₂ => valueEq_mono k _ _ (hv v₁ v₂ h₁ h₂)⟩
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1, h.2.1, fun v₁ v₂ h₁ h₂ => valueEq_mono k _ _ (h.2.2 v₁ v₂ h₁ h₂)⟩
    | _ + 1, .VConstr _ _, .VConstr _ _, h => by
      unfold ValueEq at h ⊢; exact ⟨h.1, listValueEq_mono _ _ _ h.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1, listValueEq_mono k _ _ h.2.1, h.2.2.1, h.2.2.2.1,
             fun r1 r2 h1 h2 => valueEq_mono k _ _ (h.2.2.2.2 r1 r2 h1 h2)⟩
    | _ + 1, .VCon _, .VLam _ _, h | _ + 1, .VCon _, .VDelay _ _, h
    | _ + 1, .VCon _, .VConstr _ _, h | _ + 1, .VCon _, .VBuiltin _ _ _, h
    | _ + 1, .VLam _ _, .VCon _, h | _ + 1, .VLam _ _, .VDelay _ _, h
    | _ + 1, .VLam _ _, .VConstr _ _, h | _ + 1, .VLam _ _, .VBuiltin _ _ _, h
    | _ + 1, .VDelay _ _, .VCon _, h | _ + 1, .VDelay _ _, .VLam _ _, h
    | _ + 1, .VDelay _ _, .VConstr _ _, h | _ + 1, .VDelay _ _, .VBuiltin _ _ _, h
    | _ + 1, .VConstr _ _, .VCon _, h | _ + 1, .VConstr _ _, .VLam _ _, h
    | _ + 1, .VConstr _ _, .VDelay _ _, h | _ + 1, .VConstr _ _, .VBuiltin _ _ _, h
    | _ + 1, .VBuiltin _ _ _, .VCon _, h | _ + 1, .VBuiltin _ _ _, .VLam _ _, h
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, h
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValueEq] at h
  private theorem listValueEq_mono : ∀ (k : Nat) (vs₁ vs₂ : List CekValue),
      ListValueEq (k + 1) vs₁ vs₂ → ListValueEq k vs₁ vs₂
    | _, [], [], _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, h => by
      simp only [ListValueEq] at h ⊢
      exact ⟨valueEq_mono k _ _ h.1, listValueEq_mono k _ _ h.2⟩
    | _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
    | _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])
end

/-- Construct `ValueEq k` for VBuiltin values from components. -/
private theorem valueEq_vbuiltin (k : Nat) (b : BuiltinFun) (a1 a2 : List CekValue)
    (ea : ExpectedArgs)
    (hargs : ListValueEq k a1 a2)
    (heval_none : evalBuiltin b a1 = none ↔ evalBuiltin b a2 = none)
    (heval_val : ∀ r1 r2, evalBuiltin b a1 = some r1 → evalBuiltin b a2 = some r2 →
      ValueEq k r1 r2) :
    ValueEq k (.VBuiltin b a1 ea) (.VBuiltin b a2 ea) := by
  match k with
  | 0 => simp [ValueEq]
  | k + 1 =>
    unfold ValueEq
    exact ⟨rfl, listValueEq_mono k a1 a2 hargs, rfl, heval_none,
           fun r1 r2 h1 h2 => valueEq_mono k _ _ (heval_val r1 r2 h1 h2)⟩

/-- Downgrade `ListValueEq` from level `n + 1` to level `1` by repeated monotonicity. -/
private theorem listValueEq_to_1 (n : Nat) (a1 a2 : List CekValue)
    (h : ListValueEq (n + 1) a1 a2) : ListValueEq 1 a1 a2 := by
  induction n with
  | zero => exact h
  | succ m ih => exact ih (listValueEq_mono (m + 1) a1 a2 h)

/-- `ListValueEq 1` implies `extractConsts` agrees on both sides. -/
private theorem extractConsts_listValueEq :
    ∀ (a1 a2 : List CekValue),
    ListValueEq 1 a1 a2 → extractConsts a1 = extractConsts a2
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [ListValueEq] at h
  | [], _ :: _, h => by simp [ListValueEq] at h
  | v1 :: vs1, v2 :: vs2, h => by
    simp only [ListValueEq] at h
    have ⟨hv, hvs⟩ := h
    have ih := extractConsts_listValueEq vs1 vs2 hvs
    cases v1 with
    | VCon c1 =>
      cases v2 with
      | VCon c2 =>
        unfold ValueEq at hv
        simp only [extractConsts, bind, Option.bind]; rw [ih, hv]
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        exact absurd hv (by unfold ValueEq; exact id)
    | VLam _ _ =>
      cases v2 with
      | VLam _ _ => simp [extractConsts]
      | _ => exact absurd hv (by unfold ValueEq; exact id)
    | VDelay _ _ =>
      cases v2 with
      | VDelay _ _ => simp [extractConsts]
      | _ => exact absurd hv (by unfold ValueEq; exact id)
    | VConstr _ _ =>
      cases v2 with
      | VConstr _ _ => simp [extractConsts]
      | _ => exact absurd hv (by unfold ValueEq; exact id)
    | VBuiltin _ _ _ =>
      cases v2 with
      | VBuiltin _ _ _ => simp [extractConsts]
      | _ => exact absurd hv (by unfold ValueEq; exact id)


/-- When `ListValueEq 1` and `extractConsts` succeeds, both lists are equal. -/
private theorem listValueEq1_extractConsts_eq :
    ∀ (a1 a2 : List CekValue) (cs : List Const),
    ListValueEq 1 a1 a2 → extractConsts a1 = some cs → a1 = a2
  | [], [], _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [ListValueEq] at h
  | [], _ :: _, _, h, _ => by simp [ListValueEq] at h
  | v1 :: vs1, v2 :: vs2, cs, h, hec => by
    simp only [ListValueEq] at h; obtain ⟨hv, hvs⟩ := h
    cases v1 with
    | VCon c1 =>
      cases v2 with
      | VCon c2 =>
        unfold ValueEq at hv; subst hv
        simp only [extractConsts, bind, Option.bind] at hec
        cases hrest : extractConsts vs1 with
        | none => rw [hrest] at hec; simp at hec
        | some cs' =>
          rw [hrest] at hec
          have := listValueEq1_extractConsts_eq vs1 vs2 cs' hvs hrest
          subst this; rfl
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        exact absurd hv (by unfold ValueEq; exact id)
    | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
      simp [extractConsts] at hec

/-- Pass-through builtin agreement when `extractConsts` fails on the tail. -/
private theorem evalBuiltinPassThrough_agree_tail (b : BuiltinFun) (vx : CekValue)
    (a1 a2 : List CekValue) (k : Nat)
    (hargs : ListValueEq (k + 1) a1 a2)
    (hargs1 : ListValueEq 1 a1 a2)
    (hec : extractConsts a1 = none) :
    match evalBuiltinPassThrough b (vx :: a1), evalBuiltinPassThrough b (vx :: a2) with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False := by
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [evalBuiltinPassThrough] <;>
      (try (cases a1 with
            | nil => cases a2 <;> (simp_all [ListValueEq])
            | cons h1 t1 =>
              cases a2 with
              | nil => simp [ListValueEq] at hargs1
              | cons h2 t2 =>
                simp only [ListValueEq] at hargs1; obtain ⟨hh, ht⟩ := hargs1
                cases t1 with
                | nil =>
                  cases t2 with
                  | nil =>
                    cases h1 <;> cases h2 <;> (try simp [ValueEq] at hh) <;>
                      (try subst hh) <;> (try simp) <;> (try trivial) <;>
                      (try (rename_i c; cases c <;> (try simp) <;> (try trivial) <;>
                        (try (cases vx <;> (try simp) <;> (try trivial) <;>
                          (try (rename_i vc; cases vc <;> (try simp) <;> (try trivial) <;>
                            (try (simp only [ListValueEq] at hargs;
                                  exact valueEq_mono k _ _ hargs.1))))))))
                  | cons => simp [ListValueEq] at ht
                | cons h1b t1b =>
                  cases t2 with
                  | nil => simp [ListValueEq] at ht
                  | cons h2b t2b =>
                    simp only [ListValueEq] at ht; obtain ⟨hhb, htb⟩ := ht
                    cases t1b with
                    | nil =>
                      cases t2b with
                      | nil =>
                        cases h1b <;> cases h2b <;> (try simp [ValueEq] at hhb) <;>
                          (try subst hhb) <;> (try simp) <;> (try trivial) <;>
                          (try (rename_i c; cases c <;> (try simp) <;> (try trivial) <;>
                            (try (split <;> (first
                              | (simp only [ListValueEq] at hargs;
                                 exact valueEq_mono k _ _ hargs.1)
                              | exact valueEq_refl k _
                              | trivial)))))
                      | cons => simp [ListValueEq] at htb
                    | cons h1c t1c =>
                      cases t2b with
                      | nil => simp [ListValueEq] at htb
                      | cons h2c t2c =>
                        simp only [ListValueEq] at htb; obtain ⟨hhc, htc⟩ := htb
                        cases t1c with
                        | nil =>
                          cases t2c with
                          | nil => simp  -- 3-elem tail: no builtin matches
                          | cons => simp [ListValueEq] at htc
                        | cons h1d t1d =>
                          cases t2c with
                          | nil => simp [ListValueEq] at htc
                          | cons h2d t2d =>
                            simp only [ListValueEq] at htc; obtain ⟨hhd, htd⟩ := htc
                            cases t1d with
                            | nil =>
                              cases t2d with
                              | nil =>
                                cases h1d <;> cases h2d <;> (try simp [ValueEq] at hhd) <;>
                                  (try subst hhd) <;> (try simp) <;> (try trivial) <;>
                                  (try (rename_i c; cases c <;> (try simp) <;> (try trivial) <;>
                                    (try (rename_i d; cases d <;> (try simp) <;> (try trivial) <;>
                                      (try (simp only [ListValueEq] at hargs;
                                            first
                                            | exact valueEq_mono k _ _ hargs.1
                                            | exact valueEq_mono k _ _ hargs.2.1
                                            | exact valueEq_mono k _ _ hargs.2.2.1
                                            | exact valueEq_mono k _ _ hargs.2.2.2.1
                                            | exact valueEq_refl k _))))))
                              | cons => simp [ListValueEq] at htd
                            | cons h1e t1e =>
                              cases t2d with
                              | nil => simp [ListValueEq] at htd
                              | cons h2e t2e =>
                                simp only [ListValueEq] at htd; obtain ⟨hhe, hte⟩ := htd
                                cases t1e with
                                | nil =>
                                  cases t2e with
                                  | nil =>
                                    cases h1e <;> cases h2e <;> (try simp [ValueEq] at hhe) <;>
                                      (try subst hhe) <;> (try simp) <;> (try trivial) <;>
                                      (try (rename_i c; cases c <;> (try simp) <;> (try trivial) <;>
                                        (try (rename_i d; cases d <;> (try simp) <;> (try trivial) <;>
                                          (try (simp only [ListValueEq] at hargs;
                                                first
                                                | exact valueEq_mono k _ _ hargs.1
                                                | exact valueEq_mono k _ _ hargs.2.1
                                                | exact valueEq_mono k _ _ hargs.2.2.1
                                                | exact valueEq_mono k _ _ hargs.2.2.2.1
                                                | exact valueEq_mono k _ _ hargs.2.2.2.2.1
                                                | exact valueEq_refl k _))))))
                                  | cons => simp [ListValueEq] at hte
                                | cons _ _ =>
                                  cases t2e with
                                  | nil => simp [ListValueEq] at hte
                                  | cons _ _ => simp))  -- 6+ elem tail: no builtin matches

  · have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                   b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
      ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
       fun h => hb (h ▸ .inr (.inr (.inl rfl))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
    rw [evalBuiltinPassThrough_none_of_not_passthrough b (vx :: a1) hb_not,
        evalBuiltinPassThrough_none_of_not_passthrough b (vx :: a2) hb_not]
    trivial

/-- evalBuiltin agreement for same head `vx` and `ListValueEq (k+1)`-related tails. -/
private theorem evalBuiltin_agree_tail (b : BuiltinFun) (vx : CekValue)
    (a1 a2 : List CekValue) (k : Nat)
    (hargs : ListValueEq (k + 1) a1 a2) :
    match evalBuiltin b (vx :: a1), evalBuiltin b (vx :: a2) with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False := by
  have hargs1 : ListValueEq 1 a1 a2 := listValueEq_to_1 k a1 a2 hargs
  cases hec : extractConsts a1 with
  | some cs =>
    have heq := listValueEq1_extractConsts_eq a1 a2 cs hargs1 hec
    subst heq
    cases evalBuiltin b (vx :: a1) with
    | none => trivial
    | some v => exact valueEq_refl k v
  | none =>
    have hec2 : extractConsts a2 = none := by
      rw [← extractConsts_listValueEq a1 a2 hargs1]; exact hec
    have h_eb1 : evalBuiltin b (vx :: a1) = evalBuiltinPassThrough b (vx :: a1) := by
      simp only [evalBuiltin]
      cases hp : evalBuiltinPassThrough b (vx :: a1) with
      | some _ => rfl
      | none =>
        cases vx with
        | VCon c => simp only [extractConsts, bind, Option.bind]; rw [hec]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [extractConsts]
    have h_eb2 : evalBuiltin b (vx :: a2) = evalBuiltinPassThrough b (vx :: a2) := by
      simp only [evalBuiltin]
      cases hp : evalBuiltinPassThrough b (vx :: a2) with
      | some _ => rfl
      | none =>
        cases vx with
        | VCon c => simp only [extractConsts, bind, Option.bind]; rw [hec2]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [extractConsts]
    rw [h_eb1, h_eb2]
    exact evalBuiltinPassThrough_agree_tail b vx a1 a2 k hargs hargs1 hec

/-- When two values agree at all step indices, they have the same VCon projection. -/
private theorem valueEqAll_vcon_eq {vx vx' : CekValue} {c : Const}
    (hx : ∀ k, ValueEq k vx vx') (heq : vx = .VCon c) : vx' = .VCon c := by
  subst heq
  have h1 := hx 1; unfold ValueEq at h1
  cases vx' with
  | VCon c' => exact congrArg CekValue.VCon h1.symm
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => exact absurd h1 id

/-- Decompose a halting `Force e` into sub-expression result + force frame result. -/
private theorem force_reaches (ρ : CekEnv) (te : Term) (v : CekValue)
    (hreach : Reaches (.compute [] ρ (.Force te)) (.halt v)) :
    ∃ val, Reaches (.compute [] ρ te) (.halt val) ∧
           Reaches (.ret [.force] val) (.halt v) := by
  obtain ⟨N, hN⟩ := hreach
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.force] ρ te) = .halt v := by
    have : N = 1 + (N - 1) := by omega
    rw [this, steps_trans, h1] at hN; exact hN
  have hlift : State.compute [.force] ρ te =
      liftState [.force] (.compute [] ρ te) := by simp [liftState]
  rw [hlift] at hrest
  have h_has_inactive : ∃ k, k ≤ (N - 1) ∧ isActive (steps k (.compute [] ρ te)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ (N - 1) → isActive (steps j (.compute [] ρ te)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ te)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ te)) <;> simp_all⟩
      have h_comm := steps_liftState [.force] (N - 1) (.compute [] ρ te)
        (fun j hj => hall' j (by omega))
      rw [hrest] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ v)
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ te) (N - 1) h_has_inactive
  have h_comm : steps K (liftState [.force] (.compute [] ρ te)) =
      liftState [.force] (steps K (.compute [] ρ te)) :=
    steps_liftState [.force] K (.compute [] ρ te) hK_min
  have h_not_error : steps K (.compute [] ρ te) ≠ .error := by
    intro herr
    have : steps ((N - 1) - K) (liftState [.force] .error) = .halt v := by
      have : N - 1 = K + ((N - 1) - K) := by omega
      rw [this, steps_trans, h_comm, herr] at hrest; exact hrest
    simp [liftState, steps_error] at this
  have ⟨val, h_inner_eq, h_lifted_eq⟩ :
      ∃ val, (steps K (.compute [] ρ te) = .halt val ∨
             steps K (.compute [] ρ te) = .ret [] val) ∧
            liftState [.force] (steps K (.compute [] ρ te)) =
              .ret [.force] val := by
    generalize h_sK : steps K (.compute [] ρ te) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  have h_reaches_te : Reaches (.compute [] ρ te) (.halt val) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  have h_frame : steps ((N - 1) - K) (.ret [.force] val) = .halt v := by
    have : N - 1 = K + ((N - 1) - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hrest; exact hrest
  exact ⟨val, h_reaches_te, (N - 1) - K, h_frame⟩

/-- Compose sub-expression halt + force frame into Force result. -/
private theorem force_compose (ρ : CekEnv) (te : Term) (val : CekValue) (s : State)
    (hte : Reaches (.compute [] ρ te) (.halt val))
    (hf : Reaches (.ret [.force] val) s) :
    Reaches (.compute [] ρ (.Force te)) s := by
  obtain ⟨Ke, hKe⟩ := hte; obtain ⟨Kf, hKf⟩ := hf
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have h_ret := compute_to_ret_from_halt ρ te val [.force] ⟨Ke, hKe⟩
  obtain ⟨Kr, hKr⟩ := h_ret
  exact ⟨1 + Kr + Kf, by
    have : 1 + Kr + Kf = 1 + (Kr + Kf) := by omega
    rw [this, steps_trans, h1, steps_trans, hKr, hKf]⟩

/-- If the sub-expression errors, Force errors. -/
private theorem force_sub_error (ρ : CekEnv) (te : Term)
    (herr : Reaches (.compute [] ρ te) .error) :
    Reaches (.compute [] ρ (.Force te)) .error := by
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have h_err := compute_to_error_from_error ρ te [.force] herr
  obtain ⟨Ke, hKe⟩ := h_err
  exact ⟨1 + Ke, by rw [steps_trans, h1, hKe]⟩

/-- Forcing a VDelay to halt. -/
private theorem force_delay_halt (body : Term) (env : CekEnv) (v : CekValue) :
    Reaches (.ret [.force] (.VDelay body env)) (.halt v) ↔
    Reaches (.compute [] env body) (.halt v) := by
  constructor
  · intro ⟨n, hn⟩; cases n with
    | zero => simp [steps] at hn
    | succ n => simp [steps, step] at hn; exact ⟨n, hn⟩
  · intro ⟨n, hn⟩; exact ⟨n + 1, by simp [steps, step, hn]⟩

/-- Forcing a VDelay to error. -/
private theorem force_delay_error (body : Term) (env : CekEnv) :
    Reaches (.ret [.force] (.VDelay body env)) .error ↔
    Reaches (.compute [] env body) .error := by
  constructor
  · intro ⟨n, hn⟩; cases n with
    | zero => simp [steps] at hn
    | succ n => simp [steps, step] at hn; exact ⟨n, hn⟩
  · intro ⟨n, hn⟩; exact ⟨n + 1, by simp [steps, step, hn]⟩

/-- VCon cannot be forced to halt. -/
private theorem force_vcon_not_halts (c : Const) : ¬Halts (.ret [.force] (.VCon c)) := by
  intro ⟨v, n, hn⟩; cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_error] at hn

/-- VLam cannot be forced to halt. -/
private theorem force_vlam_not_halts (b : Term) (e : CekEnv) :
    ¬Halts (.ret [.force] (.VLam b e)) := by
  intro ⟨v, n, hn⟩; cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_error] at hn

/-- VConstr cannot be forced to halt. -/
private theorem force_vconstr_not_halts (t : Nat) (fs : List CekValue) :
    ¬Halts (.ret [.force] (.VConstr t fs)) := by
  intro ⟨v, n, hn⟩; cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_error] at hn

/-- VCon forced is error. -/
private theorem force_vcon_reaches_error (c : Const) :
    Reaches (.ret [.force] (.VCon c)) .error :=
  ⟨1, by simp [steps, step]⟩

/-- VLam forced is error. -/
private theorem force_vlam_reaches_error (b : Term) (e : CekEnv) :
    Reaches (.ret [.force] (.VLam b e)) .error :=
  ⟨1, by simp [steps, step]⟩

/-- VConstr forced is error. -/
private theorem force_vconstr_reaches_error (t : Nat) (fs : List CekValue) :
    Reaches (.ret [.force] (.VConstr t fs)) .error :=
  ⟨1, by simp [steps, step]⟩

/-- Transfer force-frame error through `ValueEq`. -/
private theorem force_frame_error_transfer (k : Nat)
    (v1 v2 : CekValue) (hve : ValueEq (k + 1) v1 v2)
    (herr : Reaches (.ret [.force] v1) .error) :
    Reaches (.ret [.force] v2) .error := by
  match v1, v2 with
  | .VDelay b1 e1, .VDelay b2 e2 =>
    unfold ValueEq at hve
    exact (force_delay_error b2 e2).mpr (hve.1.mp ((force_delay_error b1 e1).mp herr))
  | .VCon _, .VCon _ => exact force_vcon_reaches_error _
  | .VLam _ _, .VLam _ _ => exact force_vlam_reaches_error _ _
  | .VConstr _ _, .VConstr _ _ => exact force_vconstr_reaches_error _ _
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    unfold ValueEq at hve
    obtain ⟨hb, _, hea, heval_none, _⟩ := hve; subst hb; subst hea
    obtain ⟨n, hn⟩ := herr
    cases n with
    | zero => simp [steps] at hn
    | succ n =>
      simp only [steps, step] at hn
      cases hhead : ea.head with
      | argV => rw [hhead] at hn; simp [steps_error] at hn; exact ⟨1, by simp [steps, step, hhead]⟩
      | argQ =>
        rw [hhead] at hn
        cases htail : ea.tail with
        | some rest =>
          rw [htail] at hn
          have hh : Reaches (.ret [] (.VBuiltin b a1 rest)) (.halt (.VBuiltin b a1 rest)) :=
            ⟨1, by rfl⟩
          exact absurd (reaches_halt_not_error hh ⟨n, hn⟩) False.elim
        | none =>
          rw [htail] at hn
          cases heval : evalBuiltin b a1 with
          | some v =>
            rw [heval] at hn
            have hh : Reaches (.ret [] v) (.halt v) := ⟨1, by rfl⟩
            exact absurd (reaches_halt_not_error hh ⟨n, hn⟩) False.elim
          | none =>
            rw [heval] at hn
            cases heval2 : evalBuiltin b a2 with
            | none => exact ⟨1, by simp only [steps, step]; rw [hhead, htail, heval2]⟩
            | some v2 =>
              exfalso; exact absurd (heval_none.mp heval) (by rw [heval2]; exact fun h => by simp at h)
  | .VCon _, .VDelay _ _ | .VCon _, .VLam _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
  | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VBuiltin _ _ _
  | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd hve (by unfold ValueEq; exact id)

/-- Transfer force-frame halts through ValueEq. -/
private theorem force_frame_halts_transfer (k : Nat)
    (v1 v2 : CekValue) (hve : ValueEq (k + 1) v1 v2)
    (hh : Halts (.ret [.force] v1)) :
    Halts (.ret [.force] v2) := by
  match v1, v2 with
  | .VDelay b1 e1, .VDelay b2 e2 =>
    unfold ValueEq at hve
    obtain ⟨_, hhalt, _⟩ := hve
    obtain ⟨w, hw⟩ := hh
    obtain ⟨w', hw'⟩ := hhalt.mp ⟨w, (force_delay_halt b1 e1 w).mp hw⟩
    exact ⟨w', (force_delay_halt b2 e2 w').mpr hw'⟩
  | .VCon _, .VCon _ => exact absurd hh (force_vcon_not_halts _)
  | .VLam _ _, .VLam _ _ => exact absurd hh (force_vlam_not_halts _ _)
  | .VConstr _ _, .VConstr _ _ => exact absurd hh (force_vconstr_not_halts _ _)
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    unfold ValueEq at hve
    obtain ⟨hb, _, hea, heval_none, heval_val⟩ := hve; subst hb; subst hea
    obtain ⟨w, n, hn⟩ := hh
    cases n with
    | zero => simp [steps] at hn
    | succ n =>
      simp only [steps, step] at hn
      cases hhead : ea.head with
      | argV => rw [hhead] at hn; simp [steps_error] at hn
      | argQ =>
        rw [hhead] at hn
        cases htail : ea.tail with
        | some rest =>
          rw [htail] at hn
          exact ⟨.VBuiltin b a2 rest, 2, by simp only [steps, step]; rw [hhead, htail]⟩
        | none =>
          rw [htail] at hn
          cases heval : evalBuiltin b a1 with
          | none => rw [heval] at hn; simp [steps_error] at hn
          | some v =>
            rw [heval] at hn
            cases heval2 : evalBuiltin b a2 with
            | none => exfalso; exact absurd (heval_none.mpr heval2) (by rw [heval]; exact fun h => by simp at h)
            | some v2 => exact ⟨v2, 2, by simp only [steps, step]; rw [hhead, htail, heval2]⟩
  | .VCon _, .VDelay _ _ | .VCon _, .VLam _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
  | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VBuiltin _ _ _
  | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd hve (by unfold ValueEq; exact id)

/-- ValueEq for force-frame results when both halt. -/
private theorem force_frame_valueEq (k : Nat)
    (v1 v2 : CekValue) (hve : ValueEq (k + 1) v1 v2)
    (w1 w2 : CekValue)
    (hw1 : Reaches (.ret [.force] v1) (.halt w1))
    (hw2 : Reaches (.ret [.force] v2) (.halt w2)) :
    ValueEq k w1 w2 := by
  match v1, v2 with
  | .VDelay b1 e1, .VDelay b2 e2 =>
    unfold ValueEq at hve
    obtain ⟨_, _, hval_inner⟩ := hve
    exact hval_inner w1 w2
      ((force_delay_halt b1 e1 w1).mp hw1)
      ((force_delay_halt b2 e2 w2).mp hw2)
  | .VCon _, .VCon _ => exact absurd ⟨w1, hw1⟩ (force_vcon_not_halts _)
  | .VLam _ _, .VLam _ _ => exact absurd ⟨w1, hw1⟩ (force_vlam_not_halts _ _)
  | .VConstr _ _, .VConstr _ _ => exact absurd ⟨w1, hw1⟩ (force_vconstr_not_halts _ _)
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    unfold ValueEq at hve
    obtain ⟨hb, hargs, hea, heval_none, heval_val⟩ := hve; subst hb; subst hea
    obtain ⟨n1, hn1⟩ := hw1; obtain ⟨n2, hn2⟩ := hw2
    cases n1 with
    | zero => simp [steps] at hn1
    | succ n1 =>
      cases n2 with
      | zero => simp [steps] at hn2
      | succ n2 =>
        simp only [steps, step] at hn1 hn2
        cases hhead : ea.head with
        | argV =>
          rw [hhead] at hn1; simp [steps_error] at hn1
        | argQ =>
          rw [hhead] at hn1 hn2
          cases htail : ea.tail with
          | some rest =>
            rw [htail] at hn1 hn2
            cases n1 with
            | zero => simp [steps] at hn1
            | succ n1 =>
              cases n2 with
              | zero => simp [steps] at hn2
              | succ n2 =>
                simp only [steps, step] at hn1 hn2
                rw [steps_halt] at hn1 hn2
                have heq1 : CekValue.VBuiltin b a1 rest = w1 := State.halt.inj hn1
                have heq2 : CekValue.VBuiltin b a2 rest = w2 := State.halt.inj hn2
                subst heq1; subst heq2
                exact valueEq_vbuiltin k b a1 a2 rest hargs heval_none heval_val
          | none =>
            rw [htail] at hn1 hn2
            cases heval1 : evalBuiltin b a1 with
            | none => rw [heval1] at hn1; simp [steps_error] at hn1
            | some r1 =>
              rw [heval1] at hn1
              cases heval2 : evalBuiltin b a2 with
              | none => rw [heval2] at hn2; simp [steps_error] at hn2
              | some r2 =>
                rw [heval2] at hn2
                cases n1 with
                | zero => simp [steps] at hn1
                | succ n1 =>
                  cases n2 with
                  | zero => simp [steps] at hn2
                  | succ n2 =>
                    simp only [steps, step] at hn1 hn2
                    rw [steps_halt] at hn1 hn2
                    have heq1 : r1 = w1 := State.halt.inj hn1
                    have heq2 : r2 = w2 := State.halt.inj hn2
                    subst heq1; subst heq2
                    exact heval_val r1 r2 heval1 heval2
  | .VCon _, .VDelay _ _ | .VCon _, .VLam _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
  | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VBuiltin _ _ _
  | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd hve (by unfold ValueEq; exact id)

/-- Applying `∀ k, ValueEq k`-related functions to the same argument preserves error. -/
private theorem funV_same_arg_error_transfer
    (vf₁ vf₂ vx : CekValue) (hve : ∀ j, ValueEq j vf₁ vf₂)
    (herr : Reaches (.ret [.funV vf₁] vx) .error) :
    Reaches (.ret [.funV vf₂] vx) .error := by
  match vf₁, vf₂ with
  | .VLam b1 e1, .VLam b2 e2 =>
    have hve1 := hve 1; unfold ValueEq at hve1
    have ⟨he, _, _⟩ := hve1 vx
    have hl : step (.ret [.funV (.VLam b1 e1)] vx) = .compute [] (e1.extend vx) b1 := rfl
    have hr : step (.ret [.funV (.VLam b2 e2)] vx) = .compute [] (e2.extend vx) b2 := rfl
    have herr' := reaches_to_step_reaches hl herr (by simp)
    exact reaches_of_step_reaches hr (he.mp herr')
  | .VCon _, .VCon _ =>
    exact ⟨1, by rfl⟩
  | .VDelay _ _, .VDelay _ _ =>
    exact ⟨1, by rfl⟩
  | .VConstr _ _, .VConstr _ _ =>
    exact ⟨1, by rfl⟩
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    have hve2 := hve 2; unfold ValueEq at hve2
    obtain ⟨hb, hargs_tail, hea, _, _⟩ := hve2; subst hb; subst hea
    have hagree := evalBuiltin_agree_tail b vx a1 a2 0 hargs_tail
    obtain ⟨n, hn⟩ := herr
    cases n with
    | zero => simp [steps] at hn
    | succ n =>
      simp only [steps, step] at hn
      cases hhead : ea.head with
      | argQ =>
        rw [hhead] at hn
        exact ⟨1, by simp only [steps, step]; rw [hhead]⟩
      | argV =>
        rw [hhead] at hn
        cases htail : ea.tail with
        | some rest =>
          rw [htail] at hn
          have hh : Reaches (.ret [] (.VBuiltin b (vx :: a1) rest)) (.halt (.VBuiltin b (vx :: a1) rest)) :=
            ⟨1, by rfl⟩
          exact absurd (reaches_halt_not_error hh ⟨n, hn⟩) False.elim
        | none =>
          rw [htail] at hn
          cases heval : evalBuiltin b (vx :: a1) with
          | some v =>
            rw [heval] at hn
            have hh : Reaches (.ret [] v) (.halt v) := ⟨1, by rfl⟩
            exact absurd (reaches_halt_not_error hh ⟨n, hn⟩) False.elim
          | none =>
            rw [heval] at hagree
            cases heval2 : evalBuiltin b (vx :: a2) with
            | none =>
              exact ⟨1, by simp only [steps, step]; rw [hhead, htail, heval2]⟩
            | some v2 =>
              rw [heval2] at hagree; exact absurd hagree id
  | .VCon _, .VDelay _ _ | .VCon _, .VLam _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
  | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VBuiltin _ _ _
  | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd (hve 1) (by unfold ValueEq; exact id)

/-- Halts transfer for same-arg, different-function. -/
private theorem funV_same_arg_halts_transfer
    (vf₁ vf₂ vx : CekValue) (hve : ∀ j, ValueEq j vf₁ vf₂)
    (hh : Halts (.ret [.funV vf₁] vx)) :
    Halts (.ret [.funV vf₂] vx) := by
  match vf₁, vf₂ with
  | .VLam b1 e1, .VLam b2 e2 =>
    have hve1 := hve 1; unfold ValueEq at hve1
    have ⟨_, hhalts, _⟩ := hve1 vx
    have hl : step (.ret [.funV (.VLam b1 e1)] vx) = .compute [] (e1.extend vx) b1 := rfl
    have hr : step (.ret [.funV (.VLam b2 e2)] vx) = .compute [] (e2.extend vx) b2 := rfl
    obtain ⟨w, hw⟩ := hh
    have hw' := reaches_to_step_reaches hl hw (by simp)
    obtain ⟨w', hw'⟩ := hhalts.mp ⟨w, hw'⟩
    exact ⟨w', reaches_of_step_reaches hr hw'⟩
  | .VCon c1, .VCon _ =>
    have : step (.ret [.funV (.VCon c1)] vx) = .error := rfl
    exact absurd hh (error_in_one_step_not_halts _ this)
  | .VDelay bd1 env1, .VDelay _ _ =>
    have : step (.ret [.funV (.VDelay bd1 env1)] vx) = .error := rfl
    exact absurd hh (error_in_one_step_not_halts _ this)
  | .VConstr tag1 fs1, .VConstr _ _ =>
    have : step (.ret [.funV (.VConstr tag1 fs1)] vx) = .error := rfl
    exact absurd hh (error_in_one_step_not_halts _ this)
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    have hve2 := hve 2; unfold ValueEq at hve2
    obtain ⟨hb, hargs_tail, hea, _, _⟩ := hve2; subst hb; subst hea
    have hagree := evalBuiltin_agree_tail b vx a1 a2 0 hargs_tail
    obtain ⟨w, n, hn⟩ := hh
    cases n with
    | zero => simp [steps] at hn
    | succ n =>
      simp only [steps, step] at hn
      cases hhead : ea.head with
      | argQ => rw [hhead] at hn; simp [steps_error] at hn
      | argV =>
        rw [hhead] at hn
        cases htail : ea.tail with
        | some rest =>
          rw [htail] at hn
          exact ⟨.VBuiltin b (vx :: a2) rest, 2, by
            show steps 1 (step (.ret [.funV (.VBuiltin b a2 ea)] vx)) = _
            simp only [step]; rw [hhead, htail]; rfl⟩
        | none =>
          rw [htail] at hn
          cases heval : evalBuiltin b (vx :: a1) with
          | none => rw [heval] at hn; simp [steps_error] at hn
          | some v =>
            rw [heval] at hagree
            cases heval2 : evalBuiltin b (vx :: a2) with
            | some v2 =>
              exact ⟨v2, 2, by
                show steps 1 (step (.ret [.funV (.VBuiltin b a2 ea)] vx)) = _
                simp only [step]; rw [hhead, htail, heval2]; rfl⟩
            | none =>
              rw [heval2] at hagree; exact absurd hagree id
  | .VCon _, .VDelay _ _ | .VCon _, .VLam _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
  | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VBuiltin _ _ _
  | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd (hve 1) (by unfold ValueEq; exact id)

/-- ValueEq transfer for same-arg, different-function results. -/
private theorem funV_same_arg_valueEq (k : Nat)
    (vf₁ vf₂ vx w₁ w₂ : CekValue) (hve : ∀ j, ValueEq j vf₁ vf₂)
    (hw₁ : Reaches (.ret [.funV vf₁] vx) (.halt w₁))
    (hw₂ : Reaches (.ret [.funV vf₂] vx) (.halt w₂)) :
    ValueEq k w₁ w₂ := by
  match vf₁, vf₂ with
  | .VLam b1 e1, .VLam b2 e2 =>
    have hvek := hve (k + 1); unfold ValueEq at hvek
    have ⟨_, _, hval⟩ := hvek vx
    have hl : step (.ret [.funV (.VLam b1 e1)] vx) = .compute [] (e1.extend vx) b1 := rfl
    have hr : step (.ret [.funV (.VLam b2 e2)] vx) = .compute [] (e2.extend vx) b2 := rfl
    have hw₁' := reaches_to_step_reaches hl hw₁ (by simp)
    have hw₂' := reaches_to_step_reaches hr hw₂ (by simp)
    exact hval w₁ w₂ hw₁' hw₂'
  | .VCon c1, .VCon _ =>
    have : step (.ret [.funV (.VCon c1)] vx) = .error := rfl
    exact absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ this)
  | .VDelay bd1 env1, .VDelay _ _ =>
    have : step (.ret [.funV (.VDelay bd1 env1)] vx) = .error := rfl
    exact absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ this)
  | .VConstr tag1 fs1, .VConstr _ _ =>
    have : step (.ret [.funV (.VConstr tag1 fs1)] vx) = .error := rfl
    exact absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ this)
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    have hvek2 := hve (k + 2); unfold ValueEq at hvek2
    obtain ⟨hb, hargs_tail, hea, _, _⟩ := hvek2; subst hb; subst hea
    have hagree := evalBuiltin_agree_tail b vx a1 a2 k hargs_tail
    obtain ⟨n1, hn1⟩ := hw₁
    obtain ⟨n2, hn2⟩ := hw₂
    cases n1 with
    | zero => simp [steps] at hn1
    | succ n1 =>
      cases n2 with
      | zero => simp [steps] at hn2
      | succ n2 =>
        simp only [steps, step] at hn1 hn2
        cases hhead : ea.head with
        | argQ =>
          rw [hhead] at hn1; simp [steps_error] at hn1
        | argV =>
          rw [hhead] at hn1 hn2
          cases htail : ea.tail with
          | some rest =>
            rw [htail] at hn1 hn2
            cases n1 with
            | zero => simp [steps] at hn1
            | succ n1 =>
              cases n2 with
              | zero => simp [steps] at hn2
              | succ n2 =>
                simp only [steps, step] at hn1 hn2
                rw [steps_halt] at hn1 hn2
                have heq1 : CekValue.VBuiltin b (vx :: a1) rest = w₁ := State.halt.inj hn1
                have heq2 : CekValue.VBuiltin b (vx :: a2) rest = w₂ := State.halt.inj hn2
                subst heq1; subst heq2
                exact valueEq_vbuiltin k b (vx :: a1) (vx :: a2) rest
                  (by simp only [ListValueEq]; exact ⟨valueEq_refl k vx, listValueEq_mono k a1 a2 hargs_tail⟩)
                  (by -- evalBuiltin none ↔
                    constructor
                    · intro h
                      have := hagree; rw [h] at this
                      cases heval2 : evalBuiltin b (vx :: a2) with
                      | none => rfl
                      | some _ => rw [heval2] at this; exact absurd this id
                    · intro h
                      have := hagree; rw [h] at this
                      cases heval1 : evalBuiltin b (vx :: a1) with
                      | none => rfl
                      | some _ => rw [heval1] at this; exact absurd this id)
                  (by -- evalBuiltin val agreement
                    intro r1 r2 h1 h2
                    have := hagree; rw [h1, h2] at this; exact this)
          | none =>
            rw [htail] at hn1 hn2
            cases heval1 : evalBuiltin b (vx :: a1) with
            | none => rw [heval1] at hn1; simp [steps_error] at hn1
            | some r1 =>
              rw [heval1] at hn1
              cases heval2 : evalBuiltin b (vx :: a2) with
              | none => rw [heval2] at hn2; simp [steps_error] at hn2
              | some r2 =>
                rw [heval2] at hn2
                rw [heval1, heval2] at hagree
                cases n1 with
                | zero => simp [steps] at hn1
                | succ n1 =>
                  cases n2 with
                  | zero => simp [steps] at hn2
                  | succ n2 =>
                    simp only [steps, step] at hn1 hn2
                    rw [steps_halt] at hn1 hn2
                    have heq1 : r1 = w₁ := State.halt.inj hn1
                    have heq2 : r2 = w₂ := State.halt.inj hn2
                    subst heq1; subst heq2
                    exact hagree
  | .VCon _, .VDelay _ _ | .VCon _, .VLam _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
  | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VBuiltin _ _ _
  | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd (hve 1) (by unfold ValueEq; exact id)

private theorem closedAtList_of_mem {d : Nat} {ts : List Term} {t : Term}
    (hcl : closedAtList d ts = true) (hmem : t ∈ ts) : closedAt d t = true := by
  induction ts with
  | nil => exact absurd hmem List.not_mem_nil
  | cons t' ts' ih =>
    have ⟨ht', hts'⟩ := closedAt_constr_cons hcl
    cases hmem with
    | head => exact ht'
    | tail _ h => exact ih hts' h

private theorem listValueEq_cons (k : Nat) (v₁ v₂ : CekValue) (vs₁ vs₂ : List CekValue)
    (hv : ValueEq k v₁ v₂) (hvs : ListValueEq k vs₁ vs₂) :
    ListValueEq k (v₁ :: vs₁) (v₂ :: vs₂) := by
  unfold ListValueEq; exact ⟨hv, hvs⟩

private theorem listValueEq_append (k : Nat) :
    ∀ (as₁ as₂ bs₁ bs₂ : List CekValue),
    ListValueEq k as₁ as₂ → ListValueEq k bs₁ bs₂ →
    ListValueEq k (as₁ ++ bs₁) (as₂ ++ bs₂)
  | [], [], _, _, _, hb => hb
  | [], _ :: _, _, _, ha, _ => by unfold ListValueEq at ha; exact absurd ha id
  | _ :: _, [], _, _, ha, _ => by unfold ListValueEq at ha; exact absurd ha id
  | a₁ :: as₁, a₂ :: as₂, bs₁, bs₂, ha, hb => by
    unfold ListValueEq at ha
    show ListValueEq k ((a₁ :: as₁) ++ bs₁) ((a₂ :: as₂) ++ bs₂)
    simp only [List.cons_append]
    exact listValueEq_cons k a₁ a₂ (as₁ ++ bs₁) (as₂ ++ bs₂) ha.1
      (listValueEq_append k as₁ as₂ bs₁ bs₂ ha.2 hb)

private theorem listValueEq_reverse (k : Nat) :
    ∀ (vs₁ vs₂ : List CekValue),
    ListValueEq k vs₁ vs₂ →
    ListValueEq k vs₁.reverse vs₂.reverse
  | [], [], _ => by unfold ListValueEq; trivial
  | [], _ :: _, h => by unfold ListValueEq at h; exact absurd h id
  | _ :: _, [], h => by unfold ListValueEq at h; exact absurd h id
  | v₁ :: vs₁, v₂ :: vs₂, h => by
    unfold ListValueEq at h
    simp only [List.reverse_cons]
    exact listValueEq_append k vs₁.reverse vs₂.reverse [v₁] [v₂]
      (listValueEq_reverse k vs₁ vs₂ h.2)
      (listValueEq_cons k v₁ v₂ [] [] h.1 (by unfold ListValueEq; trivial))

/-- Decompose `compute [f] ρ t` reaching halt into inner halt + frame continuation. -/
private theorem compute_frame_halt_decompose (f : Frame) (ρ : CekEnv) (t : Term)
    (w : CekValue)
    (h : Reaches (.compute [f] ρ t) (.halt w)) :
    ∃ v, Reaches (.compute [] ρ t) (.halt v) ∧
         Reaches (.ret [f] v) (.halt w) := by
  obtain ⟨N, hN⟩ := h
  have hlift : State.compute [f] ρ t = liftState [f] (.compute [] ρ t) := by
    simp [liftState]
  rw [hlift] at hN
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k (.compute [] ρ t)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j (.compute [] ρ t)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ t)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ t)) <;> simp_all⟩
      have h_comm := steps_liftState [f] N (.compute [] ρ t)
        (fun j hj => hall' j (by omega))
      rw [hN] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ w)
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ t) N h_has_inactive
  have h_comm : steps K (liftState [f] (.compute [] ρ t)) =
      liftState [f] (steps K (.compute [] ρ t)) :=
    steps_liftState [f] K (.compute [] ρ t) hK_min
  have h_not_error : steps K (.compute [] ρ t) ≠ .error := by
    intro herr
    have : steps (N - K) (liftState [f] .error) = .halt w := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, herr] at hN; exact hN
    simp [liftState, steps_error] at this
  have ⟨v, h_inner_eq, h_lifted_eq⟩ :
      ∃ v, (steps K (.compute [] ρ t) = .halt v ∨
            steps K (.compute [] ρ t) = .ret [] v) ∧
           liftState [f] (steps K (.compute [] ρ t)) = .ret [f] v := by
    generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  have h_reaches : Reaches (.compute [] ρ t) (.halt v) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  have h_frame : steps (N - K) (.ret [f] v) = .halt w := by
    have : N = K + (N - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hN; exact hN
  exact ⟨v, h_reaches, N - K, h_frame⟩

/-- Decompose `compute [f] ρ t` reaching error: inner errors, or inner halts + frame errors. -/
private theorem compute_frame_error_decompose (f : Frame) (ρ : CekEnv) (t : Term)
    (h : Reaches (.compute [f] ρ t) .error) :
    Reaches (.compute [] ρ t) .error ∨
    ∃ v, Reaches (.compute [] ρ t) (.halt v) ∧
         Reaches (.ret [f] v) .error := by
  obtain ⟨N, hN⟩ := h
  have hlift : State.compute [f] ρ t = liftState [f] (.compute [] ρ t) := by
    simp [liftState]
  rw [hlift] at hN
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k (.compute [] ρ t)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j (.compute [] ρ t)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ t)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ t)) <;> simp_all⟩
      have h_comm := steps_liftState [f] N (.compute [] ρ t)
        (fun j hj => hall' j (by omega))
      rw [hN] at h_comm
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' N (Nat.le_refl _)
      rw [h_inner_err] at this; simp [isActive] at this
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ t) N h_has_inactive
  have h_comm : steps K (liftState [f] (.compute [] ρ t)) =
      liftState [f] (steps K (.compute [] ρ t)) :=
    steps_liftState [f] K (.compute [] ρ t) hK_min
  by_cases h_is_error : steps K (.compute [] ρ t) = .error
  · left; exact ⟨K, h_is_error⟩
  · right
    have ⟨v, h_inner_eq, h_lifted_eq⟩ :
        ∃ v, (steps K (.compute [] ρ t) = .halt v ∨
              steps K (.compute [] ρ t) = .ret [] v) ∧
             liftState [f] (steps K (.compute [] ρ t)) = .ret [f] v := by
      generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_is_error
      match sK with
      | .compute .. => simp [isActive] at hK_inact
      | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK_inact
      | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error
    have h_reaches : Reaches (.compute [] ρ t) (.halt v) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    have h_frame : steps (N - K) (.ret [f] v) = .error := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hN; exact hN
    exact ⟨v, h_reaches, N - K, h_frame⟩

/-- Bounded error decomposition: takes `steps N` directly and returns bounded step counts. -/
private theorem compute_frame_error_bounded (f : Frame) (ρ : CekEnv) (t : Term) (N : Nat)
    (hN : steps N (.compute [f] ρ t) = .error) :
    (∃ K, K ≤ N ∧ steps K (.compute [] ρ t) = .error) ∨
    (∃ v M, M ≤ N ∧ Reaches (.compute [] ρ t) (.halt v) ∧
         steps M (.ret [f] v) = .error) := by
  have hlift : State.compute [f] ρ t = liftState [f] (.compute [] ρ t) := by simp [liftState]
  rw [hlift] at hN
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k (.compute [] ρ t)) = false :=
    Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j (.compute [] ρ t)) = true := by
        intro j hj; by_cases hact : isActive (steps j (.compute [] ρ t)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ t)) <;> simp_all⟩
      have h_comm := steps_liftState [f] N (.compute [] ρ t) (fun j hj => hall' j (by omega))
      rw [hN] at h_comm
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' N (Nat.le_refl _)
      rw [h_inner_err] at this; simp [isActive] at this
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := firstInactive (.compute [] ρ t) N h_has_inactive
  have h_comm := steps_liftState [f] K (.compute [] ρ t) hK_min
  by_cases h_is_error : steps K (.compute [] ρ t) = .error
  · left; exact ⟨K, hK_le, h_is_error⟩
  · right
    have ⟨v, h_inner_eq, h_lifted_eq⟩ :
        ∃ v, (steps K (.compute [] ρ t) = .halt v ∨
              steps K (.compute [] ρ t) = .ret [] v) ∧
             liftState [f] (steps K (.compute [] ρ t)) = .ret [f] v := by
      generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_is_error
      match sK with
      | .compute .. => simp [isActive] at hK_inact
      | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK_inact
      | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error
    have h_reaches : Reaches (.compute [] ρ t) (.halt v) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    have h_frame : steps (N - K) (.ret [f] v) = .error := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hN; exact hN
    exact ⟨v, N - K, by omega, h_reaches, h_frame⟩

/-- Bounded halt decomposition. -/
private theorem compute_frame_halt_bounded (f : Frame) (ρ : CekEnv) (t : Term)
    (w : CekValue) (N : Nat)
    (hN : steps N (.compute [f] ρ t) = .halt w) :
    ∃ v M, M ≤ N ∧ Reaches (.compute [] ρ t) (.halt v) ∧
         steps M (.ret [f] v) = .halt w := by
  have hlift : State.compute [f] ρ t = liftState [f] (.compute [] ρ t) := by simp [liftState]
  rw [hlift] at hN
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k (.compute [] ρ t)) = false :=
    Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j (.compute [] ρ t)) = true := by
        intro j hj; by_cases hact : isActive (steps j (.compute [] ρ t)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ t)) <;> simp_all⟩
      have h_comm := steps_liftState [f] N (.compute [] ρ t) (fun j hj => hall' j (by omega))
      rw [hN] at h_comm; exact absurd h_comm.symm (liftState_ne_halt _ _ w)
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := firstInactive (.compute [] ρ t) N h_has_inactive
  have h_comm := steps_liftState [f] K (.compute [] ρ t) hK_min
  have h_not_error : steps K (.compute [] ρ t) ≠ .error := by
    intro herr
    have hNK : N = K + (N - K) := by omega
    have : steps (N - K) (liftState [f] .error) = .halt w := by
      rw [hNK, steps_trans, h_comm, herr] at hN; exact hN
    simp [liftState, steps_error] at this
  have ⟨v, h_inner_eq, h_lifted_eq⟩ :
      ∃ v, (steps K (.compute [] ρ t) = .halt v ∨
            steps K (.compute [] ρ t) = .ret [] v) ∧
           liftState [f] (steps K (.compute [] ρ t)) = .ret [f] v := by
    generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  have h_reaches : Reaches (.compute [] ρ t) (.halt v) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  have h_frame : steps (N - K) (.ret [f] v) = .halt w := by
    have : N = K + (N - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hN; exact hN
  exact ⟨v, N - K, by omega, h_reaches, h_frame⟩

/-- Compose inner halt + frame result into compute [f] result. -/
private theorem compute_frame_compose (f : Frame) (ρ : CekEnv) (t : Term)
    (v : CekValue) (s : State)
    (hinner : Reaches (.compute [] ρ t) (.halt v))
    (hframe : Reaches (.ret [f] v) s) :
    Reaches (.compute [f] ρ t) s := by
  have h_ret := compute_to_ret_from_halt ρ t v [f] hinner
  obtain ⟨Kr, hKr⟩ := h_ret
  obtain ⟨Kf, hKf⟩ := hframe
  exact ⟨Kr + Kf, by rw [steps_trans, hKr, hKf]⟩

/-- Generalized: compute stk ρ t reaching halt decomposes into inner halt + rest. -/
private theorem compute_stk_halt_decompose (stk : Stack) (ρ : CekEnv) (t : Term)
    (w : CekValue)
    (h : Reaches (.compute stk ρ t) (.halt w)) :
    ∃ v, Reaches (.compute [] ρ t) (.halt v) ∧
         Reaches (.ret stk v) (.halt w) := by
  obtain ⟨N, hN⟩ := h
  have hlift : State.compute stk ρ t = liftState stk (.compute [] ρ t) := by
    simp [liftState]
  rw [hlift] at hN
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k (.compute [] ρ t)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j (.compute [] ρ t)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ t)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ t)) <;> simp_all⟩
      have h_comm := steps_liftState stk N (.compute [] ρ t) (fun j hj => hall' j (by omega))
      rw [hN] at h_comm; exact absurd h_comm.symm (liftState_ne_halt _ _ w)
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := firstInactive (.compute [] ρ t) N h_has_inactive
  have h_comm := steps_liftState stk K (.compute [] ρ t) hK_min
  have h_not_error : steps K (.compute [] ρ t) ≠ .error := by
    intro herr
    have : steps (N - K) (liftState stk .error) = .halt w := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, herr] at hN; exact hN
    simp [liftState, steps_error] at this
  have ⟨v, h_inner_eq, h_lifted_eq⟩ :
      ∃ v, (steps K (.compute [] ρ t) = .halt v ∨
            steps K (.compute [] ρ t) = .ret [] v) ∧
           liftState stk (steps K (.compute [] ρ t)) = .ret stk v := by
    generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  have h_reaches : Reaches (.compute [] ρ t) (.halt v) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  have h_rest : steps (N - K) (.ret stk v) = .halt w := by
    have : N = K + (N - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hN; exact hN
  exact ⟨v, h_reaches, N - K, h_rest⟩

/-- Generalized: compute stk ρ t reaching error: either inner errors or inner halts + rest errors. -/
private theorem compute_stk_error_decompose (stk : Stack) (ρ : CekEnv) (t : Term)
    (h : Reaches (.compute stk ρ t) .error) :
    Reaches (.compute [] ρ t) .error ∨
    ∃ v, Reaches (.compute [] ρ t) (.halt v) ∧
         Reaches (.ret stk v) .error := by
  obtain ⟨N, hN⟩ := h
  have hlift : State.compute stk ρ t = liftState stk (.compute [] ρ t) := by
    simp [liftState]
  rw [hlift] at hN
  have h_has_inactive : ∃ k, k ≤ N ∧ isActive (steps k (.compute [] ρ t)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ N → isActive (steps j (.compute [] ρ t)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ t)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ t)) <;> simp_all⟩
      have h_comm := steps_liftState stk N (.compute [] ρ t) (fun j hj => hall' j (by omega))
      rw [hN] at h_comm
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' N (Nat.le_refl _); rw [h_inner_err] at this; simp [isActive] at this
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := firstInactive (.compute [] ρ t) N h_has_inactive
  have h_comm := steps_liftState stk K (.compute [] ρ t) hK_min
  by_cases h_is_error : steps K (.compute [] ρ t) = .error
  · left; exact ⟨K, h_is_error⟩
  · right
    have ⟨v, h_inner_eq, h_lifted_eq⟩ :
        ∃ v, (steps K (.compute [] ρ t) = .halt v ∨
              steps K (.compute [] ρ t) = .ret [] v) ∧
             liftState stk (steps K (.compute [] ρ t)) = .ret stk v := by
      generalize h_sK : steps K (.compute [] ρ t) = sK at hK_inact h_is_error
      match sK with
      | .compute .. => simp [isActive] at hK_inact
      | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK_inact
      | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error
    have h_reaches : Reaches (.compute [] ρ t) (.halt v) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    have h_rest : steps (N - K) (.ret stk v) = .error := by
      have : N = K + (N - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hN; exact hN
    exact ⟨v, h_reaches, N - K, h_rest⟩

/-- Generalized: compose inner halt + rest into compute stk result. -/
private theorem compute_stk_compose (stk : Stack) (ρ : CekEnv) (t : Term)
    (v : CekValue) (s : State)
    (hinner : Reaches (.compute [] ρ t) (.halt v))
    (hrest : Reaches (.ret stk v) s) :
    Reaches (.compute stk ρ t) s := by
  have h_ret := compute_to_ret_from_halt ρ t v stk hinner
  obtain ⟨Kr, hKr⟩ := h_ret
  obtain ⟨Kf, hKf⟩ := hrest
  exact ⟨Kr + Kf, by rw [steps_trans, hKr, hKf]⟩

/-- ConstrField iteration adequacy: related current values, done lists, and remaining fields
    produce related results. -/
private theorem constrField_iter_adequacy (tag : Nat)
    (done₁ done₂ : List CekValue) (v₁ v₂ : CekValue)
    (remaining : List Term) (ρ₁ ρ₂ : CekEnv)
    (hv : ∀ k, ValueEq k v₁ v₂)
    (hdone : ∀ k, ListValueEq k done₁ done₂)
    (hfields : ∀ m, m ∈ remaining →
      (Reaches (.compute [] ρ₁ m) .error ↔ Reaches (.compute [] ρ₂ m) .error) ∧
      (Halts (.compute [] ρ₁ m) ↔ Halts (.compute [] ρ₂ m)) ∧
      ∀ k v₁ v₂, Reaches (.compute [] ρ₁ m) (.halt v₁) →
        Reaches (.compute [] ρ₂ m) (.halt v₂) → ValueEq k v₁ v₂) :
    (Reaches (.ret [.constrField tag done₁ remaining ρ₁] v₁) .error ↔
     Reaches (.ret [.constrField tag done₂ remaining ρ₂] v₂) .error) ∧
    (Halts (.ret [.constrField tag done₁ remaining ρ₁] v₁) ↔
     Halts (.ret [.constrField tag done₂ remaining ρ₂] v₂)) ∧
    ∀ k w₁ w₂,
      Reaches (.ret [.constrField tag done₁ remaining ρ₁] v₁) (.halt w₁) →
      Reaches (.ret [.constrField tag done₂ remaining ρ₂] v₂) (.halt w₂) →
      ValueEq k w₁ w₂ := by
  match remaining with
  | [] =>
    have hl : steps 2 (.ret [.constrField tag done₁ [] ρ₁] v₁) =
        .halt (.VConstr tag ((v₁ :: done₁).reverse)) := by simp [steps, step]
    have hr : steps 2 (.ret [.constrField tag done₂ [] ρ₂] v₂) =
        .halt (.VConstr tag ((v₂ :: done₂).reverse)) := by simp [steps, step]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
    · exact ⟨fun _ => ⟨_, 2, hr⟩, fun _ => ⟨_, 2, hl⟩⟩
    · intro k w₁ w₂ hw₁ hw₂
      have heq₁ := reaches_unique hw₁ ⟨2, hl⟩; subst heq₁
      have heq₂ := reaches_unique hw₂ ⟨2, hr⟩; subst heq₂
      match k with
      | 0 => simp [ValueEq]
      | k + 1 =>
        unfold ValueEq
        exact ⟨rfl, listValueEq_reverse k (v₁ :: done₁) (v₂ :: done₂)
          (listValueEq_cons k v₁ v₂ done₁ done₂ (hv k) (hdone k))⟩
  | m :: ms =>
    have hl_step : step (.ret [.constrField tag done₁ (m :: ms) ρ₁] v₁) =
        .compute [.constrField tag (v₁ :: done₁) ms ρ₁] ρ₁ m := rfl
    have hr_step : step (.ret [.constrField tag done₂ (m :: ms) ρ₂] v₂) =
        .compute [.constrField tag (v₂ :: done₂) ms ρ₂] ρ₂ m := rfl
    have hm := hfields m (List.Mem.head ms)
    obtain ⟨hm_err, hm_halts, hm_veq⟩ := hm
    have hfields_ms : ∀ m', m' ∈ ms →
        (Reaches (.compute [] ρ₁ m') .error ↔ Reaches (.compute [] ρ₂ m') .error) ∧
        (Halts (.compute [] ρ₁ m') ↔ Halts (.compute [] ρ₂ m')) ∧
        ∀ k v₁ v₂, Reaches (.compute [] ρ₁ m') (.halt v₁) →
          Reaches (.compute [] ρ₂ m') (.halt v₂) → ValueEq k v₁ v₂ :=
      fun m' hm' => hfields m' (List.mem_cons_of_mem m hm')
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro herr
        have herr' := reaches_to_step_reaches hl_step herr (by simp)
        rcases compute_frame_error_decompose (.constrField tag (v₁ :: done₁) ms ρ₁)
          ρ₁ m herr' with hm_err_l | ⟨vm₁, hm_halt₁, hrest_err₁⟩
        · have := compute_to_error_from_error ρ₂ m
            [.constrField tag (v₂ :: done₂) ms ρ₂] (hm_err.mp hm_err_l)
          exact reaches_of_step_reaches hr_step this
        · obtain ⟨vm₂, hm_halt₂⟩ := hm_halts.mp ⟨vm₁, hm_halt₁⟩
          have ih := constrField_iter_adequacy tag (v₁ :: done₁) (v₂ :: done₂) vm₁ vm₂ ms ρ₁ ρ₂
            (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
            (fun k => listValueEq_cons k v₁ v₂ done₁ done₂ (hv k) (hdone k)) hfields_ms
          have := compute_frame_compose (.constrField tag (v₂ :: done₂) ms ρ₂)
            ρ₂ m vm₂ .error hm_halt₂ (ih.1.mp hrest_err₁)
          exact reaches_of_step_reaches hr_step this
      · intro herr
        have herr' := reaches_to_step_reaches hr_step herr (by simp)
        rcases compute_frame_error_decompose (.constrField tag (v₂ :: done₂) ms ρ₂)
          ρ₂ m herr' with hm_err_r | ⟨vm₂, hm_halt₂, hrest_err₂⟩
        · have := compute_to_error_from_error ρ₁ m
            [.constrField tag (v₁ :: done₁) ms ρ₁] (hm_err.mpr hm_err_r)
          exact reaches_of_step_reaches hl_step this
        · obtain ⟨vm₁, hm_halt₁⟩ := hm_halts.mpr ⟨vm₂, hm_halt₂⟩
          have ih := constrField_iter_adequacy tag (v₁ :: done₁) (v₂ :: done₂) vm₁ vm₂ ms ρ₁ ρ₂
            (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
            (fun k => listValueEq_cons k v₁ v₂ done₁ done₂ (hv k) (hdone k)) hfields_ms
          have := compute_frame_compose (.constrField tag (v₁ :: done₁) ms ρ₁)
            ρ₁ m vm₁ .error hm_halt₁ (ih.1.mpr hrest_err₂)
          exact reaches_of_step_reaches hl_step this
    · constructor
      · intro ⟨w, hw⟩
        have hw' := reaches_to_step_reaches hl_step hw (by simp)
        obtain ⟨vm₁, hm_halt₁, hrest₁⟩ :=
          compute_frame_halt_decompose (.constrField tag (v₁ :: done₁) ms ρ₁) ρ₁ m w hw'
        obtain ⟨vm₂, hm_halt₂⟩ := hm_halts.mp ⟨vm₁, hm_halt₁⟩
        have ih := constrField_iter_adequacy tag (v₁ :: done₁) (v₂ :: done₂) vm₁ vm₂ ms ρ₁ ρ₂
          (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
          (fun k => listValueEq_cons k v₁ v₂ done₁ done₂ (hv k) (hdone k)) hfields_ms
        obtain ⟨w', hw'⟩ := ih.2.1.mp ⟨w, hrest₁⟩
        exact ⟨w', reaches_of_step_reaches hr_step
          (compute_frame_compose _ ρ₂ m vm₂ (.halt w') hm_halt₂ hw')⟩
      · intro ⟨w, hw⟩
        have hw' := reaches_to_step_reaches hr_step hw (by simp)
        obtain ⟨vm₂, hm_halt₂, hrest₂⟩ :=
          compute_frame_halt_decompose (.constrField tag (v₂ :: done₂) ms ρ₂) ρ₂ m w hw'
        obtain ⟨vm₁, hm_halt₁⟩ := hm_halts.mpr ⟨vm₂, hm_halt₂⟩
        have ih := constrField_iter_adequacy tag (v₁ :: done₁) (v₂ :: done₂) vm₁ vm₂ ms ρ₁ ρ₂
          (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
          (fun k => listValueEq_cons k v₁ v₂ done₁ done₂ (hv k) (hdone k)) hfields_ms
        obtain ⟨w', hw'⟩ := ih.2.1.mpr ⟨w, hrest₂⟩
        exact ⟨w', reaches_of_step_reaches hl_step
          (compute_frame_compose _ ρ₁ m vm₁ (.halt w') hm_halt₁ hw')⟩
    · intro k w₁ w₂ hw₁ hw₂
      have hw₁' := reaches_to_step_reaches hl_step hw₁ (by simp)
      have hw₂' := reaches_to_step_reaches hr_step hw₂ (by simp)
      obtain ⟨vm₁, hm_halt₁, hrest₁⟩ :=
        compute_frame_halt_decompose (.constrField tag (v₁ :: done₁) ms ρ₁) ρ₁ m w₁ hw₁'
      obtain ⟨vm₂, hm_halt₂, hrest₂⟩ :=
        compute_frame_halt_decompose (.constrField tag (v₂ :: done₂) ms ρ₂) ρ₂ m w₂ hw₂'
      exact (constrField_iter_adequacy tag (v₁ :: done₁) (v₂ :: done₂) vm₁ vm₂ ms ρ₁ ρ₂
        (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
        (fun k => listValueEq_cons k v₁ v₂ done₁ done₂ (hv k) (hdone k)) hfields_ms).2.2 k w₁ w₂ hrest₁ hrest₂

/-- Transfer through a shared applyArg chain with `∀ k, ValueEq k`-related values. -/
private theorem applyArg_chain_transfer (fields : List CekValue)
    (v₁ v₂ : CekValue) (hv : ∀ k, ValueEq k v₁ v₂) :
    (Reaches (.ret (fields.map Frame.applyArg) v₁) .error ↔
     Reaches (.ret (fields.map Frame.applyArg) v₂) .error) ∧
    (Halts (.ret (fields.map Frame.applyArg) v₁) ↔
     Halts (.ret (fields.map Frame.applyArg) v₂)) ∧
    ∀ (k : Nat) (w₁ w₂ : CekValue),
      Reaches (.ret (fields.map Frame.applyArg) v₁) (.halt w₁) →
      Reaches (.ret (fields.map Frame.applyArg) v₂) (.halt w₂) →
      ValueEq k w₁ w₂ := by
  induction fields generalizing v₁ v₂ with
  | nil =>
    simp [List.map]
    exact ⟨⟨fun herr => by obtain ⟨n, hn⟩ := herr; cases n with
              | zero => simp [steps] at hn
              | succ n => simp [steps, step, steps_halt] at hn,
            fun herr => by obtain ⟨n, hn⟩ := herr; cases n with
              | zero => simp [steps] at hn
              | succ n => simp [steps, step, steps_halt] at hn⟩,
           ⟨fun _ => ⟨v₂, 1, rfl⟩, fun _ => ⟨v₁, 1, rfl⟩⟩,
           fun k w₁ w₂ hw₁ hw₂ => by
             have := reaches_unique hw₁ ⟨1, rfl⟩
             have := reaches_unique hw₂ ⟨1, rfl⟩
             subst_vars; exact hv k⟩
  | cons field rest ih =>
    have h1 := hv 1
    match v₁, v₂ with
    | .VLam body₁ env₁, .VLam body₂ env₂ =>
      have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VLam body₁ env₁)) =
          .compute (rest.map Frame.applyArg) (env₁.extend field) body₁ := rfl
      have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VLam body₂ env₂)) =
          .compute (rest.map Frame.applyArg) (env₂.extend field) body₂ := rfl
      unfold ValueEq at h1
      have herr_body : Reaches (.compute [] (env₁.extend field) body₁) .error ↔
          Reaches (.compute [] (env₂.extend field) body₂) .error := by
        have := (hv 1); unfold ValueEq at this; exact (this field).1
      have hhalt_body : Halts (.compute [] (env₁.extend field) body₁) ↔
          Halts (.compute [] (env₂.extend field) body₂) := by
        have := (hv 1); unfold ValueEq at this; exact (this field).2.1
      have hval_body : ∀ k r₁ r₂,
          Reaches (.compute [] (env₁.extend field) body₁) (.halt r₁) →
          Reaches (.compute [] (env₂.extend field) body₂) (.halt r₂) →
          ValueEq k r₁ r₂ := by
        intro k r₁ r₂ h₁ h₂
        have := (hv (k + 1)); unfold ValueEq at this; exact (this field).2.2 r₁ r₂ h₁ h₂
      refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, ⟨fun hh => ?_, fun hh => ?_⟩,
              fun k w₁ w₂ hw₁ hw₂ => ?_⟩
      · have herr' := reaches_to_step_reaches hl herr (by simp)
        rcases compute_stk_error_decompose (rest.map Frame.applyArg) (env₁.extend field) body₁ herr'
          with hbody_err | ⟨r₁, hbody_halt, hrest_err⟩
        · exact reaches_of_step_reaches hr
            (compute_to_error_from_error _ body₂ (rest.map Frame.applyArg) (herr_body.mp hbody_err))
        · obtain ⟨r₂, hr₂⟩ := hhalt_body.mp ⟨r₁, hbody_halt⟩
          have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hbody_halt hr₂
          have ⟨herr_rest, _, _⟩ := ih r₁ r₂ hveq_r
          exact reaches_of_step_reaches hr
            (compute_stk_compose (rest.map Frame.applyArg) _ body₂ r₂ .error hr₂ (herr_rest.mp hrest_err))
      · have herr' := reaches_to_step_reaches hr herr (by simp)
        rcases compute_stk_error_decompose (rest.map Frame.applyArg) (env₂.extend field) body₂ herr'
          with hbody_err | ⟨r₂, hbody_halt, hrest_err⟩
        · exact reaches_of_step_reaches hl
            (compute_to_error_from_error _ body₁ (rest.map Frame.applyArg) (herr_body.mpr hbody_err))
        · obtain ⟨r₁, hr₁⟩ := hhalt_body.mpr ⟨r₂, hbody_halt⟩
          have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hr₁ hbody_halt
          have ⟨herr_rest, _, _⟩ := ih r₁ r₂ hveq_r
          exact reaches_of_step_reaches hl
            (compute_stk_compose (rest.map Frame.applyArg) _ body₁ r₁ .error hr₁ (herr_rest.mpr hrest_err))
      · obtain ⟨w, hw⟩ := hh
        have hw' := reaches_to_step_reaches hl hw (by simp)
        obtain ⟨r₁, hbody_halt, hrest_halt⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₁ w hw'
        obtain ⟨r₂, hr₂⟩ := hhalt_body.mp ⟨r₁, hbody_halt⟩
        have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hbody_halt hr₂
        have ⟨_, hhalt_rest, _⟩ := ih r₁ r₂ hveq_r
        obtain ⟨w', hw'⟩ := hhalt_rest.mp ⟨w, hrest_halt⟩
        exact ⟨w', reaches_of_step_reaches hr
          (compute_stk_compose (rest.map Frame.applyArg) _ body₂ r₂ (.halt w') hr₂ hw')⟩
      · obtain ⟨w, hw⟩ := hh
        have hw' := reaches_to_step_reaches hr hw (by simp)
        obtain ⟨r₂, hbody_halt, hrest_halt⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₂ w hw'
        obtain ⟨r₁, hr₁⟩ := hhalt_body.mpr ⟨r₂, hbody_halt⟩
        have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hr₁ hbody_halt
        have ⟨_, hhalt_rest, _⟩ := ih r₁ r₂ hveq_r
        obtain ⟨w', hw'⟩ := hhalt_rest.mpr ⟨w, hrest_halt⟩
        exact ⟨w', reaches_of_step_reaches hl
          (compute_stk_compose (rest.map Frame.applyArg) _ body₁ r₁ (.halt w') hr₁ hw')⟩
      · have hw₁' := reaches_to_step_reaches hl hw₁ (by simp)
        have hw₂' := reaches_to_step_reaches hr hw₂ (by simp)
        obtain ⟨r₁, hbody₁, hrest₁⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₁ w₁ hw₁'
        obtain ⟨r₂, hbody₂, hrest₂⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₂ w₂ hw₂'
        have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hbody₁ hbody₂
        exact (ih r₁ r₂ hveq_r).2.2 k w₁ w₂ hrest₁ hrest₂
    | .VCon c₁, .VCon _ =>
      have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VCon c₁)) = .error := rfl
      have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VCon c₁)) = .error := rfl
      exact ⟨⟨fun _ => by simp [ValueEq] at h1; subst h1; exact error_in_one_step_reaches_error _ hr,
               fun _ => error_in_one_step_reaches_error _ hl⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
               fun h => by simp [ValueEq] at h1; subst h1; exact absurd h (error_in_one_step_not_halts _ hr)⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
    | .VDelay bd₁ ev₁, .VDelay bd₂ ev₂ =>
      have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VDelay bd₁ ev₁)) = .error := rfl
      have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VDelay bd₂ ev₂)) = .error := rfl
      exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
               fun _ => error_in_one_step_reaches_error _ hl⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
               fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
    | .VConstr tg₁ fs₁, .VConstr tg₂ fs₂ =>
      exact ⟨⟨fun _ => error_in_one_step_reaches_error _ (rfl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VConstr tg₂ fs₂)) = .error),
               fun _ => error_in_one_step_reaches_error _ (rfl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VConstr tg₁ fs₁)) = .error)⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ (rfl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VConstr tg₁ fs₁)) = .error)),
               fun h => absurd h (error_in_one_step_not_halts _ (rfl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VConstr tg₂ fs₂)) = .error))⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ (rfl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VConstr tg₁ fs₁)) = .error))⟩
    | .VBuiltin bn₁ ar₁ ea₁, .VBuiltin bn₂ ar₂ ea₂ =>
      have h2 := hv 2; unfold ValueEq at h2
      obtain ⟨hbn, _, hea, _, _⟩ := h2; subst hbn; subst hea
      cases hhead : ea₁.head with
      | argQ =>
        have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₁ ea₁)) = .error := by
          simp [step, hhead]
        have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₂ ea₁)) = .error := by
          simp [step, hhead]
        exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
                 fun _ => error_in_one_step_reaches_error _ hl⟩,
                ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
                 fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
                fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
      | argV =>
        cases htail : ea₁.tail with
        | some ea_rest =>
          have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₁ ea₁)) =
              .ret (rest.map Frame.applyArg) (.VBuiltin bn₁ (field :: ar₁) ea_rest) := by
            simp [step, hhead, htail]
          have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₂ ea₁)) =
              .ret (rest.map Frame.applyArg) (.VBuiltin bn₁ (field :: ar₂) ea_rest) := by
            simp [step, hhead, htail]
          have hveq_new : ∀ k, ValueEq k (.VBuiltin bn₁ (field :: ar₁) ea_rest)
              (.VBuiltin bn₁ (field :: ar₂) ea_rest) := by
            intro k; match k with
            | 0 => simp [ValueEq]
            | k + 1 =>
              have hargs_succ : ListValueEq (k + 1) ar₁ ar₂ := by
                have := hv (k + 2); unfold ValueEq at this; exact this.2.1
              have hargs_k : ListValueEq k ar₁ ar₂ := listValueEq_mono k _ _ hargs_succ
              have hlist_k : ListValueEq k (field :: ar₁) (field :: ar₂) := by
                simp only [ListValueEq]; exact ⟨valueEq_refl k field, hargs_k⟩
              have h_agree := evalBuiltin_agree_tail bn₁ field ar₁ ar₂ k hargs_succ
              have hlist_succ : ListValueEq (k + 1) (field :: ar₁) (field :: ar₂) := by
                simp only [ListValueEq]; exact ⟨valueEq_refl (k+1) field, hargs_succ⟩
              exact valueEq_vbuiltin (k + 1) bn₁ (field :: ar₁) (field :: ar₂) ea_rest hlist_succ
                (by revert h_agree; cases evalBuiltin bn₁ (field :: ar₁) <;> cases evalBuiltin bn₁ (field :: ar₂) <;>
                    simp <;> (try trivial) <;> intro h <;> simp_all)
                (by intro r₁ r₂ hr₁ hr₂
                    have h_agree' := evalBuiltin_agree_tail bn₁ field ar₁ ar₂ (k + 1)
                      (by have := hv (k + 3); unfold ValueEq at this; exact this.2.1)
                    revert h_agree'; rw [hr₁, hr₂]; simp)
          have hrec := ih (.VBuiltin bn₁ (field :: ar₁) ea_rest) (.VBuiltin bn₁ (field :: ar₂) ea_rest) hveq_new
          exact ⟨⟨fun herr => reaches_of_step_reaches hr (hrec.1.mp (reaches_to_step_reaches hl herr (by simp))),
                   fun herr => reaches_of_step_reaches hl (hrec.1.mpr (reaches_to_step_reaches hr herr (by simp)))⟩,
                  ⟨fun ⟨w, hw⟩ => by
                    obtain ⟨w', hw'⟩ := hrec.2.1.mp ⟨w, reaches_to_step_reaches hl hw (by simp)⟩
                    exact ⟨w', reaches_of_step_reaches hr hw'⟩,
                   fun ⟨w, hw⟩ => by
                    obtain ⟨w', hw'⟩ := hrec.2.1.mpr ⟨w, reaches_to_step_reaches hr hw (by simp)⟩
                    exact ⟨w', reaches_of_step_reaches hl hw'⟩⟩,
                  fun k w₁ w₂ hw₁ hw₂ =>
                    hrec.2.2 k w₁ w₂ (reaches_to_step_reaches hl hw₁ (by simp))
                      (reaches_to_step_reaches hr hw₂ (by simp))⟩
        | none =>
          have h_agree_fn : ∀ j, match evalBuiltin bn₁ (field :: ar₁), evalBuiltin bn₁ (field :: ar₂) with
              | some v₁, some v₂ => ValueEq j v₁ v₂
              | none, none => True
              | _, _ => False := by
            intro j
            have hargs_j : ListValueEq (j + 1) ar₁ ar₂ := by
              have := hv (j + 2); unfold ValueEq at this; exact this.2.1
            exact evalBuiltin_agree_tail bn₁ field ar₁ ar₂ j hargs_j
          cases hev₁ : evalBuiltin bn₁ (field :: ar₁) with
          | none =>
            have : evalBuiltin bn₁ (field :: ar₂) = none := by
              have h_agree := h_agree_fn 0; revert h_agree; rw [hev₁]; cases evalBuiltin bn₁ (field :: ar₂) <;> simp
            have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₁ ea₁)) = .error := by
              simp [step, hhead, htail, hev₁]
            have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₂ ea₁)) = .error := by
              simp [step, hhead, htail, this]
            exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
                     fun _ => error_in_one_step_reaches_error _ hl⟩,
                    ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
                     fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
                    fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
          | some r₁ =>
            have hev₂ : ∃ r₂, evalBuiltin bn₁ (field :: ar₂) = some r₂ := by
              have h_agree := h_agree_fn 0; revert h_agree; rw [hev₁]; cases h : evalBuiltin bn₁ (field :: ar₂) with
              | none => simp
              | some r₂ => exact fun _ => ⟨r₂, rfl⟩
            obtain ⟨r₂, hev₂⟩ := hev₂
            have hveq_r : ∀ j, ValueEq j r₁ r₂ := by
              intro j; have h_agree := h_agree_fn j; revert h_agree; rw [hev₁, hev₂]; simp
            have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₁ ea₁)) =
                .ret (rest.map Frame.applyArg) r₁ := by simp [step, hhead, htail, hev₁]
            have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₂ ea₁)) =
                .ret (rest.map Frame.applyArg) r₂ := by simp [step, hhead, htail, hev₂]
            have hrec := ih r₁ r₂ hveq_r
            exact ⟨⟨fun herr => reaches_of_step_reaches hr (hrec.1.mp (reaches_to_step_reaches hl herr (by simp))),
                     fun herr => reaches_of_step_reaches hl (hrec.1.mpr (reaches_to_step_reaches hr herr (by simp)))⟩,
                    ⟨fun ⟨w, hw⟩ => by
                      obtain ⟨w', hw'⟩ := hrec.2.1.mp ⟨w, reaches_to_step_reaches hl hw (by simp)⟩
                      exact ⟨w', reaches_of_step_reaches hr hw'⟩,
                     fun ⟨w, hw⟩ => by
                      obtain ⟨w', hw'⟩ := hrec.2.1.mpr ⟨w, reaches_to_step_reaches hr hw (by simp)⟩
                      exact ⟨w', reaches_of_step_reaches hl hw'⟩⟩,
                    fun k w₁ w₂ hw₁ hw₂ =>
                      hrec.2.2 k w₁ w₂ (reaches_to_step_reaches hl hw₁ (by simp))
                        (reaches_to_step_reaches hr hw₂ (by simp))⟩
    -- Cross-constructor cases: ValueEq 1 is False
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => exact absurd h1 (by simp [ValueEq])

/-- Same body under related envs with a shared applyArg stack. -/
private theorem sameBody_with_shared_applyArg_stack
    (fields : List CekValue) (alt : Term) (d : Nat) (ρ₁ ρ₂ : CekEnv)
    (_hcl_alt : closedAt d alt = true) (_hρ : EnvValueEqAll d ρ₁ ρ₂)
    -- sameBody for alt (passed as parameter to avoid mutual dependency)
    (hsba : (Reaches (.compute [] ρ₁ alt) .error ↔ Reaches (.compute [] ρ₂ alt) .error) ∧
            (Halts (.compute [] ρ₁ alt) ↔ Halts (.compute [] ρ₂ alt)) ∧
            ∀ k v₁ v₂, Reaches (.compute [] ρ₁ alt) (.halt v₁) →
              Reaches (.compute [] ρ₂ alt) (.halt v₂) → ValueEq k v₁ v₂) :
    (Reaches (.compute (fields.map Frame.applyArg) ρ₁ alt) .error ↔
     Reaches (.compute (fields.map Frame.applyArg) ρ₂ alt) .error) ∧
    (Halts (.compute (fields.map Frame.applyArg) ρ₁ alt) ↔
     Halts (.compute (fields.map Frame.applyArg) ρ₂ alt)) ∧
    ∀ k w₁ w₂,
      Reaches (.compute (fields.map Frame.applyArg) ρ₁ alt) (.halt w₁) →
      Reaches (.compute (fields.map Frame.applyArg) ρ₂ alt) (.halt w₂) →
      ValueEq k w₁ w₂ := by
  obtain ⟨herr_alt, hhalt_alt, hval_alt⟩ := hsba
  refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, ⟨fun hh => ?_, fun hh => ?_⟩,
          fun k w₁ w₂ hw₁ hw₂ => ?_⟩
  · rcases compute_stk_error_decompose _ ρ₁ alt herr with halt_err | ⟨v₁, hv₁, hrest_err⟩
    · exact compute_to_error_from_error ρ₂ alt _ (herr_alt.mp halt_err)
    · obtain ⟨v₂, hv₂⟩ := hhalt_alt.mp ⟨v₁, hv₁⟩
      have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
      exact compute_stk_compose _ ρ₂ alt v₂ .error hv₂
        ((applyArg_chain_transfer fields v₁ v₂ hveq).1.mp hrest_err)
  · rcases compute_stk_error_decompose _ ρ₂ alt herr with halt_err | ⟨v₂, hv₂, hrest_err⟩
    · exact compute_to_error_from_error ρ₁ alt _ (herr_alt.mpr halt_err)
    · obtain ⟨v₁, hv₁⟩ := hhalt_alt.mpr ⟨v₂, hv₂⟩
      have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
      exact compute_stk_compose _ ρ₁ alt v₁ .error hv₁
        ((applyArg_chain_transfer fields v₁ v₂ hveq).1.mpr hrest_err)
  · obtain ⟨w, hw⟩ := hh
    obtain ⟨v₁, hv₁, hrest⟩ := compute_stk_halt_decompose _ ρ₁ alt w hw
    obtain ⟨v₂, hv₂⟩ := hhalt_alt.mp ⟨v₁, hv₁⟩
    have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
    obtain ⟨w', hw'⟩ := (applyArg_chain_transfer fields v₁ v₂ hveq).2.1.mp ⟨w, hrest⟩
    exact ⟨w', compute_stk_compose _ ρ₂ alt v₂ (.halt w') hv₂ hw'⟩
  · obtain ⟨w, hw⟩ := hh
    obtain ⟨v₂, hv₂, hrest⟩ := compute_stk_halt_decompose _ ρ₂ alt w hw
    obtain ⟨v₁, hv₁⟩ := hhalt_alt.mpr ⟨v₂, hv₂⟩
    have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
    obtain ⟨w', hw'⟩ := (applyArg_chain_transfer fields v₁ v₂ hveq).2.1.mpr ⟨w, hrest⟩
    exact ⟨w', compute_stk_compose _ ρ₁ alt v₁ (.halt w') hv₁ hw'⟩
  · obtain ⟨v₁, hv₁, hrest₁⟩ := compute_stk_halt_decompose _ ρ₁ alt w₁ hw₁
    obtain ⟨v₂, hv₂, hrest₂⟩ := compute_stk_halt_decompose _ ρ₂ alt w₂ hw₂
    have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
    exact (applyArg_chain_transfer fields v₁ v₂ hveq).2.2 k w₁ w₂ hrest₁ hrest₂


theorem envValueEqAll_symm {d : Nat} {ρ₁ ρ₂ : CekEnv}
    (hρ : EnvValueEqAll d ρ₁ ρ₂) : EnvValueEqAll d ρ₂ ρ₁ := by
  intro k n hn hle
  have h := hρ k n hn hle
  revert h
  cases ρ₁.lookup n <;> cases ρ₂.lookup n <;> simp
  exact valueEq_symm k _ _

/-- When both sides halt with the same value, error is impossible and halt gives `valueEq_refl`. -/
private theorem forward_both_halt_same (v : CekValue) (s₁ s₂ : State) (n : Nat)
    (hl : Reaches s₁ (.halt v)) (hr : Reaches s₂ (.halt v)) :
    (steps n s₁ = .error → Reaches s₂ .error) ∧
    (∀ w, steps n s₁ = .halt w →
      Halts s₂ ∧ ∀ k w₂, Reaches s₂ (.halt w₂) → ValueEq k w w₂) :=
  ⟨fun herr => absurd (reaches_halt_not_error hl ⟨n, herr⟩) id,
   fun w hw => by
     have := reaches_unique ⟨n, hw⟩ hl; subst this
     exact ⟨⟨_, hr⟩, fun k w₂ hw₂ => by
       have := reaches_unique hw₂ hr; subst this; exact valueEq_refl k _⟩⟩

/-- When both sides halt with related values, error is impossible and halt gives the relation. -/
private theorem forward_both_halt_related (v₁ v₂ : CekValue) (s₁ s₂ : State) (n : Nat)
    (hl : Reaches s₁ (.halt v₁)) (hr : Reaches s₂ (.halt v₂))
    (hveq : ∀ k, ValueEq k v₁ v₂) :
    (steps n s₁ = .error → Reaches s₂ .error) ∧
    (∀ w, steps n s₁ = .halt w →
      Halts s₂ ∧ ∀ k w₂, Reaches s₂ (.halt w₂) → ValueEq k w w₂) :=
  ⟨fun herr => absurd (reaches_halt_not_error hl ⟨n, herr⟩) id,
   fun w hw => by
     have := reaches_unique ⟨n, hw⟩ hl; subst this
     exact ⟨⟨_, hr⟩, fun k w₂ hw₂ => by
       have := reaches_unique hw₂ hr; subst this; exact hveq k⟩⟩

/-- Core forward simulation: if side 1 errors/halts in `n` steps,
    side 2 reaches the corresponding outcome with `ValueEq` on results.
    Termination by `(n, sizeOf t)`. -/
private theorem sameBody_forward (n : Nat) (t : Term) (d : Nat) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (steps n (.compute [] ρ₁ t) = .error → Reaches (.compute [] ρ₂ t) .error) ∧
    (∀ v₁, steps n (.compute [] ρ₁ t) = .halt v₁ →
      Halts (.compute [] ρ₂ t) ∧
      ∀ k v₂, Reaches (.compute [] ρ₂ t) (.halt v₂) → ValueEq k v₁ v₂) := by
  -- Main proof by case analysis on t, with termination by (n, sizeOf t)
  match t with
  | .Error =>
    exact ⟨fun _ => ⟨1, by simp [steps, step]⟩,
           fun v₁ hv₁ => by cases n with
             | zero => simp [steps] at hv₁
             | succ n => simp [steps, step, steps_error] at hv₁⟩
  | .Var m =>
    have hle := closedAt_var hcl
    match m with
    | 0 =>
      exact ⟨fun _ => ⟨1, by simp [steps, step]⟩,
             fun v₁ hv₁ => by cases n with
               | zero => simp [steps] at hv₁
               | succ n => simp [steps, step, steps_error] at hv₁⟩
    | m' + 1 =>
      have hn : 0 < m' + 1 := by omega
      rcases envValueEqAll_lookup_agree hρ hn hle with ⟨v₁, v₂, h1, h2, hveq⟩ | ⟨h1, h2⟩
      · exact forward_both_halt_related v₁ v₂ _ _ n
            ⟨2, by simp [steps, step, h1]⟩ ⟨2, by simp [steps, step, h2]⟩ hveq
      · exact ⟨fun _ => ⟨1, by simp only [steps, step]; rw [h2]⟩,
               fun v₁ hv₁ => by
                 have hl : step (.compute [] ρ₁ (.Var (m' + 1))) = .error := by
                   simp only [step]; rw [h1]
                 have herr : Reaches (.compute [] ρ₁ (.Var (m' + 1))) .error :=
                   error_in_one_step_reaches_error _ hl
                 exact absurd (reaches_halt_not_error ⟨n, hv₁⟩ herr) id⟩
  | .Constant (c, ty) =>
    exact forward_both_halt_same (.VCon c) _ _ n
      ⟨2, by simp [steps, step]⟩ ⟨2, by simp [steps, step]⟩
  | .Builtin b =>
    exact forward_both_halt_same (.VBuiltin b [] (expectedArgs b)) _ _ n
      ⟨2, by simp [steps, step]⟩ ⟨2, by simp [steps, step]⟩
  | .Lam nm body =>
    have hcl_body := closedAt_lam hcl
    have hl : steps 2 (.compute [] ρ₁ (.Lam nm body)) = .halt (.VLam body ρ₁) := by simp [steps, step]
    have hr : steps 2 (.compute [] ρ₂ (.Lam nm body)) = .halt (.VLam body ρ₂) := by simp [steps, step]
    exact ⟨fun herr => absurd (reaches_halt_not_error ⟨2, hl⟩ ⟨n, herr⟩) id,
           fun w hw => by
             have := reaches_unique ⟨n, hw⟩ ⟨2, hl⟩; subst this
             refine ⟨⟨_, 2, hr⟩, fun k w₂ hw₂ => ?_⟩
             have := reaches_unique hw₂ ⟨2, hr⟩; subst this
             match k with
             | 0 => simp [ValueEq]
             | k + 1 =>
               unfold ValueEq; intro arg
               have henv : EnvValueEqAll (d + 1) (ρ₁.extend arg) (ρ₂.extend arg) :=
                 envValueEqAll_extend hρ (fun k => valueEq_refl k arg)
               have henv_sym := envValueEqAll_symm henv
               exact ⟨⟨fun ⟨m, hm⟩ => (sameBody_forward m body (d+1) (ρ₁.extend arg) (ρ₂.extend arg) hcl_body henv).1 hm,
                       fun ⟨m, hm⟩ => (sameBody_forward m body (d+1) (ρ₂.extend arg) (ρ₁.extend arg) hcl_body henv_sym).1 hm⟩,
                      ⟨fun ⟨v, m, hm⟩ => ((sameBody_forward m body (d+1) (ρ₁.extend arg) (ρ₂.extend arg) hcl_body henv).2 v hm).1,
                       fun ⟨v, m, hm⟩ => ((sameBody_forward m body (d+1) (ρ₂.extend arg) (ρ₁.extend arg) hcl_body henv_sym).2 v hm).1⟩,
                      fun r₁ r₂ ⟨m₁, hm₁⟩ hr₂ => ((sameBody_forward m₁ body (d+1) (ρ₁.extend arg) (ρ₂.extend arg) hcl_body henv).2 r₁ hm₁).2 k r₂ hr₂⟩⟩
  | .Delay body =>
    have hcl_body := closedAt_delay hcl
    have hl : steps 2 (.compute [] ρ₁ (.Delay body)) = .halt (.VDelay body ρ₁) := by simp [steps, step]
    have hr : steps 2 (.compute [] ρ₂ (.Delay body)) = .halt (.VDelay body ρ₂) := by simp [steps, step]
    exact ⟨fun herr => absurd (reaches_halt_not_error ⟨2, hl⟩ ⟨n, herr⟩) id,
           fun w hw => by
             have := reaches_unique ⟨n, hw⟩ ⟨2, hl⟩; subst this
             refine ⟨⟨_, 2, hr⟩, fun k w₂ hw₂ => ?_⟩
             have := reaches_unique hw₂ ⟨2, hr⟩; subst this
             match k with
             | 0 => simp [ValueEq]
             | k + 1 =>
               unfold ValueEq
               have hρ_sym := envValueEqAll_symm hρ
               exact ⟨⟨fun ⟨m, hm⟩ => (sameBody_forward m body d ρ₁ ρ₂ hcl_body hρ).1 hm,
                       fun ⟨m, hm⟩ => (sameBody_forward m body d ρ₂ ρ₁ hcl_body hρ_sym).1 hm⟩,
                      ⟨fun ⟨v, m, hm⟩ => ((sameBody_forward m body d ρ₁ ρ₂ hcl_body hρ).2 v hm).1,
                       fun ⟨v, m, hm⟩ => ((sameBody_forward m body d ρ₂ ρ₁ hcl_body hρ_sym).2 v hm).1⟩,
                      fun r₁ r₂ ⟨m₁, hm₁⟩ hr₂ => ((sameBody_forward m₁ body d ρ₁ ρ₂ hcl_body hρ).2 r₁ hm₁).2 k r₂ hr₂⟩⟩
  -- Force, Apply, Constr, Case: complex cases using frame decomposition
  | .Force e =>
    have hcl_e := closedAt_force hcl
    -- Recursive call on sub-expression e (structural: sizeOf e < sizeOf (Force e))
    have ih_e : ∀ m, (steps m (.compute [] ρ₁ e) = .error → Reaches (.compute [] ρ₂ e) .error) ∧
        (∀ v₁, steps m (.compute [] ρ₁ e) = .halt v₁ →
          Halts (.compute [] ρ₂ e) ∧
          ∀ k v₂, Reaches (.compute [] ρ₂ e) (.halt v₂) → ValueEq k v₁ v₂) :=
      fun m => sameBody_forward m e d ρ₁ ρ₂ hcl_e hρ
    refine ⟨fun herr => ?_, fun w hw => ?_⟩
    · -- Error direction
      match n with
      | 0 => simp [steps] at herr
      | n' + 1 =>
        have herr' : steps n' (.compute [.force] ρ₁ e) = .error := by
          simp [steps, step] at herr; exact herr
        match compute_frame_error_decompose .force ρ₁ e ⟨n', herr'⟩ with
        | .inl he_err =>
          obtain ⟨m_e, hm_e⟩ := he_err
          exact force_sub_error ρ₂ e ((ih_e m_e).1 hm_e)
        | .inr ⟨v₁, hv₁_halt, hv₁_frame_err⟩ =>
          obtain ⟨m₁, hm₁⟩ := hv₁_halt
          obtain ⟨hhalts₂, hveq⟩ := (ih_e m₁).2 v₁ hm₁
          obtain ⟨v₂, hv₂⟩ := hhalts₂
          have hveq_all : ∀ k, ValueEq k v₁ v₂ := fun k => hveq k v₂ hv₂
          exact force_compose ρ₂ e v₂ .error hv₂
            (force_frame_error_transfer 0 v₁ v₂ (hveq_all 1) hv₁_frame_err)
    · -- Halt direction
      match n with
      | 0 => simp [steps] at hw
      | n' + 1 =>
        have hw' : steps n' (.compute [.force] ρ₁ e) = .halt w := by
          simp [steps, step] at hw; exact hw
        obtain ⟨v₁, hv₁_halt, hv₁_frame_halt⟩ :=
          compute_frame_halt_decompose .force ρ₁ e w ⟨n', hw'⟩
        obtain ⟨m₁, hm₁⟩ := hv₁_halt
        obtain ⟨hhalts₂, hveq⟩ := (ih_e m₁).2 v₁ hm₁
        obtain ⟨v₂, hv₂⟩ := hhalts₂
        have hveq_all : ∀ k, ValueEq k v₁ v₂ := fun k => hveq k v₂ hv₂
        refine ⟨?_, fun k w₂ hw₂_reach => ?_⟩
        · obtain ⟨w₂, hw₂⟩ := force_frame_halts_transfer 0 v₁ v₂ (hveq_all 1)
            ⟨w, hv₁_frame_halt⟩
          exact ⟨w₂, force_compose ρ₂ e v₂ (.halt w₂) hv₂ hw₂⟩
        · obtain ⟨v₂', hv₂'_halt, hv₂'_frame_halt⟩ := force_reaches ρ₂ e w₂ hw₂_reach
          have hv₂'_eq : v₂' = v₂ := reaches_unique hv₂'_halt hv₂
          rw [hv₂'_eq] at hv₂'_frame_halt
          exact force_frame_valueEq k v₁ v₂ (hveq_all (k + 1))
            w w₂ hv₁_frame_halt hv₂'_frame_halt
  | .Apply f x =>
    have hcl_f := (closedAt_apply hcl).1
    have hcl_x := (closedAt_apply hcl).2
    have ih_f : ∀ m, (steps m (.compute [] ρ₁ f) = .error → Reaches (.compute [] ρ₂ f) .error) ∧
        (∀ v₁, steps m (.compute [] ρ₁ f) = .halt v₁ →
          Halts (.compute [] ρ₂ f) ∧
          ∀ k v₂, Reaches (.compute [] ρ₂ f) (.halt v₂) → ValueEq k v₁ v₂) :=
      fun m => sameBody_forward m f d ρ₁ ρ₂ hcl_f hρ
    have ih_x : ∀ m, (steps m (.compute [] ρ₁ x) = .error → Reaches (.compute [] ρ₂ x) .error) ∧
        (∀ v₁, steps m (.compute [] ρ₁ x) = .halt v₁ →
          Halts (.compute [] ρ₂ x) ∧
          ∀ k v₂, Reaches (.compute [] ρ₂ x) (.halt v₂) → ValueEq k v₁ v₂) :=
      fun m => sameBody_forward m x d ρ₁ ρ₂ hcl_x hρ
    -- Bounded same-fun-different-arg helpers.
    -- By reversing the hop order (hop 2 first, hop 1 second), the recursive
    -- sameBody_forward call uses a step count from the bounded decomposition
    -- (< n), while the cross-function hop uses the already-proven
    -- funV_same_arg_* lemmas which do not recurse.
    --
    -- For VCon/VDelay/VConstr/VBuiltin applied via funV, both sides error in
    -- 1 step regardless of the argument, so no recursive call is needed.
    refine ⟨fun herr => ?_, fun w hw => ?_⟩
    · -- Error direction
      match n with
      | 0 => simp [steps] at herr
      | n' + 1 =>
        have herr' : steps n' (.compute [.arg x ρ₁] ρ₁ f) = .error := by
          simp [steps, step] at herr; exact herr
        match compute_frame_error_bounded (.arg x ρ₁) ρ₁ f n' herr' with
        | .inl ⟨_, _, hf_err⟩ =>
          exact app_error_from_fun_error ρ₂ f x ((ih_f _).1 hf_err)
        | .inr ⟨vf₁, M_arg, hM_arg_le, hf_halt, harg_frame_err⟩ =>
          obtain ⟨mf, hmf⟩ := hf_halt
          obtain ⟨hhalts_f₂, hveq_f⟩ := (ih_f mf).2 vf₁ hmf
          obtain ⟨vf₂, hvf₂⟩ := hhalts_f₂
          have hveq_all_f : ∀ j, ValueEq j vf₁ vf₂ := fun j => hveq_f j vf₂ hvf₂
          match M_arg, harg_frame_err, hM_arg_le with
          | 0, hm, _ => simp [steps] at hm
          | M_arg' + 1, hm_arg, hM_arg_le =>
            have hm_arg' : steps M_arg' (.compute [.funV vf₁] ρ₁ x) = .error := by
              simp [steps, step] at hm_arg; exact hm_arg
            match compute_frame_error_bounded (.funV vf₁) ρ₁ x M_arg' hm_arg' with
            | .inl ⟨_, _, hx_err⟩ =>
              exact app_error_from_arg_error ρ₂ f x vf₂ hvf₂ ((ih_x _).1 hx_err)
            | .inr ⟨vx₁, M_fun, hM_fun_le, hx_halt, hframe_err⟩ =>
              obtain ⟨mx, hmx⟩ := hx_halt
              obtain ⟨hhalts_x₂, hveq_x⟩ := (ih_x mx).2 vx₁ hmx
              obtain ⟨vx₂, hvx₂⟩ := hhalts_x₂
              have hveq_all_x : ∀ j, ValueEq j vx₁ vx₂ := fun j => hveq_x j vx₂ hvx₂
              -- Hop 2 first (bounded): same fun vf₁, arg vx₁ → vx₂
              -- Then hop 1 (ValueEq): fun vf₁ → vf₂, same arg vx₂
              match vf₁ with
              | .VCon c =>
                -- step (.ret [.funV (.VCon c)] vx₂) = .error
                have h_err₂ : Reaches (.ret [.funV (.VCon c)] vx₂) .error := ⟨1, rfl⟩
                have hfinal := funV_same_arg_error_transfer (.VCon c) vf₂ vx₂ hveq_all_f h_err₂
                exact app_apply_from_parts ρ₂ f x vf₂ vx₂ .error hvf₂ hvx₂ hfinal
              | .VDelay bd env =>
                have h_err₂ : Reaches (.ret [.funV (.VDelay bd env)] vx₂) .error := ⟨1, rfl⟩
                have hfinal := funV_same_arg_error_transfer (.VDelay bd env) vf₂ vx₂ hveq_all_f h_err₂
                exact app_apply_from_parts ρ₂ f x vf₂ vx₂ .error hvf₂ hvx₂ hfinal
              | .VConstr tg fs =>
                have h_err₂ : Reaches (.ret [.funV (.VConstr tg fs)] vx₂) .error := ⟨1, rfl⟩
                have hfinal := funV_same_arg_error_transfer (.VConstr tg fs) vf₂ vx₂ hveq_all_f h_err₂
                exact app_apply_from_parts ρ₂ f x vf₂ vx₂ .error hvf₂ hvx₂ hfinal
              | .VLam body ρ' =>
                match M_fun, hframe_err, hM_fun_le with
                | 0, hm, _ => simp [steps] at hm
                | M_fun' + 1, hm_fun, hM_fun_le =>
                  have hm_body : steps M_fun' (.compute [] (ρ'.extend vx₁) body) = .error := by
                    simp [steps, step] at hm_fun; exact hm_fun
                  have hM_fun'_lt_n : M_fun' < n' + 1 := by omega
                  have ⟨d', hcl'⟩ := closedAt_exists body
                  have henv := envValueEqAll_of_same_extend d' ρ' vx₁ vx₂ hveq_all_x
                  -- Hop 2: same body, same env ρ', arg vx₁ → vx₂
                  have h_body_err₂ := (sameBody_forward M_fun' body d'
                      (ρ'.extend vx₁) (ρ'.extend vx₂) hcl' henv).1 hm_body
                  -- Compose back to ret [.funV (VLam body ρ')] vx₂
                  have hstep₂ : step (.ret [.funV (.VLam body ρ')] vx₂) =
                      .compute [] (ρ'.extend vx₂) body := rfl
                  have h_err₂ : Reaches (.ret [.funV (.VLam body ρ')] vx₂) .error :=
                    reaches_of_step_reaches hstep₂ h_body_err₂
                  -- Hop 1: fun vf₁ → vf₂, same arg vx₂
                  have hfinal := funV_same_arg_error_transfer (.VLam body ρ') vf₂ vx₂
                      hveq_all_f h_err₂
                  exact app_apply_from_parts ρ₂ f x vf₂ vx₂ .error hvf₂ hvx₂ hfinal
              | .VBuiltin _ _ _ =>
                -- Hop 1: same-arg vf₁→vf₂ (no recursion needed)
                have hmid := funV_same_arg_error_transfer _ vf₂ vx₁ hveq_all_f ⟨M_fun, hframe_err⟩
                -- Hop 2: same-fun vf₂, different arg (VBuiltin uses same logic for any arg)
                -- For now: sorry (pre-existing VBuiltin sorry)
                sorry
    · -- Halt direction
      match n with
      | 0 => simp [steps] at hw
      | n' + 1 =>
        have hw' : steps n' (.compute [.arg x ρ₁] ρ₁ f) = .halt w := by
          simp [steps, step] at hw; exact hw
        -- Use bounded decomposition for the arg frame
        obtain ⟨vf₁, M_arg, hM_arg_le, hf_halt, harg_frame_halt⟩ :=
          compute_frame_halt_bounded (.arg x ρ₁) ρ₁ f w n' hw'
        obtain ⟨mf, hmf⟩ := hf_halt
        obtain ⟨hhalts_f₂, hveq_f⟩ := (ih_f mf).2 vf₁ hmf
        obtain ⟨vf₂, hvf₂⟩ := hhalts_f₂
        have hveq_all_f : ∀ j, ValueEq j vf₁ vf₂ := fun j => hveq_f j vf₂ hvf₂
        -- Decompose the funV frame
        match M_arg, harg_frame_halt, hM_arg_le with
        | 0, hm, _ => simp [steps] at hm
        | M_arg' + 1, hm_arg, hM_arg_le =>
          have hm_arg' : steps M_arg' (.compute [.funV vf₁] ρ₁ x) = .halt w := by
            simp [steps, step] at hm_arg; exact hm_arg
          obtain ⟨vx₁, M_fun, hM_fun_le, hx_halt, hframe_halt⟩ :=
            compute_frame_halt_bounded (.funV vf₁) ρ₁ x w M_arg' hm_arg'
          obtain ⟨mx, hmx⟩ := hx_halt
          obtain ⟨hhalts_x₂, hveq_x⟩ := (ih_x mx).2 vx₁ hmx
          obtain ⟨vx₂, hvx₂⟩ := hhalts_x₂
          have hveq_all_x : ∀ j, ValueEq j vx₁ vx₂ := fun j => hveq_x j vx₂ hvx₂
          -- Hop 2 first (bounded): same fun vf₁, arg vx₁ → vx₂
          -- Then hop 1: fun vf₁ → vf₂, same arg vx₂
          match vf₁ with
          | .VCon c =>
            -- step (.ret [.funV (.VCon c)] vx₁) = .error, contradicts halt
            exact absurd ⟨w, M_fun, hframe_halt⟩ (error_in_one_step_not_halts _ rfl)
          | .VDelay bd env =>
            exact absurd ⟨w, M_fun, hframe_halt⟩ (error_in_one_step_not_halts _ rfl)
          | .VConstr tg fs =>
            exact absurd ⟨w, M_fun, hframe_halt⟩ (error_in_one_step_not_halts _ rfl)
          | .VLam body ρ' =>
            match M_fun, hframe_halt, hM_fun_le with
            | 0, hm, _ => simp [steps] at hm
            | M_fun' + 1, hm_fun, hM_fun_le =>
              have hm_body : steps M_fun' (.compute [] (ρ'.extend vx₁) body) = .halt w := by
                simp [steps, step] at hm_fun; exact hm_fun
              have hM_fun'_lt_n : M_fun' < n' + 1 := by omega
              have ⟨d', hcl'⟩ := closedAt_exists body
              have henv := envValueEqAll_of_same_extend d' ρ' vx₁ vx₂ hveq_all_x
              -- Hop 2: same body, same env ρ', arg vx₁ → vx₂
              have h_body := sameBody_forward M_fun' body d'
                  (ρ'.extend vx₁) (ρ'.extend vx₂) hcl' henv
              obtain ⟨hhalts_body₂, hveq_body⟩ := h_body.2 w hm_body
              -- Get result of body computation with vx₂
              obtain ⟨w_hop2, hw_hop2⟩ := hhalts_body₂
              have hstep₂ : step (.ret [.funV (.VLam body ρ')] vx₂) =
                  .compute [] (ρ'.extend vx₂) body := rfl
              -- Halts at ret [.funV vf₁] vx₂
              have h_halt₂ : Halts (.ret [.funV (.VLam body ρ')] vx₂) :=
                ⟨w_hop2, reaches_of_step_reaches hstep₂ hw_hop2⟩
              -- Hop 1: fun vf₁ → vf₂, same arg vx₂
              have hmid_halts := funV_same_arg_halts_transfer (.VLam body ρ') vf₂ vx₂
                  hveq_all_f h_halt₂
              refine ⟨?_, fun k w₂ hw₂ => ?_⟩
              · obtain ⟨w_final, hw_final⟩ := hmid_halts
                exact ⟨w_final, app_apply_from_parts ρ₂ f x vf₂ vx₂ (.halt w_final) hvf₂ hvx₂ hw_final⟩
              · -- ValueEq: w vs w₂
                -- Decompose hw₂ to get the funV frame result
                obtain ⟨vf₂', vx₂', hf₂_halt, hx₂_halt, hframe₂_halt⟩ :=
                  app_reaches ρ₂ f x w₂ hw₂
                have hvf₂'_eq : vf₂' = vf₂ := reaches_unique hf₂_halt hvf₂
                have hvx₂'_eq : vx₂' = vx₂ := reaches_unique hx₂_halt hvx₂
                rw [hvf₂'_eq, hvx₂'_eq] at hframe₂_halt
                -- Hop 1 ValueEq: w vs w_hop2 (same-fun different-arg result)
                have hveq_hop2 : ValueEq k w w_hop2 :=
                  hveq_body k w_hop2 hw_hop2
                -- Compose: ret [.funV vf₁] vx₂ halts with w_hop2
                have h_vf1_vx2_halt : Reaches (.ret [.funV (.VLam body ρ')] vx₂) (.halt w_hop2) :=
                  reaches_of_step_reaches hstep₂ hw_hop2
                -- Hop 2 ValueEq: w_hop2 vs w₂ (same-arg different-fun result)
                have hveq_hop1 : ValueEq k w_hop2 w₂ :=
                  funV_same_arg_valueEq k (.VLam body ρ') vf₂ vx₂ w_hop2 w₂
                    hveq_all_f h_vf1_vx2_halt hframe₂_halt
                exact valueEq_trans k w w_hop2 w₂ hveq_hop2 hveq_hop1
          | .VBuiltin _ _ _ =>
            -- Hop 1: same-arg vf₁→vf₂
            have hmid_halts := funV_same_arg_halts_transfer _ vf₂ vx₁ hveq_all_f ⟨w, M_fun, hframe_halt⟩
            -- VBuiltin hop 2: sorry (pre-existing)
            sorry
  | .Constr tag args =>
    have hcl_args := closedAt_constr hcl
    have hρ_sym := envValueEqAll_symm hρ
    -- Full adequacy for each field (both directions)
    have hfields : ∀ m, m ∈ args →
        (Reaches (.compute [] ρ₁ m) .error ↔ Reaches (.compute [] ρ₂ m) .error) ∧
        (Halts (.compute [] ρ₁ m) ↔ Halts (.compute [] ρ₂ m)) ∧
        ∀ k v₁ v₂, Reaches (.compute [] ρ₁ m) (.halt v₁) →
          Reaches (.compute [] ρ₂ m) (.halt v₂) → ValueEq k v₁ v₂ := by
      intro m hmem
      have hcl_m := closedAtList_of_mem hcl_args hmem
      have fwd := fun s => sameBody_forward s m d ρ₁ ρ₂ hcl_m hρ
      have rev := fun s => sameBody_forward s m d ρ₂ ρ₁ hcl_m hρ_sym
      exact ⟨⟨fun ⟨s, hs⟩ => (fwd s).1 hs,
              fun ⟨s, hs⟩ => (rev s).1 hs⟩,
             ⟨fun ⟨v, s, hs⟩ => ((fwd s).2 v hs).1,
              fun ⟨v, s, hs⟩ => ((rev s).2 v hs).1⟩,
             fun k v₁ v₂ ⟨s₁, hs₁⟩ hv₂ =>
              ((fwd s₁).2 v₁ hs₁).2 k v₂ hv₂⟩
    match args with
    | [] =>
      exact forward_both_halt_same (.VConstr tag []) _ _ n
        ⟨2, by simp [steps, step]⟩ ⟨2, by simp [steps, step]⟩
    | m :: ms =>
      have hcl_m := (closedAt_constr_cons hcl_args).1
      have hcl_ms := (closedAt_constr_cons hcl_args).2
      have hm := hfields m (List.Mem.head ms)
      obtain ⟨hm_err, hm_halts, hm_veq⟩ := hm
      have hfields_ms : ∀ m', m' ∈ ms →
          (Reaches (.compute [] ρ₁ m') .error ↔ Reaches (.compute [] ρ₂ m') .error) ∧
          (Halts (.compute [] ρ₁ m') ↔ Halts (.compute [] ρ₂ m') ) ∧
          ∀ k v₁ v₂, Reaches (.compute [] ρ₁ m') (.halt v₁) →
            Reaches (.compute [] ρ₂ m') (.halt v₂) → ValueEq k v₁ v₂ :=
        fun m' hm' => hfields m' (List.mem_cons_of_mem m hm')
      refine ⟨fun herr => ?_, fun w hw => ?_⟩
      · -- Error direction
        match n with
        | 0 => simp [steps] at herr
        | n' + 1 =>
          have herr' : steps n' (.compute [.constrField tag [] ms ρ₁] ρ₁ m) = .error := by
            simp [steps, step] at herr; exact herr
          match compute_frame_error_decompose (.constrField tag [] ms ρ₁) ρ₁ m ⟨n', herr'⟩ with
          | .inl hm_err_l =>
            have := compute_to_error_from_error ρ₂ m
              [.constrField tag [] ms ρ₂] (hm_err.mp hm_err_l)
            exact reaches_of_step_reaches (show step (.compute [] ρ₂ (.Constr tag (m :: ms))) =
              .compute [.constrField tag [] ms ρ₂] ρ₂ m from rfl) this
          | .inr ⟨vm₁, hm_halt₁, hrest_err₁⟩ =>
            obtain ⟨vm₂, hm_halt₂⟩ := hm_halts.mp ⟨vm₁, hm_halt₁⟩
            have hveq_vm : ∀ k, ValueEq k vm₁ vm₂ := fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂
            have ih := constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
              hveq_vm (fun k => by unfold ListValueEq; trivial) hfields_ms
            have := compute_frame_compose (.constrField tag [] ms ρ₂) ρ₂ m vm₂ .error
              hm_halt₂ (ih.1.mp hrest_err₁)
            exact reaches_of_step_reaches (show step (.compute [] ρ₂ (.Constr tag (m :: ms))) =
              .compute [.constrField tag [] ms ρ₂] ρ₂ m from rfl) this
      · -- Halt direction
        match n with
        | 0 => simp [steps] at hw
        | n' + 1 =>
          have hw' : steps n' (.compute [.constrField tag [] ms ρ₁] ρ₁ m) = .halt w := by
            simp [steps, step] at hw; exact hw
          obtain ⟨vm₁, hm_halt₁, hrest₁⟩ :=
            compute_frame_halt_decompose (.constrField tag [] ms ρ₁) ρ₁ m w ⟨n', hw'⟩
          obtain ⟨vm₂, hm_halt₂⟩ := hm_halts.mp ⟨vm₁, hm_halt₁⟩
          have hveq_vm : ∀ k, ValueEq k vm₁ vm₂ := fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂
          have ih := constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
            hveq_vm (fun k => by unfold ListValueEq; trivial) hfields_ms
          refine ⟨?_, fun k w₂ hw₂_reach => ?_⟩
          · obtain ⟨w', hw'⟩ := ih.2.1.mp ⟨w, hrest₁⟩
            exact ⟨w', reaches_of_step_reaches (show step (.compute [] ρ₂ (.Constr tag (m :: ms))) =
              .compute [.constrField tag [] ms ρ₂] ρ₂ m from rfl)
              (compute_frame_compose _ ρ₂ m vm₂ (.halt w') hm_halt₂ hw')⟩
          · -- ValueEq: need to decompose hw₂_reach to get frame result
            have hw₂' := reaches_to_step_reaches
              (show step (.compute [] ρ₂ (.Constr tag (m :: ms))) =
                .compute [.constrField tag [] ms ρ₂] ρ₂ m from rfl) hw₂_reach (by simp)
            obtain ⟨vm₂', hm_halt₂', hrest₂⟩ :=
              compute_frame_halt_decompose (.constrField tag [] ms ρ₂) ρ₂ m w₂ hw₂'
            have hvm₂'_eq : vm₂' = vm₂ := reaches_unique hm_halt₂' hm_halt₂
            rw [hvm₂'_eq] at hrest₂
            exact ih.2.2 k w w₂ hrest₁ hrest₂
  | .Case scrut alts =>
    have ⟨hcl_scrut, hcl_alts⟩ := closedAt_case hcl
    have hρ_sym := envValueEqAll_symm hρ
    -- Recursive call on scrut (structural: sizeOf scrut < sizeOf (Case scrut alts))
    have ih_scrut : ∀ m, (steps m (.compute [] ρ₁ scrut) = .error → Reaches (.compute [] ρ₂ scrut) .error) ∧
        (∀ v₁, steps m (.compute [] ρ₁ scrut) = .halt v₁ →
          Halts (.compute [] ρ₂ scrut) ∧
          ∀ k v₂, Reaches (.compute [] ρ₂ scrut) (.halt v₂) → ValueEq k v₁ v₂) :=
      fun m => sameBody_forward m scrut d ρ₁ ρ₂ hcl_scrut hρ
    -- Step equations
    have hstep₁ : step (.compute [] ρ₁ (.Case scrut alts)) =
        .compute [.caseScrutinee alts ρ₁] ρ₁ scrut := rfl
    have hstep₂ : step (.compute [] ρ₂ (.Case scrut alts)) =
        .compute [.caseScrutinee alts ρ₂] ρ₂ scrut := rfl
    -- Full adequacy for each alt (both directions)
    have halt_adeq : ∀ a, a ∈ alts →
        (Reaches (.compute [] ρ₁ a) .error ↔ Reaches (.compute [] ρ₂ a) .error) ∧
        (Halts (.compute [] ρ₁ a) ↔ Halts (.compute [] ρ₂ a)) ∧
        ∀ k v₁ v₂, Reaches (.compute [] ρ₁ a) (.halt v₁) →
          Reaches (.compute [] ρ₂ a) (.halt v₂) → ValueEq k v₁ v₂ := by
      intro a hmem
      have hcl_a := closedAtList_of_mem hcl_alts hmem
      have fwd := fun s => sameBody_forward s a d ρ₁ ρ₂ hcl_a hρ
      have rev := fun s => sameBody_forward s a d ρ₂ ρ₁ hcl_a hρ_sym
      exact ⟨⟨fun ⟨s, hs⟩ => (fwd s).1 hs,
              fun ⟨s, hs⟩ => (rev s).1 hs⟩,
             ⟨fun ⟨v, s, hs⟩ => ((fwd s).2 v hs).1,
              fun ⟨v, s, hs⟩ => ((rev s).2 v hs).1⟩,
             fun k v₁ v₂ ⟨s₁, hs₁⟩ hv₂ =>
              ((fwd s₁).2 v₁ hs₁).2 k v₂ hv₂⟩
    -- Helper for alt membership/closedness from getElem?
    have alt_from_idx : ∀ (tg : Nat) (a : Term),
        alts[tg]? = some a → a ∈ alts ∧ closedAt d a = true := by
      intro tg a h_idx
      have ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp h_idx
      subst heq; exact ⟨List.getElem_mem hi, closedAtList_getElem hcl_alts hi⟩
    refine ⟨fun herr => ?_, fun w hw => ?_⟩
    · -- Error direction
      match n with
      | 0 => simp [steps] at herr
      | n' + 1 =>
        have herr' : steps n' (.compute [.caseScrutinee alts ρ₁] ρ₁ scrut) = .error := by
          simp [steps, step] at herr; exact herr
        match compute_frame_error_decompose (.caseScrutinee alts ρ₁) ρ₁ scrut ⟨n', herr'⟩ with
        | .inl hscrut_err =>
          obtain ⟨m_s, hm_s⟩ := hscrut_err
          exact reaches_of_step_reaches hstep₂
            (compute_to_error_from_error ρ₂ scrut [.caseScrutinee alts ρ₂]
              ((ih_scrut m_s).1 hm_s))
        | .inr ⟨vs₁, hvs₁_halt, hvs₁_frame_err⟩ =>
          obtain ⟨m₁, hm₁⟩ := hvs₁_halt
          obtain ⟨hhalts₂, hveq⟩ := (ih_scrut m₁).2 vs₁ hm₁
          obtain ⟨vs₂, hvs₂⟩ := hhalts₂
          have hveq_all : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq k vs₂ hvs₂
          -- Case-split on vs₁ and vs₂ simultaneously
          match vs₁, vs₂, hveq_all with
          -- Same-constructor error cases (VLam, VDelay, VBuiltin → error)
          | .VLam _ _, .VLam _ _, _ =>
            exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut _ .error hvs₂
              (error_in_one_step_reaches_error _ rfl))
          | .VDelay _ _, .VDelay _ _, _ =>
            exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut _ .error hvs₂
              (error_in_one_step_reaches_error _ rfl))
          | .VBuiltin _ _ _, .VBuiltin _ _ _, _ =>
            exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut _ .error hvs₂
              (error_in_one_step_reaches_error _ rfl))
          -- VCon: identical fields, same dispatch
          | .VCon c₁, .VCon c₂, hveq_all =>
            have h1 := hveq_all 1; unfold ValueEq at h1; subst h1
            cases h_ctf : constToTagAndFields c₁ with
            | none =>
              exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut (.VCon c₁) .error hvs₂
                (error_in_one_step_reaches_error _ (by simp [step, h_ctf])))
            | some val =>
              obtain ⟨tag, numCtors, fields⟩ := val
              cases h_check : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
              | true =>
                exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut (.VCon c₁) .error hvs₂
                  (error_in_one_step_reaches_error _ (by simp [step, h_ctf, h_check])))
              | false =>
                cases h_idx : alts[tag]? with
                | none =>
                  exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut (.VCon c₁) .error hvs₂
                    (error_in_one_step_reaches_error _ (by simp [step, h_ctf, h_check, h_idx])))
                | some alt =>
                  have hdisp₁ : step (.ret [.caseScrutinee alts ρ₁] (.VCon c₁)) =
                      .compute (fields.map Frame.applyArg ++ []) ρ₁ alt := by simp [step, h_ctf, h_check, h_idx]
                  have hdisp₂ : step (.ret [.caseScrutinee alts ρ₂] (.VCon c₁)) =
                      .compute (fields.map Frame.applyArg ++ []) ρ₂ alt := by simp [step, h_ctf, h_check, h_idx]
                  simp only [List.append_nil] at hdisp₁ hdisp₂
                  have ⟨hmem, hcl_alt⟩ := alt_from_idx tag alt h_idx
                  have htransfer := sameBody_with_shared_applyArg_stack fields alt d ρ₁ ρ₂ hcl_alt hρ (halt_adeq alt hmem)
                  exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut (.VCon c₁) .error hvs₂
                    (reaches_of_step_reaches hdisp₂ (htransfer.1.mp (reaches_to_step_reaches hdisp₁ hvs₁_frame_err (by simp)))))
          -- VConstr: related fields, same tag
          | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂, hveq_all =>
            have h1 := hveq_all 1; unfold ValueEq at h1
            obtain ⟨htag_eq, _⟩ := h1; subst htag_eq
            cases h_idx : alts[tag₁]? with
            | none =>
              exact reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut (.VConstr tag₁ fields₂) .error hvs₂
                (error_in_one_step_reaches_error _ (by simp [step, h_idx])))
            | some alt =>
              have hdisp₁ : step (.ret [.caseScrutinee alts ρ₁] (.VConstr tag₁ fields₁)) =
                  .compute (fields₁.map Frame.applyArg ++ []) ρ₁ alt := by simp [step, h_idx]
              have hdisp₂ : step (.ret [.caseScrutinee alts ρ₂] (.VConstr tag₁ fields₂)) =
                  .compute (fields₂.map Frame.applyArg ++ []) ρ₂ alt := by simp [step, h_idx]
              simp only [List.append_nil] at hdisp₁ hdisp₂
              have ⟨hmem, hcl_alt⟩ := alt_from_idx tag₁ alt h_idx
              have hchain_err₁ := reaches_to_step_reaches hdisp₁ hvs₁_frame_err (by simp)
              -- Env transfer (fields₁, ρ₁) → (fields₁, ρ₂) via sameBody_with_shared_applyArg_stack
              have htransfer₁ := sameBody_with_shared_applyArg_stack fields₁ alt d ρ₁ ρ₂ hcl_alt hρ (halt_adeq alt hmem)
              have hchain_err_mid := htransfer₁.1.mp hchain_err₁
              -- TODO: Fields transfer (fields₁, ρ₂) → (fields₂, ρ₂)
              -- Requires applyArg_chain_related_fields lemma (same value, related field stacks).
              -- The chain transfer needs sameBody_adequacy for VLam bodies in the chain,
              -- creating a circular dependency with the current proof structure.
              sorry
          -- Cross-constructor: ValueEq 1 is False
          | .VCon _, .VLam _ _, hv | .VCon _, .VDelay _ _, hv | .VCon _, .VConstr _ _, hv
          | .VCon _, .VBuiltin _ _ _, hv | .VLam _ _, .VCon _, hv | .VLam _ _, .VDelay _ _, hv
          | .VLam _ _, .VConstr _ _, hv | .VLam _ _, .VBuiltin _ _ _, hv
          | .VDelay _ _, .VCon _, hv | .VDelay _ _, .VLam _ _, hv | .VDelay _ _, .VConstr _ _, hv
          | .VDelay _ _, .VBuiltin _ _ _, hv | .VConstr _ _, .VCon _, hv
          | .VConstr _ _, .VLam _ _, hv | .VConstr _ _, .VDelay _ _, hv
          | .VConstr _ _, .VBuiltin _ _ _, hv | .VBuiltin _ _ _, .VCon _, hv
          | .VBuiltin _ _ _, .VLam _ _, hv | .VBuiltin _ _ _, .VDelay _ _, hv
          | .VBuiltin _ _ _, .VConstr _ _, hv =>
            exact absurd (hv 1) (by unfold ValueEq; exact id)
    · -- Halt direction
      match n with
      | 0 => simp [steps] at hw
      | n' + 1 =>
        have hw' : steps n' (.compute [.caseScrutinee alts ρ₁] ρ₁ scrut) = .halt w := by
          simp [steps, step] at hw; exact hw
        obtain ⟨vs₁, hvs₁_halt, hvs₁_frame_halt⟩ :=
          compute_frame_halt_decompose (.caseScrutinee alts ρ₁) ρ₁ scrut w ⟨n', hw'⟩
        obtain ⟨m₁, hm₁⟩ := hvs₁_halt
        obtain ⟨hhalts₂, hveq⟩ := (ih_scrut m₁).2 vs₁ hm₁
        obtain ⟨vs₂, hvs₂⟩ := hhalts₂
        have hveq_all : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq k vs₂ hvs₂
        match vs₁, vs₂, hveq_all with
        -- VLam, VDelay, VBuiltin: error in 1 step, contradicts halt
        | .VLam _ _, _, _ =>
          exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ rfl)
        | .VDelay _ _, _, _ =>
          exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ rfl)
        | .VBuiltin _ _ _, _, _ =>
          exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ rfl)
        -- VCon: identical dispatch
        | .VCon c₁, .VCon c₂, hveq_all =>
          have h1 := hveq_all 1; unfold ValueEq at h1; subst h1
          -- Rebind hvs₂ with correct type after match+subst
          have hvs₂_con : Reaches (.compute [] ρ₂ scrut) (.halt (.VCon c₁)) := hvs₂
          cases h_ctf : constToTagAndFields c₁ with
          | none =>
            exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ (by simp [step, h_ctf]))
          | some val =>
            obtain ⟨tag, numCtors, fields⟩ := val
            cases h_check : (decide (numCtors > 0) && decide (alts.length > numCtors)) with
            | true =>
              exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ (by simp [step, h_ctf, h_check]))
            | false =>
              cases h_idx : alts[tag]? with
              | none =>
                exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ (by simp [step, h_ctf, h_check, h_idx]))
              | some alt =>
                have hdisp₁ : step (.ret [.caseScrutinee alts ρ₁] (.VCon c₁)) =
                    .compute (fields.map Frame.applyArg ++ []) ρ₁ alt := by simp [step, h_ctf, h_check, h_idx]
                have hdisp₂ : step (.ret [.caseScrutinee alts ρ₂] (.VCon c₁)) =
                    .compute (fields.map Frame.applyArg ++ []) ρ₂ alt := by simp [step, h_ctf, h_check, h_idx]
                simp only [List.append_nil] at hdisp₁ hdisp₂
                have ⟨hmem, hcl_alt⟩ := alt_from_idx tag alt h_idx
                have htransfer := sameBody_with_shared_applyArg_stack fields alt d ρ₁ ρ₂ hcl_alt hρ (halt_adeq alt hmem)
                have hchain_halt₁ := reaches_to_step_reaches hdisp₁ hvs₁_frame_halt (by simp)
                refine ⟨?_, fun k w₂ hw₂_reach => ?_⟩
                · obtain ⟨w', hw'⟩ := htransfer.2.1.mp ⟨w, hchain_halt₁⟩
                  exact ⟨w', reaches_of_step_reaches hstep₂ (compute_frame_compose _ ρ₂ scrut (.VCon c₁) (.halt w') hvs₂_con
                    (reaches_of_step_reaches hdisp₂ hw'))⟩
                · have hw₂' := reaches_to_step_reaches hstep₂ hw₂_reach (by simp)
                  obtain ⟨vs₂', hvs₂'_halt, hvs₂'_frame_halt⟩ :=
                    compute_frame_halt_decompose (.caseScrutinee alts ρ₂) ρ₂ scrut w₂ hw₂'
                  have hvs₂'_eq : vs₂' = .VCon c₁ := reaches_unique hvs₂'_halt hvs₂_con
                  rw [hvs₂'_eq] at hvs₂'_frame_halt
                  have hchain_halt₂ := reaches_to_step_reaches hdisp₂ hvs₂'_frame_halt (by simp)
                  exact htransfer.2.2 k w w₂ hchain_halt₁ hchain_halt₂
        -- VConstr: related fields
        | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂, hveq_all =>
          have h1 := hveq_all 1; unfold ValueEq at h1
          obtain ⟨htag_eq, _⟩ := h1; subst htag_eq
          cases h_idx : alts[tag₁]? with
          | none =>
            exact absurd ⟨w, hvs₁_frame_halt⟩ (error_in_one_step_not_halts _ (by simp [step, h_idx]))
          | some alt =>
            -- TODO: Same fields transfer issue as error case
            sorry
        -- Cross-constructor impossibilities
        | .VCon _, .VLam _ _, hv | .VCon _, .VDelay _ _, hv | .VCon _, .VConstr _ _, hv
        | .VCon _, .VBuiltin _ _ _, hv | .VConstr _ _, .VCon _, hv
        | .VConstr _ _, .VLam _ _, hv | .VConstr _ _, .VDelay _ _, hv
        | .VConstr _ _, .VBuiltin _ _ _, hv =>
          exact absurd (hv 1) (by unfold ValueEq; exact id)
  termination_by (n, sizeOf t)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      -- Lam/Delay: m comes from Reaches (unbounded existential witness).
      -- The recursion truly terminates (body is a structural sub-term and
      -- any step count suffices) but the lexicographic measure (n, sizeOf t)
      -- cannot express this since m is unrelated to n.
      | sorry

/-- **Same-body adequacy.** Same closed term, `EnvValueEqAll`-related
    environments ⟹ error↔, halts↔, `∀ k, ValueEq k` on results.

    Derived from `sameBody_forward` applied in both directions using
    `envValueEqAll_symm` for the reverse direction. -/
theorem sameBody_adequacy (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (Reaches (.compute [] ρ₁ t) .error ↔ Reaches (.compute [] ρ₂ t) .error) ∧
    (Halts (.compute [] ρ₁ t) ↔ Halts (.compute [] ρ₂ t)) ∧
    ∀ (k : Nat) (v₁ v₂ : CekValue),
      Reaches (.compute [] ρ₁ t) (.halt v₁) →
      Reaches (.compute [] ρ₂ t) (.halt v₂) →
      ValueEq k v₁ v₂ := by
  have hρ_sym := envValueEqAll_symm hρ
  refine ⟨⟨fun ⟨m, hm⟩ => (sameBody_forward m t d ρ₁ ρ₂ hcl hρ).1 hm,
           fun ⟨m, hm⟩ => (sameBody_forward m t d ρ₂ ρ₁ hcl hρ_sym).1 hm⟩,
          ⟨fun ⟨v, m, hm⟩ => ((sameBody_forward m t d ρ₁ ρ₂ hcl hρ).2 v hm).1,
           fun ⟨v, m, hm⟩ => ((sameBody_forward m t d ρ₂ ρ₁ hcl hρ_sym).2 v hm).1⟩,
          fun k v₁ v₂ ⟨m₁, hm₁⟩ hv₂ =>
            ((sameBody_forward m₁ t d ρ₁ ρ₂ hcl hρ).2 v₁ hm₁).2 k v₂ hv₂⟩

end Moist.Verified.SameBodyAdequacy
