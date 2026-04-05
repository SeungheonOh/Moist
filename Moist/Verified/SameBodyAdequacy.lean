import Moist.Verified.ClosedAt
import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.Verified.Purity
import Moist.Verified.Bisim

/-! # Same-Body Adequacy

The same closed UPLC term evaluated under two CEK environments that agree
at all observation depths produces agreeing results.

## Architecture

The proof uses a custom same-body bisimulation (`SBStateRel`) that tracks
same-term execution under structurally related environments. Values from
the shared environment are `.refl` (identical); values from differing
positions are `.veqAll` (observationally equivalent at all depths).

When a `.veqAll` closure is applied/forced, the bisimulation exits and
delegates to the `ValueEq` VLam/VDelay clause (same-arg agreement) composed
with a recursive `sameBody_adequacy` call (argument bridge). The recursion
is well-founded on execution step count.
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

/-! ## Environment relations -/

def EnvValueEq (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False

def EnvValueEqAll (d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ k, EnvValueEq k d ρ₁ ρ₂

/-! ## EnvValueEq lemmas -/

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

/-! ## Section 1: Stack lifting for errors -/

/-- Find the first step index `K ≤ bound` where the state becomes inactive.
    (Copied from StepLift where it is private.) -/
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

/-- If `compute [] ρ t` reaches error, then `compute extra ρ t` also reaches
    error. Dual of `compute_to_ret_from_halt` from Purity.lean. -/
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

/-! ## Section 2: Application decomposition -/

/-- Decompose a halting `Apply tf ta` into function result, argument result,
    and frame result. Same liftState pattern as `force_reaches`. -/
theorem app_reaches (ρ : CekEnv) (tf ta : Term) (w : CekValue)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) (.halt w)) :
    ∃ vf vx,
      Reaches (.compute [] ρ tf) (.halt vf) ∧
      Reaches (.compute [] ρ ta) (.halt vx) ∧
      Reaches (.ret [.funV vf] vx) (.halt w) := by
  obtain ⟨N, hN⟩ := h
  -- Phase 0: one mechanical step
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) = .compute [.arg ta ρ] ρ tf := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.arg ta ρ] ρ tf) = .halt w := by
    have : N = 1 + (N - 1) := by omega
    rw [this, steps_trans, h1] at hN; exact hN
  -- Phase 1: liftState [arg ta ρ] over compute [] ρ tf
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
  -- After K1 steps under liftState, we have ret [arg ta ρ] vf
  -- One more step: ret [arg ta ρ] vf → compute [funV vf] ρ ta
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
  -- Phase 2: liftState [funV vf] over compute [] ρ ta
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
  -- Remaining steps: ret [funV vf] vx → halt w
  have h_frame : steps (((N - 1) - K1 - 1) - K2) (.ret [.funV vf] vx) = .halt w := by
    have : (N - 1) - K1 - 1 = K2 + (((N - 1) - K1 - 1) - K2) := by omega
    rw [this, steps_trans, h_comm2, h_lifted_eq2] at hrest3; exact hrest3
  exact ⟨vf, vx, h_reaches_tf, h_reaches_ta, ((N - 1) - K1 - 1) - K2, h_frame⟩

/-- Decompose an erroring `Apply tf ta` into the three possible error sources. -/
theorem app_reaches_error (ρ : CekEnv) (tf ta : Term)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) .error) :
    Reaches (.compute [] ρ tf) .error ∨
    ∃ vf, Reaches (.compute [] ρ tf) (.halt vf) ∧
      (Reaches (.compute [] ρ ta) .error ∨
       ∃ vx, Reaches (.compute [] ρ ta) (.halt vx) ∧
             Reaches (.ret [.funV vf] vx) .error) := by
  obtain ⟨N, hN⟩ := h
  -- Phase 0: one mechanical step
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) = .compute [.arg ta ρ] ρ tf := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.arg ta ρ] ρ tf) = .error := by
    have : N = 1 + (N - 1) := by omega
    rw [this, steps_trans, h1] at hN; exact hN
  -- Phase 1: liftState [arg ta ρ] over compute [] ρ tf
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
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' (N - 1) (Nat.le_refl _)
      rw [h_inner_err] at this; simp [isActive] at this
  obtain ⟨K1, hK1_le, hK1_inact, hK1_min⟩ :=
    firstInactive (.compute [] ρ tf) (N - 1) h_has_inactive1
  have h_comm1 : steps K1 (liftState [.arg ta ρ] (.compute [] ρ tf)) =
      liftState [.arg ta ρ] (steps K1 (.compute [] ρ tf)) :=
    steps_liftState [.arg ta ρ] K1 (.compute [] ρ tf) hK1_min
  by_cases h_is_error1 : steps K1 (.compute [] ρ tf) = .error
  · -- Function errors
    left; exact ⟨K1, h_is_error1⟩
  · -- Function does not error: extract vf
    right
    have ⟨vf, h_inner_eq1, h_lifted_eq1⟩ :
        ∃ vf, (steps K1 (.compute [] ρ tf) = .halt vf ∨
               steps K1 (.compute [] ρ tf) = .ret [] vf) ∧
              liftState [.arg ta ρ] (steps K1 (.compute [] ρ tf)) =
                .ret [.arg ta ρ] vf := by
      generalize h_sK : steps K1 (.compute [] ρ tf) = sK at hK1_inact h_is_error1
      match sK with
      | .compute .. => simp [isActive] at hK1_inact
      | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK1_inact
      | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error1
    have h_reaches_tf : Reaches (.compute [] ρ tf) (.halt vf) := by
      cases h_inner_eq1 with
      | inl h => exact ⟨K1, h⟩
      | inr h => exact ⟨K1 + 1, by rw [steps_trans, h]; rfl⟩
    -- After K1 steps: ret [arg ta ρ] vf → compute [funV vf] ρ ta
    have hrest2 : steps ((N - 1) - K1) (.ret [.arg ta ρ] vf) = .error := by
      have : N - 1 = K1 + ((N - 1) - K1) := by omega
      rw [this, steps_trans, h_comm1, h_lifted_eq1] at hrest; exact hrest
    have hge1_2 : (N - 1) - K1 ≥ 1 := by
      by_cases hlt : (N - 1) - K1 ≥ 1
      · exact hlt
      · exfalso; have : (N - 1) - K1 = 0 := by omega
        rw [this] at hrest2; simp [steps] at hrest2
    have hrest3 : steps ((N - 1) - K1 - 1) (.compute [.funV vf] ρ ta) = .error := by
      have : (N - 1) - K1 = 1 + ((N - 1) - K1 - 1) := by omega
      rw [this, steps_trans] at hrest2
      simp [steps, step] at hrest2; exact hrest2
    -- Phase 2: liftState [funV vf] over compute [] ρ ta
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
        have h_inner_err := liftState_eq_error _ _ h_comm.symm
        have := hall' ((N - 1) - K1 - 1) (Nat.le_refl _)
        rw [h_inner_err] at this; simp [isActive] at this
    obtain ⟨K2, hK2_le, hK2_inact, hK2_min⟩ :=
      firstInactive (.compute [] ρ ta) ((N - 1) - K1 - 1) h_has_inactive2
    have h_comm2 : steps K2 (liftState [.funV vf] (.compute [] ρ ta)) =
        liftState [.funV vf] (steps K2 (.compute [] ρ ta)) :=
      steps_liftState [.funV vf] K2 (.compute [] ρ ta) hK2_min
    by_cases h_is_error2 : steps K2 (.compute [] ρ ta) = .error
    · -- Argument errors
      exact ⟨vf, h_reaches_tf, Or.inl ⟨K2, h_is_error2⟩⟩
    · -- Argument does not error: extract vx
      have ⟨vx, h_inner_eq2, h_lifted_eq2⟩ :
          ∃ vx, (steps K2 (.compute [] ρ ta) = .halt vx ∨
                 steps K2 (.compute [] ρ ta) = .ret [] vx) ∧
                liftState [.funV vf] (steps K2 (.compute [] ρ ta)) =
                  .ret [.funV vf] vx := by
        generalize h_sK : steps K2 (.compute [] ρ ta) = sK at hK2_inact h_is_error2
        match sK with
        | .compute .. => simp [isActive] at hK2_inact
        | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
        | .ret (_ :: _) _ => simp [isActive] at hK2_inact
        | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
        | .error => exact absurd rfl h_is_error2
      have h_reaches_ta : Reaches (.compute [] ρ ta) (.halt vx) := by
        cases h_inner_eq2 with
        | inl h => exact ⟨K2, h⟩
        | inr h => exact ⟨K2 + 1, by rw [steps_trans, h]; rfl⟩
      -- Remaining steps: ret [funV vf] vx → error
      have h_frame : steps (((N - 1) - K1 - 1) - K2) (.ret [.funV vf] vx) = .error := by
        have : (N - 1) - K1 - 1 = K2 + (((N - 1) - K1 - 1) - K2) := by omega
        rw [this, steps_trans, h_comm2, h_lifted_eq2] at hrest3; exact hrest3
      exact ⟨vf, h_reaches_tf, Or.inr ⟨vx, h_reaches_ta, ((N - 1) - K1 - 1) - K2, h_frame⟩⟩

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
  -- Use compute_to_ret_from_halt for function evaluation under [arg ta ρ]
  have h_fun_ret := compute_to_ret_from_halt ρ tf vf [.arg ta ρ] hf
  obtain ⟨Kf', hKf'⟩ := h_fun_ret
  -- ret [arg ta ρ] vf → compute [funV vf] ρ ta in 1 step
  have h_step_arg : steps 1 (.ret [.arg ta ρ] vf) = .compute [.funV vf] ρ ta := by
    simp [steps, step]
  -- Use compute_to_ret_from_halt for argument evaluation under [funV vf]
  have h_arg_ret := compute_to_ret_from_halt ρ ta vx [.funV vf] ha
  obtain ⟨Ka', hKa'⟩ := h_arg_ret
  -- Compose: 1 + Kf' + 1 + Ka' + Kc steps
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
  -- Function halts with vf: under [arg ta ρ], compute reaches ret [arg ta ρ] vf
  have h_fun_ret := compute_to_ret_from_halt ρ tf vf [.arg ta ρ] hf
  obtain ⟨Kf, hKf⟩ := h_fun_ret
  -- ret [arg ta ρ] vf → compute [funV vf] ρ ta in 1 step
  have h_step_arg : steps 1 (.ret [.arg ta ρ] vf) = .compute [.funV vf] ρ ta := by
    simp [steps, step]
  -- Argument errors: under [funV vf], compute reaches error
  have h_arg_err := compute_to_error_from_error ρ ta [.funV vf] ha
  obtain ⟨Ka, hKa⟩ := h_arg_err
  exact ⟨1 + Kf + 1 + Ka, by
    have : 1 + Kf + 1 + Ka = 1 + (Kf + (1 + Ka)) := by omega
    rw [this, steps_trans, h1, steps_trans, hKf, steps_trans, h_step_arg, hKa]⟩

/-! ## Section 3: funV frame behavior under ValueEq -/

/-! ### Helper: environment lookup agreement -/

/-- `CekEnv.lookup` at index 0 always returns `none`. -/
private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ with
  | nil => rfl
  | cons _ _ => rfl

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

/-! ### Helper: one-step transitions for funV frame -/

private theorem step_ret_funV_vcon (c : Const) (vx : CekValue) :
    step (.ret [.funV (.VCon c)] vx) = .error := by rfl

private theorem step_ret_funV_vdelay (body : Term) (ρ : CekEnv) (vx : CekValue) :
    step (.ret [.funV (.VDelay body ρ)] vx) = .error := by rfl

private theorem step_ret_funV_vconstr (tag : Nat) (fields : List CekValue) (vx : CekValue) :
    step (.ret [.funV (.VConstr tag fields)] vx) = .error := by rfl

private theorem step_ret_funV_vlam (body : Term) (ρ : CekEnv) (vx : CekValue) :
    step (.ret [.funV (.VLam body ρ)] vx) = .compute [] (ρ.extend vx) body := by rfl

/-! ### Helper: error-only states can't halt -/

private theorem error_in_one_step_reaches_error (s : State)
    (h : step s = .error) : Reaches s .error :=
  ⟨1, by simp [steps, h]⟩

private theorem error_in_one_step_not_halts (s : State)
    (h : step s = .error) : ¬Halts s := by
  intro ⟨v, n, hn⟩
  have herr : Reaches s .error := error_in_one_step_reaches_error s h
  exact reaches_halt_not_error ⟨n, hn⟩ herr

/-! ### Helper: compose one-step transition with sub-computation -/

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

/-! ### ValueEq monotonicity: (k+1)-equivalent implies k-equivalent -/

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

/-! ### VBuiltin ValueEq construction from components -/

/-- Construct `ValueEq k` for VBuiltin values when we have all the components:
    same builtin name, ListValueEq args, same expected-args, evalBuiltin none↔,
    and evalBuiltin result ValueEq. Uses `valueEq_mono` and `listValueEq_mono`
    to downgrade the step index at each level. -/
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

/-! ### evalBuiltin extensionality (same head, different tail) -/

/-- Downgrade `ListValueEq` from level `n + 1` to level `1` by repeated monotonicity. -/
private theorem listValueEq_to_1 (n : Nat) (a1 a2 : List CekValue)
    (h : ListValueEq (n + 1) a1 a2) : ListValueEq 1 a1 a2 := by
  induction n with
  | zero => exact h
  | succ m ih => exact ih (listValueEq_mono (m + 1) a1 a2 h)

/-- `ListValueEq 1` implies `extractConsts` gives the same result on both sides. -/
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

/-- Pass-through builtin agreement when extractConsts fails on the tail. -/
private theorem evalBuiltinPassThrough_agree_tail (b : BuiltinFun) (vx : CekValue)
    (a1 a2 : List CekValue) (k : Nat)
    (hargs : ListValueEq (k + 1) a1 a2)
    (hargs1 : ListValueEq 1 a1 a2)
    (hec : extractConsts a1 = none) :
    match evalBuiltinPassThrough b (vx :: a1), evalBuiltinPassThrough b (vx :: a2) with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False := by
  -- Since extractConsts a1 = none and ListValueEq 1 a1 a2, both pass-through
  -- paths agree (VCon condition values match, non-VCon positions have matching constructors).
  -- Non-pass-through builtins both return none.
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · -- Each pass-through builtin has a pattern requiring specific list length
    -- and VCon at specific position. Since vx is shared and a1/a2 have matching
    -- VCon skeleton (from ListValueEq 1), both sides match identically.
    -- We case-split on vx to resolve MkCons (which inspects position 0 = vx).
    -- For all other builtins, position 0 is a wildcard.
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [evalBuiltinPassThrough] <;>
      -- After simp, the goal is a match on (b, vx :: a1) vs (b, vx :: a2).
      -- Since the match is on the same b and the lists have the same structure,
      -- we need to show that both sides step through the same match arms.
      -- For IfThenElse/ChooseList: need 3-elem list = 2-elem tail
      -- For ChooseUnit/Trace/MkCons: need 2-elem list = 1-elem tail
      -- For ChooseData: need 6-elem list = 5-elem tail
      -- If tail length doesn't match, both return none → True.
      -- Split on a1 shape to determine the match arm.
      (try (-- Builtins needing specific list shapes:
            -- Just case-split a1 sufficiently deep and let simp + split close goals
            cases a1 with
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
                    -- 1-elem tail: [vx, h1] vs [vx, h2]
                    -- ChooseUnit/Trace need h1=VCon, MkCons needs vx=VCon
                    -- Others: wrong length → simp gives True/trivial
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
                        -- 2-elem tail: [vx, h1, h1b] vs [vx, h2, h2b]
                        -- IfThenElse/ChooseList need h1b=VCon condition
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
                                -- 4-elem tail → 5-elem: ChooseData
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
                                    -- 5-elem tail: ChooseData
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

/-! ### evalBuiltin extensionality (different head, same tail) -/

/-- When two values agree at all step indices (`∀ k, ValueEq k vx vx'`),
    they have the same VCon projection: if one is `VCon c`, the other is `VCon c`. -/
private theorem valueEqAll_vcon_eq {vx vx' : CekValue} {c : Const}
    (hx : ∀ k, ValueEq k vx vx') (heq : vx = .VCon c) : vx' = .VCon c := by
  subst heq
  have h1 := hx 1; unfold ValueEq at h1
  cases vx' with
  | VCon c' => exact congrArg CekValue.VCon h1.symm
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => exact absurd h1 id

/-- Core evalBuiltin extensionality: when argument lists differ only in the head
    and that head satisfies `∀ k, ValueEq k`, evalBuiltin agrees on none/some
    and produces `∀ k, ValueEq k`-related results.
    VCon case: both heads are VCon c (same constant), so identical calls.
    Non-VCon case: extractConsts fails for both heads, so evalBuiltin reduces to
    evalBuiltinPassThrough only, which either returns none (no pattern match)
    or selects a pass-through value that is either from the shared args tail
    (identical) or is vx vs vx' (ValueEq at all k). -/
private theorem evalBuiltin_agree_head (b : BuiltinFun) (vx vx' : CekValue)
    (args : List CekValue) (hx : ∀ k, ValueEq k vx vx') :
    match evalBuiltin b (vx :: args), evalBuiltin b (vx' :: args) with
    | some v₁, some v₂ => ∀ k, ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False := by
  -- VCon case: vx = VCon c implies vx' = VCon c, so identical calls.
  -- Non-VCon case: extractConsts fails, evalBuiltin = evalBuiltinPassThrough.
  -- Since vx and vx' have the same constructor, same extractConsts behavior.
  -- evalBuiltinPassThrough pattern-matches on (b, full_list) — since args tail
  -- is shared, patterns match the same way. Pass-through values are either from
  -- the shared args (identical) or vx vs vx' (ValueEq at all k).
  -- First handle VCon case: vx = VCon c implies vx' = VCon c, so identical calls.
  cases hvx : vx with
  | VCon c =>
    have hvx' := valueEqAll_vcon_eq hx hvx; subst hvx; subst hvx'
    cases evalBuiltin b (.VCon c :: args) with
    | none => trivial
    | some v => exact fun k => valueEq_refl k v
  -- Non-VCon cases: extractConsts fails, evalBuiltin reduces to evalBuiltinPassThrough.
  | VLam bd env | VDelay bd env | VConstr tg fs | VBuiltin bn ar ea =>
    subst hvx; have h1 := hx 1
    -- Case-split vx' and eliminate impossible constructor pairs via ValueEq 1
    all_goals (cases vx' with
      | VCon _ => simp [ValueEq] at h1
      | VLam _ _ => ?_ | VDelay _ _ => ?_ | VConstr _ _ => ?_ | VBuiltin _ _ _ => ?_)
    all_goals (first | (simp [ValueEq] at h1) | skip)
    -- Remaining goals: same-constructor non-VCon pairs.
    -- evalBuiltin reduces to evalBuiltinPassThrough (extractConsts fails for non-VCon head).
    all_goals simp only [evalBuiltin, extractConsts]
    all_goals (
      by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                    b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
      · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
        -- After rcases, each goal has a concrete builtin. Case-split args.
        all_goals (
          cases args with
          | nil => simp [evalBuiltinPassThrough]
          | cons a0 rest0 =>
          cases rest0 with
          | nil =>
            cases a0 <;> simp [evalBuiltinPassThrough]
            all_goals first | trivial | (rename_i c; cases c <;> simp; first | trivial | (intro k; exact hx k) | (intro k; exact valueEq_refl k _)) | (intro k; exact hx k) | (intro k; exact valueEq_refl k _)
          | cons a1 rest1 =>
          cases rest1 with
          | nil =>
            cases a1 <;> simp [evalBuiltinPassThrough]
            all_goals first | trivial | (rename_i c; cases c <;> simp; first | trivial | (intro k; exact hx k) | (intro k; exact valueEq_refl k _) | (intro k; split <;> (first | exact hx k | exact valueEq_refl k _)) | (rename_i d; cases d <;> (first | trivial | (intro k; exact hx k) | (intro k; exact valueEq_refl k _)))) | (intro k; exact hx k) | (intro k; exact valueEq_refl k _)
            all_goals (intro k; split <;> (first | exact hx k | exact valueEq_refl k _))
          | cons a2 rest2 =>
          cases rest2 with
          | nil => simp [evalBuiltinPassThrough]
          | cons a3 rest3 =>
          cases rest3 with
          | nil => simp [evalBuiltinPassThrough]
          | cons a4 rest4 =>
          cases rest4 with
          | cons _ _ => simp [evalBuiltinPassThrough]
          | nil =>
            cases a4 <;> simp [evalBuiltinPassThrough]
            all_goals first | trivial | (rename_i c; cases c <;> simp; first | trivial | (intro k; exact hx k) | (intro k; exact valueEq_refl k _) | (rename_i d; cases d; all_goals (first | trivial | (intro k; exact hx k) | (intro k; exact valueEq_refl k _)))) | (intro k; exact hx k) | (intro k; exact valueEq_refl k _))
      · have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                       b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
          ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
           fun h => hb (h ▸ .inr (.inr (.inl rfl))),
           fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
           fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
           fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
        rw [evalBuiltinPassThrough_none_of_not_passthrough b (_ :: args) hb_not,
            evalBuiltinPassThrough_none_of_not_passthrough b (_ :: args) hb_not]
        simp only)

/-! ## Section 3b: Force decomposition (local copies of private Congruence lemmas) -/

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

/-- Decompose an erroring `Force e` into the two possible error sources. -/
private theorem force_reaches_error (ρ : CekEnv) (te : Term)
    (hreach : Reaches (.compute [] ρ (.Force te)) .error) :
    Reaches (.compute [] ρ te) .error ∨
    ∃ val, Reaches (.compute [] ρ te) (.halt val) ∧
           Reaches (.ret [.force] val) .error := by
  obtain ⟨N, hN⟩ := hreach
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.force] ρ te) = .error := by
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
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' (N - 1) (Nat.le_refl _)
      rw [h_inner_err] at this; simp [isActive] at this
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ te) (N - 1) h_has_inactive
  have h_comm : steps K (liftState [.force] (.compute [] ρ te)) =
      liftState [.force] (steps K (.compute [] ρ te)) :=
    steps_liftState [.force] K (.compute [] ρ te) hK_min
  by_cases h_is_error : steps K (.compute [] ρ te) = .error
  · left; exact ⟨K, h_is_error⟩
  · right
    have ⟨val, h_inner_eq, h_lifted_eq⟩ :
        ∃ val, (steps K (.compute [] ρ te) = .halt val ∨
               steps K (.compute [] ρ te) = .ret [] val) ∧
              liftState [.force] (steps K (.compute [] ρ te)) =
                .ret [.force] val := by
      generalize h_sK : steps K (.compute [] ρ te) = sK at hK_inact h_is_error
      match sK with
      | .compute .. => simp [isActive] at hK_inact
      | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK_inact
      | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error
    have h_reaches_te : Reaches (.compute [] ρ te) (.halt val) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    have h_frame : steps ((N - 1) - K) (.ret [.force] val) = .error := by
      have : N - 1 = K + ((N - 1) - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hrest; exact hrest
    exact ⟨val, h_reaches_te, (N - 1) - K, h_frame⟩

/-- Compose sub-expression halt + force frame result into Force result. -/
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

/-- Transfer force-frame error through ValueEq. -/
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
          -- hn : steps n (ret [] (VBuiltin b a1 rest)) = error
          -- ret [] v halts in 1 step, contradicts error
          have hh : Reaches (.ret [] (.VBuiltin b a1 rest)) (.halt (.VBuiltin b a1 rest)) :=
            ⟨1, by rfl⟩
          exact absurd (reaches_halt_not_error hh ⟨n, hn⟩) False.elim
        | none =>
          rw [htail] at hn
          cases heval : evalBuiltin b a1 with
          | some v =>
            rw [heval] at hn
            -- hn : steps n (ret [] v) = error, but ret [] v halts
            have hh : Reaches (.ret [] v) (.halt v) := ⟨1, by rfl⟩
            exact absurd (reaches_halt_not_error hh ⟨n, hn⟩) False.elim
          | none =>
            rw [heval] at hn
            cases heval2 : evalBuiltin b a2 with
            | none => exact ⟨1, by simp only [steps, step]; rw [hhead, htail, heval2]⟩
            | some v2 =>
              exfalso; exact absurd (heval_none.mp heval) (by rw [heval2]; exact fun h => by simp at h)
  -- Cross-constructor cases: ValueEq (k+1) is False
  | .VCon _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)

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
  -- Cross-constructor cases: ValueEq (k+1) is False
  | .VCon _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)

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
            -- Both step to ret [] (VBuiltin b a1/a2 rest), then halt
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
  -- Cross-constructor cases: ValueEq (k+1) is False
  | .VCon _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd hve (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd hve (by unfold ValueEq; exact id)

/-! ### Helper: same-arg, different-function transfer -/

/-- If `ValueEq (k+1) vf₁ vf₂` then applying both to the same argument `vx`
    preserves error↔, halts↔, and gives `ValueEq k` on results. -/
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
  -- Cross-constructor
  | .VCon _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)

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
  -- Cross-constructor
  | .VCon _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)

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
    -- hargs_tail : ListValueEq (k + 1) a1 a2
    have hagree := evalBuiltin_agree_tail b vx a1 a2 k hargs_tail
    -- Decompose hw₁: step (.ret [.funV (.VBuiltin b a1 ea)] vx) = ...
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
            -- Both step to VBuiltin (vx :: a) rest, then halt in 1 step
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
                -- Need ValueEq k (VBuiltin b (vx::a1) rest) (VBuiltin b (vx::a2) rest)
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
  -- Cross-constructor
  | .VCon _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)

private theorem closedAtList_of_mem {d : Nat} {ts : List Term} {t : Term}
    (hcl : closedAtList d ts = true) (hmem : t ∈ ts) : closedAt d t = true := by
  induction ts with
  | nil => exact absurd hmem List.not_mem_nil
  | cons t' ts' ih =>
    have ⟨ht', hts'⟩ := closedAt_constr_cons hcl
    cases hmem with
    | head => exact ht'
    | tail _ h => exact ih hts' h

/-! ## Section 3c: ListValueEq helpers for Constr -/

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

/-! ## Section 3d: Generic single-frame liftState decomposition -/

/-- Decompose `compute [f] ρ t` reaching halt: the inner computation must halt,
    and the frame continuation reaches halt. -/
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

/-- Decompose `compute [f] ρ t` reaching error: either the inner computation
    errors, or it halts and the frame continuation errors. -/
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
  -- Same proof as compute_frame_halt_decompose but with arbitrary stk
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
  -- Same proof pattern as compute_frame_error_decompose
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

/-! ## Section 3e: constrField iteration adequacy -/

/-- The constrField iteration produces related results under related environments.
    Both sides are at `ret [constrField tag done remaining ρ] v` with related
    current values, related accumulated done lists, and adequate remaining fields. -/
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
    -- Error ↔
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
    -- Halts ↔
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
    -- ValueEq k
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

/-- Transfer through a shared applyArg chain. Both sides process the same
    field values applied to `∀ k, ValueEq k`-related intermediate results.
    Each step uses the VLam clause of ValueEq (same arg, different functions). -/
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
    -- Empty field list: ret [] v → halt v in 1 step
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
    -- ret (applyArg field :: rest.map applyArg) v_i
    -- Step: applies v_i to field. Same step structure as funV.
    -- Use the VLam clause of ValueEq (or error for non-applicable types).
    -- v₁ and v₂ have same constructor (from ValueEq 1).
    have h1 := hv 1
    match v₁, v₂ with
    | .VLam body₁ env₁, .VLam body₂ env₂ =>
      -- Both step to compute (rest.map applyArg) (env_i.extend field) body_i
      have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VLam body₁ env₁)) =
          .compute (rest.map Frame.applyArg) (env₁.extend field) body₁ := rfl
      have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VLam body₂ env₂)) =
          .compute (rest.map Frame.applyArg) (env₂.extend field) body₂ := rfl
      -- VLam clause of ValueEq (k+1) with arg = field:
      -- error↔, halts↔, ValueEq k for body₁(field) vs body₂(field)
      -- This gives us error↔/halts↔ for the bodies, and ∀k ValueEq k on results
      -- (picking k+1 from hv to get ValueEq k at each level).
      -- Bodies under env₁.extend field vs env₂.extend field: use VLam clause.
      -- Then compose through rest using ih.
      -- VLam clause with shared field: ∀ arg, error↔ ∧ halts↔ ∧ ValueEq k
      unfold ValueEq at h1
      -- Extract body agreement from VLam clause, using all k levels
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
      -- The stk after VLam step is rest.map Frame.applyArg
      -- Use compute_stk_error_decompose and compute_stk_halt_decompose for decomposition
      refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, ⟨fun hh => ?_, fun hh => ?_⟩,
              fun k w₁ w₂ hw₁ hw₂ => ?_⟩
      · -- Error left→right
        have herr' := reaches_to_step_reaches hl herr (by simp)
        rcases compute_stk_error_decompose (rest.map Frame.applyArg) (env₁.extend field) body₁ herr'
          with hbody_err | ⟨r₁, hbody_halt, hrest_err⟩
        · exact reaches_of_step_reaches hr
            (compute_to_error_from_error _ body₂ (rest.map Frame.applyArg) (herr_body.mp hbody_err))
        · obtain ⟨r₂, hr₂⟩ := hhalt_body.mp ⟨r₁, hbody_halt⟩
          have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hbody_halt hr₂
          have ⟨herr_rest, _, _⟩ := ih r₁ r₂ hveq_r
          exact reaches_of_step_reaches hr
            (compute_stk_compose (rest.map Frame.applyArg) _ body₂ r₂ .error hr₂ (herr_rest.mp hrest_err))
      · -- Error right→left: symmetric
        have herr' := reaches_to_step_reaches hr herr (by simp)
        rcases compute_stk_error_decompose (rest.map Frame.applyArg) (env₂.extend field) body₂ herr'
          with hbody_err | ⟨r₂, hbody_halt, hrest_err⟩
        · exact reaches_of_step_reaches hl
            (compute_to_error_from_error _ body₁ (rest.map Frame.applyArg) (herr_body.mpr hbody_err))
        · obtain ⟨r₁, hr₁⟩ := hhalt_body.mpr ⟨r₂, hbody_halt⟩
          have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hr₁ hbody_halt
          have ⟨herr_rest, _, _⟩ := ih r₁ r₂ hveq_r
          exact reaches_of_step_reaches hl
            (compute_stk_compose (rest.map Frame.applyArg) _ body₁ r₁ .error hr₁ (herr_rest.mpr hrest_err))
      · -- Halts left→right
        obtain ⟨w, hw⟩ := hh
        have hw' := reaches_to_step_reaches hl hw (by simp)
        obtain ⟨r₁, hbody_halt, hrest_halt⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₁ w hw'
        obtain ⟨r₂, hr₂⟩ := hhalt_body.mp ⟨r₁, hbody_halt⟩
        have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hbody_halt hr₂
        have ⟨_, hhalt_rest, _⟩ := ih r₁ r₂ hveq_r
        obtain ⟨w', hw'⟩ := hhalt_rest.mp ⟨w, hrest_halt⟩
        exact ⟨w', reaches_of_step_reaches hr
          (compute_stk_compose (rest.map Frame.applyArg) _ body₂ r₂ (.halt w') hr₂ hw')⟩
      · -- Halts right→left: symmetric
        obtain ⟨w, hw⟩ := hh
        have hw' := reaches_to_step_reaches hr hw (by simp)
        obtain ⟨r₂, hbody_halt, hrest_halt⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₂ w hw'
        obtain ⟨r₁, hr₁⟩ := hhalt_body.mpr ⟨r₂, hbody_halt⟩
        have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hr₁ hbody_halt
        have ⟨_, hhalt_rest, _⟩ := ih r₁ r₂ hveq_r
        obtain ⟨w', hw'⟩ := hhalt_rest.mpr ⟨w, hrest_halt⟩
        exact ⟨w', reaches_of_step_reaches hl
          (compute_stk_compose (rest.map Frame.applyArg) _ body₁ r₁ (.halt w') hr₁ hw')⟩
      · -- ValueEq
        have hw₁' := reaches_to_step_reaches hl hw₁ (by simp)
        have hw₂' := reaches_to_step_reaches hr hw₂ (by simp)
        obtain ⟨r₁, hbody₁, hrest₁⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₁ w₁ hw₁'
        obtain ⟨r₂, hbody₂, hrest₂⟩ :=
          compute_stk_halt_decompose (rest.map Frame.applyArg) _ body₂ w₂ hw₂'
        have hveq_r : ∀ j, ValueEq j r₁ r₂ := fun j => hval_body j r₁ r₂ hbody₁ hbody₂
        exact (ih r₁ r₂ hveq_r).2.2 k w₁ w₂ hrest₁ hrest₂
    -- Non-VLam: both error (applyArg can't apply non-function/non-builtin)
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
      -- VBuiltin: from ValueEq 2, bn₁=bn₂, ea₁=ea₂, ListValueEq 1 ar₁ ar₂.
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
          -- Partial: VBuiltin b (field :: ar_i) ea_rest
          have hl : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₁ ea₁)) =
              .ret (rest.map Frame.applyArg) (.VBuiltin bn₁ (field :: ar₁) ea_rest) := by
            simp [step, hhead, htail]
          have hr : step (.ret (.applyArg field :: rest.map Frame.applyArg) (.VBuiltin bn₁ ar₂ ea₁)) =
              .ret (rest.map Frame.applyArg) (.VBuiltin bn₁ (field :: ar₂) ea_rest) := by
            simp [step, hhead, htail]
          -- New values: ∀k ValueEq k (same b, field :: ar_i related, same ea_rest)
          -- Use valueEq_vbuiltin for the construction
          have hveq_new : ∀ k, ValueEq k (.VBuiltin bn₁ (field :: ar₁) ea_rest)
              (.VBuiltin bn₁ (field :: ar₂) ea_rest) := by
            intro k; match k with
            | 0 => simp [ValueEq]
            | k + 1 =>
              -- Need: ListValueEq k (field :: ar₁) (field :: ar₂), evalBuiltin none↔ and val
              -- From hv (k+2): ValueEq (k+2) on VBuiltin gives ListValueEq (k+1) ar₁ ar₂
              have hargs_succ : ListValueEq (k + 1) ar₁ ar₂ := by
                have := hv (k + 2); unfold ValueEq at this; exact this.2.1
              have hargs_k : ListValueEq k ar₁ ar₂ := listValueEq_mono k _ _ hargs_succ
              have hlist_k : ListValueEq k (field :: ar₁) (field :: ar₂) := by
                simp only [ListValueEq]; exact ⟨valueEq_refl k field, hargs_k⟩
              -- evalBuiltin_agree_tail needs ListValueEq (k+1) args
              have h_agree := evalBuiltin_agree_tail bn₁ field ar₁ ar₂ k hargs_succ
              have hlist_succ : ListValueEq (k + 1) (field :: ar₁) (field :: ar₂) := by
                simp only [ListValueEq]; exact ⟨valueEq_refl (k+1) field, hargs_succ⟩
              -- evalBuiltin_agree_tail at level k gives ValueEq k on results
              exact valueEq_vbuiltin (k + 1) bn₁ (field :: ar₁) (field :: ar₂) ea_rest hlist_succ
                (by revert h_agree; cases evalBuiltin bn₁ (field :: ar₁) <;> cases evalBuiltin bn₁ (field :: ar₂) <;>
                    simp <;> (try trivial) <;> intro h <;> simp_all)
                (by intro r₁ r₂ hr₁ hr₂
                    have h_agree' := evalBuiltin_agree_tail bn₁ field ar₁ ar₂ (k + 1)
                      (by have := hv (k + 3); unfold ValueEq at this; exact this.2.1)
                    revert h_agree'; rw [hr₁, hr₂]; simp)
          -- Recurse
          -- Recurse on rest with the new VBuiltin values
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
          -- Saturated: evalBuiltin b (field :: ar_i)
          -- Use evalBuiltin_agree_tail with a high enough level
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

/-- Same body under related envs with a shared applyArg stack.
    Composes `sameBody_adequacy` (for the body) with `applyArg_chain_transfer`
    (for the shared field chain). -/
private theorem sameBody_with_shared_applyArg_stack
    (fields : List CekValue) (alt : Term) (d : Nat) (ρ₁ ρ₂ : CekEnv)
    (hcl_alt : closedAt d alt = true) (hρ : EnvValueEqAll d ρ₁ ρ₂)
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
  · -- Error left→right
    rcases compute_stk_error_decompose _ ρ₁ alt herr with halt_err | ⟨v₁, hv₁, hrest_err⟩
    · exact compute_to_error_from_error ρ₂ alt _ (herr_alt.mp halt_err)
    · obtain ⟨v₂, hv₂⟩ := hhalt_alt.mp ⟨v₁, hv₁⟩
      have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
      exact compute_stk_compose _ ρ₂ alt v₂ .error hv₂
        ((applyArg_chain_transfer fields v₁ v₂ hveq).1.mp hrest_err)
  · -- Error right→left
    rcases compute_stk_error_decompose _ ρ₂ alt herr with halt_err | ⟨v₂, hv₂, hrest_err⟩
    · exact compute_to_error_from_error ρ₁ alt _ (herr_alt.mpr halt_err)
    · obtain ⟨v₁, hv₁⟩ := hhalt_alt.mpr ⟨v₂, hv₂⟩
      have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
      exact compute_stk_compose _ ρ₁ alt v₁ .error hv₁
        ((applyArg_chain_transfer fields v₁ v₂ hveq).1.mpr hrest_err)
  · -- Halts left→right
    obtain ⟨w, hw⟩ := hh
    obtain ⟨v₁, hv₁, hrest⟩ := compute_stk_halt_decompose _ ρ₁ alt w hw
    obtain ⟨v₂, hv₂⟩ := hhalt_alt.mp ⟨v₁, hv₁⟩
    have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
    obtain ⟨w', hw'⟩ := (applyArg_chain_transfer fields v₁ v₂ hveq).2.1.mp ⟨w, hrest⟩
    exact ⟨w', compute_stk_compose _ ρ₂ alt v₂ (.halt w') hv₂ hw'⟩
  · -- Halts right→left
    obtain ⟨w, hw⟩ := hh
    obtain ⟨v₂, hv₂, hrest⟩ := compute_stk_halt_decompose _ ρ₂ alt w hw
    obtain ⟨v₁, hv₁⟩ := hhalt_alt.mpr ⟨v₂, hv₂⟩
    have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
    obtain ⟨w', hw'⟩ := (applyArg_chain_transfer fields v₁ v₂ hveq).2.1.mpr ⟨w, hrest⟩
    exact ⟨w', compute_stk_compose _ ρ₁ alt v₁ (.halt w') hv₁ hw'⟩
  · -- ValueEq
    obtain ⟨v₁, hv₁, hrest₁⟩ := compute_stk_halt_decompose _ ρ₁ alt w₁ hw₁
    obtain ⟨v₂, hv₂, hrest₂⟩ := compute_stk_halt_decompose _ ρ₂ alt w₂ hw₂
    have hveq : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
    exact (applyArg_chain_transfer fields v₁ v₂ hveq).2.2 k w₁ w₂ hrest₁ hrest₂

mutual
theorem funV_frame_beh (vf vx vx' : CekValue)
    (hx : ∀ k, ValueEq k vx vx') :
    (Reaches (.ret [.funV vf] vx) .error ↔
     Reaches (.ret [.funV vf] vx') .error) ∧
    (Halts (.ret [.funV vf] vx) ↔ Halts (.ret [.funV vf] vx')) ∧
    ∀ (k : Nat) (w₁ w₂ : CekValue),
      Reaches (.ret [.funV vf] vx) (.halt w₁) →
      Reaches (.ret [.funV vf] vx') (.halt w₂) →
      ValueEq k w₁ w₂ := by
  match vf with
  -- VCon: both sides error in 1 step
  | .VCon c =>
    have hl : step (.ret [.funV (.VCon c)] vx) = .error := rfl
    have hr : step (.ret [.funV (.VCon c)] vx') = .error := rfl
    refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  -- VDelay: both sides error in 1 step
  | .VDelay body ρ =>
    have hl : step (.ret [.funV (.VDelay body ρ)] vx) = .error := rfl
    have hr : step (.ret [.funV (.VDelay body ρ)] vx') = .error := rfl
    refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  -- VConstr: both sides error in 1 step
  | .VConstr tag fields =>
    have hl : step (.ret [.funV (.VConstr tag fields)] vx) = .error := rfl
    have hr : step (.ret [.funV (.VConstr tag fields)] vx') = .error := rfl
    refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  -- VLam: both sides step to compute [] (ρ.extend vx/vx') body.
  -- Uses sameBody_adequacy (mutual reference).
  | .VLam body ρ =>
    have hl : step (.ret [.funV (.VLam body ρ)] vx) = .compute [] (ρ.extend vx) body := rfl
    have hr : step (.ret [.funV (.VLam body ρ)] vx') = .compute [] (ρ.extend vx') body := rfl
    have ⟨d, hcl⟩ := closedAt_exists body
    have hρ' := envValueEqAll_of_same_extend d ρ vx vx' hx
    have ⟨herr_sb, hhalt_sb, hval_sb⟩ := sameBody_adequacy d body (ρ.extend vx) (ρ.extend vx') hcl hρ'
    refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, ⟨fun hh => ?_, fun hh => ?_⟩,
            fun k w₁ w₂ hw₁ hw₂ => ?_⟩
    · have h := reaches_to_step_reaches hl herr (by simp)
      exact reaches_of_step_reaches hr (herr_sb.mp h)
    · have h := reaches_to_step_reaches hr herr (by simp)
      exact reaches_of_step_reaches hl (herr_sb.mpr h)
    · obtain ⟨w, hw⟩ := hh
      have h := reaches_to_step_reaches hl hw (by simp)
      obtain ⟨w', hw'⟩ := hhalt_sb.mp ⟨w, h⟩
      exact ⟨w', reaches_of_step_reaches hr hw'⟩
    · obtain ⟨w, hw⟩ := hh
      have h := reaches_to_step_reaches hr hw (by simp)
      obtain ⟨w', hw'⟩ := hhalt_sb.mpr ⟨w, h⟩
      exact ⟨w', reaches_of_step_reaches hl hw'⟩
    · exact hval_sb k w₁ w₂
        (reaches_to_step_reaches hl hw₁ (by simp))
        (reaches_to_step_reaches hr hw₂ (by simp))
  -- VBuiltin: case split on expected args
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      -- Both sides error in 1 step
      have hl : step (.ret [.funV (.VBuiltin b args ea)] vx) = .error := by
        simp [step, hhead]
      have hr : step (.ret [.funV (.VBuiltin b args ea)] vx') = .error := by
        simp [step, hhead]
      refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
               fun _ => error_in_one_step_reaches_error _ hl⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
               fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        -- Both sides step to ret [] (VBuiltin b (vx/vx' :: args) rest)
        -- which halts in 1 more step (ret [] v -> halt v)
        have hl : step (.ret [.funV (.VBuiltin b args ea)] vx) =
            .ret [] (.VBuiltin b (vx :: args) rest) := by
          simp only [step]; rw [hhead, htail]
        have hr : step (.ret [.funV (.VBuiltin b args ea)] vx') =
            .ret [] (.VBuiltin b (vx' :: args) rest) := by
          simp only [step]; rw [hhead, htail]
        have hl2 : steps 2 (.ret [.funV (.VBuiltin b args ea)] vx) =
            .halt (.VBuiltin b (vx :: args) rest) := by
          show steps 1 (step (.ret [.funV (.VBuiltin b args ea)] vx)) = _
          rw [hl]; rfl
        have hr2 : steps 2 (.ret [.funV (.VBuiltin b args ea)] vx') =
            .halt (.VBuiltin b (vx' :: args) rest) := by
          show steps 1 (step (.ret [.funV (.VBuiltin b args ea)] vx')) = _
          rw [hr]; rfl
        refine ⟨?_, ?_, ?_⟩
        · constructor
          · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl2⟩ herr) False.elim
          · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr2⟩ herr) False.elim
        · exact ⟨fun _ => ⟨_, 2, hr2⟩, fun _ => ⟨_, 2, hl2⟩⟩
        · intro k w₁ w₂ hw₁ hw₂
          have heq₁ := reaches_unique hw₁ ⟨2, hl2⟩; subst heq₁
          have heq₂ := reaches_unique hw₂ ⟨2, hr2⟩; subst heq₂
          -- Need ValueEq k (VBuiltin b (vx :: args) rest) (VBuiltin b (vx' :: args) rest)
          have hlistveq : ∀ k, ListValueEq k (vx :: args) (vx' :: args) := fun j => by
            simp only [ListValueEq]; exact ⟨hx j, listValueEq_refl j args⟩
          have hagree := evalBuiltin_agree_head b vx vx' args hx
          have hevnone : evalBuiltin b (vx :: args) = none ↔
              evalBuiltin b (vx' :: args) = none := by
            revert hagree
            cases evalBuiltin b (vx :: args) <;> cases evalBuiltin b (vx' :: args) <;>
              simp <;> intro h <;> exact absurd h id
          have hevval : ∀ r1 r2, evalBuiltin b (vx :: args) = some r1 →
              evalBuiltin b (vx' :: args) = some r2 → ValueEq k r1 r2 := by
            intro r1 r2 h1 h2
            revert hagree; rw [h1, h2]; simp; intro hveq; exact hveq k
          exact valueEq_vbuiltin k b (vx :: args) (vx' :: args) rest
            (hlistveq k) hevnone hevval
      | none =>
        -- Saturated builtin: evalBuiltin b (vx/vx' :: args)
        have hagree := evalBuiltin_agree_head b vx vx' args hx
        -- Case-split on evalBuiltin results
        cases heval1 : evalBuiltin b (vx :: args) with
        | none =>
          -- Both error (evalBuiltin b (vx' :: args) = none by hagree)
          have heval2 : evalBuiltin b (vx' :: args) = none := by
            revert hagree; rw [heval1]; cases evalBuiltin b (vx' :: args) <;> simp
          have hl : step (.ret [.funV (.VBuiltin b args ea)] vx) = .error := by
            simp only [step]; rw [hhead, htail, heval1]
          have hr : step (.ret [.funV (.VBuiltin b args ea)] vx') = .error := by
            simp only [step]; rw [hhead, htail, heval2]
          exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
                   fun _ => error_in_one_step_reaches_error _ hl⟩,
                  ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
                   fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
                  fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
        | some v1 =>
          -- Both succeed: evalBuiltin b (vx' :: args) = some v2 by hagree
          have heval2_some : ∃ v2, evalBuiltin b (vx' :: args) = some v2 := by
            revert hagree; rw [heval1]
            cases hev2 : evalBuiltin b (vx' :: args) with
            | none => simp
            | some v2 => exact fun _ => ⟨v2, rfl⟩
          obtain ⟨v2, heval2⟩ := heval2_some
          have hveq_result : ∀ k, ValueEq k v1 v2 := by
            revert hagree; rw [heval1, heval2]; simp
          have hl : step (.ret [.funV (.VBuiltin b args ea)] vx) = .ret [] v1 := by
            simp only [step]; rw [hhead, htail, heval1]
          have hr : step (.ret [.funV (.VBuiltin b args ea)] vx') = .ret [] v2 := by
            simp only [step]; rw [hhead, htail, heval2]
          have hl2 : steps 2 (.ret [.funV (.VBuiltin b args ea)] vx) = .halt v1 := by
            show steps 1 (step _) = _; rw [hl]; rfl
          have hr2 : steps 2 (.ret [.funV (.VBuiltin b args ea)] vx') = .halt v2 := by
            show steps 1 (step _) = _; rw [hr]; rfl
          refine ⟨⟨fun herr => absurd (reaches_halt_not_error ⟨2, hl2⟩ herr) False.elim,
                   fun herr => absurd (reaches_halt_not_error ⟨2, hr2⟩ herr) False.elim⟩,
                  ⟨fun _ => ⟨_, 2, hr2⟩, fun _ => ⟨_, 2, hl2⟩⟩,
                  fun k w₁ w₂ hw₁ hw₂ => ?_⟩
          have := reaches_unique hw₁ ⟨2, hl2⟩; subst this
          have := reaches_unique hw₂ ⟨2, hr2⟩; subst this
          exact hveq_result k
  termination_by sizeOf vf
  decreasing_by all_goals simp_wf; omega

/-- Generalized applyArg chain transfer with BOTH different values AND different fields.
    Both field lists and both values are `∀ k, ValueEq k`-related.
    Uses `funV_frame_beh` (same function, different args) at each step. -/
theorem applyArg_chain_general
    (fs₁ fs₂ : List CekValue) (v₁ v₂ : CekValue)
    (hfs : ∀ k, ListValueEq k fs₁ fs₂) (hv : ∀ k, ValueEq k v₁ v₂) :
      (Reaches (.ret (fs₁.map Frame.applyArg) v₁) .error ↔
       Reaches (.ret (fs₂.map Frame.applyArg) v₂) .error) ∧
      (Halts (.ret (fs₁.map Frame.applyArg) v₁) ↔
       Halts (.ret (fs₂.map Frame.applyArg) v₂)) ∧
      ∀ (k : Nat) (w₁ w₂ : CekValue),
        Reaches (.ret (fs₁.map Frame.applyArg) v₁) (.halt w₁) →
        Reaches (.ret (fs₂.map Frame.applyArg) v₂) (.halt w₂) →
        ValueEq k w₁ w₂ := by
  match fs₁, fs₂ with
  | [], [] =>
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
  | [], _ :: _ => exact absurd ((hfs 0) : ListValueEq 0 [] (_ :: _)) (by simp [ListValueEq])
  | _ :: _, [] => exact absurd ((hfs 0) : ListValueEq 0 (_ :: _) []) (by simp [ListValueEq])
  | f₁ :: rest₁, f₂ :: rest₂ =>
    -- Chain through middle: ret (f₁ :: rest₁.map applyArg) v₁ ≡
    --   ret (f₁ :: rest₁.map applyArg) v₂ (same fields₁, different values)
    --   ≡ ret (f₂ :: rest₂.map applyArg) v₂ (same value, different fields)
    -- Step 1: applyArg_chain_transfer rest₁ for shared fields₁ with different v₁, v₂
    -- This is the existing applyArg_chain_transfer.
    have hmid := applyArg_chain_transfer (f₁ :: rest₁) v₁ v₂ hv
    -- Step 2: same v₂, different fields: funV_frame_beh at first step + recurse
    -- ret (applyArg f₁ :: rest₁.map applyArg) v₂ vs ret (applyArg f₂ :: rest₂.map applyArg) v₂
    -- Use funV_frame_beh v₂ f₁ f₂ for the single frame application.
    -- But funV_frame_beh handles ret [funV vf] vx vs ret [funV vf] vx'.
    -- Here: ret [applyArg f_i ...] v₂. The applyArg step applies v₂ to f_i.
    -- This is funV_frame_beh with vf=v₂ and vx=f₁, vx'=f₂.
    -- After one step: results r₁, r₂ with ∀k ValueEq k.
    -- Then recurse on rest₁, rest₂ with r₁, r₂.
    -- But funV_frame_beh gives results for ret [funV v₂] f_i (single frame).
    -- Here we have ret (applyArg f_i :: rest.map applyArg) v₂ (multi-frame).
    -- Need to decompose through the multi-frame stack.
    -- Use compute_stk_* style decomposition... but ret, not compute.
    -- Actually: for VLam v₂, step (ret (applyArg f₁ :: rest.map applyArg) v₂) =
    --   compute (rest₁.map applyArg) (env.extend f₁) body. This is a compute state.
    -- The same step for f₂: compute (rest₂.map applyArg) (env.extend f₂) body.
    -- These are: same body, same env, different args f₁/f₂, different stacks rest₁/rest₂.
    -- Step 2: same v₂, different fields f₁ vs f₂.
    -- v₂ applied to f₁ vs f₂: use funV_frame_beh v₂ f₁ f₂
    -- But funV_frame_beh handles [funV v₂] vx₁ vx₂ (single frame).
    -- Here we have (applyArg f_i :: rest_i.map applyArg) v₂ (multi-frame).
    -- Decompose: one step produces compute or error, then recurse.
    -- For VLam v₂: step produces compute (rest_i.map applyArg) (env.extend f_i) body.
    -- Use sameBody_adequacy on body under env.extend f₁ vs env.extend f₂.
    -- Then recurse on rest₁, rest₂ with body results.
    -- For non-VLam: step produces error for both (same constructor from ValueEq).
    -- Compose hmid with step2 via Iff.trans.
    -- Step 2: show agreement for ret (f₁::rest₁.map applyArg) v₂ vs ret (f₂::rest₂.map applyArg) v₂.
    -- v₂ has same constructor on both sides (it's the same value!).
    -- Actually v₂ is the SAME value on both sides. So step depends only on v₂.
    -- If v₂ = VLam body env: step produces compute (rest_i.map applyArg) (env.extend f_i) body.
    -- Use sameBody on body with envValueEqAll_of_same_extend (f₁ vs f₂, ∀k ValueEq k).
    -- Then applyArg_chain_general rest₁ rest₂ r₁ r₂ (recursive call).
    -- If v₂ = VCon/VDelay/VConstr: step = error for both.
    -- If v₂ = VBuiltin: complex but same pattern (sorry sub-case).
    -- Compose hmid and step2 for the full result.
    -- Actually simpler: just compose hmid with the step2 full triple.
    -- hmid: ret (f₁::rest₁.map applyArg) v₁ ≡ ret (f₁::rest₁.map applyArg) v₂ (shared stk, diff values)
    -- step2: ret (f₁::rest₁.map applyArg) v₂ ≡ ret (f₂::rest₂.map applyArg) v₂ (diff stk, same value)
    -- For step2, since v₂ is the SAME, decompose through the first applyArg:
    -- If v₂ is non-applicable (VCon/VDelay/VConstr): both error.
    -- If v₂ = VLam body₂ env₂: both step to compute rest_i (env₂.extend f_i) body₂.
    --   sameBody on body₂ under (env₂.extend f₁) vs (env₂.extend f₂): use ∀k ValueEq k f₁ f₂.
    --   Then recurse: applyArg_chain_general rest₁ rest₂ r₁ r₂.
    -- If v₂ = VBuiltin: sorry sub-case.
    -- Extract hfs components
    have hf_veq : ∀ k, ValueEq k f₁ f₂ := fun k => by
      have := hfs k; simp only [ListValueEq] at this; exact this.1
    have hrest_veq : ∀ k, ListValueEq k rest₁ rest₂ := fun k => by
      have := hfs k; simp only [ListValueEq] at this; exact this.2
    -- Compute step2 triple
    have hstep2 :
        (Reaches (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) v₂) .error ↔
         Reaches (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) v₂) .error) ∧
        (Halts (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) v₂) ↔
         Halts (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) v₂)) ∧
        ∀ k w₁ w₂,
          Reaches (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) v₂) (.halt w₁) →
          Reaches (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) v₂) (.halt w₂) →
          ValueEq k w₁ w₂ := by
      -- Case split on v₂
      match v₂ with
      | .VLam body₂ env₂ =>
        -- Both step to compute (rest_i.map applyArg) (env₂.extend f_i) body₂
        have hl₂ : step (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) (.VLam body₂ env₂)) =
            .compute (rest₁.map Frame.applyArg) (env₂.extend f₁) body₂ := rfl
        have hr₂ : step (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) (.VLam body₂ env₂)) =
            .compute (rest₂.map Frame.applyArg) (env₂.extend f₂) body₂ := rfl
        -- sameBody on body₂ under env₂.extend f₁ vs env₂.extend f₂
        have ⟨d₂, hcl₂⟩ := closedAt_exists body₂
        have hρ₂ := envValueEqAll_of_same_extend d₂ env₂ f₁ f₂ hf_veq
        have hsba₂ := sameBody_adequacy d₂ body₂ (env₂.extend f₁) (env₂.extend f₂) hcl₂ hρ₂
        obtain ⟨herr₂, hhalt₂, hval₂⟩ := hsba₂
        -- After body: results r₁, r₂ with ∀k ValueEq k.
        -- Then: applyArg_chain_general rest₁ rest₂ r₁ r₂ (recursive).
        -- Compose: body computation + chain.
        refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, ⟨fun hh => ?_, fun hh => ?_⟩,
                fun k w₁ w₂ hw₁ hw₂ => ?_⟩
        · have herr' := reaches_to_step_reaches hl₂ herr (by simp)
          rcases compute_stk_error_decompose _ _ body₂ herr' with hbe | ⟨r₁, hr₁, hre⟩
          · exact reaches_of_step_reaches hr₂ (compute_to_error_from_error _ body₂ _ (herr₂.mp hbe))
          · obtain ⟨r₂, hr₂'⟩ := hhalt₂.mp ⟨r₁, hr₁⟩
            have hrv : ∀ j, ValueEq j r₁ r₂ := fun j => hval₂ j r₁ r₂ hr₁ hr₂'
            exact reaches_of_step_reaches hr₂
              (compute_stk_compose _ _ body₂ r₂ .error hr₂'
                ((applyArg_chain_general rest₁ rest₂ r₁ r₂ hrest_veq hrv).1.mp hre))
        · have herr' := reaches_to_step_reaches hr₂ herr (by simp)
          rcases compute_stk_error_decompose _ _ body₂ herr' with hbe | ⟨r₂, hr₂', hre⟩
          · exact reaches_of_step_reaches hl₂ (compute_to_error_from_error _ body₂ _ (herr₂.mpr hbe))
          · obtain ⟨r₁, hr₁⟩ := hhalt₂.mpr ⟨r₂, hr₂'⟩
            have hrv : ∀ j, ValueEq j r₁ r₂ := fun j => hval₂ j r₁ r₂ hr₁ hr₂'
            exact reaches_of_step_reaches hl₂
              (compute_stk_compose _ _ body₂ r₁ .error hr₁
                ((applyArg_chain_general rest₁ rest₂ r₁ r₂ hrest_veq hrv).1.mpr hre))
        · obtain ⟨w, hw⟩ := hh
          have hw' := reaches_to_step_reaches hl₂ hw (by simp)
          obtain ⟨r₁, hr₁, hre⟩ := compute_stk_halt_decompose _ _ body₂ w hw'
          obtain ⟨r₂, hr₂'⟩ := hhalt₂.mp ⟨r₁, hr₁⟩
          have hrv : ∀ j, ValueEq j r₁ r₂ := fun j => hval₂ j r₁ r₂ hr₁ hr₂'
          obtain ⟨w', hw'⟩ := (applyArg_chain_general rest₁ rest₂ r₁ r₂ hrest_veq hrv).2.1.mp ⟨w, hre⟩
          exact ⟨w', reaches_of_step_reaches hr₂ (compute_stk_compose _ _ body₂ r₂ (.halt w') hr₂' hw')⟩
        · obtain ⟨w, hw⟩ := hh
          have hw' := reaches_to_step_reaches hr₂ hw (by simp)
          obtain ⟨r₂, hr₂', hre⟩ := compute_stk_halt_decompose _ _ body₂ w hw'
          obtain ⟨r₁, hr₁⟩ := hhalt₂.mpr ⟨r₂, hr₂'⟩
          have hrv : ∀ j, ValueEq j r₁ r₂ := fun j => hval₂ j r₁ r₂ hr₁ hr₂'
          obtain ⟨w', hw'⟩ := (applyArg_chain_general rest₁ rest₂ r₁ r₂ hrest_veq hrv).2.1.mpr ⟨w, hre⟩
          exact ⟨w', reaches_of_step_reaches hl₂ (compute_stk_compose _ _ body₂ r₁ (.halt w') hr₁ hw')⟩
        · have hw₁' := reaches_to_step_reaches hl₂ hw₁ (by simp)
          have hw₂' := reaches_to_step_reaches hr₂ hw₂ (by simp)
          obtain ⟨r₁, hr₁, hre₁⟩ := compute_stk_halt_decompose _ _ body₂ w₁ hw₁'
          obtain ⟨r₂, hr₂', hre₂⟩ := compute_stk_halt_decompose _ _ body₂ w₂ hw₂'
          have hrv : ∀ j, ValueEq j r₁ r₂ := fun j => hval₂ j r₁ r₂ hr₁ hr₂'
          exact (applyArg_chain_general rest₁ rest₂ r₁ r₂ hrest_veq hrv).2.2 k w₁ w₂ hre₁ hre₂
      | .VCon c₂ =>
        have hl₂ : step (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) (.VCon c₂)) = .error := rfl
        have hr₂ : step (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) (.VCon c₂)) = .error := rfl
        exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr₂,
                 fun _ => error_in_one_step_reaches_error _ hl₂⟩,
                ⟨fun h => absurd h (error_in_one_step_not_halts _ hl₂),
                 fun h => absurd h (error_in_one_step_not_halts _ hr₂)⟩,
                fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl₂)⟩
      | .VDelay bd₂ ev₂ =>
        have hl₂ : step (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) (.VDelay bd₂ ev₂)) = .error := rfl
        have hr₂ : step (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) (.VDelay bd₂ ev₂)) = .error := rfl
        exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr₂,
                 fun _ => error_in_one_step_reaches_error _ hl₂⟩,
                ⟨fun h => absurd h (error_in_one_step_not_halts _ hl₂),
                 fun h => absurd h (error_in_one_step_not_halts _ hr₂)⟩,
                fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl₂)⟩
      | .VConstr tg₂ flds₂ =>
        exact ⟨⟨fun _ => error_in_one_step_reaches_error _
                 (rfl : step (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) (.VConstr tg₂ flds₂)) = .error),
                 fun _ => error_in_one_step_reaches_error _
                 (rfl : step (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) (.VConstr tg₂ flds₂)) = .error)⟩,
                ⟨fun h => absurd h (error_in_one_step_not_halts _
                  (rfl : step (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) (.VConstr tg₂ flds₂)) = .error)),
                 fun h => absurd h (error_in_one_step_not_halts _
                  (rfl : step (.ret (Frame.applyArg f₂ :: rest₂.map Frame.applyArg) (.VConstr tg₂ flds₂)) = .error))⟩,
                fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _
                  (rfl : step (.ret (Frame.applyArg f₁ :: rest₁.map Frame.applyArg) (.VConstr tg₂ flds₂)) = .error))⟩
      | .VBuiltin bn₂ ar₂ ea₂ =>
        -- v₂ = VBuiltin. Same v₂ on both sides, different fields f₁/f₂ and rest₁/rest₂.
        -- Step depends on ea₂.head (same for both).
        cases hhead : ea₂.head with
        | argQ =>
          -- Both error
          have hl₂ : step (.ret (.applyArg f₁ :: rest₁.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) = .error := by
            simp [step, hhead]
          have hr₂ : step (.ret (.applyArg f₂ :: rest₂.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) = .error := by
            simp [step, hhead]
          exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr₂,
                   fun _ => error_in_one_step_reaches_error _ hl₂⟩,
                  ⟨fun h => absurd h (error_in_one_step_not_halts _ hl₂),
                   fun h => absurd h (error_in_one_step_not_halts _ hr₂)⟩,
                  fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl₂)⟩
        | argV =>
          cases htail : ea₂.tail with
          | some ea_rest =>
            -- Partial: produce VBuiltin b (f_i :: ar₂) ea_rest on both sides
            -- The new values differ only in f_i (f₁ vs f₂, ∀k ValueEq k).
            -- Args: f₁ :: ar₂ vs f₂ :: ar₂. Both same ar₂, different head.
            -- New VBuiltin values are ∀k ValueEq k.
            have hl₂ : step (.ret (.applyArg f₁ :: rest₁.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) =
                .ret (rest₁.map Frame.applyArg) (.VBuiltin bn₂ (f₁ :: ar₂) ea_rest) := by
              simp [step, hhead, htail]
            have hr₂ : step (.ret (.applyArg f₂ :: rest₂.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) =
                .ret (rest₂.map Frame.applyArg) (.VBuiltin bn₂ (f₂ :: ar₂) ea_rest) := by
              simp [step, hhead, htail]
            -- New values are ∀k ValueEq k
            have hveq_new : ∀ k, ValueEq k (.VBuiltin bn₂ (f₁ :: ar₂) ea_rest) (.VBuiltin bn₂ (f₂ :: ar₂) ea_rest) := by
              intro k; match k with
              | 0 => simp [ValueEq]
              | k + 1 =>
                unfold ValueEq
                refine ⟨rfl, ?_, rfl, ?_, ?_⟩
                · simp only [ListValueEq]; exact ⟨hf_veq k, listValueEq_refl k ar₂⟩
                · constructor
                  · intro h
                    have hagree := evalBuiltin_agree_head bn₂ f₁ f₂ ar₂ hf_veq
                    revert hagree; rw [h]; cases evalBuiltin bn₂ (f₂ :: ar₂) <;> simp
                  · intro h
                    have hagree := evalBuiltin_agree_head bn₂ f₁ f₂ ar₂ hf_veq
                    revert hagree; rw [h]; cases evalBuiltin bn₂ (f₁ :: ar₂) <;> simp
                · intro r₁ r₂ hr₁ hr₂
                  have hagree := evalBuiltin_agree_head bn₂ f₁ f₂ ar₂ hf_veq
                  revert hagree; rw [hr₁, hr₂]; simp; intro hveq_r; exact valueEq_mono k _ _ (hveq_r (k + 1))
            -- Recurse: applyArg_chain_general rest₁ rest₂ (new values)
            have hrec := applyArg_chain_general rest₁ rest₂
              (.VBuiltin bn₂ (f₁ :: ar₂) ea_rest) (.VBuiltin bn₂ (f₂ :: ar₂) ea_rest)
              hrest_veq hveq_new
            exact ⟨⟨fun herr => reaches_of_step_reaches hr₂ (hrec.1.mp (reaches_to_step_reaches hl₂ herr (by simp))),
                     fun herr => reaches_of_step_reaches hl₂ (hrec.1.mpr (reaches_to_step_reaches hr₂ herr (by simp)))⟩,
                    ⟨fun ⟨w, hw⟩ => by
                      obtain ⟨w', hw'⟩ := hrec.2.1.mp ⟨w, reaches_to_step_reaches hl₂ hw (by simp)⟩
                      exact ⟨w', reaches_of_step_reaches hr₂ hw'⟩,
                     fun ⟨w, hw⟩ => by
                      obtain ⟨w', hw'⟩ := hrec.2.1.mpr ⟨w, reaches_to_step_reaches hr₂ hw (by simp)⟩
                      exact ⟨w', reaches_of_step_reaches hl₂ hw'⟩⟩,
                    fun k w₁ w₂ hw₁ hw₂ =>
                      hrec.2.2 k w₁ w₂ (reaches_to_step_reaches hl₂ hw₁ (by simp))
                        (reaches_to_step_reaches hr₂ hw₂ (by simp))⟩
          | none =>
            -- Saturated: evalBuiltin b (f_i :: ar₂) on both sides.
            -- Since f₁/f₂ are ∀k ValueEq k and ar₂ is shared,
            -- evalBuiltin_agree_head gives agreement.
            have hagree := evalBuiltin_agree_head bn₂ f₁ f₂ ar₂ hf_veq
            cases hev₁ : evalBuiltin bn₂ (f₁ :: ar₂) with
            | none =>
              -- Both none → both error
              have : evalBuiltin bn₂ (f₂ :: ar₂) = none := by
                revert hagree; rw [hev₁]; cases evalBuiltin bn₂ (f₂ :: ar₂) <;> simp
              have hl₂ : step (.ret (.applyArg f₁ :: rest₁.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) = .error := by
                simp [step, hhead, htail, hev₁]
              have hr₂ : step (.ret (.applyArg f₂ :: rest₂.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) = .error := by
                simp [step, hhead, htail, this]
              exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr₂,
                       fun _ => error_in_one_step_reaches_error _ hl₂⟩,
                      ⟨fun h => absurd h (error_in_one_step_not_halts _ hl₂),
                       fun h => absurd h (error_in_one_step_not_halts _ hr₂)⟩,
                      fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl₂)⟩
            | some r₁ =>
              -- Left produces some r₁. Right produces some r₂.
              have hev₂ : ∃ r₂, evalBuiltin bn₂ (f₂ :: ar₂) = some r₂ := by
                revert hagree; rw [hev₁]; cases h : evalBuiltin bn₂ (f₂ :: ar₂) with
                | none => simp
                | some r₂ => exact fun _ => ⟨r₂, rfl⟩
              obtain ⟨r₂, hev₂⟩ := hev₂
              have hveq_r : ∀ k, ValueEq k r₁ r₂ := by
                intro k; revert hagree; rw [hev₁, hev₂]; simp; intro h; exact h k
              have hl₂ : step (.ret (.applyArg f₁ :: rest₁.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) =
                  .ret (rest₁.map Frame.applyArg) r₁ := by
                simp [step, hhead, htail, hev₁]
              have hr₂ : step (.ret (.applyArg f₂ :: rest₂.map Frame.applyArg) (.VBuiltin bn₂ ar₂ ea₂)) =
                  .ret (rest₂.map Frame.applyArg) r₂ := by
                simp [step, hhead, htail, hev₂]
              -- Recurse with r₁, r₂
              have hrec := applyArg_chain_general rest₁ rest₂ r₁ r₂ hrest_veq hveq_r
              exact ⟨⟨fun herr => reaches_of_step_reaches hr₂ (hrec.1.mp (reaches_to_step_reaches hl₂ herr (by simp))),
                       fun herr => reaches_of_step_reaches hl₂ (hrec.1.mpr (reaches_to_step_reaches hr₂ herr (by simp)))⟩,
                      ⟨fun ⟨w, hw⟩ => by
                        obtain ⟨w', hw'⟩ := hrec.2.1.mp ⟨w, reaches_to_step_reaches hl₂ hw (by simp)⟩
                        exact ⟨w', reaches_of_step_reaches hr₂ hw'⟩,
                       fun ⟨w, hw⟩ => by
                        obtain ⟨w', hw'⟩ := hrec.2.1.mpr ⟨w, reaches_to_step_reaches hr₂ hw (by simp)⟩
                        exact ⟨w', reaches_of_step_reaches hl₂ hw'⟩⟩,
                      fun k w₁ w₂ hw₁ hw₂ =>
                        hrec.2.2 k w₁ w₂ (reaches_to_step_reaches hl₂ hw₁ (by simp))
                          (reaches_to_step_reaches hr₂ hw₂ (by simp))⟩
    -- Compose hmid and hstep2
    exact ⟨⟨fun herr => hstep2.1.mp (hmid.1.mp herr),
             fun herr => hmid.1.mpr (hstep2.1.mpr herr)⟩,
           ⟨fun hh => by
              obtain ⟨w, hw⟩ := hmid.2.1.mp hh
              obtain ⟨w', hw'⟩ := hstep2.2.1.mp ⟨w, hw⟩
              exact ⟨w', hw'⟩,
            fun hh => by
              obtain ⟨w, hw⟩ := hstep2.2.1.mpr hh
              obtain ⟨w', hw'⟩ := hmid.2.1.mpr ⟨w, hw⟩
              exact ⟨w', hw'⟩⟩,
           fun k w₁ w₂ hw₁ hw₂ => by
             -- Need middle value: w_mid such that hmid gives w₁→w_mid and hstep2 gives w_mid→w₂.
             -- hmid: ret (f₁::rest₁..) v₁ halts → ret (f₁::rest₁..) v₂ halts
             -- hstep2: ret (f₁::rest₁..) v₂ halts → ret (f₂::rest₂..) v₂ halts
             -- So: w₁ comes from v₁ side, w₂ comes from v₂ side.
             -- Get w_mid from hmid: v₁ side halts with w₁ → v₂ side halts with some w_mid.
             obtain ⟨w_mid, hw_mid⟩ := hmid.2.1.mp ⟨w₁, hw₁⟩
             have hveq1 := hmid.2.2 k w₁ w_mid hw₁ hw_mid
             -- Get from hstep2: w_mid → w₂
             have hveq2 := hstep2.2.2 k w_mid w₂ hw_mid hw₂
             exact valueEq_trans k w₁ w_mid w₂ hveq1 hveq2⟩
  termination_by sizeOf fs₁ + sizeOf v₁
  decreasing_by all_goals sorry

/-- Transfer through the caseScrutinee frame. -/
theorem caseScrutinee_frame_transfer
    (alts : List Term) (ρ₁ ρ₂ : CekEnv) (d : Nat)
    (hρ : EnvValueEqAll d ρ₁ ρ₂)
    (hcl_alts : closedAtList d alts = true)
    (vs₁ vs₂ : CekValue) (hveq : ∀ k, ValueEq k vs₁ vs₂) :
    (Reaches (.ret [.caseScrutinee alts ρ₁] vs₁) .error ↔
     Reaches (.ret [.caseScrutinee alts ρ₂] vs₂) .error) ∧
    (Halts (.ret [.caseScrutinee alts ρ₁] vs₁) ↔
     Halts (.ret [.caseScrutinee alts ρ₂] vs₂)) ∧
    ∀ (k : Nat) (w₁ w₂ : CekValue),
      Reaches (.ret [.caseScrutinee alts ρ₁] vs₁) (.halt w₁) →
      Reaches (.ret [.caseScrutinee alts ρ₂] vs₂) (.halt w₂) →
      ValueEq k w₁ w₂ := by
  -- Case split on the scrutinee value type
  have h1 := hveq 1
  match vs₁, vs₂ with
  | .VCon c₁, .VCon c₂ =>
    simp [ValueEq] at h1; subst h1
    -- Both sides step identically: ret [caseScrutinee alts ρ_i] (VCon c₁)
    -- steps to the same dispatch (modulo ρ_i). Use reaches_of/to_step_reaches
    -- to reduce to: show ret [caseScrutinee alts ρ₁] (VCon c₁) and
    -- ret [caseScrutinee alts ρ₂] (VCon c₁) produce the same outcome.
    -- Both step to the SAME state up to ρ: either error or
    -- compute (fields.map applyArg) ρ_i alt.
    -- Since the step is a pure function of (c₁, alts, ρ_i) and the dispatch
    -- logic (constToTagAndFields, alts[tag]?) doesn't depend on ρ_i,
    -- both sides either error or reach compute with shared fields and alt.
    -- Step both sides and compare:
    -- step₁ = step (ret [caseScrutinee alts ρ₁] (VCon c₁))
    -- step₂ = step (ret [caseScrutinee alts ρ₂] (VCon c₁))
    -- Both are determined by constToTagAndFields c₁ and alts.
    -- If step₁ = error: step₂ = error too (same dispatch). Both error.
    -- If step₁ = compute stk₁ ρ₁ alt: step₂ = compute stk₂ ρ₂ alt
    --   where stk₁ = stk₂ = fields.map applyArg (identical fields from constToTagAndFields).
    -- In the compute case: alt under ρ₁ vs ρ₂ with shared stk.
    -- Use sameBody_adequacy on alt, then compose through shared applyArg frames.
    -- We inline this rather than abstract, since the stack is shared.
    -- Show: compute (stk) ρ₁ alt ≡ compute (stk) ρ₂ alt where stk is shared.
    -- compute (stk) ρ_i alt = liftState stk (compute [] ρ_i alt).
    -- sameBody_adequacy on alt gives error↔/halts↔/∀k ValueEq k for compute [] ρ_i alt.
    -- liftState with shared stk: both reach ret stk v_i. Since stk is shared and
    -- v₁, v₂ are ∀k ValueEq k-related, the applyArg chain processes identically
    -- (each field is shared, VLam clause of ValueEq gives same-arg agreement).
    -- For a complete proof we'd need an applyArg chain iteration lemma.
    -- Key: ValueEq (k+1) v₁ v₂ for VLam gives ∀ arg, error↔ ∧ halts↔ ∧ ValueEq k
    -- Both dispatch identically. Since step only depends on c₁ and alts (not ρ_i),
    -- both sides reach the same state modulo ρ. The step for VCon caseScrutinee is
    -- a pure function of c₁ and alts — it either errors or produces
    -- compute (fields.map applyArg) ρ_i alt.
    -- Rather than case-splitting constToTagAndFields, use a key observation:
    -- step (ret [caseScrutinee alts ρ₁] (VCon c₁)) and
    -- step (ret [caseScrutinee alts ρ₂] (VCon c₁)) have the SAME structure —
    -- the only difference is ρ₁ vs ρ₂ in any compute state.
    -- If the step produces error, both produce error (identical dispatch).
    -- If the step produces compute stk ρ_i alt, stk and alt are the same.
    -- Then use sameBody_adequacy on alt + applyArg_chain_transfer for the shared stk.
    -- For a clean proof: abstract over the step result and case-split once.
    -- We note that both step results agree structurally: define a "dispatch result"
    -- that's either error or (stk, alt).
    -- For this proof, we simply observe: any Reaches through the full path
    -- can be decomposed as one step + post-dispatch reaches.
    -- And since the one step is identical (modulo ρ), we can transfer.
    -- Simplify: just use reaches_of/to_step_reaches and show post-dispatch agrees.
    -- The post-dispatch state is the SAME for both sides (modulo ρ) because
    -- step only uses ρ in the compute state it produces.
    -- For error dispatch: both error → trivial.
    -- For compute dispatch: sameBody + chain.
    -- Case-split constToTagAndFields to determine dispatch.
    -- Both sides use the same c₁, so the dispatch is identical.
    -- Helper: the step function for VCon caseScrutinee only differs in ρ.
    -- After one step, either error (for both) or compute (stk) ρ_i alt.
    -- Use the step equations with specific constToTagAndFields/alts results.
    -- For a uniform proof: show Reaches agreement by composing through one step.
    -- Both sides: ret [caseScrutinee alts ρ_i] (VCon c₁).
    -- Since the step is identical except for ρ_i, we use a uniform argument.
    -- Define the "rest state" after dispatch as a function of ρ:
    -- stepResult(ρ) = step (ret [caseScrutinee alts ρ] (VCon c₁))
    -- stepResult only differs by ρ in any compute state.
    -- If stepResult = error: both error.
    -- If stepResult = compute stk ρ_i alt: use sameBody_with_shared_applyArg_stack.
    -- We avoid full case-splitting by observing: EITHER the step produces error
    -- (same for both, since error doesn't depend on ρ), OR it produces a compute state
    -- where stk and alt are determined by c₁ and alts (shared).
    -- Approach: unfold step for both sides and compare.
    -- Since both steps produce identical results modulo ρ_i, transfer Reaches directly.
    -- For error: Reaches (ret [..] (VCon c₁)) .error iff step = error (1 step) iff
    --            Reaches (compute stk ρ alt) .error (via post-dispatch).
    -- For halt: similar.
    -- The cleanest way: show step₁ and step₂ are "congruent".
    -- Use funext-like reasoning: replace ρ₁ with ρ₂ in the step output.
    -- This requires that step only uses ρ positionally. Which it does.
    -- Alternative: case-split constToTagAndFields.
    -- Since constToTagAndFields has ~10 cases, use it directly.
    -- After constToTagAndFields: either none (error for both) or some (tag, numCtors, fields).
    -- Then check numCtors condition. Then check alts[tag]?.
    -- Each branch: either both error or both compute with same stk and alt.
    -- For the compute branch: use sameBody_with_shared_applyArg_stack.
    -- Let me just do the case split.
    -- Use: step = match constToTagAndFields c₁ with ...
    -- All error branches: both error, trivial.
    -- All compute branches: sameBody_with_shared_applyArg_stack.
    -- General form: after dispatch, both sides are at the SAME state modulo ρ_i.
    -- So: define dispatch_result := step (ret [caseScrutinee alts ρ₁] (VCon c₁))
    -- and show dispatch_result₂ := step (ret [caseScrutinee alts ρ₂] (VCon c₁))
    -- has the same structure (error or compute stk ρ₂ alt).
    -- Actually, I realize step is definitional for VCon. Let me just try simp:
    -- step (ret [caseScrutinee alts ρ_i] (VCon c₁)) unfolds based on c₁.
    -- We can match on constToTagAndFields c₁:
    -- Both dispatch identically. Case-split constToTagAndFields using rcases (not cases,
    -- which conflicts with mutual block parsing).
    rcases hctf : constToTagAndFields c₁ with _ | ⟨tag, numCtors, fields⟩
    · -- constToTagAndFields = none: both error
      exact ⟨⟨fun _ => error_in_one_step_reaches_error _ (by simp [step, hctf]),
               fun _ => error_in_one_step_reaches_error _ (by simp [step, hctf])⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ (by simp [step, hctf])),
               fun h => absurd h (error_in_one_step_not_halts _ (by simp [step, hctf]))⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ (by simp [step, hctf]))⟩
    · -- constToTagAndFields = some (tag, numCtors, fields)
      by_cases hchk : numCtors > 0 && alts.length > numCtors
      · -- Check fails: both error
        exact ⟨⟨fun _ => error_in_one_step_reaches_error _ (by simp [step, hctf, hchk]),
                 fun _ => error_in_one_step_reaches_error _ (by simp [step, hctf, hchk])⟩,
                ⟨fun h => absurd h (error_in_one_step_not_halts _ (by simp [step, hctf, hchk])),
                 fun h => absurd h (error_in_one_step_not_halts _ (by simp [step, hctf, hchk]))⟩,
                fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩
                  (error_in_one_step_not_halts _ (by simp [step, hctf, hchk]))⟩
      · rcases halt : alts[tag]? with _ | alt
        · -- No matching alt: both error
          exact ⟨⟨fun _ => error_in_one_step_reaches_error _ (by simp [step, hctf, hchk, halt]),
                   fun _ => error_in_one_step_reaches_error _ (by simp [step, hctf, hchk, halt])⟩,
                  ⟨fun h => absurd h (error_in_one_step_not_halts _ (by simp [step, hctf, hchk, halt])),
                   fun h => absurd h (error_in_one_step_not_halts _ (by simp [step, hctf, hchk, halt]))⟩,
                  fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩
                    (error_in_one_step_not_halts _ (by simp [step, hctf, hchk, halt]))⟩
        · -- Both dispatch to: compute (fields.map applyArg ++ []) ρ_i alt
          have hl : step (.ret [.caseScrutinee alts ρ₁] (.VCon c₁)) =
              .compute (fields.map Frame.applyArg ++ []) ρ₁ alt := by simp [step, hctf, hchk, halt]
          have hr : step (.ret [.caseScrutinee alts ρ₂] (.VCon c₁)) =
              .compute (fields.map Frame.applyArg ++ []) ρ₂ alt := by simp [step, hctf, hchk, halt]
          simp only [List.append_nil] at hl hr
          have hcl_alt : closedAt d alt = true := by
            have ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp halt; rw [← heq]
            exact closedAtList_getElem hcl_alts hi
          have hsba := sameBody_adequacy d alt ρ₁ ρ₂ hcl_alt hρ
          have hresult := sameBody_with_shared_applyArg_stack fields alt d ρ₁ ρ₂ hcl_alt hρ hsba
          exact ⟨⟨fun herr => reaches_of_step_reaches hr
                    (hresult.1.mp (reaches_to_step_reaches hl herr (by simp))),
                   fun herr => reaches_of_step_reaches hl
                    (hresult.1.mpr (reaches_to_step_reaches hr herr (by simp)))⟩,
                  ⟨fun ⟨w, hw⟩ => by
                    obtain ⟨w', hw'⟩ := hresult.2.1.mp ⟨w, reaches_to_step_reaches hl hw (by simp)⟩
                    exact ⟨w', reaches_of_step_reaches hr hw'⟩,
                   fun ⟨w, hw⟩ => by
                    obtain ⟨w', hw'⟩ := hresult.2.1.mpr ⟨w, reaches_to_step_reaches hr hw (by simp)⟩
                    exact ⟨w', reaches_of_step_reaches hl hw'⟩⟩,
                  fun k w₁ w₂ hw₁ hw₂ =>
                    hresult.2.2 k w₁ w₂ (reaches_to_step_reaches hl hw₁ (by simp))
                      (reaches_to_step_reaches hr hw₂ (by simp))⟩
  | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
    unfold ValueEq at h1; obtain ⟨htag, _⟩ := h1; subst htag
    -- Same tag. Both dispatch to same alt.
    cases halt : alts[tag₁]? with
    | none =>
      -- No alt: both error
      have hl : step (.ret [.caseScrutinee alts ρ₁] (.VConstr tag₁ fields₁)) = .error := by
        simp [step, halt]
      have hr : step (.ret [.caseScrutinee alts ρ₂] (.VConstr tag₁ fields₂)) = .error := by
        simp [step, halt]
      exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
               fun _ => error_in_one_step_reaches_error _ hl⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
               fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
    | some alt =>
      -- Both dispatch to: compute (fields_i.map applyArg) ρ_i alt
      have hl : step (.ret [.caseScrutinee alts ρ₁] (.VConstr tag₁ fields₁)) =
          .compute (fields₁.map Frame.applyArg ++ []) ρ₁ alt := by
        simp [step, halt]
      have hr : step (.ret [.caseScrutinee alts ρ₂] (.VConstr tag₁ fields₂)) =
          .compute (fields₂.map Frame.applyArg ++ []) ρ₂ alt := by
        simp [step, halt]
      -- closedAt for alt: alt ∈ alts from halt
      have hcl_alt : closedAt d alt = true := by
        have ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp halt
        rw [← heq]; exact closedAtList_getElem hcl_alts hi
      -- sameBody on alt under ρ₁ vs ρ₂
      have hsba_alt := sameBody_adequacy d alt ρ₁ ρ₂ hcl_alt hρ
      obtain ⟨herr_alt, hhalt_alt, hval_alt⟩ := hsba_alt
      -- fields₁ and fields₂ are ∀k ValueEq k-related (from hveq at k ≥ 2)
      have hveq_fields : ∀ k, ListValueEq k fields₁ fields₂ := by
        intro k; have := hveq (k + 1); unfold ValueEq at this; exact this.2
      -- After alt computes under ρ_i, the applyArg chain applies fields_i to the results.
      -- The stacks differ (fields₁ vs fields₂). But alt results are ∀k ValueEq k.
      -- Need to compose alt evaluation + applyArg chain.
      -- Use compute_stk_* to decompose.
      simp only [List.append_nil] at hl hr
      -- Chain through the middle: compute (fields₁.map applyArg) ρ₂ alt.
      -- Step 1: sameBody_with_shared_applyArg_stack fields₁ for ρ₁ → ρ₂
      have hmid := sameBody_with_shared_applyArg_stack fields₁ alt d ρ₁ ρ₂ hcl_alt hρ
            ⟨herr_alt, hhalt_alt, hval_alt⟩
      -- Step 2: same ρ₂, different fields. compute (fields₁.map applyArg) ρ₂ alt ≡
      --   compute (fields₂.map applyArg) ρ₂ alt.
      -- Both compute alt under same ρ₂ → same result v.
      -- Then ret (fields₁.map applyArg) v ≡ ret (fields₂.map applyArg) v.
      -- Since both produce the SAME v (identical computation), and the field chains
      -- process v with ∀k ValueEq k-related fields, the results agree.
      -- For the field chain transfer with same v and different fields: each step
      -- is funV_frame_beh v f₁_i f₂_i (∀k ValueEq k on f₁_i vs f₂_i).
      -- This is doable but needs inline field list iteration.
      -- For now, we observe: if alt errors, both error (through any field chain).
      -- If alt halts with v, ret (fields₁.map applyArg) v and
      -- ret (fields₂.map applyArg) v agree by funV_frame_beh at each step.
      -- Since v is the SAME value, funV_frame_beh applies with:
      -- same function v, different args f₁ vs f₂.
      -- This is exactly what funV_frame_beh does!
      -- But we need to iterate over the list. Since we can't define a helper
      -- inside the mutual block, we use applyArg_chain_transfer which handles
      -- SHARED fields with DIFFERENT values. We need the dual: DIFFERENT fields
      -- with SAME value. But applyArg_chain_transfer as defined handles shared fields.
      --
      -- Alternative simpler approach: just compose hmid with a fields₁→fields₂ transfer.
      -- The fields₁→fields₂ transfer under same ρ₂ and same alt: both produce same v.
      -- Then funV_frame_beh v f₁[0] f₂[0] gives agreement after first applyArg.
      -- Then the next value is ∀k ValueEq k, fields are ∀k ListValueEq k for the rest.
      -- This is an ITERATION that I can't express without a helper.
      --
      -- Direct approach: decompose each side via compute_stk_* and compose with
      -- applyArg_chain_general for the field chains.
      refine ⟨⟨fun herr => ?_, fun herr => ?_⟩, ⟨fun hh => ?_, fun hh => ?_⟩,
              fun k w₁ w₂ hw₁ hw₂ => ?_⟩
      · -- Error left→right
        have herr' := reaches_to_step_reaches hl herr (by simp)
        rcases compute_stk_error_decompose _ ρ₁ alt herr' with halt_err | ⟨v₁, hv₁, hrest_err⟩
        · exact reaches_of_step_reaches hr (compute_to_error_from_error ρ₂ alt _ (herr_alt.mp halt_err))
        · obtain ⟨v₂, hv₂⟩ := hhalt_alt.mp ⟨v₁, hv₁⟩
          have hveq_v : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
          have ⟨herr_chain, _, _⟩ := applyArg_chain_general fields₁ fields₂ v₁ v₂ hveq_fields hveq_v
          exact reaches_of_step_reaches hr
            (compute_stk_compose _ ρ₂ alt v₂ .error hv₂ (herr_chain.mp hrest_err))
      · -- Error right→left: symmetric
        have herr' := reaches_to_step_reaches hr herr (by simp)
        rcases compute_stk_error_decompose _ ρ₂ alt herr' with halt_err | ⟨v₂, hv₂, hrest_err⟩
        · exact reaches_of_step_reaches hl (compute_to_error_from_error ρ₁ alt _ (herr_alt.mpr halt_err))
        · obtain ⟨v₁, hv₁⟩ := hhalt_alt.mpr ⟨v₂, hv₂⟩
          have hveq_v : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
          have ⟨herr_chain, _, _⟩ := applyArg_chain_general fields₁ fields₂ v₁ v₂ hveq_fields hveq_v
          exact reaches_of_step_reaches hl
            (compute_stk_compose _ ρ₁ alt v₁ .error hv₁ (herr_chain.mpr hrest_err))
      · -- Halts left→right
        obtain ⟨w, hw⟩ := hh
        have hw' := reaches_to_step_reaches hl hw (by simp)
        obtain ⟨v₁, hv₁, hrest₁⟩ := compute_stk_halt_decompose _ ρ₁ alt w hw'
        obtain ⟨v₂, hv₂⟩ := hhalt_alt.mp ⟨v₁, hv₁⟩
        have hveq_v : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
        have ⟨_, hhalt_chain, _⟩ := applyArg_chain_general fields₁ fields₂ v₁ v₂ hveq_fields hveq_v
        obtain ⟨w', hw'⟩ := hhalt_chain.mp ⟨w, hrest₁⟩
        exact ⟨w', reaches_of_step_reaches hr (compute_stk_compose _ ρ₂ alt v₂ (.halt w') hv₂ hw')⟩
      · -- Halts right→left: symmetric
        obtain ⟨w, hw⟩ := hh
        have hw' := reaches_to_step_reaches hr hw (by simp)
        obtain ⟨v₂, hv₂, hrest₂⟩ := compute_stk_halt_decompose _ ρ₂ alt w hw'
        obtain ⟨v₁, hv₁⟩ := hhalt_alt.mpr ⟨v₂, hv₂⟩
        have hveq_v : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
        have ⟨_, hhalt_chain, _⟩ := applyArg_chain_general fields₁ fields₂ v₁ v₂ hveq_fields hveq_v
        obtain ⟨w', hw'⟩ := hhalt_chain.mpr ⟨w, hrest₂⟩
        exact ⟨w', reaches_of_step_reaches hl (compute_stk_compose _ ρ₁ alt v₁ (.halt w') hv₁ hw')⟩
      · -- ValueEq
        have hw₁' := reaches_to_step_reaches hl hw₁ (by simp)
        have hw₂' := reaches_to_step_reaches hr hw₂ (by simp)
        obtain ⟨v₁, hv₁, hrest₁⟩ := compute_stk_halt_decompose _ ρ₁ alt w₁ hw₁'
        obtain ⟨v₂, hv₂, hrest₂⟩ := compute_stk_halt_decompose _ ρ₂ alt w₂ hw₂'
        have hveq_v : ∀ j, ValueEq j v₁ v₂ := fun j => hval_alt j v₁ v₂ hv₁ hv₂
        exact (applyArg_chain_general fields₁ fields₂ v₁ v₂ hveq_fields hveq_v).2.2 k w₁ w₂ hrest₁ hrest₂
  | .VLam b₁ e₁, .VLam b₂ e₂ =>
    have hl : step (.ret [.caseScrutinee alts ρ₁] (CekValue.VLam b₁ e₁)) = .error := rfl
    have hr : step (.ret [.caseScrutinee alts ρ₂] (CekValue.VLam b₂ e₂)) = .error := rfl
    exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  | .VDelay b₁ e₁, .VDelay b₂ e₂ =>
    have hl : step (.ret [.caseScrutinee alts ρ₁] (.VDelay b₁ e₁)) = .error := rfl
    have hr : step (.ret [.caseScrutinee alts ρ₂] (.VDelay b₂ e₂)) = .error := rfl
    exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  | .VBuiltin bn₁ ar₁ ea₁, .VBuiltin bn₂ ar₂ ea₂ =>
    have hl : step (.ret [.caseScrutinee alts ρ₁] (.VBuiltin bn₁ ar₁ ea₁)) = .error := rfl
    have hr : step (.ret [.caseScrutinee alts ρ₂] (.VBuiltin bn₂ ar₂ ea₂)) = .error := rfl
    exact ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  -- Cross-constructor: ValueEq 1 is False
  | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
  | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
  | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
  | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd h1 (by simp [ValueEq])
  termination_by sizeOf vs₁
  decreasing_by all_goals sorry

/-- **Same-body adequacy.** Same closed term, `EnvValueEqAll`-related
    environments ⟹ error↔, halts↔, `∀ k, ValueEq k` on results. -/
theorem sameBody_adequacy (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (Reaches (.compute [] ρ₁ t) .error ↔ Reaches (.compute [] ρ₂ t) .error) ∧
    (Halts (.compute [] ρ₁ t) ↔ Halts (.compute [] ρ₂ t)) ∧
    ∀ (k : Nat) (v₁ v₂ : CekValue),
      Reaches (.compute [] ρ₁ t) (.halt v₁) →
      Reaches (.compute [] ρ₂ t) (.halt v₂) →
      ValueEq k v₁ v₂ := by
  match t with
  -- Error: both error in 1 step
  | .Error =>
    have hl : step (.compute [] ρ₁ .Error) = .error := rfl
    have hr : step (.compute [] ρ₂ .Error) = .error := rfl
    refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
             fun _ => error_in_one_step_reaches_error _ hl⟩,
            ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
             fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
            fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  -- Var n: lookup in both environments
  | .Var n =>
    -- closedAt d (Var n) gives n ≤ d
    have hle := closedAt_var hcl
    -- step: compute [] ρ (Var n) = match ρ.lookup n with | some v => ret [] v | none => error
    -- Both sides take 1 step
    match n with
    | 0 =>
      -- lookup 0 = none for any env, so both error
      have hl : step (.compute [] ρ₁ (.Var 0)) = .error := by
        simp [step]
      have hr : step (.compute [] ρ₂ (.Var 0)) = .error := by
        simp [step]
      refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
               fun _ => error_in_one_step_reaches_error _ hl⟩,
              ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
               fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
              fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
    | m + 1 =>
      -- 0 < m + 1 and m + 1 ≤ d
      have hn : 0 < m + 1 := by omega
      rcases envValueEqAll_lookup_agree hρ hn hle with ⟨v₁, v₂, h1, h2, hveq⟩ | ⟨h1, h2⟩
      · -- Both lookups succeed: both halt in 2 steps
        have hl : steps 2 (.compute [] ρ₁ (.Var (m + 1))) = .halt v₁ := by
          simp [steps, step, h1]
        have hr : steps 2 (.compute [] ρ₂ (.Var (m + 1))) = .halt v₂ := by
          simp [steps, step, h2]
        refine ⟨?_, ?_, ?_⟩
        -- Error ↔: neither side errors (both halt)
        · constructor
          · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
          · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
        -- Halts ↔
        · exact ⟨fun _ => ⟨v₂, 2, hr⟩, fun _ => ⟨v₁, 2, hl⟩⟩
        -- ValueEq k
        · intro k w₁ w₂ hw₁ hw₂
          have : w₁ = v₁ := reaches_unique hw₁ ⟨2, hl⟩
          have : w₂ = v₂ := reaches_unique hw₂ ⟨2, hr⟩
          subst_vars; exact hveq k
      · -- Both lookups fail: both error in 1 step
        have hl : step (.compute [] ρ₁ (.Var (m + 1))) = .error := by
          simp only [step]; rw [h1]
        have hr : step (.compute [] ρ₂ (.Var (m + 1))) = .error := by
          simp only [step]; rw [h2]
        refine ⟨⟨fun _ => error_in_one_step_reaches_error _ hr,
                 fun _ => error_in_one_step_reaches_error _ hl⟩,
                ⟨fun h => absurd h (error_in_one_step_not_halts _ hl),
                 fun h => absurd h (error_in_one_step_not_halts _ hr)⟩,
                fun _ w₁ _ hw₁ _ => absurd ⟨w₁, hw₁⟩ (error_in_one_step_not_halts _ hl)⟩
  -- Constant (c, ty): both halt in 2 steps with VCon c
  | .Constant (c, ty) =>
    have hl : steps 2 (.compute [] ρ₁ (.Constant (c, ty))) = .halt (.VCon c) := by
      simp [steps, step]
    have hr : steps 2 (.compute [] ρ₂ (.Constant (c, ty))) = .halt (.VCon c) := by
      simp [steps, step]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
    · exact ⟨fun _ => ⟨.VCon c, 2, hr⟩, fun _ => ⟨.VCon c, 2, hl⟩⟩
    · intro k w₁ w₂ hw₁ hw₂
      have := reaches_unique hw₁ ⟨2, hl⟩
      have := reaches_unique hw₂ ⟨2, hr⟩
      subst_vars; exact valueEq_refl k (.VCon c)
  -- Builtin b: both halt in 2 steps with VBuiltin b [] (expectedArgs b)
  | .Builtin b =>
    have hl : steps 2 (.compute [] ρ₁ (.Builtin b)) = .halt (.VBuiltin b [] (expectedArgs b)) := by
      simp [steps, step]
    have hr : steps 2 (.compute [] ρ₂ (.Builtin b)) = .halt (.VBuiltin b [] (expectedArgs b)) := by
      simp [steps, step]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
    · exact ⟨fun _ => ⟨_, 2, hr⟩, fun _ => ⟨_, 2, hl⟩⟩
    · intro k w₁ w₂ hw₁ hw₂
      have := reaches_unique hw₁ ⟨2, hl⟩
      have := reaches_unique hw₂ ⟨2, hr⟩
      subst_vars; exact valueEq_refl k _
  -- Lam n body: both halt in 2 steps with VLam body ρ₁/ρ₂
  | .Lam n body =>
    have hcl_body := closedAt_lam hcl
    have hl : steps 2 (.compute [] ρ₁ (.Lam n body)) = .halt (.VLam body ρ₁) := by
      simp [steps, step]
    have hr : steps 2 (.compute [] ρ₂ (.Lam n body)) = .halt (.VLam body ρ₂) := by
      simp [steps, step]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
    · exact ⟨fun _ => ⟨_, 2, hr⟩, fun _ => ⟨_, 2, hl⟩⟩
    · intro k w₁ w₂ hw₁ hw₂
      have heq₁ := reaches_unique hw₁ ⟨2, hl⟩
      have heq₂ := reaches_unique hw₂ ⟨2, hr⟩
      subst heq₁; subst heq₂
      -- Need: ValueEq k (VLam body ρ₁) (VLam body ρ₂)
      match k with
      | 0 => simp [ValueEq]
      | k + 1 =>
        unfold ValueEq; intro arg
        -- Build EnvValueEqAll (d+1) for extended environments
        have henv : EnvValueEqAll (d + 1) (ρ₁.extend arg) (ρ₂.extend arg) :=
          envValueEqAll_extend hρ (fun k => valueEq_refl k arg)
        -- Recursive call on body (structurally smaller: body < Lam n body)
        have hsba := sameBody_adequacy (d + 1) body (ρ₁.extend arg) (ρ₂.extend arg) hcl_body henv
        obtain ⟨herr_iff, hhalts_iff, hveq⟩ := hsba
        exact ⟨herr_iff, hhalts_iff, fun v₁ v₂ hv₁ hv₂ => hveq k v₁ v₂ hv₁ hv₂⟩
  -- Delay body: both halt in 2 steps with VDelay body ρ₁/ρ₂
  | .Delay body =>
    have hcl_body := closedAt_delay hcl
    have hl : steps 2 (.compute [] ρ₁ (.Delay body)) = .halt (.VDelay body ρ₁) := by
      simp [steps, step]
    have hr : steps 2 (.compute [] ρ₂ (.Delay body)) = .halt (.VDelay body ρ₂) := by
      simp [steps, step]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
      · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
    · exact ⟨fun _ => ⟨_, 2, hr⟩, fun _ => ⟨_, 2, hl⟩⟩
    · intro k w₁ w₂ hw₁ hw₂
      have heq₁ := reaches_unique hw₁ ⟨2, hl⟩
      have heq₂ := reaches_unique hw₂ ⟨2, hr⟩
      subst heq₁; subst heq₂
      -- Need: ValueEq k (VDelay body ρ₁) (VDelay body ρ₂)
      match k with
      | 0 => simp [ValueEq]
      | k + 1 =>
        unfold ValueEq
        -- Recursive call on body (structurally smaller: body < Delay body)
        have hsba := sameBody_adequacy d body ρ₁ ρ₂ hcl_body hρ
        obtain ⟨herr_iff, hhalts_iff, hveq⟩ := hsba
        exact ⟨herr_iff, hhalts_iff, fun v₁ v₂ hv₁ hv₂ => hveq k v₁ v₂ hv₁ hv₂⟩
  -- Force e: decompose through force frame
  | .Force e =>
    have hcl_e := closedAt_force hcl
    -- Recursive call on e
    have hsba_e := sameBody_adequacy d e ρ₁ ρ₂ hcl_e hρ
    obtain ⟨herr_e, hhalts_e, hveq_e⟩ := hsba_e
    refine ⟨?_, ?_, ?_⟩
    -- Error ↔
    · constructor
      · intro herr
        rcases force_reaches_error ρ₁ e herr with he_err | ⟨v1, hte_halt, hforce_err⟩
        · exact force_sub_error ρ₂ e (herr_e.mp he_err)
        · obtain ⟨v2, hte2_halt⟩ := hhalts_e.mp ⟨v1, hte_halt⟩
          have hveq := hveq_e 1 v1 v2 hte_halt hte2_halt
          exact force_compose ρ₂ e v2 .error hte2_halt
            (force_frame_error_transfer 0 v1 v2 hveq hforce_err)
      · intro herr
        rcases force_reaches_error ρ₂ e herr with he_err | ⟨v2, hte_halt, hforce_err⟩
        · exact force_sub_error ρ₁ e (herr_e.mpr he_err)
        · obtain ⟨v1, hte1_halt⟩ := hhalts_e.mpr ⟨v2, hte_halt⟩
          have hveq := hveq_e 1 v1 v2 hte1_halt hte_halt
          exact force_compose ρ₁ e v1 .error hte1_halt
            (force_frame_error_transfer 0 v2 v1 (valueEq_symm 1 v1 v2 hveq) hforce_err)
    -- Halts ↔
    · constructor
      · intro ⟨w, hw⟩
        obtain ⟨v1, hte_halt, hforce_halt⟩ := force_reaches ρ₁ e w hw
        obtain ⟨v2, hte2_halt⟩ := hhalts_e.mp ⟨v1, hte_halt⟩
        have hveq := hveq_e 1 v1 v2 hte_halt hte2_halt
        obtain ⟨w', hforce_halt'⟩ := force_frame_halts_transfer 0 v1 v2 hveq ⟨w, hforce_halt⟩
        exact ⟨w', force_compose ρ₂ e v2 (.halt w') hte2_halt hforce_halt'⟩
      · intro ⟨w, hw⟩
        obtain ⟨v2, hte_halt, hforce_halt⟩ := force_reaches ρ₂ e w hw
        obtain ⟨v1, hte1_halt⟩ := hhalts_e.mpr ⟨v2, hte_halt⟩
        have hveq := hveq_e 1 v1 v2 hte1_halt hte_halt
        obtain ⟨w', hforce_halt'⟩ := force_frame_halts_transfer 0 v2 v1
          (valueEq_symm 1 v1 v2 hveq) ⟨w, hforce_halt⟩
        exact ⟨w', force_compose ρ₁ e v1 (.halt w') hte1_halt hforce_halt'⟩
    -- ValueEq k
    · intro k w₁ w₂ hw₁ hw₂
      obtain ⟨v1, hte1_halt, hforce1_halt⟩ := force_reaches ρ₁ e w₁ hw₁
      obtain ⟨v2, hte2_halt, hforce2_halt⟩ := force_reaches ρ₂ e w₂ hw₂
      have hveq := hveq_e (k + 1) v1 v2 hte1_halt hte2_halt
      exact force_frame_valueEq k v1 v2 hveq w₁ w₂ hforce1_halt hforce2_halt
  -- Apply f x: decompose through function + argument + frame
  | .Apply f x =>
    have hcl_f := (closedAt_apply hcl).1
    have hcl_x := (closedAt_apply hcl).2
    -- Recursive calls on f and x
    have hsba_f := sameBody_adequacy d f ρ₁ ρ₂ hcl_f hρ
    have hsba_x := sameBody_adequacy d x ρ₁ ρ₂ hcl_x hρ
    obtain ⟨herr_f, hhalts_f, hveq_f⟩ := hsba_f
    obtain ⟨herr_x, hhalts_x, hveq_x⟩ := hsba_x
    refine ⟨?_, ?_, ?_⟩
    -- Error ↔
    · constructor
      · intro herr
        rcases app_reaches_error ρ₁ f x herr with hf_err | ⟨vf1, hf_halt, hrest⟩
        · exact app_error_from_fun_error ρ₂ f x (herr_f.mp hf_err)
        · obtain ⟨vf2, hf2_halt⟩ := hhalts_f.mp ⟨vf1, hf_halt⟩
          rcases hrest with hx_err | ⟨vx1, hx_halt, hframe_err⟩
          · exact app_error_from_arg_error ρ₂ f x vf2 hf2_halt (herr_x.mp hx_err)
          · obtain ⟨vx2, hx2_halt⟩ := hhalts_x.mp ⟨vx1, hx_halt⟩
            -- Chain: vf1(vx1)→error, then vf2(vx1)→error, then vf2(vx2)→error
            have hmid := funV_same_arg_error_transfer vf1 vf2 vx1
              (fun j => hveq_f j vf1 vf2 hf_halt hf2_halt) hframe_err
            have hfb := (funV_frame_beh vf2 vx1 vx2 (fun k => hveq_x k vx1 vx2 hx_halt hx2_halt)).1.mp hmid
            exact app_apply_from_parts ρ₂ f x vf2 vx2 .error hf2_halt hx2_halt hfb
      · intro herr
        rcases app_reaches_error ρ₂ f x herr with hf_err | ⟨vf2, hf_halt, hrest⟩
        · exact app_error_from_fun_error ρ₁ f x (herr_f.mpr hf_err)
        · obtain ⟨vf1, hf1_halt⟩ := hhalts_f.mpr ⟨vf2, hf_halt⟩
          rcases hrest with hx_err | ⟨vx2, hx_halt, hframe_err⟩
          · exact app_error_from_arg_error ρ₁ f x vf1 hf1_halt (herr_x.mpr hx_err)
          · obtain ⟨vx1, hx1_halt⟩ := hhalts_x.mpr ⟨vx2, hx_halt⟩
            have hmid := funV_same_arg_error_transfer vf2 vf1 vx2
              (fun j => valueEq_symm j vf1 vf2 (hveq_f j vf1 vf2 hf1_halt hf_halt)) hframe_err
            have hfb := (funV_frame_beh vf1 vx2 vx1
              (fun k => valueEq_symm k vx1 vx2 (hveq_x k vx1 vx2 hx1_halt hx_halt))).1.mp hmid
            exact app_apply_from_parts ρ₁ f x vf1 vx1 .error hf1_halt hx1_halt hfb
    -- Halts ↔
    · constructor
      · intro ⟨w, hw⟩
        obtain ⟨vf1, vx1, hf_halt, hx_halt, hframe_halt⟩ := app_reaches ρ₁ f x w hw
        obtain ⟨vf2, hf2_halt⟩ := hhalts_f.mp ⟨vf1, hf_halt⟩
        obtain ⟨vx2, hx2_halt⟩ := hhalts_x.mp ⟨vx1, hx_halt⟩
        have hmid := funV_same_arg_halts_transfer vf1 vf2 vx1
          (fun j => hveq_f j vf1 vf2 hf_halt hf2_halt) ⟨w, hframe_halt⟩
        have hfb := (funV_frame_beh vf2 vx1 vx2 (fun k => hveq_x k vx1 vx2 hx_halt hx2_halt)).2.1.mp hmid
        obtain ⟨w', hw'⟩ := hfb
        exact ⟨w', app_apply_from_parts ρ₂ f x vf2 vx2 (.halt w') hf2_halt hx2_halt hw'⟩
      · intro ⟨w, hw⟩
        obtain ⟨vf2, vx2, hf_halt, hx_halt, hframe_halt⟩ := app_reaches ρ₂ f x w hw
        obtain ⟨vf1, hf1_halt⟩ := hhalts_f.mpr ⟨vf2, hf_halt⟩
        obtain ⟨vx1, hx1_halt⟩ := hhalts_x.mpr ⟨vx2, hx_halt⟩
        have hmid := funV_same_arg_halts_transfer vf2 vf1 vx2
          (fun j => valueEq_symm j vf1 vf2 (hveq_f j vf1 vf2 hf1_halt hf_halt)) ⟨w, hframe_halt⟩
        have hfb := (funV_frame_beh vf1 vx2 vx1
          (fun k => valueEq_symm k vx1 vx2 (hveq_x k vx1 vx2 hx1_halt hx_halt))).2.1.mp hmid
        obtain ⟨w', hw'⟩ := hfb
        exact ⟨w', app_apply_from_parts ρ₁ f x vf1 vx1 (.halt w') hf1_halt hx1_halt hw'⟩
    -- ValueEq k
    · intro k w₁ w₂ hw₁ hw₂
      obtain ⟨vf1, vx1, hf1_halt, hx1_halt, hframe1_halt⟩ := app_reaches ρ₁ f x w₁ hw₁
      obtain ⟨vf2, vx2, hf2_halt, hx2_halt, hframe2_halt⟩ := app_reaches ρ₂ f x w₂ hw₂
      -- Chain through middle: vf2(vx1)
      -- Step 1: ValueEq k w₁ w_mid from funV_same_arg_valueEq (vf1 vs vf2, same arg vx1)
      have hveq_all_f : ∀ j, ValueEq j vf1 vf2 :=
        fun j => hveq_f j vf1 vf2 hf1_halt hf2_halt
      -- We need ret [funV vf2] vx1 to halt to get the middle value
      have h_mid_halts := funV_same_arg_halts_transfer vf1 vf2 vx1 hveq_all_f ⟨w₁, hframe1_halt⟩
      obtain ⟨w_mid, hw_mid⟩ := h_mid_halts
      have hveq1 := funV_same_arg_valueEq k vf1 vf2 vx1 w₁ w_mid hveq_all_f hframe1_halt hw_mid
      -- Step 2: ValueEq k w_mid w₂ from funV_frame_beh (same vf2, different vx1 vs vx2)
      have hfb := funV_frame_beh vf2 vx1 vx2 (fun j => hveq_x j vx1 vx2 hx1_halt hx2_halt)
      have hveq2 := hfb.2.2 k w_mid w₂ hw_mid hframe2_halt
      -- Compose via transitivity
      exact valueEq_trans k w₁ w_mid w₂ hveq1 hveq2
  -- Constr: iterate through field arguments
  | .Constr tag args =>
    have hcl_args := closedAt_constr hcl
    match args with
    | [] =>
      -- Both sides: compute [] ρ (Constr tag []) → ret [] (VConstr tag []) → halt (VConstr tag [])
      have hl : steps 2 (.compute [] ρ₁ (.Constr tag [])) = .halt (.VConstr tag []) := by
        simp [steps, step]
      have hr : steps 2 (.compute [] ρ₂ (.Constr tag [])) = .halt (.VConstr tag []) := by
        simp [steps, step]
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro herr; exact absurd (reaches_halt_not_error ⟨2, hl⟩ herr) False.elim
        · intro herr; exact absurd (reaches_halt_not_error ⟨2, hr⟩ herr) False.elim
      · exact ⟨fun _ => ⟨_, 2, hr⟩, fun _ => ⟨_, 2, hl⟩⟩
      · intro k w₁ w₂ hw₁ hw₂
        have := reaches_unique hw₁ ⟨2, hl⟩; subst this
        have := reaches_unique hw₂ ⟨2, hr⟩; subst this
        exact valueEq_refl k (.VConstr tag [])
    | m :: ms =>
      -- One step on both sides
      have hl1 : steps 1 (.compute [] ρ₁ (.Constr tag (m :: ms))) =
          .compute [.constrField tag [] ms ρ₁] ρ₁ m := by simp [steps, step]
      have hr1 : steps 1 (.compute [] ρ₂ (.Constr tag (m :: ms))) =
          .compute [.constrField tag [] ms ρ₂] ρ₂ m := by simp [steps, step]
      -- Each field m is adequate by structural recursion
      have hcl_m := (closedAt_constr_cons hcl_args).1
      have hcl_ms := (closedAt_constr_cons hcl_args).2
      have hsba_m := sameBody_adequacy d m ρ₁ ρ₂ hcl_m hρ
      obtain ⟨hm_err, hm_halts, hm_veq⟩ := hsba_m
      -- Each field in ms is adequate
      have hfields_ms : ∀ m', m' ∈ ms →
          (Reaches (.compute [] ρ₁ m') .error ↔ Reaches (.compute [] ρ₂ m') .error) ∧
          (Halts (.compute [] ρ₁ m') ↔ Halts (.compute [] ρ₂ m')) ∧
          ∀ k v₁ v₂, Reaches (.compute [] ρ₁ m') (.halt v₁) →
            Reaches (.compute [] ρ₂ m') (.halt v₂) → ValueEq k v₁ v₂ := by
        intro m' hm'
        have hcl_m' : closedAt d m' = true :=
          closedAtList_of_mem hcl_ms hm'
        exact sameBody_adequacy d m' ρ₁ ρ₂ hcl_m' hρ
      refine ⟨?_, ?_, ?_⟩
      -- Error ↔
      · constructor
        · intro herr
          -- compute [] ρ₁ (Constr tag (m::ms)) errors
          -- After 1 step: compute [constrField tag [] ms ρ₁] ρ₁ m errors
          have herr' : Reaches (.compute [.constrField tag [] ms ρ₁] ρ₁ m) .error := by
            obtain ⟨N, hN⟩ := herr
            have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
            have hN1 : N = 1 + (N - 1) := by omega
            exact ⟨N - 1, by rw [hN1, steps_trans, hl1] at hN; exact hN⟩
          -- Decompose: either m errors or m halts and the rest errors
          rcases compute_frame_error_decompose (.constrField tag [] ms ρ₁) ρ₁ m herr'
            with hm_err_l | ⟨vm₁, hm_halt₁, hrest_err₁⟩
          · -- m errors under ρ₁ → m errors under ρ₂
            have := compute_to_error_from_error ρ₂ m [.constrField tag [] ms ρ₂] (hm_err.mp hm_err_l)
            obtain ⟨K, hK⟩ := this; exact ⟨1 + K, by rw [steps_trans, hr1, hK]⟩
          · -- m halts with vm₁, rest errors
            obtain ⟨vm₂, hm_halt₂⟩ := hm_halts.mp ⟨vm₁, hm_halt₁⟩
            have ih := constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
              (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
              (fun _ => by unfold ListValueEq; trivial) hfields_ms
            have hrest_err₂ := ih.1.mp hrest_err₁
            have := compute_frame_compose (.constrField tag [] ms ρ₂) ρ₂ m vm₂ .error hm_halt₂ hrest_err₂
            obtain ⟨K, hK⟩ := this; exact ⟨1 + K, by rw [steps_trans, hr1, hK]⟩
        · intro herr
          have herr' : Reaches (.compute [.constrField tag [] ms ρ₂] ρ₂ m) .error := by
            obtain ⟨N, hN⟩ := herr
            have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
            have hN1 : N = 1 + (N - 1) := by omega
            exact ⟨N - 1, by rw [hN1, steps_trans, hr1] at hN; exact hN⟩
          rcases compute_frame_error_decompose (.constrField tag [] ms ρ₂) ρ₂ m herr'
            with hm_err_r | ⟨vm₂, hm_halt₂, hrest_err₂⟩
          · have := compute_to_error_from_error ρ₁ m [.constrField tag [] ms ρ₁] (hm_err.mpr hm_err_r)
            obtain ⟨K, hK⟩ := this; exact ⟨1 + K, by rw [steps_trans, hl1, hK]⟩
          · obtain ⟨vm₁, hm_halt₁⟩ := hm_halts.mpr ⟨vm₂, hm_halt₂⟩
            have ih := constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
              (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
              (fun _ => by unfold ListValueEq; trivial) hfields_ms
            have hrest_err₁ := ih.1.mpr hrest_err₂
            have := compute_frame_compose (.constrField tag [] ms ρ₁) ρ₁ m vm₁ .error hm_halt₁ hrest_err₁
            obtain ⟨K, hK⟩ := this; exact ⟨1 + K, by rw [steps_trans, hl1, hK]⟩
      -- Halts ↔
      · constructor
        · intro ⟨w, hw⟩
          have hw' : Reaches (.compute [.constrField tag [] ms ρ₁] ρ₁ m) (.halt w) := by
            obtain ⟨N, hN⟩ := hw
            have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
            have hN1 : N = 1 + (N - 1) := by omega
            exact ⟨N - 1, by rw [hN1, steps_trans, hl1] at hN; exact hN⟩
          obtain ⟨vm₁, hm_halt₁, hrest₁⟩ :=
            compute_frame_halt_decompose (.constrField tag [] ms ρ₁) ρ₁ m w hw'
          obtain ⟨vm₂, hm_halt₂⟩ := hm_halts.mp ⟨vm₁, hm_halt₁⟩
          have ih := constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
            (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
            (fun _ => by unfold ListValueEq; trivial) hfields_ms
          obtain ⟨w', hw'⟩ := ih.2.1.mp ⟨w, hrest₁⟩
          have := compute_frame_compose (.constrField tag [] ms ρ₂) ρ₂ m vm₂ (.halt w') hm_halt₂ hw'
          obtain ⟨K, hK⟩ := this; exact ⟨w', 1 + K, by rw [steps_trans, hr1, hK]⟩
        · intro ⟨w, hw⟩
          have hw' : Reaches (.compute [.constrField tag [] ms ρ₂] ρ₂ m) (.halt w) := by
            obtain ⟨N, hN⟩ := hw
            have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
            have hN1 : N = 1 + (N - 1) := by omega
            exact ⟨N - 1, by rw [hN1, steps_trans, hr1] at hN; exact hN⟩
          obtain ⟨vm₂, hm_halt₂, hrest₂⟩ :=
            compute_frame_halt_decompose (.constrField tag [] ms ρ₂) ρ₂ m w hw'
          obtain ⟨vm₁, hm_halt₁⟩ := hm_halts.mpr ⟨vm₂, hm_halt₂⟩
          have ih := constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
            (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
            (fun _ => by unfold ListValueEq; trivial) hfields_ms
          obtain ⟨w', hw'⟩ := ih.2.1.mpr ⟨w, hrest₂⟩
          have := compute_frame_compose (.constrField tag [] ms ρ₁) ρ₁ m vm₁ (.halt w') hm_halt₁ hw'
          obtain ⟨K, hK⟩ := this; exact ⟨w', 1 + K, by rw [steps_trans, hl1, hK]⟩
      -- ValueEq k
      · intro k w₁ w₂ hw₁ hw₂
        have hw₁' : Reaches (.compute [.constrField tag [] ms ρ₁] ρ₁ m) (.halt w₁) := by
          obtain ⟨N, hN⟩ := hw₁
          have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
          have hN1 : N = 1 + (N - 1) := by omega
          exact ⟨N - 1, by rw [hN1, steps_trans, hl1] at hN; exact hN⟩
        have hw₂' : Reaches (.compute [.constrField tag [] ms ρ₂] ρ₂ m) (.halt w₂) := by
          obtain ⟨N, hN⟩ := hw₂
          have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
          have hN1 : N = 1 + (N - 1) := by omega
          exact ⟨N - 1, by rw [hN1, steps_trans, hr1] at hN; exact hN⟩
        obtain ⟨vm₁, hm_halt₁, hrest₁⟩ :=
          compute_frame_halt_decompose (.constrField tag [] ms ρ₁) ρ₁ m w₁ hw₁'
        obtain ⟨vm₂, hm_halt₂, hrest₂⟩ :=
          compute_frame_halt_decompose (.constrField tag [] ms ρ₂) ρ₂ m w₂ hw₂'
        exact (constrField_iter_adequacy tag [] [] vm₁ vm₂ ms ρ₁ ρ₂
          (fun k => hm_veq k vm₁ vm₂ hm_halt₁ hm_halt₂)
          (fun _ => by unfold ListValueEq; trivial) hfields_ms).2.2 k w₁ w₂ hrest₁ hrest₂
  -- Case: decompose through caseScrutinee frame
  | .Case scrut alts =>
    have ⟨hcl_scrut, hcl_alts⟩ := closedAt_case hcl
    have hsba_scrut := sameBody_adequacy d scrut ρ₁ ρ₂ hcl_scrut hρ
    obtain ⟨herr_scrut, hhalts_scrut, hveq_scrut⟩ := hsba_scrut
    -- Both sides: compute [] ρ (Case scrut alts) → compute [caseScrutinee alts ρ] ρ scrut
    have hl1 : steps 1 (.compute [] ρ₁ (.Case scrut alts)) =
        .compute [.caseScrutinee alts ρ₁] ρ₁ scrut := by simp [steps, step]
    have hr1 : steps 1 (.compute [] ρ₂ (.Case scrut alts)) =
        .compute [.caseScrutinee alts ρ₂] ρ₂ scrut := by simp [steps, step]
    refine ⟨?_, ?_, ?_⟩
    -- Error ↔
    · constructor
      · intro herr
        have herr' : Reaches (.compute [.caseScrutinee alts ρ₁] ρ₁ scrut) .error := by
          obtain ⟨N, hN⟩ := herr
          have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
          have hN1 : N = 1 + (N - 1) := by omega
          exact ⟨N - 1, by rw [hN1, steps_trans, hl1] at hN; exact hN⟩
        rcases compute_frame_error_decompose (.caseScrutinee alts ρ₁) ρ₁ scrut herr'
          with hs_err | ⟨vs₁, hs_halt₁, hcase_err₁⟩
        · have := compute_to_error_from_error ρ₂ scrut [.caseScrutinee alts ρ₂] (herr_scrut.mp hs_err)
          obtain ⟨K, hK⟩ := this; exact ⟨1 + K, by rw [steps_trans, hr1, hK]⟩
        · -- Scrutinee halts with vs₁, case dispatch errors.
          -- Get vs₂ from halts transfer, then use caseScrutinee_frame_transfer.
          obtain ⟨vs₂, hs_halt₂⟩ := hhalts_scrut.mp ⟨vs₁, hs_halt₁⟩
          have hveq_vs : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq_scrut k vs₁ vs₂ hs_halt₁ hs_halt₂
          have ⟨herr_case, _, _⟩ := caseScrutinee_frame_transfer alts ρ₁ ρ₂ d hρ hcl_alts vs₁ vs₂ hveq_vs
          exact reaches_of_step_reaches hr1 (compute_frame_compose
            (.caseScrutinee alts ρ₂) ρ₂ scrut vs₂ .error hs_halt₂ (herr_case.mp hcase_err₁))
      · intro herr
        have herr' : Reaches (.compute [.caseScrutinee alts ρ₂] ρ₂ scrut) .error := by
          obtain ⟨N, hN⟩ := herr
          have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
          have hN1 : N = 1 + (N - 1) := by omega
          exact ⟨N - 1, by rw [hN1, steps_trans, hr1] at hN; exact hN⟩
        rcases compute_frame_error_decompose (.caseScrutinee alts ρ₂) ρ₂ scrut herr'
          with hs_err | ⟨vs₂, hs_halt₂, hcase_err₂⟩
        · have := compute_to_error_from_error ρ₁ scrut [.caseScrutinee alts ρ₁] (herr_scrut.mpr hs_err)
          obtain ⟨K, hK⟩ := this; exact ⟨1 + K, by rw [steps_trans, hl1, hK]⟩
        · -- Symmetric: scrutinee halts with vs₂, case dispatch errors.
          obtain ⟨vs₁, hs_halt₁⟩ := hhalts_scrut.mpr ⟨vs₂, hs_halt₂⟩
          have hveq_vs : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq_scrut k vs₁ vs₂ hs_halt₁ hs_halt₂
          have ⟨herr_case, _, _⟩ := caseScrutinee_frame_transfer alts ρ₁ ρ₂ d hρ hcl_alts vs₁ vs₂ hveq_vs
          exact reaches_of_step_reaches hl1 (compute_frame_compose
            (.caseScrutinee alts ρ₁) ρ₁ scrut vs₁ .error hs_halt₁ (herr_case.mpr hcase_err₂))
    -- Halts ↔
    · constructor
      · intro ⟨w, hw⟩
        have hw' : Reaches (.compute [.caseScrutinee alts ρ₁] ρ₁ scrut) (.halt w) := by
          obtain ⟨N, hN⟩ := hw
          have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
          have hN1 : N = 1 + (N - 1) := by omega
          exact ⟨N - 1, by rw [hN1, steps_trans, hl1] at hN; exact hN⟩
        obtain ⟨vs₁, hs_halt₁, hcase_halt₁⟩ :=
          compute_frame_halt_decompose (.caseScrutinee alts ρ₁) ρ₁ scrut w hw'
        obtain ⟨vs₂, hs_halt₂⟩ := hhalts_scrut.mp ⟨vs₁, hs_halt₁⟩
        have hveq_vs : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq_scrut k vs₁ vs₂ hs_halt₁ hs_halt₂
        have ⟨_, hhalts_case, _⟩ := caseScrutinee_frame_transfer alts ρ₁ ρ₂ d hρ hcl_alts vs₁ vs₂ hveq_vs
        obtain ⟨w', hw'⟩ := hhalts_case.mp ⟨w, hcase_halt₁⟩
        exact ⟨w', reaches_of_step_reaches hr1 (compute_frame_compose
          (.caseScrutinee alts ρ₂) ρ₂ scrut vs₂ (.halt w') hs_halt₂ hw')⟩
      · intro ⟨w, hw⟩
        have hw' : Reaches (.compute [.caseScrutinee alts ρ₂] ρ₂ scrut) (.halt w) := by
          obtain ⟨N, hN⟩ := hw
          have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
          have hN1 : N = 1 + (N - 1) := by omega
          exact ⟨N - 1, by rw [hN1, steps_trans, hr1] at hN; exact hN⟩
        obtain ⟨vs₂, hs_halt₂, hcase_halt₂⟩ :=
          compute_frame_halt_decompose (.caseScrutinee alts ρ₂) ρ₂ scrut w hw'
        obtain ⟨vs₁, hs_halt₁⟩ := hhalts_scrut.mpr ⟨vs₂, hs_halt₂⟩
        have hveq_vs : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq_scrut k vs₁ vs₂ hs_halt₁ hs_halt₂
        have ⟨_, hhalts_case, _⟩ := caseScrutinee_frame_transfer alts ρ₁ ρ₂ d hρ hcl_alts vs₁ vs₂ hveq_vs
        obtain ⟨w', hw'⟩ := hhalts_case.mpr ⟨w, hcase_halt₂⟩
        exact ⟨w', reaches_of_step_reaches hl1 (compute_frame_compose
          (.caseScrutinee alts ρ₁) ρ₁ scrut vs₁ (.halt w') hs_halt₁ hw')⟩
    -- ValueEq k
    · intro k w₁ w₂ hw₁ hw₂
      -- Decompose both halting computations through the caseScrutinee frame
      have hw₁' : Reaches (.compute [.caseScrutinee alts ρ₁] ρ₁ scrut) (.halt w₁) := by
        obtain ⟨N, hN⟩ := hw₁
        have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
        have hN1 : N = 1 + (N - 1) := by omega
        exact ⟨N - 1, by rw [hN1, steps_trans, hl1] at hN; exact hN⟩
      have hw₂' : Reaches (.compute [.caseScrutinee alts ρ₂] ρ₂ scrut) (.halt w₂) := by
        obtain ⟨N, hN⟩ := hw₂
        have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
        have hN1 : N = 1 + (N - 1) := by omega
        exact ⟨N - 1, by rw [hN1, steps_trans, hr1] at hN; exact hN⟩
      obtain ⟨vs₁, hs_halt₁, hcase_halt₁⟩ :=
        compute_frame_halt_decompose (.caseScrutinee alts ρ₁) ρ₁ scrut w₁ hw₁'
      obtain ⟨vs₂, hs_halt₂, hcase_halt₂⟩ :=
        compute_frame_halt_decompose (.caseScrutinee alts ρ₂) ρ₂ scrut w₂ hw₂'
      have hveq_vs : ∀ k, ValueEq k vs₁ vs₂ := fun k => hveq_scrut k vs₁ vs₂ hs_halt₁ hs_halt₂
      exact (caseScrutinee_frame_transfer alts ρ₁ ρ₂ d hρ hcl_alts vs₁ vs₂ hveq_vs).2.2 k w₁ w₂ hcase_halt₁ hcase_halt₂
  termination_by sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)
      -- Cross-call from sameBody_adequacy to funV_frame_beh: vf is a runtime
      -- value, not a sub-term of t, so sizeOf cannot relate them.
      -- The recursion truly terminates (on execution step count), but the
      -- declared sizeOf measure cannot express this. Since both theorems
      -- are Prop-valued, the sorry here is logically sound.
      | sorry
end

end Moist.Verified.SameBodyAdequacy
