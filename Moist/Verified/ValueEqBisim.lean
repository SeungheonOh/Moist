import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.Verified.FundamentalLemma
import Moist.Verified.Congruence

set_option linter.unusedSimpArgs false
set_option maxErrors 500

namespace Moist.Verified.ValueEqBisim

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.Verified.Semantics
open Moist.Verified.StepLift (liftState isActive step_liftState_active
  steps_liftState liftState_ne_halt liftState_eq_error)
open Moist.Verified.Semantics (valueEq_mono listValueEq_mono)

/-! # ValueEq Bisimulation for the Fundamental Lemma

This module proves the **fundamental lemma** of the step-indexed logical
relation by establishing a bisimulation on CEK states where values are
related by `ValueEq k` (or structurally by same-body closures with
`ValueEq k`-related environments).

The proof is by double induction: outer on `k` (step index), inner on
`n` (step count). The main difficulty is handling the case where a
`ValueEq k`-related VLam (with potentially different body) is applied
during execution — here we use the VLam clause of `ValueEq` together
with the stack-lifting infrastructure from `StepLift.lean`.
-/

/-! ## firstInactive (local copy — private in StepLift) -/

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

/-! ## Environment pointwise ValueEq -/

/-- Pointwise `ValueEq k` on environments. -/
inductive EnvEq : Nat → CekEnv → CekEnv → Prop where
  | nil : EnvEq k .nil .nil
  | cons : ValueEq k v1 v2 → EnvEq k e1 e2 →
      EnvEq k (.cons v1 e1) (.cons v2 e2)

theorem envEq_lookup {k : Nat} {env1 env2 : CekEnv} (h : EnvEq k env1 env2)
    (n : Nat) :
    match env1.lookup n, env2.lookup n with
    | some v1, some v2 => ValueEq k v1 v2
    | none, none => True
    | _, _ => False := by
  induction h generalizing n with
  | nil => cases n <;> simp [CekEnv.lookup]
  | cons hv _ ih =>
    match n with
    | 0 => simp [CekEnv.lookup]
    | 1 => simp [CekEnv.lookup]; exact hv
    | n + 2 => simp only [CekEnv.lookup]; exact ih (n + 1)

theorem envEq_extend {k : Nat} {env1 env2 : CekEnv} (henv : EnvEq k env1 env2)
    {v1 v2 : CekValue} (hv : ValueEq k v1 v2) :
    EnvEq k (env1.extend v1) (env2.extend v2) :=
  .cons hv henv

theorem envEq_refl {k : Nat} (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    (env : CekEnv) : EnvEq k env env := by
  cases env with
  | nil => exact .nil
  | cons v rest =>
    exact .cons (veq_refl k (Nat.le_refl k) v) (envEq_refl veq_refl rest)

/-! ## Structural frame / stack / state relations -/

/-- Same-term frame relation: frames share the same terms but have
    `ValueEq k`-related values and `EnvEq k`-related environments. -/
inductive FrameEq (k : Nat) : Frame → Frame → Prop where
  | force : FrameEq k .force .force
  | arg : EnvEq k env1 env2 → FrameEq k (.arg t env1) (.arg t env2)
  | funV : ValueEq k v1 v2 → FrameEq k (.funV v1) (.funV v2)
  | applyArg : ValueEq k v1 v2 → FrameEq k (.applyArg v1) (.applyArg v2)
  | constrField : ListValueEq k done1 done2 → EnvEq k env1 env2 →
      FrameEq k (.constrField tag done1 todo env1) (.constrField tag done2 todo env2)
  | caseScrutinee : EnvEq k env1 env2 →
      FrameEq k (.caseScrutinee alts env1) (.caseScrutinee alts env2)

/-- Pointwise frame relation on stacks. -/
inductive StackEq (k : Nat) : Stack → Stack → Prop where
  | nil : StackEq k [] []
  | cons : FrameEq k f1 f2 → StackEq k s1 s2 → StackEq k (f1 :: s1) (f2 :: s2)

/-- Same-term state relation with `ValueEq k`-related values. -/
inductive StateEq (k : Nat) : State → State → Prop where
  | compute : StackEq k s1 s2 → EnvEq k env1 env2 →
      StateEq k (.compute s1 env1 t) (.compute s2 env2 t)
  | ret : StackEq k s1 s2 → ValueEq k v1 v2 →
      StateEq k (.ret s1 v1) (.ret s2 v2)
  | error : StateEq k .error .error
  | halt : ValueEq k v1 v2 →
      StateEq k (.halt v1) (.halt v2)

/-! ## Conversions between local inductives and Semantics.lean StackEqR/EnvEqR -/

/-- Convert local inductive `EnvEq k` to parametric `EnvEqR (ValueEq k)`. -/
private theorem envEq_to_envEqR {k : Nat} {e1 e2 : CekEnv}
    (h : EnvEq k e1 e2) : EnvEqR (ValueEq k) e1 e2 := by
  induction h with
  | nil => exact trivial
  | cons hv _ ih => exact ⟨hv, ih⟩

/-- Convert parametric `EnvEqR (ValueEq k)` to local inductive `EnvEq k`. -/
private theorem envEqR_to_envEq : ∀ {k : Nat} {e1 e2 : CekEnv},
    EnvEqR (ValueEq k) e1 e2 → EnvEq k e1 e2
  | _, .nil, .nil, _ => .nil
  | _, .cons _ _, .cons _ _, ⟨hv, he⟩ => .cons hv (envEqR_to_envEq he)
  | _, .nil, .cons _ _, h => absurd h (by simp [EnvEqR])
  | _, .cons _ _, .nil, h => absurd h (by simp [EnvEqR])

/-- Convert `ListValueEq k` to `ListR (ValueEq k)`. -/
private theorem listValueEq_to_listR {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListValueEq k vs1 vs2) : ListR (ValueEq k) vs1 vs2 := by
  induction vs1 generalizing vs2 with
  | nil => cases vs2 with | nil => exact trivial | cons _ _ => simp [ListValueEq] at h
  | cons a as ih =>
    cases vs2 with
    | nil => simp [ListValueEq] at h
    | cons b bs =>
      simp only [ListValueEq] at h
      exact ⟨h.1, ih h.2⟩

/-- Convert `ListR (ValueEq k)` to `ListValueEq k`. -/
private theorem listR_to_listValueEq {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListR (ValueEq k) vs1 vs2) : ListValueEq k vs1 vs2 := by
  induction vs1 generalizing vs2 with
  | nil => cases vs2 with | nil => simp [ListValueEq] | cons _ _ => simp [ListR] at h
  | cons a as ih =>
    cases vs2 with
    | nil => simp [ListR] at h
    | cons b bs =>
      simp only [ListR] at h
      simp only [ListValueEq]
      exact ⟨h.1, ih h.2⟩

/-- Convert local inductive `FrameEq k` to parametric `FrameEqR (ValueEq k)`. -/
private theorem frameEq_to_frameEqR {k : Nat} {f1 f2 : Frame}
    (h : FrameEq k f1 f2) : FrameEqR (ValueEq k) f1 f2 := by
  cases h with
  | force => exact trivial
  | arg henv => exact ⟨rfl, envEq_to_envEqR henv⟩
  | funV hv => exact hv
  | applyArg hv => exact hv
  | constrField hdone henv =>
    exact ⟨rfl, rfl, listValueEq_to_listR hdone, envEq_to_envEqR henv⟩
  | caseScrutinee henv => exact ⟨rfl, envEq_to_envEqR henv⟩

/-- Convert parametric `FrameEqR (ValueEq k)` to local inductive `FrameEq k`. -/
private theorem frameEqR_to_frameEq {k : Nat} {f1 f2 : Frame}
    (h : FrameEqR (ValueEq k) f1 f2) : FrameEq k f1 f2 := by
  cases f1 <;> cases f2 <;> simp [FrameEqR] at h
  case force.force => exact .force
  case arg.arg t1 e1 t2 e2 => exact h.1 ▸ .arg (envEqR_to_envEq h.2)
  case funV.funV => exact .funV h
  case applyArg.applyArg => exact .applyArg h
  case constrField.constrField tag1 d1 todo1 env1 tag2 d2 todo2 env2 =>
    exact h.1 ▸ h.2.1 ▸ .constrField (listR_to_listValueEq h.2.2.1) (envEqR_to_envEq h.2.2.2)
  case caseScrutinee.caseScrutinee alts1 env1 alts2 env2 =>
    exact h.1 ▸ .caseScrutinee (envEqR_to_envEq h.2)

/-- Convert local inductive `StackEq k` to parametric `StackEqR (ValueEq k)`. -/
private theorem stackEq_to_stackEqR {k : Nat} {s1 s2 : Stack}
    (h : StackEq k s1 s2) : StackEqR (ValueEq k) s1 s2 := by
  induction h with
  | nil => exact trivial
  | cons hf _ ih => exact ⟨frameEq_to_frameEqR hf, ih⟩

/-- Convert parametric `StackEqR (ValueEq k)` to local inductive `StackEq k`. -/
private theorem stackEqR_to_stackEq : ∀ {k : Nat} {s1 s2 : Stack},
    StackEqR (ValueEq k) s1 s2 → StackEq k s1 s2
  | _, [], [], _ => .nil
  | _, _ :: _, _ :: _, ⟨hf, hs⟩ => .cons (frameEqR_to_frameEq hf) (stackEqR_to_stackEq hs)
  | _, [], _ :: _, h => absurd h (by simp [StackEqR])
  | _, _ :: _, [], h => absurd h (by simp [StackEqR])

/-! ## StepCompat: the semantic compatibility predicate -/

/-- Two states are `n`-step `k`-compatible when they agree on error/halt
    after exactly `n` steps, with `ValueEq (k - n)` for halted values.

    The decaying observation level `k - n` accounts for the fact that after
    `n` steps from budget `k`, only `k - n` observation units remain. Every
    "consuming" step (force, apply, case) naturally costs one level, and the
    decay accounts for it. -/
def StepCompat (k n : Nat) (s1 s2 : State) : Prop :=
  (steps n s1 = .error ↔ steps n s2 = .error) ∧
  (∀ v1, steps n s1 = .halt v1 →
    ∃ v2, steps n s2 = .halt v2 ∧ ValueEq (k - n) v1 v2) ∧
  (∀ v2, steps n s2 = .halt v2 →
    ∃ v1, steps n s1 = .halt v1 ∧ ValueEq (k - n) v1 v2)

/-- Asymmetric compatibility: each side's outcome at step `n` is matched
    by the other side within `k` steps (possibly at a different step count).
    This is the 4-tuple shape matching the new VLam/VDelay clause. -/
def AsymCompat (k n : Nat) (s1 s2 : State) : Prop :=
  (steps n s1 = .error → ∃ m, m ≤ k ∧ steps m s2 = .error) ∧
  (∀ v1, steps n s1 = .halt v1 →
    ∃ v2 m, m ≤ k ∧ steps m s2 = .halt v2 ∧ ValueEq (k - n) v1 v2) ∧
  (steps n s2 = .error → ∃ m, m ≤ k ∧ steps m s1 = .error) ∧
  (∀ v2, steps n s2 = .halt v2 →
    ∃ v1 m, m ≤ k ∧ steps m s1 = .halt v1 ∧ ValueEq (k - n) v1 v2)

theorem stepCompat_to_asymCompat {k n : Nat} (hn : n ≤ k) {s1 s2 : State}
    (h : StepCompat k n s1 s2) : AsymCompat k n s1 s2 :=
  ⟨fun he => ⟨n, hn, h.1.mp he⟩,
   fun v1 hv1 => let ⟨v2, hv2, hve⟩ := h.2.1 v1 hv1; ⟨v2, n, hn, hv2, hve⟩,
   fun he => ⟨n, hn, h.1.mpr he⟩,
   fun v2 hv2 => let ⟨v1, hv1, hve⟩ := h.2.2 v2 hv2; ⟨v1, n, hn, hv1, hve⟩⟩

/-- Level-dropping step for AsymCompat: `AsymCompat k n (step s1) (step s2)` implies
    `AsymCompat (k+1) (n+1) s1 s2`. This is exact because
    `(k+1) - (n+1) = k - n`, so no `valueEq_mono` is needed.
    For the existential witnesses, `m` steps on `step s` becomes `m+1` steps on `s`. -/
private theorem asymCompat_step_lower {k n : Nat} {s1 s2 : State}
    (h : AsymCompat k n (step s1) (step s2)) :
    AsymCompat (k + 1) (n + 1) s1 s2 := by
  have hlevel : k + 1 - (n + 1) = k - n := by omega
  constructor
  · -- error forward
    intro he
    rw [show steps (n + 1) s1 = steps n (step s1) from rfl] at he
    obtain ⟨m, hm, hme⟩ := h.1 he
    exact ⟨m + 1, by omega, show steps (m + 1) s2 = .error from hme⟩
  constructor
  · -- halt forward
    intro v1 hv1
    rw [show steps (n + 1) s1 = steps n (step s1) from rfl] at hv1
    obtain ⟨v2, m, hm, hme, hve⟩ := h.2.1 v1 hv1
    exact ⟨v2, m + 1, by omega, show steps (m + 1) s2 = .halt v2 from hme, by rw [hlevel]; exact hve⟩
  constructor
  · -- error backward
    intro he
    rw [show steps (n + 1) s2 = steps n (step s2) from rfl] at he
    obtain ⟨m, hm, hme⟩ := h.2.2.1 he
    exact ⟨m + 1, by omega, show steps (m + 1) s1 = .error from hme⟩
  · -- halt backward
    intro v2 hv2
    rw [show steps (n + 1) s2 = steps n (step s2) from rfl] at hv2
    obtain ⟨v1, m, hm, hme, hve⟩ := h.2.2.2 v2 hv2
    exact ⟨v1, m + 1, by omega, show steps (m + 1) s1 = .halt v1 from hme, by rw [hlevel]; exact hve⟩

theorem stepCompat_error (k n : Nat) :
    StepCompat k n .error .error := by
  refine ⟨Iff.rfl, fun v1 h => ?_, fun v2 h => ?_⟩
  · rw [steps_error] at h; exact absurd h (by simp)
  · rw [steps_error] at h; exact absurd h (by simp)

theorem stepCompat_halt (k n : Nat) (v1 v2 : CekValue) (hv : ValueEq (k - n) v1 v2) :
    StepCompat k n (.halt v1) (.halt v2) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun w1 h => ?_, fun w2 h => ?_⟩
  · rw [steps_halt] at h; simp at h
  · rw [steps_halt] at h; simp at h
  · rw [steps_halt] at h; injection h with h; subst h; exact ⟨v2, steps_halt v2 n, hv⟩
  · rw [steps_halt] at h; injection h with h; subst h; exact ⟨v1, steps_halt v1 n, hv⟩

/-- If one-step results are compatible for `n`, the original states are
    compatible for `n+1`. Uses `valueEq_mono` to account for the level
    decay: results at `k - n` are downgraded to `k - (n + 1)`. -/
theorem stepCompat_step {k n : Nat} {s1 s2 : State}
    (h : StepCompat k n (step s1) (step s2)) :
    StepCompat k (n + 1) s1 s2 := by
  simp only [StepCompat, steps] at h ⊢
  exact ⟨h.1,
    fun v1 hv1 => let ⟨v2, hv2, hve⟩ := h.2.1 v1 hv1; ⟨v2, hv2, valueEq_mono _ _ (by omega) _ _ hve⟩,
    fun v2 hv2 => let ⟨v1, hv1, hve⟩ := h.2.2 v2 hv2; ⟨v1, hv1, valueEq_mono _ _ (by omega) _ _ hve⟩⟩

/-- Level-dropping step: `StepCompat k n (step s1) (step s2)` implies
    `StepCompat (k+1) (n+1) s1 s2`. This is exact because
    `(k+1) - (n+1) = k - n`, so no `valueEq_mono` is needed. -/
theorem stepCompat_step_lower {k n : Nat} {s1 s2 : State}
    (h : StepCompat k n (step s1) (step s2)) :
    StepCompat (k + 1) (n + 1) s1 s2 := by
  simp only [StepCompat, steps] at h ⊢
  have : k + 1 - (n + 1) = k - n := by omega
  rw [this]; exact h

/-- `StepCompat k 0` for two `ret` states (trivially true since
    `steps 0 (.ret s v) = .ret s v` which is neither error nor halt). -/
theorem stepCompat_zero_ret (k : Nat) (s1 s2 : Stack) (v1 v2 : CekValue) :
    StepCompat k 0 (.ret s1 v1) (.ret s2 v2) := by
  simp only [StepCompat, steps]
  exact ⟨⟨fun h => by simp at h, fun h => by simp at h⟩,
         fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- `StepCompat k 0` for two `compute` states (trivially true). -/
theorem stepCompat_zero_compute (k : Nat) (s1 s2 : Stack) (e1 e2 : CekEnv) (t1 t2 : Term) :
    StepCompat k 0 (.compute s1 e1 t1) (.compute s2 e2 t2) := by
  simp only [StepCompat, steps]
  exact ⟨⟨fun h => by simp at h, fun h => by simp at h⟩,
         fun _ h => by simp at h, fun _ h => by simp at h⟩

/-! ## Mono helpers for step compatibility -/

/-- Helper: downgrade a `StepCompat (m+1) n` to `StepCompat m n`.
    With decaying levels, results go from `ValueEq ((m+1) - n)` to
    `ValueEq (m - n)`, which follows from `valueEq_mono` since `m - n ≤ (m+1) - n`. -/
private theorem stepCompat_anti_mono {m n : Nat} {s1 s2 : State}
    (h : StepCompat (m + 1) n s1 s2) : StepCompat m n s1 s2 :=
  ⟨h.1,
   fun v1 hv1 => let ⟨v2, hv2, hv⟩ := h.2.1 v1 hv1; ⟨v2, hv2, valueEq_mono _ _ (by omega) _ _ hv⟩,
   fun v2 hv2 => let ⟨v1, hv1, hv⟩ := h.2.2 v2 hv2; ⟨v1, hv1, valueEq_mono _ _ (by omega) _ _ hv⟩⟩

/-! ## Mono helpers for structural relations -/

/-- Downgrade `FrameEq` from level `k` to any `j ≤ k`. -/
private theorem frameEq_mono {j k : Nat} (hjk : j ≤ k)
    {f1 f2 : Frame} (h : FrameEq k f1 f2) : FrameEq j f1 f2 := by
  cases h with
  | force => exact .force
  | arg henv =>
    exact .arg (by induction henv with
      | nil => exact .nil
      | cons hv _ ih => exact .cons (valueEq_mono j k hjk _ _ hv) ih)
  | funV hv => exact .funV (valueEq_mono j k hjk _ _ hv)
  | applyArg hv => exact .applyArg (valueEq_mono j k hjk _ _ hv)
  | constrField hdone henv =>
    exact .constrField (listValueEq_mono j k hjk _ _ hdone)
      (by induction henv with
        | nil => exact .nil
        | cons hv _ ih => exact .cons (valueEq_mono j k hjk _ _ hv) ih)
  | caseScrutinee henv =>
    exact .caseScrutinee (by induction henv with
      | nil => exact .nil
      | cons hv _ ih => exact .cons (valueEq_mono j k hjk _ _ hv) ih)

/-- Downgrade `StackEq` from level `k` to any `j ≤ k`. -/
private theorem stackEq_mono {j k : Nat} (hjk : j ≤ k)
    {s1 s2 : Stack} (h : StackEq k s1 s2) : StackEq j s1 s2 := by
  induction h with
  | nil => exact .nil
  | cons hf _ ih => exact .cons (frameEq_mono hjk hf) ih

/-- Downgrade `EnvEq` from level `k` to any `j ≤ k`. -/
private theorem envEq_mono {j k : Nat} (hjk : j ≤ k)
    {env1 env2 : CekEnv} (h : EnvEq k env1 env2) : EnvEq j env1 env2 := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (valueEq_mono j k hjk _ _ hv) ih

/-- Downgrade `StateEq` from level `k` to any `j ≤ k`. -/
private theorem stateEq_mono {j k : Nat} (hjk : j ≤ k)
    {s1 s2 : State} (h : StateEq k s1 s2) : StateEq j s1 s2 := by
  cases h with
  | compute hstk henv => exact .compute (stackEq_mono hjk hstk) (envEq_mono hjk henv)
  | ret hstk hv => exact .ret (stackEq_mono hjk hstk) (valueEq_mono j k hjk _ _ hv)
  | error => exact .error
  | halt hv => exact .halt (valueEq_mono j k hjk _ _ hv)

/-! ## Main theorem: generalized fundamental lemma -/

private theorem stepCompat_ret_nil {k n : Nat} {v1 v2 : CekValue} (hv : ValueEq k v1 v2) :
    StepCompat k n (.ret [] v1) (.ret [] v2) := by
  induction n with
  | zero =>
    simp only [StepCompat, steps]
    exact ⟨⟨fun h => by simp at h, fun h => by simp at h⟩,
      fun _ h => by simp at h, fun _ h => by simp at h⟩
  | succ n' _ =>
    apply stepCompat_step; simp only [step]
    exact stepCompat_halt k n' v1 v2 (valueEq_mono _ _ (by omega) _ _ hv)

/-- Helper: `ListValueEq k` implies the lists have the same length. -/
private theorem listValueEq_length {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListValueEq k vs1 vs2) : vs1.length = vs2.length := by
  induction vs1 generalizing vs2 with
  | nil => cases vs2 with | nil => rfl | cons _ _ => simp [ListValueEq] at h
  | cons v1 rest1 ih =>
    cases vs2 with
    | nil => simp [ListValueEq] at h
    | cons v2 rest2 => simp [ListValueEq] at h; simp [List.length_cons, ih h.2]

/-- Helper: `ListValueEq k` pointwise access. -/
private theorem listValueEq_getElem? {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListValueEq k vs1 vs2) (i : Nat) :
    match vs1[i]?, vs2[i]? with
    | some v1, some v2 => ValueEq k v1 v2
    | none, none => True
    | _, _ => False := by
  induction vs1 generalizing vs2 i with
  | nil =>
    cases vs2 with
    | nil => cases i <;> simp
    | cons _ _ => simp [ListValueEq] at h
  | cons a as ih =>
    cases vs2 with
    | nil => simp [ListValueEq] at h
    | cons b bs =>
      simp [ListValueEq] at h
      cases i with
      | zero => simp; exact h.1
      | succ j => simp; exact ih h.2 j

/-- Helper: mapping `Frame.applyArg` over `ListValueEq k` gives `StackEq k`. -/
private theorem listValueEq_map_applyArg_stackEq {k : Nat}
    {fs1 fs2 : List CekValue} (h : ListValueEq k fs1 fs2) :
    StackEq k (fs1.map Frame.applyArg) (fs2.map Frame.applyArg) := by
  induction fs1 generalizing fs2 with
  | nil =>
    cases fs2 with | nil => exact .nil | cons _ _ => simp [ListValueEq] at h
  | cons v1 rest1 ih =>
    cases fs2 with
    | nil => simp [ListValueEq] at h
    | cons v2 rest2 =>
      simp [ListValueEq] at h
      exact .cons (.applyArg h.1) (ih h.2)

/-- Helper: append two `StackEq k` stacks. -/
private theorem stackEq_append {k : Nat} {s1 s2 t1 t2 : Stack}
    (hs : StackEq k s1 s2) (ht : StackEq k t1 t2) :
    StackEq k (s1 ++ t1) (s2 ++ t2) := by
  induction hs with
  | nil => exact ht
  | cons hf _ ih => exact .cons hf ih

/-- Helper: append two `ListValueEq k` lists. -/
private theorem listValueEq_append {k : Nat} {a1 a2 b1 b2 : List CekValue}
    (ha : ListValueEq k a1 a2) (hb : ListValueEq k b1 b2) :
    ListValueEq k (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp; exact hb
    | cons _ _ => simp [ListValueEq] at ha
  | cons v1 rest1 ih =>
    cases a2 with
    | nil => simp [ListValueEq] at ha
    | cons v2 rest2 =>
      simp only [ListValueEq] at ha
      simp only [List.cons_append, ListValueEq]
      exact ⟨ha.1, ih ha.2⟩

/-- If `ValueEq (k+1) (.VCon c) v`, then `v = .VCon c`. -/
private theorem vcon_eq_of_valueEq_succ {k : Nat} {c : Const} {v : CekValue}
    (h : ValueEq (k + 1) (.VCon c) v) : v = .VCon c := by
  cases v with
  | VCon c' => simp only [ValueEq] at h; exact congrArg CekValue.VCon h.symm
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEq] at h

/-- Helper: reverse preserves `ListValueEq k`. -/
private theorem listValueEq_reverse {k : Nat} {a1 a2 : List CekValue}
    (h : ListValueEq k a1 a2) :
    ListValueEq k a1.reverse a2.reverse := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp [ListValueEq]
    | cons _ _ => simp [ListValueEq] at h
  | cons v1 rest1 ih =>
    cases a2 with
    | nil => simp [ListValueEq] at h
    | cons v2 rest2 =>
      simp only [ListValueEq] at h
      simp only [List.reverse_cons]
      exact listValueEq_append (ih h.2) (by simp [ListValueEq]; exact h.1)

/-- Helper: `ListValueEq k` for cons-then-reverse. -/
private theorem listValueEq_cons_rev {k : Nat} {v1 v2 : CekValue}
    {done1 done2 : List CekValue}
    (hv : ValueEq k v1 v2) (hd : ListValueEq k done1 done2) :
    ListValueEq k ((v1 :: done1).reverse) ((v2 :: done2).reverse) := by
  simp only [List.reverse_cons]
  exact listValueEq_append (listValueEq_reverse hd) (by simp [ListValueEq]; exact hv)

/-- `extractConsts` agreement from `ListValueEq (k+1)`. -/
private theorem extractConsts_eq_of_listValueEq {k : Nat} {args1 args2 : List CekValue}
    (h : ListValueEq (k + 1) args1 args2) :
    Moist.CEK.extractConsts args1 = Moist.CEK.extractConsts args2 := by
  induction args1 generalizing args2 with
  | nil =>
    cases args2 with | nil => rfl | cons _ _ => simp [ListValueEq] at h
  | cons a1 rest1 ih =>
    cases args2 with
    | nil => simp [ListValueEq] at h
    | cons a2 rest2 =>
      simp only [ListValueEq] at h
      have hv := h.1
      have ht := h.2
      cases a1 with
      | VCon c1 =>
        cases a2 with
        | VCon c2 =>
          simp only [ValueEq] at hv; subst hv
          simp only [Moist.CEK.extractConsts]; rw [ih ht]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEq])
      | VLam _ _ =>
        cases a2 with
        | VLam _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEq])
      | VDelay _ _ =>
        cases a2 with
        | VDelay _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEq])
      | VConstr _ _ =>
        cases a2 with
        | VConstr _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEq])
      | VBuiltin _ _ _ =>
        cases a2 with
        | VBuiltin _ _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
          exact absurd hv (by simp [ValueEq])

/-- evalBuiltinPassThrough isNone agreement and same-level value agreement
    from ListValueEq (k+1). The passthrough either fails on both sides
    (VCon at decision positions must agree by ValueEq), or succeeds on both
    with results that are ValueEq (k+1) (being input elements or same VCon). -/
-- Helper: when args have wrong shape, evalBuiltinPassThrough .IfThenElse = none
-- We use cases on the argument list structure and simp to discharge.
-- This private helper avoids code duplication in the main proof.

private theorem evalBuiltinPassThrough_cong_same_level {k : Nat}
    (b : BuiltinFun) {args1 args2 : List CekValue}
    (hargs : ListValueEq (k + 1) args1 args2)
    (veq_refl_k : ∀ v : CekValue, ValueEq (k + 1) v v) :
    (Moist.CEK.evalBuiltinPassThrough b args1).isNone =
    (Moist.CEK.evalBuiltinPassThrough b args2).isNone ∧
    (∀ r1 r2, Moist.CEK.evalBuiltinPassThrough b args1 = some r1 →
              Moist.CEK.evalBuiltinPassThrough b args2 = some r2 →
              ValueEq (k + 1) r1 r2) := by
  -- Strategy: case split on the builtin, then on the argument list structure.
  -- For passthrough builtins: use cases to destructure args, show VCon agreement
  --   via vcon_eq_of_valueEq_succ, and show results are ValueEq (k+1).
  -- For non-passthrough builtins: simp [evalBuiltinPassThrough] closes the AND goal.
  match b with
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- IfThenElse: matches [elseV, thenV, VCon (Bool cond)]
  -- (args in reversed order, so args[2] is the Bool condition)
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .IfThenElse =>
    cases args1 with
    | nil =>
      cases args2 with
      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases t1 with
      | nil =>
        cases args2 with
        | nil => simp [ListValueEq] at hargs
        | cons a2 t2 =>
          cases t2 with
          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ => simp [ListValueEq] at hargs
      | cons b1 t2 =>
        cases t2 with
        | nil =>
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | nil => simp [Moist.CEK.evalBuiltinPassThrough]
              | cons _ _ => simp [ListValueEq] at hargs
        | cons c1 t3 =>
          cases t3 with
          | cons _ _ =>
            cases args2 with
            | nil => simp [ListValueEq] at hargs
            | cons a2 t2' =>
              cases t2' with
              | nil => simp [ListValueEq] at hargs
              | cons b2 t3' =>
                cases t3' with
                | nil => simp [ListValueEq] at hargs
                | cons c2 t4 =>
                  cases t4 with
                  | nil => simp [ListValueEq] at hargs
                  | cons _ _ => simp [Moist.CEK.evalBuiltinPassThrough]
          | nil =>
            -- args1 = [a1, b1, c1]
            cases args2 with
            | nil => simp [ListValueEq] at hargs
            | cons a2 t2' =>
              cases t2' with
              | nil => simp [ListValueEq] at hargs
              | cons b2 t3' =>
                cases t3' with
                | nil => simp [ListValueEq] at hargs
                | cons c2 t4 =>
                  cases t4 with
                  | cons _ _ => simp [ListValueEq] at hargs
                  | nil =>
                    -- args2 = [a2, b2, c2]
                    simp only [ListValueEq] at hargs
                    obtain ⟨ha12, hb12, hc12, _⟩ := hargs
                    -- c1 and c2 are the condition at decision position
                    cases c1 with
                    | VCon cst1 =>
                      have hc2eq : c2 = .VCon cst1 := vcon_eq_of_valueEq_succ hc12
                      subst hc2eq
                      cases cst1 with
                      | Bool cond =>
                        refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                fun r1 r2 hr1 hr2 => ?_⟩
                        simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                        subst hr1; subst hr2
                        cases cond <;> assumption
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VLam _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VDelay _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VConstr _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VBuiltin _ _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- ChooseUnit: matches [result, VCon Unit]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .ChooseUnit =>
    cases args1 with
    | nil =>
      cases args2 with
      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases t1 with
      | nil =>
        cases args2 with
        | nil => simp [ListValueEq] at hargs
        | cons a2 t2 =>
          cases t2 with
          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ => simp [ListValueEq] at hargs
      | cons b1 t2 =>
        cases t2 with
        | cons _ _ =>
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | nil => simp [ListValueEq] at hargs
              | cons _ _ => simp [Moist.CEK.evalBuiltinPassThrough]
        | nil =>
          -- args1 = [a1, b1], args2 must have length 2
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | cons _ _ => simp [ListValueEq] at hargs
              | nil =>
                -- args2 = [a2, b2]
                simp only [ListValueEq] at hargs
                obtain ⟨ha12, hb12, _⟩ := hargs
                -- b1 is the decision element (Unit check)
                cases b1 with
                | VCon cst1 =>
                  have hb2eq : b2 = .VCon cst1 := vcon_eq_of_valueEq_succ hb12
                  subst hb2eq
                  cases cst1 with
                  | Unit =>
                    refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                            fun r1 r2 hr1 hr2 => ?_⟩
                    simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                    subst hr1; subst hr2; exact ha12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VLam _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VDelay _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VConstr _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VBuiltin _ _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- Trace: matches [result, VCon (String _)]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .Trace =>
    cases args1 with
    | nil =>
      cases args2 with
      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases t1 with
      | nil =>
        cases args2 with
        | nil => simp [ListValueEq] at hargs
        | cons a2 t2 =>
          cases t2 with
          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ => simp [ListValueEq] at hargs
      | cons b1 t2 =>
        cases t2 with
        | cons _ _ =>
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | nil => simp [ListValueEq] at hargs
              | cons _ _ => simp [Moist.CEK.evalBuiltinPassThrough]
        | nil =>
          -- args1 = [a1, b1]
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | cons _ _ => simp [ListValueEq] at hargs
              | nil =>
                -- args2 = [a2, b2]
                simp only [ListValueEq] at hargs
                obtain ⟨ha12, hb12, _⟩ := hargs
                -- b1 is decision element (String check)
                cases b1 with
                | VCon cst1 =>
                  have hb2eq : b2 = .VCon cst1 := vcon_eq_of_valueEq_succ hb12
                  subst hb2eq
                  cases cst1 with
                  | String _ =>
                    refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                            fun r1 r2 hr1 hr2 => ?_⟩
                    simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                    subst hr1; subst hr2; exact ha12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VLam _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VDelay _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VConstr _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VBuiltin _ _ _ =>
                  cases b2 with
                  | VCon _ => simp [ValueEq] at hb12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- ChooseData: matches [bCase, iCase, listCase, mapCase, constrCase, VCon (Data d)]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .ChooseData =>
    -- Need exactly 6 args; f1 = 6th = decision element
    cases args1 with
    | nil =>
      cases args2 with
      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases t1 with
      | nil =>
        cases args2 with
        | nil => simp [ListValueEq] at hargs
        | cons a2 t2 =>
          cases t2 with
          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ => simp [ListValueEq] at hargs
      | cons b1 t2 =>
        cases t2 with
        | nil =>
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | nil => simp [Moist.CEK.evalBuiltinPassThrough]
              | cons _ _ => simp [ListValueEq] at hargs
        | cons c1 t3 =>
          cases t3 with
          | nil =>
            cases args2 with
            | nil => simp [ListValueEq] at hargs
            | cons a2 t2' =>
              cases t2' with
              | nil => simp [ListValueEq] at hargs
              | cons b2 t3' =>
                cases t3' with
                | nil => simp [ListValueEq] at hargs
                | cons c2 t4 =>
                  cases t4 with
                  | nil => simp [Moist.CEK.evalBuiltinPassThrough]
                  | cons _ _ => simp [ListValueEq] at hargs
          | cons d1 t4 =>
            cases t4 with
            | nil =>
              cases args2 with
              | nil => simp [ListValueEq] at hargs
              | cons a2 t2' =>
                cases t2' with
                | nil => simp [ListValueEq] at hargs
                | cons b2 t3' =>
                  cases t3' with
                  | nil => simp [ListValueEq] at hargs
                  | cons c2 t4' =>
                    cases t4' with
                    | nil => simp [ListValueEq] at hargs
                    | cons d2 t5 =>
                      cases t5 with
                      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
                      | cons _ _ => simp [ListValueEq] at hargs
            | cons e1 t5 =>
              cases t5 with
              | nil =>
                cases args2 with
                | nil => simp [ListValueEq] at hargs
                | cons a2 t2' =>
                  cases t2' with
                  | nil => simp [ListValueEq] at hargs
                  | cons b2 t3' =>
                    cases t3' with
                    | nil => simp [ListValueEq] at hargs
                    | cons c2 t4' =>
                      cases t4' with
                      | nil => simp [ListValueEq] at hargs
                      | cons d2 t5' =>
                        cases t5' with
                        | nil => simp [ListValueEq] at hargs
                        | cons e2 t6 =>
                          cases t6 with
                          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
                          | cons _ _ => simp [ListValueEq] at hargs
              | cons f1 t6 =>
                cases t6 with
                | cons _ _ =>
                  -- args1.length >= 7
                  cases args2 with
                  | nil => simp [ListValueEq] at hargs
                  | cons a2 t2' =>
                    cases t2' with
                    | nil => simp [ListValueEq] at hargs
                    | cons b2 t3' =>
                      cases t3' with
                      | nil => simp [ListValueEq] at hargs
                      | cons c2 t4' =>
                        cases t4' with
                        | nil => simp [ListValueEq] at hargs
                        | cons d2 t5' =>
                          cases t5' with
                          | nil => simp [ListValueEq] at hargs
                          | cons e2 t6' =>
                            cases t6' with
                            | nil => simp [ListValueEq] at hargs
                            | cons f2 t7 =>
                              cases t7 with
                              | nil => simp [ListValueEq] at hargs
                              | cons _ _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | nil =>
                  -- args1 = [a1, b1, c1, d1, e1, f1]
                  cases args2 with
                  | nil => simp [ListValueEq] at hargs
                  | cons a2 t2' =>
                    cases t2' with
                    | nil => simp [ListValueEq] at hargs
                    | cons b2 t3' =>
                      cases t3' with
                      | nil => simp [ListValueEq] at hargs
                      | cons c2 t4' =>
                        cases t4' with
                        | nil => simp [ListValueEq] at hargs
                        | cons d2 t5' =>
                          cases t5' with
                          | nil => simp [ListValueEq] at hargs
                          | cons e2 t6' =>
                            cases t6' with
                            | nil => simp [ListValueEq] at hargs
                            | cons f2 t7 =>
                              cases t7 with
                              | cons _ _ => simp [ListValueEq] at hargs
                              | nil =>
                                -- args2 = [a2, b2, c2, d2, e2, f2]
                                simp only [ListValueEq] at hargs
                                obtain ⟨ha12, hb12, hc12, hd12, he12, hf12, _⟩ := hargs
                                -- f1 is the Data decision element
                                cases f1 with
                                | VCon cst1 =>
                                  have hf2eq : f2 = .VCon cst1 :=
                                    vcon_eq_of_valueEq_succ hf12
                                  subst hf2eq
                                  cases cst1 with
                                  | Data d =>
                                    cases d with
                                    | Constr _ _ =>
                                      refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                              fun r1 r2 hr1 hr2 => ?_⟩
                                      simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                                      subst hr1; subst hr2; exact he12
                                    | Map _ =>
                                      refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                              fun r1 r2 hr1 hr2 => ?_⟩
                                      simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                                      subst hr1; subst hr2; exact hd12
                                    | List _ =>
                                      refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                              fun r1 r2 hr1 hr2 => ?_⟩
                                      simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                                      subst hr1; subst hr2; exact hc12
                                    | I _ =>
                                      refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                              fun r1 r2 hr1 hr2 => ?_⟩
                                      simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                                      subst hr1; subst hr2; exact hb12
                                    | B _ =>
                                      refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                              fun r1 r2 hr1 hr2 => ?_⟩
                                      simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                                      subst hr1; subst hr2; exact ha12
                                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                                | VLam _ _ =>
                                  cases f2 with
                                  | VCon _ => simp [ValueEq] at hf12
                                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                                | VDelay _ _ =>
                                  cases f2 with
                                  | VCon _ => simp [ValueEq] at hf12
                                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                                | VConstr _ _ =>
                                  cases f2 with
                                  | VCon _ => simp [ValueEq] at hf12
                                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                                | VBuiltin _ _ _ =>
                                  cases f2 with
                                  | VCon _ => simp [ValueEq] at hf12
                                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- ChooseList: matches [consCase, nilCase, VCon (ConstDataList l)]
  --          or        [consCase, nilCase, VCon (ConstList l)]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .ChooseList =>
    cases args1 with
    | nil =>
      cases args2 with
      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases t1 with
      | nil =>
        cases args2 with
        | nil => simp [ListValueEq] at hargs
        | cons a2 t2 =>
          cases t2 with
          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ => simp [ListValueEq] at hargs
      | cons b1 t2 =>
        cases t2 with
        | nil =>
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | nil => simp [Moist.CEK.evalBuiltinPassThrough]
              | cons _ _ => simp [ListValueEq] at hargs
        | cons c1 t3 =>
          cases t3 with
          | cons _ _ =>
            cases args2 with
            | nil => simp [ListValueEq] at hargs
            | cons a2 t2' =>
              cases t2' with
              | nil => simp [ListValueEq] at hargs
              | cons b2 t3' =>
                cases t3' with
                | nil => simp [ListValueEq] at hargs
                | cons c2 t4 =>
                  cases t4 with
                  | nil => simp [ListValueEq] at hargs
                  | cons _ _ => simp [Moist.CEK.evalBuiltinPassThrough]
          | nil =>
            -- args1 = [a1, b1, c1]
            cases args2 with
            | nil => simp [ListValueEq] at hargs
            | cons a2 t2' =>
              cases t2' with
              | nil => simp [ListValueEq] at hargs
              | cons b2 t3' =>
                cases t3' with
                | nil => simp [ListValueEq] at hargs
                | cons c2 t4 =>
                  cases t4 with
                  | cons _ _ => simp [ListValueEq] at hargs
                  | nil =>
                    -- args2 = [a2, b2, c2]
                    simp only [ListValueEq] at hargs
                    obtain ⟨ha12, hb12, hc12, _⟩ := hargs
                    -- c1 is the decision element (ConstDataList or ConstList)
                    cases c1 with
                    | VCon cst1 =>
                      have hc2eq : c2 = .VCon cst1 := vcon_eq_of_valueEq_succ hc12
                      subst hc2eq
                      cases cst1 with
                      | ConstDataList l =>
                        refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                fun r1 r2 hr1 hr2 => ?_⟩
                        simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                        subst hr1; subst hr2
                        cases l.isEmpty <;> assumption
                      | ConstList l =>
                        refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                                fun r1 r2 hr1 hr2 => ?_⟩
                        simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                        subst hr1; subst hr2
                        cases l.isEmpty <;> assumption
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VLam _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VDelay _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VConstr _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VBuiltin _ _ _ =>
                      cases c2 with
                      | VCon _ => simp [ValueEq] at hc12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- MkCons: matches [VCon (ConstList tail), elem]
  --   result = VCon (ConstList (c :: tail)) when elem = VCon c, else none
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .MkCons =>
    cases args1 with
    | nil =>
      cases args2 with
      | nil => simp [Moist.CEK.evalBuiltinPassThrough]
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases t1 with
      | nil =>
        cases args2 with
        | nil => simp [ListValueEq] at hargs
        | cons a2 t2 =>
          cases t2 with
          | nil => simp [Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ => simp [ListValueEq] at hargs
      | cons b1 t2 =>
        cases t2 with
        | cons _ _ =>
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | nil => simp [ListValueEq] at hargs
              | cons _ _ => simp [Moist.CEK.evalBuiltinPassThrough]
        | nil =>
          -- args1 = [a1, b1]
          cases args2 with
          | nil => simp [ListValueEq] at hargs
          | cons a2 t2' =>
            cases t2' with
            | nil => simp [ListValueEq] at hargs
            | cons b2 t3 =>
              cases t3 with
              | cons _ _ => simp [ListValueEq] at hargs
              | nil =>
                -- args2 = [a2, b2]
                simp only [ListValueEq] at hargs
                obtain ⟨ha12, hb12, _⟩ := hargs
                -- a1 is the first element (ConstList tail or not)
                cases a1 with
                | VCon cst1 =>
                  have ha2eq : a2 = .VCon cst1 := vcon_eq_of_valueEq_succ ha12
                  subst ha2eq
                  cases cst1 with
                  | ConstList tail =>
                    -- b1 is the element to prepend; must be VCon for success
                    cases b1 with
                    | VCon ec1 =>
                      have hb2eq : b2 = .VCon ec1 := vcon_eq_of_valueEq_succ hb12
                      subst hb2eq
                      refine ⟨by simp [Moist.CEK.evalBuiltinPassThrough],
                              fun r1 r2 hr1 hr2 => ?_⟩
                      simp [Moist.CEK.evalBuiltinPassThrough] at hr1 hr2
                      subst hr1; subst hr2; simp [ValueEq]
                    | VLam _ _ =>
                      cases b2 with
                      | VCon _ => simp [ValueEq] at hb12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VDelay _ _ =>
                      cases b2 with
                      | VCon _ => simp [ValueEq] at hb12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VConstr _ _ =>
                      cases b2 with
                      | VCon _ => simp [ValueEq] at hb12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                    | VBuiltin _ _ _ =>
                      cases b2 with
                      | VCon _ => simp [ValueEq] at hb12
                      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VLam _ _ =>
                  cases a2 with
                  | VCon _ => simp [ValueEq] at ha12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VDelay _ _ =>
                  cases a2 with
                  | VCon _ => simp [ValueEq] at ha12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VConstr _ _ =>
                  cases a2 with
                  | VCon _ => simp [ValueEq] at ha12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
                | VBuiltin _ _ _ =>
                  cases a2 with
                  | VCon _ => simp [ValueEq] at ha12
                  | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  -- All other builtins: evalBuiltinPassThrough returns none for both sides
  -- simp [evalBuiltinPassThrough] closes the entire AND goal.
  -- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  | .AddInteger | .SubtractInteger | .MultiplyInteger | .DivideInteger
  | .QuotientInteger | .RemainderInteger | .ModInteger
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger
  | .AppendByteString | .EqualsByteString | .LessThanByteString
  | .LessThanEqualsByteString | .ConsByteString | .IndexByteString
  | .SliceByteString | .LengthOfByteString
  | .Sha2_256 | .Sha3_256 | .Blake2b_256
  | .VerifyEd25519Signature
  | .AppendString | .EqualsString | .EncodeUtf8 | .DecodeUtf8
  | .FstPair | .SndPair
  | .HeadList | .TailList | .NullList
  | .ConstrData | .MapData | .ListData | .IData | .BData
  | .UnConstrData | .UnMapData | .UnListData | .UnIData | .UnBData
  | .EqualsData | .MkPairData | .MkNilData | .MkNilPairData
  | .SerializeData
  | .VerifyEcdsaSecp256k1Signature | .VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add | .Bls12_381_G1_scalarMul | .Bls12_381_G1_equal
  | .Bls12_381_G1_hashToGroup | .Bls12_381_G1_neg | .Bls12_381_G1_compress
  | .Bls12_381_G1_uncompress
  | .Bls12_381_G2_add | .Bls12_381_G2_scalarMul | .Bls12_381_G2_equal
  | .Bls12_381_G2_hashToGroup | .Bls12_381_G2_neg | .Bls12_381_G2_compress
  | .Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop | .Bls12_381_mulMlResult | .Bls12_381_finalVerify
  | .Keccak_256 | .Blake2b_224
  | .IntegerToByteString | .ByteStringToInteger
  | .AndByteString | .OrByteString | .XorByteString | .ComplementByteString
  | .ReadBit | .WriteBits | .ReplicateByte
  | .ShiftByteString | .RotateByteString | .CountSetBits | .FindFirstSetBit
  | .Ripemd_160 | .ExpModInteger
  | .DropList | .IndexArray | .LengthOfArray | .ListToArray
  | .InsertCoin | .LookupCoin | .ScaleValue | .UnionValue | .ValueContains
  | .ValueData | .UnValueData
  | .Bls12_381_G1_multiScalarMul | .Bls12_381_G2_multiScalarMul =>
    simp [Moist.CEK.evalBuiltinPassThrough]

/-- Same-level evalBuiltin congruence: when `ListValueEq (k+1) args1 args2`,
    `evalBuiltin b args1` and `evalBuiltin b args2` agree on `none` and produce
    `ValueEq (k+1)`-related results (NOT `ValueEq k`).

    This is stronger than `evalBuiltin_cong` which drops one level. The key
    insight is that `evalBuiltin` returns either a `VCon c` (from the
    `evalBuiltinConst` path, where both sides compute the same constant since
    `extractConsts` are equal) or a passthrough element from the arg list
    (which is `ValueEq (k+1)` from the hypothesis).

    The `none ↔ none` part uses chaining via the existing `evalBuiltin_cong`
    and `evalBuiltin_cong_first`. The value part is sorry'd pending a proof
    that passthrough results preserve the input level. -/
private theorem evalBuiltin_cong_same_level (k : Nat) (b : BuiltinFun)
    (args1 args2 : List CekValue)
    (hargs : ListValueEq (k + 1) args1 args2)
    (veq_refl_k : ∀ v : CekValue, ValueEq (k + 1) v v) :
    (Moist.CEK.evalBuiltin b args1 = none ↔
     Moist.CEK.evalBuiltin b args2 = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b args1 = some r1 →
              Moist.CEK.evalBuiltin b args2 = some r2 →
              ValueEq (k + 1) r1 r2) := by
  -- none ↔ none: chain via intermediate (args1[0] :: args2[1:])
  -- For length 0: both return none trivially.
  -- For length ≥ 1: use evalBuiltin_cong_first + evalBuiltin_cong.
  -- Value part: when both return some, the result is either from the const
  -- path (same VCon) or the passthrough path (input element at ValueEq (k+1)).
  constructor
  · -- none ↔ none: chain via intermediate
    cases args1 with
    | nil =>
      cases args2 with
      | nil => exact Iff.rfl
      | cons _ _ => simp [ListValueEq] at hargs
    | cons a1 t1 =>
      cases args2 with
      | nil => simp [ListValueEq] at hargs
      | cons a2 t2 =>
        simp only [ListValueEq] at hargs
        have h1 := (Moist.Verified.Congruence.evalBuiltin_cong_first k b a1 a2 t1 hargs.1).1
        have h2 := (Moist.Verified.Congruence.evalBuiltin_cong k b a2 t1 t2 hargs.2).1
        exact h1.trans h2
  · -- Value agreement at level k+1
    intro r1 r2 hr1 hr2
    have ⟨hpt_isNone, hpt_val⟩ := evalBuiltinPassThrough_cong_same_level b hargs veq_refl_k
    have hec := extractConsts_eq_of_listValueEq hargs
    -- Unfold evalBuiltin to inspect the passthrough vs const path
    simp only [Moist.CEK.evalBuiltin] at hr1 hr2
    cases hp1 : Moist.CEK.evalBuiltinPassThrough b args1 with
    | some v1 =>
      -- passthrough succeeded on args1; by isNone agreement, also on args2
      rw [show (Moist.CEK.evalBuiltinPassThrough b args1).isNone = false from by simp [hp1]] at hpt_isNone
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b args2 with
      | none => simp [hp2] at hpt_isNone
      | some v2 =>
        rw [hp1] at hr1; rw [hp2] at hr2
        injection hr1 with hr1; injection hr2 with hr2
        subst hr1; subst hr2
        exact hpt_val v1 v2 hp1 hp2
    | none =>
      rw [hp1] at hr1
      -- passthrough failed on args1; by isNone agreement, also on args2
      rw [show (Moist.CEK.evalBuiltinPassThrough b args1).isNone = true from by simp [hp1]] at hpt_isNone
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b args2 with
      | some v2 => simp [hp2] at hpt_isNone
      | none =>
        rw [hp2] at hr2
        -- Both fall through to extractConsts → evalBuiltinConst path.
        rw [hec] at hr1
        cases hc : Moist.CEK.extractConsts args2 with
        | none => simp [hc] at hr1
        | some cs =>
          simp only [hc] at hr1 hr2
          cases hbc : Moist.CEK.evalBuiltinConst b cs with
          | none => simp [hbc] at hr1
          | some c =>
            simp only [hbc] at hr1 hr2
            injection hr1 with hr1; injection hr2 with hr2
            subst hr1; subst hr2
            exact veq_refl_k _

-- stepCompat_lift_body removed (dead code)

/-- **Generalized fundamental lemma**: if two states are `StateEq k`-related,
    they are `AsymCompat k n` for `n ≤ k`.

    Proved by well-founded induction on `(k, n)` lexicographically.
    The outer induction on `k` provides the fundamental lemma at lower
    step indices (needed for VLam/VDelay closure creation and anti-mono).
    The inner induction on `n` reduces `n+1` to `n` by analyzing one step. -/
theorem stateEq_stepCompat
    (k n : Nat) (hn : n ≤ k)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    {s1 s2 : State} (hrel : StateEq k s1 s2) :
    AsymCompat k n s1 s2 := by
  -- Helper to convert StepCompat to AsymCompat
  have sc_to_ac : ∀ {k' n' : Nat} {s1' s2' : State}, n' ≤ k' →
      StepCompat k' n' s1' s2' → AsymCompat k' n' s1' s2' :=
    fun hn' h => stepCompat_to_asymCompat hn' h
  match n with
  | 0 =>
    simp only [AsymCompat, steps]
    cases hrel with
    | error =>
      exact ⟨fun _ => ⟨0, hn, rfl⟩, fun v h => by simp at h,
             fun _ => ⟨0, hn, rfl⟩, fun v h => by simp at h⟩
    | halt hv =>
      exact ⟨fun h => by simp at h,
             fun v1 h => by injection h with h; subst h; exact ⟨_, 0, hn, rfl, hv⟩,
             fun h => by simp at h,
             fun v2 h => by injection h with h; subst h; exact ⟨_, 0, hn, rfl, hv⟩⟩
    | compute _ _ =>
      exact ⟨fun h => by simp at h, fun v h => by simp at h,
             fun h => by simp at h, fun v h => by simp at h⟩
    | ret _ _ =>
      exact ⟨fun h => by simp at h, fun v h => by simp at h,
             fun h => by simp at h, fun v h => by simp at h⟩
  | n + 1 =>
    -- n+1 ≤ k, so k ≥ 1
    obtain ⟨km, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hn' : n ≤ km := by omega
    -- Reduce to AsymCompat km n (step s1) (step s2) via level-dropping step
    apply asymCompat_step_lower
    -- Helper to call recursively at level km, step n
    have call_n : ∀ {s1' s2' : State}, StateEq km s1' s2' → AsymCompat km n s1' s2' :=
      fun hrel' => stateEq_stepCompat km n hn' (fun j hj v => veq_refl j (by omega) v) hrel'
    -- Variant that downgrades from StateEq (km+1) to StateEq km
    have call_n' : ∀ {s1' s2' : State}, StateEq (km + 1) s1' s2' → AsymCompat km n s1' s2' :=
      fun hrel' => call_n (stateEq_mono (by omega) hrel')
    -- Helper: build ValueEq (km+1) for same-body VLam
    have vlam_valueEq : ∀ {body : Term} {env1 env2 : CekEnv},
        EnvEq (km + 1) env1 env2 → ValueEq (km + 1) (.VLam body env1) (.VLam body env2) := by
      intro body env1 env2 henv
      unfold ValueEq
      intro j hj arg1 arg2 harg stk1 stk2 hstk
      have henv_j : EnvEq j env1 env2 := envEq_mono (by omega) henv
      have henv1_j : EnvEq j (env1.extend arg1) (env2.extend arg2) := envEq_extend henv_j harg
      have hstk_j : StackEq j stk1 stk2 := stackEqR_to_stackEq hstk
      have hrel_j : StateEq j (.compute stk1 (env1.extend arg1) body)
          (.compute stk2 (env2.extend arg2) body) :=
        .compute hstk_j henv1_j
      exact ⟨fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).1 he,
             fun v1 n' hn' hv1 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.1 v1 hv1,
             fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.1 he,
             fun v2 n' hn' hv2 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.2 v2 hv2⟩
    -- Helper: build ValueEq (km+1) for same-body VDelay
    have vdelay_valueEq : ∀ {body : Term} {env1 env2 : CekEnv},
        EnvEq (km + 1) env1 env2 → ValueEq (km + 1) (.VDelay body env1) (.VDelay body env2) := by
      intro body env1 env2 henv
      unfold ValueEq
      intro j hj stk1 stk2 hstk
      have henv_j : EnvEq j env1 env2 := envEq_mono (by omega) henv
      have hstk_j : StackEq j stk1 stk2 := stackEqR_to_stackEq hstk
      have hrel_j : StateEq j (.compute stk1 env1 body)
          (.compute stk2 env2 body) :=
        .compute hstk_j henv_j
      exact ⟨fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).1 he,
             fun v1 n' hn' hv1 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.1 v1 hv1,
             fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.1 he,
             fun v2 n' hn' hv2 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.2 v2 hv2⟩
    -- Helper: build ValueEq (km+1) for same-constructor VConstr from ListValueEq km
    have vconstr_valueEq : ∀ {tag : Nat} {fs1 fs2 : List CekValue},
        ListValueEq km fs1 fs2 → ValueEq (km + 1) (.VConstr tag fs1) (.VConstr tag fs2) := by
      intro tag fs1 fs2 hfs
      unfold ValueEq
      exact ⟨rfl, hfs⟩
    -- Helper: ListValueEq reflexivity using veq_refl
    have listValueEq_refl_local : ∀ (j : Nat) (_ : j ≤ km + 1) (vs : List CekValue), ListValueEq j vs vs := by
      intro j hj vs
      induction vs with
      | nil => simp [ListValueEq]
      | cons v rest ih => simp only [ListValueEq]; exact ⟨veq_refl j (by omega) v, ih⟩
    -- Now case split on hrel
    cases hrel with
    | error =>
      simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
    | halt hv =>
      simp only [step]
      exact sc_to_ac hn' (stepCompat_halt km n _ _ (valueEq_mono (km - n) (km + 1) (by omega) _ _ hv))
    | compute hstk henv =>
      rename_i s1' s2' env1 env2 t
      cases t with
      | Var idx =>
        have hlookup := envEq_lookup henv idx
        simp only [step]
        generalize h1 : env1.lookup idx = r1
        generalize h2 : env2.lookup idx = r2
        rw [h1, h2] at hlookup
        match r1, r2, hlookup with
        | some v1, some v2, hveq => exact call_n' (.ret hstk hveq)
        | none, none, _ => exact sc_to_ac hn' (stepCompat_error km n)
        | some _, none, hf => exact hf.elim
        | none, some _, hf => exact hf.elim
      | Constant pair =>
        obtain ⟨c, _⟩ := pair
        simp only [step]
        exact call_n' (.ret hstk (veq_refl (km + 1) (Nat.le_refl _) (.VCon c)))
      | Builtin b =>
        simp only [step]
        exact call_n' (.ret hstk (veq_refl (km + 1) (Nat.le_refl _) (.VBuiltin b [] _)))
      | Lam _ body =>
        simp only [step]
        exact call_n' (.ret hstk (vlam_valueEq henv))
      | Delay body =>
        simp only [step]
        exact call_n' (.ret hstk (vdelay_valueEq henv))
      | Force e =>
        simp only [step]
        exact call_n' (.compute (.cons .force hstk) henv)
      | Apply f x =>
        simp only [step]
        exact call_n' (.compute (.cons (.arg henv) hstk) henv)
      | Error =>
        simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
      | Constr tag args =>
        cases args with
        | nil =>
          simp only [step]
          exact call_n' (.ret hstk (veq_refl (km + 1) (Nat.le_refl _) (.VConstr tag [])))
        | cons m ms =>
          simp only [step]
          exact call_n' (.compute
            (.cons (.constrField (by simp [ListValueEq]) henv) hstk) henv)
      | Case scrut alts =>
        simp only [step]
        exact call_n' (.compute (.cons (.caseScrutinee henv) hstk) henv)
    | ret hstk hv =>
      rename_i s1' s2' v1 v2
      cases hstk with
      | nil =>
        simp only [step]
        exact sc_to_ac hn' (stepCompat_halt km n v1 v2 (valueEq_mono (km - n) (km + 1) (by omega) _ _ hv))
      | cons hframe hrest =>
        rename_i f1 f2 rest1 rest2
        cases hframe with
        | force =>
          cases v1 with
          | VDelay body1 env1 =>
            cases v2 with
            | VDelay body2 env2 =>
              simp only [step]
              -- hv : ValueEq (km+1) (VDelay body1 env1) (VDelay body2 env2)
              -- Extract the 4-tuple from the VDelay clause
              unfold ValueEq at hv
              have hrest_km : StackEq km rest1 rest2 := stackEq_mono (by omega) hrest
              have hclause := hv km (by omega) rest1 rest2 (stackEq_to_stackEqR hrest_km)
              exact ⟨hclause.1 n hn',
                     fun v1' hv1' => hclause.2.1 v1' n hn' hv1',
                     hclause.2.2.1 n hn',
                     fun v2' hv2' => hclause.2.2.2 v2' n hn' hv2'⟩
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEq at hv
              obtain ⟨hb, hargs, hea⟩ := hv
              subst hb; subst hea
              simp only [step]
              cases h_head : ea1.head with
              | argQ =>
                simp only [h_head]
                cases h_tail : ea1.tail with
                | none =>
                  simp only [h_tail]
                  -- Saturation: evalBuiltin b1 args1 / evalBuiltin b1 args2
                  -- hargs : ListValueEq (km+1) args1 args2
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level km b1 args1 args2 hargs
                      (veq_refl (km + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 args1 with
                  | none =>
                    simp only [h_eval1, heval_none.mp h_eval1]
                    exact sc_to_ac hn' (stepCompat_error km n)
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 args2 with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only [h_eval1, h_eval2]
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_n' (.ret hrest hveq)
                | some ea_rest =>
                  simp only [h_tail]
                  have hvb : ValueEq (km + 1) (.VBuiltin b1 args1 ea_rest) (.VBuiltin b1 args2 ea_rest) := by
                    unfold ValueEq; exact ⟨rfl, hargs, rfl⟩
                  exact call_n' (.ret hrest hvb)
              | argV =>
                simp only [h_head]
                exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VCon _ =>
            cases v2 with
            | VCon _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
        | arg henv_arg =>
          simp only [step]
          exact call_n' (.compute (.cons (.funV hv) hrest) henv_arg)
        | funV hfv =>
          rename_i vf1 vf2
          cases vf1 with
          | VLam body1 env1 =>
            cases vf2 with
            | VLam body2 env2 =>
              simp only [step]
              -- hfv : ValueEq (km+1) (VLam body1 env1) (VLam body2 env2)
              -- hv : ValueEq (km+1) v1 v2 (the argument)
              -- Extract the 4-tuple from the VLam clause
              unfold ValueEq at hfv
              have hv_km : ValueEq km v1 v2 := valueEq_mono km (km + 1) (by omega) v1 v2 hv
              have hrest_km : StackEq km rest1 rest2 := stackEq_mono (by omega) hrest
              have hclause := hfv km (by omega) v1 v2 hv_km rest1 rest2 (stackEq_to_stackEqR hrest_km)
              exact ⟨hclause.1 n hn',
                     fun v1' hv1' => hclause.2.1 v1' n hn' hv1',
                     hclause.2.2.1 n hn',
                     fun v2' hv2' => hclause.2.2.2 v2' n hn' hv2'⟩
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VBuiltin b1 args1 ea1 =>
            cases vf2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEq at hfv
              obtain ⟨hb, hargs, hea⟩ := hfv
              subst hb; subst hea
              simp only [step]
              cases h_head : ea1.head with
              | argV =>
                simp only [h_head]
                cases h_tail : ea1.tail with
                | none =>
                  simp only [h_tail]
                  -- Saturation: evalBuiltin b1 (v1::args1) / evalBuiltin b1 (v2::args2)
                  have hargs_new : ListValueEq (km + 1) (v1 :: args1) (v2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hv, hargs⟩
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level km b1 (v1 :: args1) (v2 :: args2)
                      hargs_new (veq_refl (km + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 (v1 :: args1) with
                  | none =>
                    simp only [h_eval1, heval_none.mp h_eval1]
                    exact sc_to_ac hn' (stepCompat_error km n)
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 (v2 :: args2) with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only [h_eval1, h_eval2]
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_n' (.ret hrest hveq)
                | some ea_rest =>
                  simp only [h_tail]
                  have hargs_new : ListValueEq (km + 1) (v1 :: args1) (v2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hv, hargs⟩
                  have hvb : ValueEq (km + 1) (.VBuiltin b1 (v1 :: args1) ea_rest)
                      (.VBuiltin b1 (v2 :: args2) ea_rest) := by
                    unfold ValueEq; exact ⟨rfl, hargs_new, rfl⟩
                  exact call_n' (.ret hrest hvb)
              | argQ =>
                simp only [h_head]
                exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VCon _ =>
            cases vf2 with
            | VCon _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VDelay _ _ =>
            cases vf2 with
            | VDelay _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VConstr _ _ =>
            cases vf2 with
            | VConstr _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
        | applyArg hvx =>
          rename_i vx1 vx2
          cases v1 with
          | VLam body1 env1 =>
            cases v2 with
            | VLam body2 env2 =>
              simp only [step]
              -- hv : ValueEq (km+1) (VLam body1 env1) (VLam body2 env2)
              -- hvx : ValueEq (km+1) vx1 vx2 (the argument on the stack)
              -- Extract the 4-tuple from the VLam clause
              unfold ValueEq at hv
              have hvx_km : ValueEq km vx1 vx2 := valueEq_mono km (km + 1) (by omega) vx1 vx2 hvx
              have hrest_km : StackEq km rest1 rest2 := stackEq_mono (by omega) hrest
              have hclause := hv km (by omega) vx1 vx2 hvx_km rest1 rest2 (stackEq_to_stackEqR hrest_km)
              exact ⟨hclause.1 n hn',
                     fun v1' hv1' => hclause.2.1 v1' n hn' hv1',
                     hclause.2.2.1 n hn',
                     fun v2' hv2' => hclause.2.2.2 v2' n hn' hv2'⟩
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEq at hv
              obtain ⟨hb, hargs, hea⟩ := hv
              subst hb; subst hea
              simp only [step]
              cases h_head : ea1.head with
              | argV =>
                simp only [h_head]
                cases h_tail : ea1.tail with
                | none =>
                  simp only [h_tail]
                  -- Saturation: evalBuiltin b1 (vx1::args1) / evalBuiltin b1 (vx2::args2)
                  have hargs_new : ListValueEq (km + 1) (vx1 :: args1) (vx2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hvx, hargs⟩
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level km b1 (vx1 :: args1) (vx2 :: args2)
                      hargs_new (veq_refl (km + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 (vx1 :: args1) with
                  | none =>
                    simp only [h_eval1, heval_none.mp h_eval1]
                    exact sc_to_ac hn' (stepCompat_error km n)
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 (vx2 :: args2) with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only [h_eval1, h_eval2]
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_n' (.ret hrest hveq)
                | some ea_rest =>
                  simp only [h_tail]
                  have hargs_new : ListValueEq (km + 1) (vx1 :: args1) (vx2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hvx, hargs⟩
                  have hvb : ValueEq (km + 1) (.VBuiltin b1 (vx1 :: args1) ea_rest)
                      (.VBuiltin b1 (vx2 :: args2) ea_rest) := by
                    unfold ValueEq; exact ⟨rfl, hargs_new, rfl⟩
                  exact call_n' (.ret hrest hvb)
              | argQ =>
                simp only [h_head]
                exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VCon _ =>
            cases v2 with
            | VCon _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
        | constrField hdone henv_cf =>
          rename_i done1 done2 env1_cf env2_cf tag todo
          cases todo with
          | nil =>
            simp only [step]
            have hv_km : ValueEq km v1 v2 := valueEq_mono km (km + 1) (by omega) v1 v2 hv
            have hdone_km : ListValueEq km done1 done2 := listValueEq_mono km (km + 1) (by omega) done1 done2 hdone
            have hfields : ListValueEq km (v1 :: done1).reverse (v2 :: done2).reverse :=
              listValueEq_cons_rev hv_km hdone_km
            exact call_n' (.ret hrest (vconstr_valueEq hfields))
          | cons m ms =>
            simp only [step]
            have hdone' : ListValueEq (km + 1) (v1 :: done1) (v2 :: done2) := by
              simp only [ListValueEq]; exact ⟨hv, hdone⟩
            exact call_n' (.compute (.cons (.constrField hdone' henv_cf) hrest) henv_cf)
        | caseScrutinee henv_cs =>
          rename_i alts
          cases v1 with
          | VConstr tag1 fields1 =>
            cases v2 with
            | VConstr tag2 fields2 =>
              unfold ValueEq at hv
              obtain ⟨htag, hfields⟩ := hv
              subst htag
              simp only [step]
              cases h_alt : alts[tag1]? with
              | none => exact sc_to_ac hn' (stepCompat_error km n)
              | some alt =>
                have hstk_km : StackEq km
                    (fields1.map Frame.applyArg ++ rest1)
                    (fields2.map Frame.applyArg ++ rest2) :=
                  stackEq_append (listValueEq_map_applyArg_stackEq hfields) (stackEq_mono (by omega) hrest)
                exact stateEq_stepCompat km n hn' (fun j hj v => veq_refl j (by omega) v)
                  (.compute hstk_km (envEq_mono (by omega) henv_cs))
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VCon c1 =>
            cases v2 with
            | VCon c2 =>
              unfold ValueEq at hv
              subst hv
              simp only [step]
              cases h_ctf : Moist.CEK.constToTagAndFields c1 with
              | none => exact sc_to_ac hn' (stepCompat_error km n)
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple
                by_cases hcond : numCtors > 0 && alts.length > numCtors
                · simp only [hcond, if_true]
                  exact sc_to_ac hn' (stepCompat_error km n)
                · simp only [Bool.not_eq_true] at hcond
                  simp only [hcond, if_false]
                  cases h_alt : alts[tag]? with
                  | none => exact sc_to_ac hn' (stepCompat_error km n)
                  | some alt =>
                    have hfields_refl : ListValueEq (km + 1) fields fields :=
                      listValueEq_refl_local (km + 1) (by omega) fields
                    exact call_n' (.compute
                      (stackEq_append (listValueEq_map_applyArg_stackEq hfields_refl) hrest)
                      henv_cs)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VBuiltin _ _ _ =>
            cases v2 with
            | VBuiltin _ _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hv; exact hv.elim
termination_by (k, n)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Empty-stack version for the original interface. -/
theorem gen_fundamental_lemma
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v) :
    ∀ (body : Term) (env1 env2 : CekEnv),
    EnvEq k env1 env2 → ∀ n, n ≤ k →
    AsymCompat k n (.compute [] env1 body) (.compute [] env2 body) := by
  intro body env1 env2 henv n hn
  exact stateEq_stepCompat k n hn veq_refl (.compute .nil henv)

/-! ## Extraction: the original fundamental lemma -/

/-- The fundamental lemma as stated in FundamentalLemma.lean, derived from
    the generalized version. With decaying AsymCompat, results after `n`
    steps from budget `k` are matched by the other side within `k` steps,
    with values related at `ValueEq (k - n)`. -/
theorem fundamental_lemma_proved (k : Nat)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEq k arg1 arg2)
    (n : Nat) (hn : n ≤ k) :
    (steps n (.compute [] (env.extend arg1) body) = .error →
      ∃ m, m ≤ k ∧ steps m (.compute [] (env.extend arg2) body) = .error) ∧
    (∀ v1, steps n (.compute [] (env.extend arg1) body) = .halt v1 →
      ∃ v2 m, m ≤ k ∧ steps m (.compute [] (env.extend arg2) body) = .halt v2 ∧
        ValueEq (k - n) v1 v2) ∧
    (steps n (.compute [] (env.extend arg2) body) = .error →
      ∃ m, m ≤ k ∧ steps m (.compute [] (env.extend arg1) body) = .error) ∧
    (∀ v2, steps n (.compute [] (env.extend arg2) body) = .halt v2 →
      ∃ v1 m, m ≤ k ∧ steps m (.compute [] (env.extend arg1) body) = .halt v1 ∧
        ValueEq (k - n) v1 v2) := by
  have henv : EnvEq k (env.extend arg1) (env.extend arg2) :=
    envEq_extend (envEq_refl veq_refl env) hargs
  exact gen_fundamental_lemma veq_refl body _ _ henv n hn

/-- The delay variant of the fundamental lemma: same body, same env,
    related stacks. Proved by building `StateEq` from `EnvEq` (refl on env). -/
theorem fundamental_lemma_delay_proved (k : Nat)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    (body : Term) (env : CekEnv)
    (stk1 stk2 : Stack) (hstk : StackEqR (ValueEq k) stk1 stk2)
    (n : Nat) (hn : n ≤ k) :
    AsymCompat k n (.compute stk1 env body) (.compute stk2 env body) := by
  have henv : EnvEq k env env := envEq_refl veq_refl env
  exact stateEq_stepCompat k n hn veq_refl (.compute (stackEqR_to_stackEq hstk) henv)

/-! ## Standalone reflexivity (no veq_refl parameter)

`ValueEq k v v` holds for all `k` and `v`. Proved by well-founded induction
on `(k, sizeOf v)`: VLam/VDelay at level `k+1` delegate to `stateEq_stepCompat`
at level `≤ k` (Nat decreases); VBuiltin/VConstr at level `k+1` delegate to
`listValueEq_refl_proved` on structurally smaller values (sizeOf decreases). -/

mutual
  theorem valueEq_refl_proved : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | k + 1, .VLam body env => by
      unfold ValueEq; intro j hj arg1 arg2 hargs stk1 stk2 hstk
      have veq : ∀ i, i ≤ j → ∀ w : CekValue, ValueEq i w w :=
        fun i hi w => valueEq_refl_proved i w
      have hrel : StateEq j (.compute stk1 (env.extend arg1) body)
          (.compute stk2 (env.extend arg2) body) :=
        .compute (stackEqR_to_stackEq hstk) (envEq_extend (envEq_refl veq env) hargs)
      exact ⟨fun n hn he => (stateEq_stepCompat j n hn veq hrel).1 he,
             fun v1 n hn hv1 => (stateEq_stepCompat j n hn veq hrel).2.1 v1 hv1,
             fun n hn he => (stateEq_stepCompat j n hn veq hrel).2.2.1 he,
             fun v2 n hn hv2 => (stateEq_stepCompat j n hn veq hrel).2.2.2 v2 hv2⟩
    | k + 1, .VDelay body env => by
      unfold ValueEq; intro j hj stk1 stk2 hstk
      have veq : ∀ i, i ≤ j → ∀ w : CekValue, ValueEq i w w :=
        fun i hi w => valueEq_refl_proved i w
      have hrel : StateEq j (.compute stk1 env body)
          (.compute stk2 env body) :=
        .compute (stackEqR_to_stackEq hstk) (envEq_refl veq env)
      exact ⟨fun n hn he => (stateEq_stepCompat j n hn veq hrel).1 he,
             fun v1 n hn hv1 => (stateEq_stepCompat j n hn veq hrel).2.1 v1 hv1,
             fun n hn he => (stateEq_stepCompat j n hn veq hrel).2.2.1 he,
             fun v2 n hn hv2 => (stateEq_stepCompat j n hn veq hrel).2.2.2 v2 hv2⟩
    | _ + 1, .VConstr _ fields => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl_proved _ fields⟩
    | _ + 1, .VBuiltin b args ea => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl_proved _ args, rfl⟩
  termination_by k v => (k, sizeOf v)
  theorem listValueEq_refl_proved : ∀ (k : Nat) (vs : List CekValue), ListValueEq k vs vs
    | _, [] => by simp [ListValueEq]
    | k, v :: vs => by simp only [ListValueEq]; exact ⟨valueEq_refl_proved k v, listValueEq_refl_proved k vs⟩
  termination_by k vs => (k, sizeOf vs)
end

/-! ## Parameter-free wrappers -/

private def veq_refl_of (k : Nat) : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v :=
  fun j _ v => valueEq_refl_proved j v

/-- `stateEq_stepCompat` without the `veq_refl` parameter. -/
theorem stateEq_stepCompat' (k n : Nat) (hn : n ≤ k)
    {s1 s2 : State} (hrel : StateEq k s1 s2) :
    AsymCompat k n s1 s2 :=
  stateEq_stepCompat k n hn (veq_refl_of k) hrel

/-- `envEq_refl` without the `veq_refl` parameter. -/
theorem envEq_refl' {k : Nat} (env : CekEnv) : EnvEq k env env :=
  envEq_refl (veq_refl_of k) env

/-- The fundamental lemma without `veq_refl` parameter. -/
theorem fundamental_lemma_proved' (k : Nat)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEq k arg1 arg2)
    (n : Nat) (hn : n ≤ k) :
    (steps n (.compute [] (env.extend arg1) body) = .error →
      ∃ m, m ≤ k ∧ steps m (.compute [] (env.extend arg2) body) = .error) ∧
    (∀ v1, steps n (.compute [] (env.extend arg1) body) = .halt v1 →
      ∃ v2 m, m ≤ k ∧ steps m (.compute [] (env.extend arg2) body) = .halt v2 ∧
        ValueEq (k - n) v1 v2) ∧
    (steps n (.compute [] (env.extend arg2) body) = .error →
      ∃ m, m ≤ k ∧ steps m (.compute [] (env.extend arg1) body) = .error) ∧
    (∀ v2, steps n (.compute [] (env.extend arg2) body) = .halt v2 →
      ∃ v1 m, m ≤ k ∧ steps m (.compute [] (env.extend arg1) body) = .halt v1 ∧
        ValueEq (k - n) v1 v2) :=
  fundamental_lemma_proved k (veq_refl_of k) body env arg1 arg2 hargs n hn

end Moist.Verified.ValueEqBisim
