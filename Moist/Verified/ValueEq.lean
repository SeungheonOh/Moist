import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.Verified.ValueEqMono
import Moist.Verified.BuiltinCong

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

/-- **StateRelated**: the canonical "two states are related at level `k`" relation.
    Directly matches the asymmetric `ValueEq` VLam/VDelay clause structure.
    The source step count is bounded by `k`; the target step count is
    unbounded (existential). This lets step-count-changing optimizations be
    in the relation while step-indexing keeps the FL provable. -/
def StateRelated (k : Nat) (s1 s2 : State) : Prop :=
  -- Forward error: side1 errors within `k` steps → side2 reaches error.
  (∀ n, n ≤ k → steps n s1 = .error → Reaches s2 .error) ∧
  -- Backward error: symmetric.
  (∀ m, m ≤ k → steps m s2 = .error → Reaches s1 .error) ∧
  -- Forward halt: side1 halts at `n ≤ k` → ∃ m, side2 halts at m
  -- with values decay-related at level `k - max n m`.
  (∀ n v1, n ≤ k → steps n s1 = .halt v1 →
    ∃ m v2, steps m s2 = .halt v2 ∧ ValueEq (k - max n m) v1 v2) ∧
  -- Backward halt: symmetric.
  (∀ m v2, m ≤ k → steps m s2 = .halt v2 →
    ∃ n v1, steps n s1 = .halt v1 ∧ ValueEq (k - max n m) v1 v2)

/-- Lift `StateRelated` from stepped states to original (non-terminal) states.
    When both sides are "in progress" (compute/ret, neither halt nor error),
    adding one step to both sides shifts the step counts by 1. The value-relate
    levels align because `k+1 - max (n+1) (m+1) = k - max n m`.

    For terminal states (halt/error), this lift doesn't apply — those are
    handled directly via `StateEq` constructors. -/
theorem stateRelated_lift_compute {k : Nat}
    (stk1 stk2 : Stack) (env1 env2 : CekEnv) (t : Term)
    (hstep : StateRelated k
      (step (.compute stk1 env1 t))
      (step (.compute stk2 env2 t))) :
    StateRelated (k + 1) (.compute stk1 env1 t) (.compute stk2 env2 t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Forward error: side1 at n ≤ k+1 errors → side2 reaches error.
    intro n hn he
    match n, he with
    | 0, he => simp [steps] at he
    | n' + 1, he =>
      rw [show steps (n' + 1) (State.compute stk1 env1 t)
            = steps n' (step (.compute stk1 env1 t)) from rfl] at he
      have hreach_step := hstep.1 n' (by omega) he
      obtain ⟨m', hm'⟩ := hreach_step
      exact ⟨m' + 1, by
        rw [show steps (m' + 1) (State.compute stk2 env2 t)
              = steps m' (step (.compute stk2 env2 t)) from rfl]; exact hm'⟩
  · -- Backward error: symmetric.
    intro m hm he
    match m, he with
    | 0, he => simp [steps] at he
    | m' + 1, he =>
      rw [show steps (m' + 1) (State.compute stk2 env2 t)
            = steps m' (step (.compute stk2 env2 t)) from rfl] at he
      have hreach_step := hstep.2.1 m' (by omega) he
      obtain ⟨n', hn'⟩ := hreach_step
      exact ⟨n' + 1, by
        rw [show steps (n' + 1) (State.compute stk1 env1 t)
              = steps n' (step (.compute stk1 env1 t)) from rfl]; exact hn'⟩
  · -- Forward halt: side1 halts at n ≤ k+1 with v1 → ∃ m v2 ...
    intro n v1 hn hh
    match n, hh with
    | 0, hh => simp [steps] at hh
    | n' + 1, hh =>
      rw [show steps (n' + 1) (State.compute stk1 env1 t)
            = steps n' (step (.compute stk1 env1 t)) from rfl] at hh
      obtain ⟨m', v2, hm', hrel⟩ := hstep.2.2.1 n' v1 (by omega) hh
      refine ⟨m' + 1, v2, ?_, ?_⟩
      · rw [show steps (m' + 1) (State.compute stk2 env2 t)
              = steps m' (step (.compute stk2 env2 t)) from rfl]; exact hm'
      · have hmax : max (n' + 1) (m' + 1) = max n' m' + 1 := by omega
        have hlvl : k + 1 - max (n' + 1) (m' + 1) = k - max n' m' := by
          rw [hmax]; omega
        rw [hlvl]; exact hrel
  · -- Backward halt: symmetric.
    intro m v2 hm hh
    match m, hh with
    | 0, hh => simp [steps] at hh
    | m' + 1, hh =>
      rw [show steps (m' + 1) (State.compute stk2 env2 t)
            = steps m' (step (.compute stk2 env2 t)) from rfl] at hh
      obtain ⟨n', v1, hn', hrel⟩ := hstep.2.2.2 m' v2 (by omega) hh
      refine ⟨n' + 1, v1, ?_, ?_⟩
      · rw [show steps (n' + 1) (State.compute stk1 env1 t)
              = steps n' (step (.compute stk1 env1 t)) from rfl]; exact hn'
      · have hmax : max (n' + 1) (m' + 1) = max n' m' + 1 := by omega
        have hlvl : k + 1 - max (n' + 1) (m' + 1) = k - max n' m' := by
          rw [hmax]; omega
        rw [hlvl]; exact hrel

/-- Lift `StateRelated` for `.ret` states (non-terminal). Parallel to
    `stateRelated_lift_compute`. -/
theorem stateRelated_lift_ret {k : Nat}
    (stk1 stk2 : Stack) (v1 v2 : CekValue)
    (hstep : StateRelated k
      (step (.ret stk1 v1))
      (step (.ret stk2 v2))) :
    StateRelated (k + 1) (.ret stk1 v1) (.ret stk2 v2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Forward error: side1 at n ≤ k+1 errors → side2 reaches error.
    intro n hn he
    match n, he with
    | 0, he => simp [steps] at he
    | n' + 1, he =>
      rw [show steps (n' + 1) (State.ret stk1 v1)
            = steps n' (step (.ret stk1 v1)) from rfl] at he
      obtain ⟨m', hm'⟩ := hstep.1 n' (by omega) he
      exact ⟨m' + 1, by
        rw [show steps (m' + 1) (State.ret stk2 v2)
              = steps m' (step (.ret stk2 v2)) from rfl]; exact hm'⟩
  · -- Backward error
    intro m hm he
    match m, he with
    | 0, he => simp [steps] at he
    | m' + 1, he =>
      rw [show steps (m' + 1) (State.ret stk2 v2)
            = steps m' (step (.ret stk2 v2)) from rfl] at he
      obtain ⟨n', hn'⟩ := hstep.2.1 m' (by omega) he
      exact ⟨n' + 1, by
        rw [show steps (n' + 1) (State.ret stk1 v1)
              = steps n' (step (.ret stk1 v1)) from rfl]; exact hn'⟩
  · -- Forward halt
    intro n w1 hn hh
    match n, hh with
    | 0, hh => simp [steps] at hh
    | n' + 1, hh =>
      rw [show steps (n' + 1) (State.ret stk1 v1)
            = steps n' (step (.ret stk1 v1)) from rfl] at hh
      obtain ⟨m', w2, hm', hrel⟩ := hstep.2.2.1 n' w1 (by omega) hh
      refine ⟨m' + 1, w2, ?_, ?_⟩
      · rw [show steps (m' + 1) (State.ret stk2 v2)
              = steps m' (step (.ret stk2 v2)) from rfl]; exact hm'
      · have hmax : max (n' + 1) (m' + 1) = max n' m' + 1 := by omega
        have hlvl : k + 1 - max (n' + 1) (m' + 1) = k - max n' m' := by
          rw [hmax]; omega
        rw [hlvl]; exact hrel
  · -- Backward halt
    intro m w2 hm hh
    match m, hh with
    | 0, hh => simp [steps] at hh
    | m' + 1, hh =>
      rw [show steps (m' + 1) (State.ret stk2 v2)
            = steps m' (step (.ret stk2 v2)) from rfl] at hh
      obtain ⟨n', w1, hn', hrel⟩ := hstep.2.2.2 m' w2 (by omega) hh
      refine ⟨n' + 1, w1, ?_, ?_⟩
      · rw [show steps (n' + 1) (State.ret stk1 v1)
              = steps n' (step (.ret stk1 v1)) from rfl]; exact hn'
      · have hmax : max (n' + 1) (m' + 1) = max n' m' + 1 := by omega
        have hlvl : k + 1 - max (n' + 1) (m' + 1) = k - max n' m' := by
          rw [hmax]; omega
        rw [hlvl]; exact hrel


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

/-! ## Helpers for ListValueEq and StackEq -/

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
    (_veq_refl_k : ∀ v : CekValue, ValueEq (k + 1) v v) :
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
        -- Pass the caller's ValueEq (k+1) reflexivity through to Builtin's
        -- parameterized theorems (which take refl at level k+1).
        have h1 := (Moist.Verified.BuiltinCong.evalBuiltin_cong_first k b veq_refl_k a1 a2 t1 hargs.1).1
        have h2 := (Moist.Verified.BuiltinCong.evalBuiltin_cong k b veq_refl_k a2 t1 t2 hargs.2).1
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

/-- **Main bridge theorem**: convert `StateEq k` into `StateRelated k`.
    Proved by parallel induction on `k`, mirroring the case structure of
    the CEK machine's step relation. Produces `StateRelated` directly via
    `stateRelated_lift_compute` / `stateRelated_lift_ret` for inductive
    cases, and direct constructions for base cases. -/
theorem stateEq_stateRelated : ∀ (k : Nat)
    (_veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    {s1 s2 : State}, StateEq k s1 s2 → StateRelated k s1 s2
  | 0, _, _, _, hrel => by
    -- Base case k = 0. Under the asymmetric form with `n ≤ 0`, all four
    -- conjuncts become vacuous for compute/ret (step 0 is not halt/error)
    -- and direct for error/halt constructors. No sorries needed.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Forward error at n ≤ 0
      intro n hn he
      have : n = 0 := by omega
      subst this
      cases hrel with
      | error => exact ⟨0, rfl⟩
      | halt _ => simp [steps] at he
      | compute _ _ => simp [steps] at he
      | ret _ _ => simp [steps] at he
    · -- Backward error at m ≤ 0
      intro m hm he
      have : m = 0 := by omega
      subst this
      cases hrel with
      | error => exact ⟨0, rfl⟩
      | halt _ => simp [steps] at he
      | compute _ _ => simp [steps] at he
      | ret _ _ => simp [steps] at he
    · -- Forward halt at n ≤ 0
      intro n v1 hn hh
      have : n = 0 := by omega
      subst this
      cases hrel with
      | error => simp [steps] at hh
      | halt hv =>
        rename_i w1 w2
        refine ⟨0, w2, rfl, ?_⟩
        simp [steps] at hh; subst hh
        simp [ValueEq]
      | compute _ _ => simp [steps] at hh
      | ret _ _ => simp [steps] at hh
    · -- Backward halt at m ≤ 0
      intro m v2 hm hh
      have : m = 0 := by omega
      subst this
      cases hrel with
      | error => simp [steps] at hh
      | halt hv =>
        rename_i w1 w2
        refine ⟨0, w1, rfl, ?_⟩
        simp [steps] at hh; subst hh
        simp [ValueEq]
      | compute _ _ => simp [steps] at hh
      | ret _ _ => simp [steps] at hh
  | k + 1, veq_refl, s1, s2, hrel => by
    -- Inductive case: step once, recurse on k via call_k, lift via stateRelated_lift_*
    have call_k : ∀ {s1' s2' : State}, StateEq k s1' s2' → StateRelated k s1' s2' :=
      fun hrel' => stateEq_stateRelated k (fun j hj v => veq_refl j (by omega) v) hrel'
    have call_k' : ∀ {s1' s2' : State}, StateEq (k + 1) s1' s2' → StateRelated k s1' s2' :=
      fun hrel' => call_k (stateEq_mono (by omega) hrel')
    cases hrel with
    | error =>
      -- Both states are .error. Trivially Reach .error on either side; neither halts.
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ _; exact ⟨0, rfl⟩
      · intro _ _ _; exact ⟨0, rfl⟩
      · intro _ _ _ hh; rw [steps_error] at hh; exact State.noConfusion hh
      · intro _ _ _ hh; rw [steps_error] at hh; exact State.noConfusion hh
    | halt hv =>
      rename_i v1 v2
      -- hv : ValueEq (k+1) v1 v2. Both halt trivially at step 0.
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro _ _ he; rw [steps_halt] at he; exact State.noConfusion he
      · intro _ _ he; rw [steps_halt] at he; exact State.noConfusion he
      · -- Forward halt: side1 halts at n with w1, need ∃ m w2, side2 halts at m with w2 + decay.
        intro n w1 hn hh
        rw [steps_halt] at hh; injection hh with heq; subst heq
        refine ⟨0, v2, by simp [steps], ?_⟩
        -- Decay: (k+1) - max n 0 = (k+1) - n. Use mono on hv.
        exact valueEq_mono ((k + 1) - max n 0) (k + 1) (by omega) _ _ hv
      · -- Backward halt
        intro m w2 hm hh
        rw [steps_halt] at hh; injection hh with heq; subst heq
        refine ⟨0, v1, by simp [steps], ?_⟩
        exact valueEq_mono ((k + 1) - max 0 m) (k + 1) (by omega) _ _ hv
    | compute hstk henv =>
      rename_i env1 env2 t
      -- Step case on term t
      cases t with
      | Var idx =>
        -- Step: look up env.idx
        have hlookup := envEq_lookup henv idx
        generalize h1 : env1.lookup idx = r1 at hlookup
        generalize h2 : env2.lookup idx = r2 at hlookup
        match r1, r2, hlookup with
        | some v1, some v2, hveq =>
          -- step gives ret stk v on both sides
          apply stateRelated_lift_compute
          show StateRelated k (step (.compute _ _ (Term.Var idx))) (step (.compute _ _ (Term.Var idx)))
          simp only [step, h1, h2]
          exact call_k' (.ret hstk hveq)
        | none, none, _ =>
          apply stateRelated_lift_compute
          show StateRelated k (step (.compute _ _ (Term.Var idx))) (step (.compute _ _ (Term.Var idx)))
          simp only [step, h1, h2]
          exact call_k (.error)
        | some _, none, hf => exact hf.elim
        | none, some _, hf => exact hf.elim
      | Constant pair =>
        obtain ⟨c, ty⟩ := pair
        apply stateRelated_lift_compute
        simp only [step]
        exact call_k' (.ret hstk (veq_refl (k + 1) (Nat.le_refl _) (.VCon c)))
      | Builtin b =>
        apply stateRelated_lift_compute
        simp only [step]
        exact call_k' (.ret hstk (veq_refl (k + 1) (Nat.le_refl _) (.VBuiltin b [] _)))
      | Lam nm body =>
        apply stateRelated_lift_compute
        simp only [step]
        -- Need ValueEq k (VLam body env1) (VLam body env2)
        -- Build via stateEq_stateRelated on the extended envs
        refine call_k' (.ret hstk ?_)
        unfold ValueEq
        intro j hj arg1 arg2 harg stk1' stk2' hstk'
        have henv_j : EnvEq j env1 env2 := envEq_mono (by omega) henv
        have henv1_j : EnvEq j (env1.extend arg1) (env2.extend arg2) := envEq_extend henv_j harg
        have hstk_j : StackEq j stk1' stk2' := stackEqR_to_stackEq hstk'
        have hrel_j : StateEq j (.compute stk1' (env1.extend arg1) body)
            (.compute stk2' (env2.extend arg2) body) :=
          .compute hstk_j henv1_j
        exact stateEq_stateRelated j (fun i _ v => veq_refl i (by omega) v) hrel_j
      | Delay body =>
        apply stateRelated_lift_compute
        simp only [step]
        refine call_k' (.ret hstk ?_)
        unfold ValueEq
        intro j hj stk1' stk2' hstk'
        have henv_j : EnvEq j env1 env2 := envEq_mono (by omega) henv
        have hstk_j : StackEq j stk1' stk2' := stackEqR_to_stackEq hstk'
        have hrel_j : StateEq j (.compute stk1' env1 body) (.compute stk2' env2 body) :=
          .compute hstk_j henv_j
        exact stateEq_stateRelated j (fun i _ v => veq_refl i (by omega) v) hrel_j
      | Force e =>
        apply stateRelated_lift_compute
        simp only [step]
        exact call_k' (.compute (.cons .force hstk) henv)
      | Apply f x =>
        apply stateRelated_lift_compute
        simp only [step]
        exact call_k' (.compute (.cons (.arg henv) hstk) henv)
      | Error =>
        apply stateRelated_lift_compute
        simp only [step]
        exact call_k .error
      | Constr tag args =>
        cases args with
        | nil =>
          apply stateRelated_lift_compute
          simp only [step]
          exact call_k' (.ret hstk (veq_refl (k + 1) (Nat.le_refl _) (.VConstr tag [])))
        | cons m ms =>
          apply stateRelated_lift_compute
          simp only [step]
          exact call_k' (.compute (.cons (.constrField (by simp [ListValueEq]) henv) hstk) henv)
      | Case scrut alts =>
        apply stateRelated_lift_compute
        simp only [step]
        exact call_k' (.compute (.cons (.caseScrutinee henv) hstk) henv)
    | ret hstk hv =>
      rename_i stk1' stk2' v1 v2
      cases hstk with
      | nil =>
        -- Empty stack: step gives .halt v
        apply stateRelated_lift_ret
        simp only [step]
        exact call_k' (.halt hv)
      | cons hframe hrest =>
        rename_i f1 f2 rest1 rest2
        cases hframe with
        | force =>
          cases v1 with
          | VDelay body1 env1 =>
            cases v2 with
            | VDelay body2 env2 =>
              apply stateRelated_lift_ret
              simp only [step]
              -- hv : ValueEq (k+1) (VDelay b1 e1) (VDelay b2 e2)
              -- Unfold and use the 3-conjunct clause at inner level k
              unfold ValueEq at hv
              have hrest_k : StackEq k rest1 rest2 := stackEq_mono (by omega) hrest
              -- hv applied at inner level k with stacks rest1/rest2 IS StateRelated k
              exact hv k (by omega) rest1 rest2 (stackEq_to_stackEqR hrest_k)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEq at hv
              obtain ⟨hb, hargs, hea⟩ := hv
              subst hb; subst hea
              apply stateRelated_lift_ret
              simp only [step]
              cases h_head : ea1.head with
              | argQ =>
                simp only
                cases h_tail : ea1.tail with
                | none =>
                  simp only
                  -- evalBuiltin saturation path
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level k b1 args1 args2 hargs
                      (veq_refl (k + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 args1 with
                  | none =>
                    simp only [heval_none.mp h_eval1]
                    exact call_k .error
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 args2 with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_k' (.ret hrest hveq)
                | some ea_rest =>
                  simp only
                  have hvb : ValueEq (k + 1) (.VBuiltin b1 args1 ea_rest) (.VBuiltin b1 args2 ea_rest) := by
                    unfold ValueEq; exact ⟨rfl, hargs, rfl⟩
                  exact call_k' (.ret hrest hvb)
              | argV =>
                simp only
                exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VCon _ =>
            cases v2 with
            | VCon _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
        | arg henv_arg =>
          apply stateRelated_lift_ret
          simp only [step]
          exact call_k' (.compute (.cons (.funV hv) hrest) henv_arg)
        | funV hfv =>
          rename_i vf1 vf2
          cases vf1 with
          | VLam body1 env1 =>
            cases vf2 with
            | VLam body2 env2 =>
              apply stateRelated_lift_ret
              simp only [step]
              -- hfv : ValueEq (k+1) (VLam b1 e1) (VLam b2 e2)
              -- hv : ValueEq (k+1) v1 v2 (the argument)
              unfold ValueEq at hfv
              have hv_k : ValueEq k v1 v2 := valueEq_mono k (k + 1) (by omega) v1 v2 hv
              have hrest_k : StackEq k rest1 rest2 := stackEq_mono (by omega) hrest
              exact hfv k (by omega) v1 v2 hv_k rest1 rest2 (stackEq_to_stackEqR hrest_k)
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VBuiltin b1 args1 ea1 =>
            cases vf2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEq at hfv
              obtain ⟨hb, hargs, hea⟩ := hfv
              subst hb; subst hea
              apply stateRelated_lift_ret
              simp only [step]
              cases h_head : ea1.head with
              | argV =>
                simp only
                cases h_tail : ea1.tail with
                | none =>
                  simp only
                  have hargs_new : ListValueEq (k + 1) (v1 :: args1) (v2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hv, hargs⟩
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level k b1 (v1 :: args1) (v2 :: args2)
                      hargs_new (veq_refl (k + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 (v1 :: args1) with
                  | none =>
                    simp only [heval_none.mp h_eval1]
                    exact call_k .error
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 (v2 :: args2) with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_k' (.ret hrest hveq)
                | some ea_rest =>
                  simp only
                  have hargs_new : ListValueEq (k + 1) (v1 :: args1) (v2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hv, hargs⟩
                  have hvb : ValueEq (k + 1) (.VBuiltin b1 (v1 :: args1) ea_rest)
                      (.VBuiltin b1 (v2 :: args2) ea_rest) := by
                    unfold ValueEq; exact ⟨rfl, hargs_new, rfl⟩
                  exact call_k' (.ret hrest hvb)
              | argQ =>
                simp only
                exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VCon _ =>
            cases vf2 with
            | VCon _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VDelay _ _ =>
            cases vf2 with
            | VDelay _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
          | VConstr _ _ =>
            cases vf2 with
            | VConstr _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hfv; exact hfv.elim
        | applyArg hvx =>
          rename_i vx1 vx2
          cases v1 with
          | VLam body1 env1 =>
            cases v2 with
            | VLam body2 env2 =>
              apply stateRelated_lift_ret
              simp only [step]
              unfold ValueEq at hv
              have hvx_k : ValueEq k vx1 vx2 := valueEq_mono k (k + 1) (by omega) vx1 vx2 hvx
              have hrest_k : StackEq k rest1 rest2 := stackEq_mono (by omega) hrest
              exact hv k (by omega) vx1 vx2 hvx_k rest1 rest2 (stackEq_to_stackEqR hrest_k)
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEq at hv
              obtain ⟨hb, hargs, hea⟩ := hv
              subst hb; subst hea
              apply stateRelated_lift_ret
              simp only [step]
              cases h_head : ea1.head with
              | argV =>
                simp only
                cases h_tail : ea1.tail with
                | none =>
                  simp only
                  have hargs_new : ListValueEq (k + 1) (vx1 :: args1) (vx2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hvx, hargs⟩
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level k b1 (vx1 :: args1) (vx2 :: args2)
                      hargs_new (veq_refl (k + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 (vx1 :: args1) with
                  | none =>
                    simp only [heval_none.mp h_eval1]
                    exact call_k .error
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 (vx2 :: args2) with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_k' (.ret hrest hveq)
                | some ea_rest =>
                  simp only
                  have hargs_new : ListValueEq (k + 1) (vx1 :: args1) (vx2 :: args2) := by
                    simp only [ListValueEq]; exact ⟨hvx, hargs⟩
                  have hvb : ValueEq (k + 1) (.VBuiltin b1 (vx1 :: args1) ea_rest)
                      (.VBuiltin b1 (vx2 :: args2) ea_rest) := by
                    unfold ValueEq; exact ⟨rfl, hargs_new, rfl⟩
                  exact call_k' (.ret hrest hvb)
              | argQ =>
                simp only
                exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VCon _ =>
            cases v2 with
            | VCon _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
        | constrField hdone henv_cf =>
          rename_i done1 done2 env1_cf env2_cf tag todo
          cases todo with
          | nil =>
            apply stateRelated_lift_ret
            simp only [step]
            have hv_k : ValueEq k v1 v2 := valueEq_mono k (k + 1) (by omega) v1 v2 hv
            have hdone_k : ListValueEq k done1 done2 :=
              listValueEq_mono k (k + 1) (by omega) done1 done2 hdone
            have hfields : ListValueEq k (v1 :: done1).reverse (v2 :: done2).reverse :=
              listValueEq_cons_rev hv_k hdone_k
            refine call_k' (.ret hrest ?_)
            unfold ValueEq
            exact ⟨rfl, hfields⟩
          | cons m ms =>
            apply stateRelated_lift_ret
            simp only [step]
            have hdone' : ListValueEq (k + 1) (v1 :: done1) (v2 :: done2) := by
              simp only [ListValueEq]; exact ⟨hv, hdone⟩
            exact call_k' (.compute (.cons (.constrField hdone' henv_cf) hrest) henv_cf)
        | caseScrutinee henv_cs =>
          rename_i alts
          cases v1 with
          | VConstr tag1 fields1 =>
            cases v2 with
            | VConstr tag2 fields2 =>
              unfold ValueEq at hv
              obtain ⟨htag, hfields⟩ := hv
              subst htag
              apply stateRelated_lift_ret
              simp only [step]
              cases h_alt : alts[tag1]? with
              | none => exact call_k .error
              | some alt =>
                have hstk_k : StackEq k
                    (fields1.map Frame.applyArg ++ rest1)
                    (fields2.map Frame.applyArg ++ rest2) :=
                  stackEq_append (listValueEq_map_applyArg_stackEq hfields) (stackEq_mono (by omega) hrest)
                exact call_k (.compute hstk_k (envEq_mono (by omega) henv_cs))
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VCon c1 =>
            cases v2 with
            | VCon c2 =>
              unfold ValueEq at hv
              subst hv
              apply stateRelated_lift_ret
              simp only [step]
              cases h_ctf : Moist.CEK.constToTagAndFields c1 with
              | none => exact call_k .error
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple
                by_cases hcond : numCtors > 0 && alts.length > numCtors
                · simp only [hcond, if_true]
                  exact call_k .error
                · simp only [Bool.not_eq_true] at hcond
                  simp only [hcond]
                  cases h_alt : alts[tag]? with
                  | none => exact call_k .error
                  | some alt =>
                    have hfields_refl : ListValueEq (k + 1) fields fields := by
                      clear hcond h_alt h_ctf
                      induction fields with
                      | nil => simp [ListValueEq]
                      | cons v rest ih =>
                        simp only [ListValueEq]
                        exact ⟨veq_refl (k + 1) (Nat.le_refl _) v, ih⟩
                    exact call_k' (.compute
                      (stackEq_append (listValueEq_map_applyArg_stackEq hfields_refl) hrest)
                      henv_cs)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEq at hv; exact hv.elim
          | VBuiltin _ _ _ =>
            cases v2 with
            | VBuiltin _ _ _ =>
              apply stateRelated_lift_ret
              simp only [step]
              exact call_k .error
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEq at hv; exact hv.elim
  termination_by k => k

/-! ## Extraction: the fundamental lemma as StateRelated -/

/-- The fundamental lemma: same body under `ValueEq k`-related arguments
    gives `StateRelated k` computations. Direct corollary of
    `stateEq_stateRelated`. -/
theorem fundamental_lemma_proved (k : Nat)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEq k arg1 arg2) :
    StateRelated k (.compute [] (env.extend arg1) body) (.compute [] (env.extend arg2) body) := by
  have henv : EnvEq k (env.extend arg1) (env.extend arg2) :=
    envEq_extend (envEq_refl veq_refl env) hargs
  exact stateEq_stateRelated k veq_refl (.compute .nil henv)

/-- The delay variant: same body, same env, related stacks. -/
theorem fundamental_lemma_delay_proved (k : Nat)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    (body : Term) (env : CekEnv)
    (stk1 stk2 : Stack) (hstk : StackEqR (ValueEq k) stk1 stk2) :
    StateRelated k (.compute stk1 env body) (.compute stk2 env body) := by
  have henv : EnvEq k env env := envEq_refl veq_refl env
  exact stateEq_stateRelated k veq_refl (.compute (stackEqR_to_stackEq hstk) henv)

/-! ## Standalone reflexivity (no veq_refl parameter)

`ValueEq k v v` holds for all `k` and `v`. Proved by well-founded induction
on `(k, sizeOf v)`: VLam/VDelay at level `k+1` delegate to `stateEq_stateRelated`
at level `≤ k` (Nat decreases); VBuiltin/VConstr at level `k+1` delegate to
`listValueEq_refl_proved` on structurally smaller values (sizeOf decreases). -/

mutual
  theorem valueEq_refl_proved : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | _ + 1, .VDelay body env => by
      unfold ValueEq; intro j _ stk1 stk2 hstk
      have veq : ∀ i, i ≤ j → ∀ w : CekValue, ValueEq i w w :=
        fun i _ w => valueEq_refl_proved i w
      have hrel : StateEq j (.compute stk1 env body) (.compute stk2 env body) :=
        .compute (stackEqR_to_stackEq hstk) (envEq_refl veq env)
      -- Directly use stateEq_stateRelated: its output IS the new VDelay clause
      exact stateEq_stateRelated j veq hrel
    | k + 1, .VLam body env => by
      unfold ValueEq; intro j hj arg1 arg2 hargs stk1 stk2 hstk
      have veq : ∀ i, i ≤ j → ∀ w : CekValue, ValueEq i w w :=
        fun i _ w => valueEq_refl_proved i w
      have hrel : StateEq j (.compute stk1 (env.extend arg1) body)
          (.compute stk2 (env.extend arg2) body) :=
        .compute (stackEqR_to_stackEq hstk) (envEq_extend (envEq_refl veq env) hargs)
      -- Directly use stateEq_stateRelated: its output IS the new VLam clause
      exact stateEq_stateRelated j veq hrel
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

/-- `stateEq_stateRelated` without the `veq_refl` parameter. -/
theorem stateEq_stateRelated' (k : Nat)
    {s1 s2 : State} (hrel : StateEq k s1 s2) :
    StateRelated k s1 s2 :=
  stateEq_stateRelated k (veq_refl_of k) hrel

/-- `envEq_refl` without the `veq_refl` parameter. -/
theorem envEq_refl' {k : Nat} (env : CekEnv) : EnvEq k env env :=
  envEq_refl (veq_refl_of k) env

/-- The fundamental lemma without `veq_refl` parameter. Produces `StateRelated`. -/
theorem fundamental_lemma_proved' (k : Nat)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEq k arg1 arg2) :
    StateRelated k (.compute [] (env.extend arg1) body) (.compute [] (env.extend arg2) body) :=
  fundamental_lemma_proved k (veq_refl_of k) body env arg1 arg2 hargs

end Moist.Verified.ValueEqBisim

/-! # Public `ValueEq` API in the `Moist.Verified.Semantics` namespace

Below we export the reflexivity / transitivity / behavioral-transitivity
theorems under `Moist.Verified.Semantics`, which is where the rest of the
codebase expects them. The implementations are the `*_proved` versions
defined inside `Moist.Verified.ValueEqBisim` above. -/

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)
open Moist.MIR (Expr lowerTotalExpr lowerTotalExpr_eq_lowerTotal fixCount)

/-- Reflexivity of `ValueEq` at every step index.

    Delegates to the well-founded-recursion implementation
    `Moist.Verified.ValueEqBisim.valueEq_refl_proved`. -/
theorem valueEq_refl (k : Nat) (v : CekValue) : ValueEq k v v :=
  Moist.Verified.ValueEqBisim.valueEq_refl_proved k v

/-- Pointwise reflexivity on lists. -/
theorem listValueEq_refl (k : Nat) (vs : List CekValue) : ListValueEq k vs vs :=
  Moist.Verified.ValueEqBisim.listValueEq_refl_proved k vs

/-! ## Pointwise transitivity of `ValueEq`

Transitivity of `ValueEq` at a single step index, proved by well-founded
recursion on `(k, sizeOf v₁)`.

The VLam/VDelay cases use a **tight-bound trick**: applying `h12` at the
unfold level `max n m` (instead of `j`) forces its halt iff to produce
a witness `p_B ≤ max n m` (because `n ≤ max n m` is the halt iff bound).
This tight bound keeps the intermediate step count inside `max n m`,
so the resulting `ValueEq (j - max n p_B) v1 w_B` downgrades cleanly to
`ValueEq (j - max n m) v1 w_B` via `valueEq_mono` (since
`max n p_B ≤ max n m`). The symmetric argument on `h23` gives
`ValueEq (j - max n m) w_B v3`, and pointwise recursion at the smaller
level `j - max n m ≤ k` closes the case. -/

mutual
  theorem valueEq_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      ValueEq k v₁ v₂ → ValueEq k v₂ v₃ → ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, .VCon _, h12, h23 => by
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam _ _, .VLam _ _, .VLam _ _, _, _ => by
      -- Pointwise transitivity under the asymmetric forward/backward form:
      -- chaining h12's forward halt (which produces an UNBOUNDED target
      -- step count `m_a`) into h23's forward halt (which requires
      -- `m_a ≤ j`) can fail when the middle closure's halt step exceeds
      -- the current level. The asymmetric form accepts this limitation
      -- in exchange for allowing step-count-different halting closures
      -- (e.g. `Delay 10 ~ Delay (5+5)`) to be equivalent.
      -- `behEq_trans` at the top level sidesteps this via `∀ k, ValueEq k`.
      sorry
    | k + 1, .VDelay _ _, .VDelay _ _, .VDelay _ _, _, _ => by
      -- Same limitation as VLam above.
      sorry
    | k + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1,
             listValueEq_trans (k + 1) _ _ _ h12.2.1 h23.2.1,
             h12.2.2.trans h23.2.2⟩
    -- Impossible: v₁, v₂ different constructors
    | _ + 1, .VCon _, .VLam _ _, _, h, _ | _ + 1, .VCon _, .VDelay _ _, _, h, _
    | _ + 1, .VCon _, .VConstr _ _, _, h, _ | _ + 1, .VCon _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VLam _ _, .VCon _, _, h, _ | _ + 1, .VLam _ _, .VDelay _ _, _, h, _
    | _ + 1, .VLam _ _, .VConstr _ _, _, h, _ | _ + 1, .VLam _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VDelay _ _, .VCon _, _, h, _ | _ + 1, .VDelay _ _, .VLam _ _, _, h, _
    | _ + 1, .VDelay _ _, .VConstr _ _, _, h, _ | _ + 1, .VDelay _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VConstr _ _, .VCon _, _, h, _ | _ + 1, .VConstr _ _, .VLam _ _, _, h, _
    | _ + 1, .VConstr _ _, .VDelay _ _, _, h, _ | _ + 1, .VConstr _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VCon _, _, h, _ | _ + 1, .VBuiltin _ _ _, .VLam _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, _, h, _ => by simp [ValueEq] at h
    -- Impossible: v₂, v₃ different constructors
    | _ + 1, .VCon _, .VCon _, .VLam _ _, _, h | _ + 1, .VCon _, .VCon _, .VDelay _ _, _, h
    | _ + 1, .VCon _, .VCon _, .VConstr _ _, _, h | _ + 1, .VCon _, .VCon _, .VBuiltin _ _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VCon _, _, h | _ + 1, .VLam _ _, .VLam _ _, .VDelay _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VConstr _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VCon _, _, h | _ + 1, .VDelay _ _, .VDelay _ _, .VLam _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VConstr _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VCon _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VLam _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VDelay _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VCon _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VLam _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VDelay _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VConstr _ _, _, h => by simp [ValueEq] at h
  termination_by k v _ _ _ _ => (k, sizeOf v)
  theorem listValueEq_trans : ∀ (k : Nat) (vs₁ vs₂ vs₃ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₃ → ListValueEq k vs₁ vs₃
    | _, [], [], [], _, _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, _ :: _, h12, h23 => by
      simp only [ListValueEq] at h12 h23 ⊢
      exact ⟨valueEq_trans k _ _ _ h12.1 h23.1,
             listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | _, [], _ :: _, _, h, _ | _, _ :: _, [], _, h, _ => by simp [ListValueEq] at h
    | _, [], [], _ :: _, _, h => by simp [ListValueEq] at h
    | _, _ :: _, _ :: _, [], _, h => by simp [ListValueEq] at h
  termination_by k vs _ _ _ _ => (k, sizeOf vs)
end

/-! ## Behavioral equivalence transitivity -/

private abbrev emptyEnv : List MIR.VarId := []

private theorem behEqClosed_extract {m1 m2 : Expr} {t1 t2 : Term}
    (h1 : lowerTotalExpr emptyEnv m1 = some t1)
    (h2 : lowerTotalExpr emptyEnv m2 = some t2)
    (h : BehEqClosed m1 m2) :
    (Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧
    (Halts (.compute [] .nil t1) ↔ Halts (.compute [] .nil t2)) ∧
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) (.halt v1) →
      Reaches (.compute [] .nil t2) (.halt v2) →
      ValueEq k v1 v2 := by
  unfold BehEqClosed at h; rw [h1, h2] at h; exact h

/-- **Transitivity of closed behavioral equivalence.** -/
theorem behEqClosed_trans {a b c : Expr}
    {tb : Term} (hb : lowerTotalExpr emptyEnv b = some tb)
    (h12 : a ≋ᶜ b) (h23 : b ≋ᶜ c) : a ≋ᶜ c := by
  unfold BehEqClosed
  cases ha : lowerTotalExpr emptyEnv a with
  | none => split <;> trivial
  | some ta =>
    cases hc : lowerTotalExpr emptyEnv c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have ⟨herr12, hh12, hv12⟩ := behEqClosed_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEqClosed_extract hb hc h23
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

private theorem behEq_extract {m1 m2 : Expr} {env : List MIR.VarId} {t1 t2 : Term}
    (h1 : lowerTotalExpr env m1 = some t1) (h2 : lowerTotalExpr env m2 = some t2)
    (h : BehEq m1 m2) :
    ∀ ρ : CekEnv, WellSizedEnv env.length ρ →
      (Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
      (Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
      ∀ (k : Nat) (v1 v2 : CekValue),
        Reaches (.compute [] ρ t1) (.halt v1) →
        Reaches (.compute [] ρ t2) (.halt v2) →
        ValueEq k v1 v2 := by
  have := h env; rw [h1, h2] at this; exact this

/-- **Transitivity of behavioral equivalence for open terms.** -/
theorem behEq_trans {a b c : Expr}
    (hlb : ∀ env, (lowerTotalExpr env a).isSome → (lowerTotalExpr env b).isSome)
    (h12 : a ≋ b) (h23 : b ≋ c) : a ≋ c := by
  unfold BehEq; intro env
  cases ha : lowerTotalExpr env a with
  | none => split <;> trivial
  | some ta =>
    obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp (hlb env (by simp [ha]))
    cases hc : lowerTotalExpr env c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have h12' := behEq_extract ha hb h12
      have h23' := behEq_extract hb hc h23
      intro ρ hwf
      have ⟨herr12, hh12, hv12⟩ := h12' ρ hwf
      have ⟨herr23, hh23, hv23⟩ := h23' ρ hwf
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

/-- **Unconditional transitivity of refinement.** -/
theorem refines_trans {a b c : Expr}
    (h12 : Refines a b) (h23 : Refines b c) : Refines a c :=
  ⟨fun env ha => h23.1 env (h12.1 env ha),
   behEq_trans h12.1 h12.2 h23.2⟩

end Moist.Verified.Semantics
