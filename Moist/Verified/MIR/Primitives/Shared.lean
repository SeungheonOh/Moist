import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.DeadLet
import Moist.Verified.FundamentalRefines
import Moist.MIR.ANF

/-! # CEK-level glue for the MIR rewrite primitives

Step-shifting for `ObsRefinesK` and `StackRefK` augmentations by a single
frame (`funV`, `force`). -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Verified.Equivalence (ObsRefinesK steps obsRefinesK_mono obsRefinesK_zero_ret
  obsRefinesK_of_step_ret)
open Moist.Verified.Contextual.SoundnessRefines (EnvRefinesK ValueRefinesK StackRefK
  valueRefinesK_mono stackRefK_mono obsRefinesK_error evalBuiltin_compat_refines
  listRel_valueRefinesK_mono)

theorem steps_trans (m n : Nat) (s : State) : steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (step s)

private theorem steps_fixed {t : State} (ht : step t = t) : ∀ n, steps n t = t
  | 0 => rfl
  | n + 1 => by simp only [steps, ht]; exact steps_fixed ht n

/-- A fixed point reached after `m` steps is still reached `m - n` steps after step `n`. -/
private theorem steps_after {n m : Nat} {s t : State} (ht : step t = t) (h : steps m s = t) :
    steps (m - n) (steps n s) = t := by
  by_cases hmn : m ≤ n
  · rw [Nat.sub_eq_zero_of_le hmn, show n = m + (n - m) by omega, steps_trans, h, steps_fixed ht]
    rfl
  · rw [← steps_trans, show n + (m - n) = m by omega, h]

/-- Running the right state forward preserves refinement. -/
theorem obsRefinesK_of_steps_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefinesK k s₁ s₂') : ObsRefinesK k s₁ s₂ := by
  refine ⟨fun v hv => ?_, fun m hm herr => ?_⟩
  · obtain ⟨v', m, hm⟩ := h.1 v hv
    exact ⟨v', n + m, by rw [steps_trans, h_steps]; exact hm⟩
  · obtain ⟨m', hm'⟩ := h.2 m hm herr
    exact ⟨n + m', by rw [steps_trans, h_steps]; exact hm'⟩

/-- Running the left state forward preserves refinement. -/
theorem obsRefinesK_of_steps_left {k n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁') (h : ObsRefinesK k s₁' s₂) : ObsRefinesK k s₁ s₂ := by
  subst h_steps
  exact ⟨fun v ⟨m, hm, hs⟩ => h.1 v ⟨m - n, by omega, steps_after rfl hs⟩,
    fun m hm hs => h.2 (m - n) (by omega) (steps_after rfl hs)⟩

/-- The identity frame `funV (λ. 1)` is transparent on the right. -/
theorem stackRefK_funV_id_augment_right {j : Nat} {π₁ π₂ : Stack} {ρ₂ : CekEnv}
    (hπ : StackRefK ValueRefinesK j π₁ π₂) :
    StackRefK ValueRefinesK j π₁ (.funV (.VLam (.Var 1) ρ₂) :: π₂) :=
  fun j' hj' v₁ v₂ hv => obsRefinesK_of_steps_right (n := 2) rfl (hπ j' hj' v₁ v₂ hv)

theorem envRefinesK_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : EnvRefinesK k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    EnvRefinesK k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  match n, hn with
  | 1, _ => exact ⟨v₁, v₂, rfl, rfl, hv⟩
  | m + 2, _ => exact henv (m + 1) (by omega) (by omega)

theorem envRefinesK_mono {j k d : Nat} {ρ₁ ρ₂ : CekEnv} (hj : j ≤ k)
    (henv : EnvRefinesK k d ρ₁ ρ₂) : EnvRefinesK j d ρ₁ ρ₂ := fun n hn hnd => by
  obtain ⟨w₁, w₂, hl, hr, hw⟩ := henv n hn hnd
  exact ⟨w₁, w₂, hl, hr, valueRefinesK_mono hj _ _ hw⟩

/-- A `force` frame on related stacks. -/
theorem stackRefK_force_augment {i : Nat} {π₁ π₂ : Stack}
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.force :: π₁) (.force :: π₂) := by
  intro j hj v₁ v₂ hv
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
  refine obsRefinesK_of_step_ret ?_
  cases v₁ <;> cases v₂ <;> simp only [ValueRefinesK] at hv <;> try exact obsRefinesK_error _
  case VDelay.VDelay =>
    exact hv n (by omega) n (Nat.le_refl _) π₁ π₂ (stackRefK_mono (by omega) hπ)
  case VBuiltin.VBuiltin b₁ args₁ ea₁ b₂ args₂ ea₂ =>
    obtain ⟨rfl, rfl, hargs⟩ := hv
    simp only [step]
    split
    · split
      · refine obsRefinesK_mono (Nat.le_succ n) (hπ (n + 1) (by omega) _ _ ?_)
        simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs⟩
      · exact evalBuiltin_compat_refines hargs (stackRefK_mono (by omega) hπ)
    · exact obsRefinesK_error _

/-- A `funV` frame holding related functions on related stacks. -/
theorem stackRefK_funV_top_aug {i : Nat} {vf₁ vf₂ : CekValue} {π₁ π₂ : Stack}
    (hvf : ValueRefinesK i vf₁ vf₂) (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
  refine obsRefinesK_of_step_ret ?_
  have hvf' : ValueRefinesK (n + 1) vf₁ vf₂ := valueRefinesK_mono hj _ _ hvf
  cases vf₁ <;> cases vf₂ <;> simp only [ValueRefinesK] at hvf' <;> try exact obsRefinesK_error _
  case VLam.VLam =>
    exact hvf' n (by omega) w₁ w₂ (valueRefinesK_mono (by omega) w₁ w₂ hw) n (Nat.le_refl _)
      π₁ π₂ (stackRefK_mono (by omega) hπ)
  case VBuiltin.VBuiltin b₁ args₁ ea₁ b₂ args₂ ea₂ =>
    obtain ⟨rfl, rfl, hargs⟩ := hvf'
    have hargs' : Moist.Verified.Equivalence.ListRel (ValueRefinesK n) (w₁ :: args₁) (w₂ :: args₂) :=
      ⟨valueRefinesK_mono (by omega) w₁ w₂ hw, listRel_valueRefinesK_mono (by omega) hargs⟩
    simp only [step]
    split
    · split
      · refine obsRefinesK_mono (Nat.le_succ n) (hπ (n + 1) (by omega) _ _ ?_)
        simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs'⟩
      · exact evalBuiltin_compat_refines hargs' (stackRefK_mono (by omega) hπ)
    · exact obsRefinesK_error _

end Moist.Verified.MIR
