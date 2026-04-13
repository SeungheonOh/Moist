import Moist.VerifiedNewNew.DeadLet
import Moist.VerifiedNewNew.MIR
import Moist.VerifiedNewNew.Contextual.SoundnessRefines
import Moist.Verified.Purity
import Moist.Verified.StepLift

/-! # Unidirectional dead-let refinement at the UPLC level

This file proves the refinement-direction analogue of
`DeadLet.uplc_dead_let`. The bidirectional `DeadLet.uplc_dead_let`
theorem requires `WellSizedEnv d` on both envs and a *purity*
precondition on the rhs (the rhs must always halt to a value). Those
obligations are necessary for the reverse direction (body halts ⇒
wrapped-with-rhs halts), which requires rhs to terminate.

For the **refinement direction** alone — `Apply (Lam 0 (shift body)) rhs
⊑ body` — neither precondition is needed:

  * If rhs diverges or errors, the LHS can never halt, so the
    `ObsRefinesK` goal is vacuous.
  * If rhs halts to some value `v_rhs`, the LHS state after evaluating
    the argument is `compute π₁ (ρ₁.extend v_rhs) (shift body)`, which
    by `shiftRefines` (parallel to `shiftEquiv`) refines `compute π₂
    ρ₂ t_body` directly.

The proof structure parallels `uplc_dead_let` but works at
`ObsRefinesK` / `ValueRefinesK` / `StackRefK` levels. It reuses nothing
from `DeadLet.lean`'s internal private helpers — everything is
reproven at the unidirectional level.
-/

namespace Moist.VerifiedNewNew.DeadLetRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew
open Moist.VerifiedNewNew.Equivalence
open Moist.VerifiedNewNew.Contextual.SoundnessRefines

--------------------------------------------------------------------------------
-- 1. ShiftEnvRefK — unidirectional analogue of `DeadLet.ShiftEnvEqK`
--------------------------------------------------------------------------------

/-- Shifted environment refinement relation: `ρ₁.lookup (shiftRename c n)`
    is `ValueRefinesK`-related to `ρ₂.lookup n`. The unidirectional
    counterpart of `DeadLet.ShiftEnvEqK`. -/
def ShiftEnvRefK (c k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (Moist.Verified.shiftRename c n), ρ₂.lookup n with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

theorem shiftEnvRefK_mono {c j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : ShiftEnvRefK c k d ρ₁ ρ₂) : ShiftEnvRefK c j d ρ₁ ρ₂ := by
  intro n hn hnd; have := h n hn hnd
  cases h₁ : ρ₁.lookup (Moist.Verified.shiftRename c n) <;>
    cases h₂ : ρ₂.lookup n <;> simp_all
  exact valueRefinesK_mono hjk _ _ this

/-- Bridge `EnvRefinesK → ShiftEnvRefK 1` on an `extend`ed left env.
    Mirrors `DeadLet.envEqK_to_shiftEnvEqK`. -/
theorem envRefinesK_to_shiftEnvRefK {k d : Nat} {ρ₁ ρ₂ : CekEnv} {w : CekValue}
    (h : EnvRefinesK k d ρ₁ ρ₂) : ShiftEnvRefK 1 k d (ρ₁.extend w) ρ₂ := by
  intro n hn hnd
  have heq := Moist.VerifiedNewNew.DeadLet.extend_lookup_shift ρ₁ w n
  have henv := h n hn hnd
  cases h₁ : ρ₁.lookup n <;> cases h₂ : ρ₂.lookup n <;> simp_all

/-- Extending a `ShiftEnvRefK`-related pair under a binder bumps the shift
    counter and the depth by one. Mirrors `DeadLet.shiftEnvEqK_extend`. -/
theorem shiftEnvRefK_extend {c k d : Nat} (hc : c ≥ 1)
    {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : ShiftEnvRefK c k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    ShiftEnvRefK (c + 1) k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1
    have hsr : Moist.Verified.shiftRename (c + 1) 1 = 1 := by
      simp [Moist.Verified.shiftRename]; omega
    simp [hsr, CekEnv.extend, CekEnv.lookup]; exact hv
  · have hn2 : n ≥ 2 := by omega
    match n, hn2 with
    | n' + 2, _ =>
    have henv' := henv (n' + 1) (by omega) (by omega)
    by_cases hge : n' + 2 ≥ c + 1
    · have hsr1 : Moist.Verified.shiftRename (c + 1) (n' + 2) = n' + 3 := by
        simp [Moist.Verified.shiftRename]; omega
      have hsr2 : Moist.Verified.shiftRename c (n' + 1) = n' + 2 := by
        simp [Moist.Verified.shiftRename]; omega
      simp only [hsr1, CekEnv.extend, CekEnv.lookup]
      rw [hsr2] at henv'; exact henv'
    · have hsr1 : Moist.Verified.shiftRename (c + 1) (n' + 2) = n' + 2 := by
        simp [Moist.Verified.shiftRename]; omega
      have hsr2 : Moist.Verified.shiftRename c (n' + 1) = n' + 1 := by
        simp [Moist.Verified.shiftRename]; omega
      simp only [hsr1, CekEnv.extend, CekEnv.lookup]
      rw [hsr2] at henv'; exact henv'

--------------------------------------------------------------------------------
-- 2. Multi-step peel helpers for `ObsRefinesK`
--
-- Mirrors the private `obsEqK_of_step_left` / `obsEqK_of_steps_left` helpers
-- from `DeadLet.lean`, but at the unidirectional `ObsRefinesK` level. Local
-- copies of `steps_trans` and `no_halt_before_reach` are reproven because
-- the originals in `DeadLet.lean` are `private`.
--------------------------------------------------------------------------------

private theorem steps_trans (m n : Nat) (s : State) :
    steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (step s)

private theorem steps_halt_fixed (n : Nat) (v : CekValue) :
    steps n (.halt v) = .halt v := by
  induction n with | zero => rfl | succ n ih => simp [steps, step, ih]

private theorem no_halt_before_reach {s s' : State} {m : Nat}
    (hreach : steps m s = s') (h_not_halt : ∀ v, s' ≠ .halt v) :
    ∀ j, j ≤ m → ∀ v, steps j s ≠ .halt v := by
  intro j hj v hv
  have hsplit : steps m s = steps (m - j) (steps j s) := by
    rw [← steps_trans]; congr 1; omega
  rw [hv, steps_halt_fixed] at hsplit
  exact h_not_halt v (hsplit ▸ hreach).symm

/-- Peel one deterministic non-halt CEK step from the left side of
    `ObsRefinesK`. Mirrors `DeadLet.obsEqK_of_step_left` at the
    unidirectional level. -/
private theorem obsRefinesK_of_step_left {k : Nat} {s₁ s₂ : State}
    (h₁ : ∀ v, s₁ ≠ .halt v) (h_err : s₁ ≠ .error)
    (h : ObsRefinesK k (step s₁) s₂) :
    ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v ⟨n, hn, hs⟩
    match n with
    | 0 => exact absurd hs (h₁ v)
    | m + 1 =>
      have hstep : steps m (step s₁) = .halt v := by
        simp only [steps] at hs; exact hs
      exact h.1 v ⟨m, by omega, hstep⟩
  · intro n hn hs
    match n with
    | 0 => simp only [steps] at hs; exact absurd hs h_err
    | m + 1 =>
      have hstep : steps m (step s₁) = .error := by
        simp only [steps] at hs; exact hs
      exact h.2 m (by omega) hstep

/-- Peel `m` deterministic non-halt, non-error CEK steps from the left side of
    `ObsRefinesK`. Mirrors `DeadLet.obsEqK_of_steps_left` at the
    unidirectional level. -/
private theorem obsRefinesK_of_steps_left {k m : Nat} {s₁ s₂ : State}
    (h_no_halt : ∀ j, j ≤ m → ∀ v, steps j s₁ ≠ .halt v)
    (h_no_err : ∀ j, j ≤ m → steps j s₁ ≠ .error)
    (h : ObsRefinesK k (steps m s₁) s₂) : ObsRefinesK k s₁ s₂ := by
  induction m generalizing s₁ with
  | zero => exact h
  | succ m ih =>
    apply obsRefinesK_of_step_left
      (fun v hv => h_no_halt 0 (by omega) v (by simp [steps]; exact hv))
      (h_no_err 0 (by omega))
    apply ih (fun j hj v hv => h_no_halt (j + 1) (by omega) v
      (by simp [steps]; exact hv))
      (fun j hj hs => h_no_err (j + 1) (by omega)
        (by simp [steps]; exact hs))
    simp [steps] at h ⊢; exact h

--------------------------------------------------------------------------------
-- 3. shiftRefinesConstrField — parallel to `DeadLet.shiftConstrField`
--------------------------------------------------------------------------------

/-- `StackRefK` builder for a `.constrField` frame under the shift relation.
    Mirror of `DeadLet.shiftConstrField`, but at `ValueRefinesK` /
    `StackRefK ValueRefinesK` / `ObsRefinesK` level. -/
private theorem shiftRefinesConstrField {c d tag k : Nat}
    {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ => ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftEnvRefK c j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
      ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      ShiftEnvRefK c j d ρ₁ ρ₂ → ListRel (ValueRefinesK j) done₁ done₂ →
      StackRefK ValueRefinesK j π₁ π₂ →
      StackRefK ValueRefinesK j (.constrField tag done₁ ms₁ ρ₁ :: π₁)
                                 (.constrField tag done₂ ms₂ ρ₂ :: π₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
    cases ms₂ with
    | cons => exact absurd hfields id
    | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hrev : ListRel (ValueRefinesK n) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse
          (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone))
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueRefinesK (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse))
        (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
    exact obsRefinesK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m₁ ms₁' ih =>
    cases ms₂ with
    | nil => exact absurd hfields id
    | cons m₂ ms₂' =>
    have hm := hfields.1
    have hfs := hfields.2
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (shiftEnvRefK_mono (by omega) henv)
      (show ListRel (ValueRefinesK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone⟩)
      (stackRefK_mono (by omega) hπ)

--------------------------------------------------------------------------------
-- 4. shiftRefines — the core shift simulation at the refinement level
--
-- Mirror of `DeadLet.shiftEquiv` at the unidirectional `ObsRefinesK` level.
-- Walks all term constructors and produces a shift-based refinement from
-- the renamed LHS into the original RHS, assuming a `ShiftEnvRefK`-related
-- environment pair and a `StackRefK ValueRefinesK`-related stack pair.
--
-- The structure and case dispatch are structurally identical to
-- `shiftEquiv`, but every bidirectional helper is replaced by its
-- unidirectional sibling from `Contextual/SoundnessRefines.lean`.
--------------------------------------------------------------------------------

mutual
  private def shiftRefines (c d : Nat) (hc : c ≥ 1)
      (t : Term) (ht : closedAt d t = true) (k : Nat) :
      ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftEnvRefK c j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i
            (.compute π₁ ρ₁ (Moist.Verified.renameTerm (Moist.Verified.shiftRename c) t))
            (.compute π₂ ρ₂ t) := by
    intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    match t with
    | .Var n =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      simp [closedAt] at ht
      by_cases hn : n = 0
      · subst hn
        have : Moist.Verified.shiftRename c 0 = 0 := by
          simp [Moist.Verified.shiftRename]; omega
        have h1 : ρ₁.lookup 0 = none := by cases ρ₁ <;> rfl
        have h2 : ρ₂.lookup 0 = none := by cases ρ₂ <;> rfl
        simp [this, h1, h2]
        exact obsRefinesK_error _
      · have h_n := henv n (by omega) ht
        revert h_n
        cases ρ₁.lookup (Moist.Verified.shiftRename c n) <;>
          cases ρ₂.lookup n <;> intro h_n
        · exact obsRefinesK_error _
        · exact absurd h_n id
        · exact absurd h_n id
        · exact hπ i' (by omega) _ _
            (valueRefinesK_mono (by omega : i' ≤ j) _ _ h_n)
    | .Constant c' =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueRefinesK]
        | succ => simp only [ValueRefinesK])
    | .Builtin b =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
        | succ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial, trivial⟩)
    | .Error =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp [step]; exact obsRefinesK_error _
    | .Lam name body =>
      simp only [Moist.Verified.renameTerm]
      rw [Moist.Verified.liftRename_shiftRename (by omega : c ≥ 1)]
      simp [closedAt] at ht
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueRefinesK]
        | succ m =>
          simp only [ValueRefinesK]
          intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
          exact shiftRefines (c + 1) (d + 1) (by omega) body ht j'
            j' (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
            (shiftEnvRefK_extend hc (shiftEnvRefK_mono (by omega) henv) hargs)
            ib hib π₁' π₂' hπ')
    | .Delay body =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueRefinesK]
        | succ m =>
          simp only [ValueRefinesK]
          intro j' hj' ib hib π₁' π₂' hπ'
          exact shiftRefines c d hc body ht j'
            j' (Nat.le_refl _) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv)
            ib hib π₁' π₂' hπ')
    | .Apply f x =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply shiftRefines c d hc f hf (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) i' (by omega)
      intro i₁ hi₁ v₁ v₂ hv
      match i₁ with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | m₁ + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply shiftRefines c d hc x hx (m₁+1)
        (m₁+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) m₁ (by omega)
      intro i₂ hi₂ w₁ w₂ hw
      match i₂ with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | m₂ + 1 =>
      obsRefinesK_of_step_auto
      match v₁, v₂ with
      | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
        simp only [step, ValueRefinesK] at hv ⊢
        exact hv m₂ (by omega) w₁ w₂ (valueRefinesK_mono (by omega) w₁ w₂ hw)
          m₂ (Nat.le_refl _) π₁ π₂ (stackRefK_mono (by omega) hπ)
      | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
        simp only [ValueRefinesK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv
        simp only [step]
        split
        · split
          · rename_i rest _
            have hval : ValueRefinesK (m₂ + 1)
                (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
              simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩; simp only [ListRel]
              exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                     listRel_mono (fun a b h => valueRefinesK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
            exact obsRefinesK_mono (by omega) (hπ (m₂ + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat_refines
              (by simp only [ListRel]
                  exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                    listRel_mono (fun a b h => valueRefinesK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩)
              (stackRefK_mono (by omega) hπ)
        · exact obsRefinesK_error _
      | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
      | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsRefinesK_error _
      | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
    | .Force e =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply shiftRefines c d hc e ht (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) i' (by omega)
      intro j' hj' v₁ v₂ hv
      match j' with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | m + 1 =>
      obsRefinesK_of_step_auto
      match v₁, v₂ with
      | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
        simp only [step, ValueRefinesK] at hv ⊢
        exact hv m (by omega) m (by omega) π₁ π₂ (stackRefK_mono (by omega) hπ)
      | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
        simp only [ValueRefinesK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv; simp only [step]
        split
        · split
          · rename_i rest _
            have hval : ValueRefinesK (m + 1)
                (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
              simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs_rel⟩
            exact obsRefinesK_mono (by omega) (hπ (m + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat_refines hargs_rel (stackRefK_mono (by omega) hπ)
        · exact obsRefinesK_error _
      | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
      | .VLam _ _, .VLam _ _ => simp only [step]; exact obsRefinesK_error _
      | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
    | .Constr tag fields =>
      simp only [Moist.Verified.renameTerm]
      match fields with
      | [] =>
        simp [Moist.Verified.renameTermList]
        match i with
        | 0 => obsRefinesK_zero_nonhalt_auto
        | i' + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        have : ValueRefinesK i' (.VConstr tag []) (.VConstr tag []) := by
          cases i' with
          | zero => simp only [ValueRefinesK]
          | succ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial⟩
        exact hπ i' (by omega) _ _ this
      | m :: ms =>
        simp [closedAt] at ht
        have hm : closedAt d m = true := by
          have := ht; simp [closedAtList] at this; exact this.1
        have hms : closedAtList d ms = true := by
          have := ht; simp [closedAtList] at this; exact this.2
        simp [Moist.Verified.renameTermList]
        match i with
        | 0 => obsRefinesK_zero_nonhalt_auto
        | i' + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        apply shiftRefines c d hc m hm (i'+1)
          (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) i' (by omega)
        exact shiftRefinesConstrField (shiftRefinesList c d hc ms hms (i'+1))
          (by omega) (shiftEnvRefK_mono (by omega) henv) trivial (stackRefK_mono (by omega) hπ)
    | .Case scrut alts =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply shiftRefines c d hc scrut hscrut (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) i' (by omega)
      intro j' hj' v₁ v₂ hv
      match j' with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | n + 1 =>
      obsRefinesK_of_step_auto
      match v₁, v₂ with
      | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
        simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
        simp only [step]
        split
        · rename_i alt₁ halt₁
          have hlen_eq : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length = alts.length :=
            Moist.Verified.renameTermList_length _ _
          have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
          have hi₁ : tag₁ < (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length := hsome₁.1
          have hi₂ : tag₁ < alts.length := by omega
          have halt₂ : alts[tag₁]? = some (alts[tag₁]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
          rw [halt₂]; simp only []
          have hidx : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts)[tag₁]'hi₁ =
              Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (alts[tag₁]) :=
            Moist.Verified.renameTermList_getElem _ _ _ hi₂
          have heq₁ : alt₁ = Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (alts[tag₁]) := by
            have := hsome₁.2; rw [hidx] at this; exact this.symm
          rw [heq₁]
          have haltsList := shiftRefinesList c d hc alts halts (i'+1)
          have halt_shift := listRel_getElem haltsList
            (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
          rw [hidx] at halt_shift
          apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) n (by omega)
          exact applyArgFrames_stackRefK
            (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
            (stackRefK_mono (by omega) hπ)
        · rename_i hnone₁
          have hlen_eq : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length = alts.length :=
            Moist.Verified.renameTermList_length _ _
          have hnone₂ : alts[tag₁]? = none := by
            rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
          rw [hnone₂]; simp only []; exact obsRefinesK_error _
      | .VCon c₁, .VCon c₂ =>
        simp only [ValueRefinesK] at hv; subst hv
        simp only [step]
        have hlen_eq : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length = alts.length :=
          Moist.Verified.renameTermList_length _ _
        split
        · rename_i tag numCtors fields htag
          have hif_eq : (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length > numCtors)) =
              (decide (numCtors > 0) && decide (alts.length > numCtors)) := by
            rw [hlen_eq]
          split
          · rename_i h_check
            rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
          · rename_i h_check
            rw [hif_eq] at h_check; simp [h_check]
            split
            · rename_i alt₁ halt₁
              have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
              have hi₁ : tag < (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length := hsome₁.1
              have hi₂ : tag < alts.length := by omega
              have halt₂ : alts[tag]? = some (alts[tag]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
              rw [halt₂]; simp only []
              have hidx : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts)[tag]'hi₁ =
                  Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (alts[tag]) :=
                Moist.Verified.renameTermList_getElem _ _ _ hi₂
              have heq₁ : alt₁ = Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (alts[tag]) := by
                have := hsome₁.2; rw [hidx] at this; exact this.symm
              rw [heq₁]
              have haltsList := shiftRefinesList c d hc alts halts (i'+1)
              have halt_shift := listRel_getElem haltsList
                (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
              rw [hidx] at halt_shift
              apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (shiftEnvRefK_mono (by omega) henv) n (by omega)
              have hfields_vcon := constToTagAndFields_fields_vcon c₁
              rw [htag] at hfields_vcon
              exact applyArgFrames_stackRefK
                (listRel_refl_vcon_refines n fields hfields_vcon)
                (stackRefK_mono (by omega) hπ)
            · rename_i hnone₁
              have hnone₂ : alts[tag]? = none := by
                rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
              rw [hnone₂]; simp only []; exact obsRefinesK_error _
        · exact obsRefinesK_error _
      | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
  termination_by sizeOf t

  private def shiftRefinesList (c d : Nat) (hc : c ≥ 1)
      (ts : List Term) (hts : closedAtList d ts = true) (k : Nat) :
      ListRel (fun t₁ t₂ =>
        ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftEnvRefK c j d ρ₁ ρ₂ →
          ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
            ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) ts)
        ts := by
    match ts, hts with
    | [], _ => simp [Moist.Verified.renameTermList]; trivial
    | t :: rest, hts =>
      simp [closedAtList] at hts
      simp [Moist.Verified.renameTermList]
      exact ⟨shiftRefines c d hc t hts.1 k, shiftRefinesList c d hc rest hts.2 k⟩
  termination_by sizeOf ts
end

--------------------------------------------------------------------------------
-- 5. Stack-discipline inversion lemma
--
-- Core inversion fact: if CEK execution starting from a state whose stack
-- has `baseπ` as a suffix eventually halts, then the execution must pass
-- through `ret baseπ v_inner` for some value. This is the "stack base
-- discipline" fact that lets us extract rhs's final value without a purity
-- precondition on rhs.
--------------------------------------------------------------------------------

/-- Stack-suffix invariant: `s`'s stack contains `baseπ` as a suffix. -/
private def hasSuffix (baseπ : Stack) : State → Prop
  | .compute π _ _ => ∃ rest, π = rest ++ baseπ
  | .ret π _ => ∃ rest, π = rest ++ baseπ
  | _ => False

/-- `steps n .error = .error`. -/
private theorem steps_error_eq : ∀ (n : Nat), steps n (.error : State) = .error
  | 0 => rfl
  | n + 1 => by simp only [steps, step]; exact steps_error_eq n

/-- Packaging: given that `s` steps to `s'` (via `hstep`), `s'` has the
    invariant, and `ih` gives a witness for `s'` at halt time `n'`, produce
    a witness for `s` at halt time `n' + 1`. -/
private theorem halt_descends_package
    {baseπ : Stack} {s s' : State} {n' : Nat} {v_halt : CekValue}
    (hstep : step s = s')
    (hs_next : steps n' s' = .halt v_halt)
    (h_next_inv : hasSuffix baseπ s')
    (ih : ∀ (s : State) (v_halt : CekValue),
            steps n' s = .halt v_halt → hasSuffix baseπ s →
            ∃ m, m ≤ n' ∧ ∃ v_inner, steps m s = .ret baseπ v_inner) :
    ∃ m, m ≤ n' + 1 ∧ ∃ v_inner, steps m s = .ret baseπ v_inner := by
  obtain ⟨m, hm_le, v_inner, hm_steps⟩ := ih s' v_halt hs_next h_next_inv
  refine ⟨m + 1, by omega, v_inner, ?_⟩
  show steps (m + 1) s = .ret baseπ v_inner
  simp only [steps]
  rw [hstep]
  exact hm_steps

/-- The inversion lemma. Proved by strong induction on `n` with explicit case
    analysis on the state shape. For each state case, we compute `step s` via
    direct reflexivity and recurse on the stepped state. -/
private theorem halt_descends_to_baseπ {baseπ : Stack} :
    ∀ (n : Nat) (s : State) (v_halt : CekValue),
      steps n s = .halt v_halt →
      hasSuffix baseπ s →
      ∃ m, m ≤ n ∧ ∃ v_inner, steps m s = .ret baseπ v_inner := by
  intro n
  induction n with
  | zero =>
    intro s v_halt hs hinv
    simp only [steps] at hs
    subst hs
    cases hinv
  | succ n' ih =>
    intro s v_halt hs hinv
    by_cases hat : ∃ v, s = .ret baseπ v
    · obtain ⟨v, rfl⟩ := hat
      exact ⟨0, by omega, v, by simp [steps]⟩
    · have hs_next : steps n' (step s) = .halt v_halt := by
        have heq : steps (n' + 1) s = steps n' (step s) := by simp only [steps]
        rw [← heq]; exact hs
      have h_not_err : step s ≠ .error := by
        intro heq
        rw [heq, steps_error_eq] at hs_next
        exact State.noConfusion hs_next
      -- Case analyze s. Use tactic `cases` throughout.
      cases s with
      | error => exact absurd hinv (by intro h; cases h)
      | halt _ => exact absurd hinv (by intro h; cases h)
      | compute π ρ t =>
        obtain ⟨rest, hrest⟩ := hinv
        subst hrest
        cases t with
        | Var x =>
          cases hlk : ρ.lookup x with
          | none =>
            exfalso; apply h_not_err
            show step (.compute (rest ++ baseπ) ρ (.Var x)) = .error
            simp only [step, hlk]
          | some v_val =>
            have hstep : step (.compute (rest ++ baseπ) ρ (.Var x)) =
                .ret (rest ++ baseπ) v_val := by
              simp only [step, hlk]
            exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Constant c_pair =>
          obtain ⟨c, ty⟩ := c_pair
          have hstep : step (.compute (rest ++ baseπ) ρ (.Constant (c, ty))) =
              .ret (rest ++ baseπ) (.VCon c) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Builtin b =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Builtin b)) =
              .ret (rest ++ baseπ) (.VBuiltin b [] (expectedArgs b)) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Lam name body =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Lam name body)) =
              .ret (rest ++ baseπ) (.VLam body ρ) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Delay body =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Delay body)) =
              .ret (rest ++ baseπ) (.VDelay body ρ) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Force e =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Force e)) =
              .compute (.force :: (rest ++ baseπ)) ρ e := rfl
          have h_inv_next : hasSuffix baseπ (.compute (.force :: (rest ++ baseπ)) ρ e) := by
            refine ⟨.force :: rest, ?_⟩
            simp
          exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Apply f a =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Apply f a)) =
              .compute (.arg a ρ :: (rest ++ baseπ)) ρ f := rfl
          have h_inv_next : hasSuffix baseπ (.compute (.arg a ρ :: (rest ++ baseπ)) ρ f) := by
            refine ⟨.arg a ρ :: rest, ?_⟩
            simp
          exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Constr tag fs =>
          cases fs with
          | nil =>
            have hstep : step (.compute (rest ++ baseπ) ρ (.Constr tag [])) =
                .ret (rest ++ baseπ) (.VConstr tag []) := rfl
            exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
          | cons m ms =>
            have hstep : step (.compute (rest ++ baseπ) ρ (.Constr tag (m :: ms))) =
                .compute (.constrField tag [] ms ρ :: (rest ++ baseπ)) ρ m := rfl
            have h_inv_next : hasSuffix baseπ
                (.compute (.constrField tag [] ms ρ :: (rest ++ baseπ)) ρ m) := by
              refine ⟨.constrField tag [] ms ρ :: rest, ?_⟩
              simp
            exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Case scrut alts =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Case scrut alts)) =
              .compute (.caseScrutinee alts ρ :: (rest ++ baseπ)) ρ scrut := rfl
          have h_inv_next : hasSuffix baseπ
              (.compute (.caseScrutinee alts ρ :: (rest ++ baseπ)) ρ scrut) := by
            refine ⟨.caseScrutinee alts ρ :: rest, ?_⟩
            simp
          exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Error =>
          exfalso; apply h_not_err
          show step (.compute (rest ++ baseπ) ρ .Error) = .error
          rfl
      | ret π v =>
        obtain ⟨rest, hrest⟩ := hinv
        subst hrest
        cases rest with
        | nil => exact absurd ⟨v, rfl⟩ hat
        | cons f rest' =>
          cases f with
          | force =>
            cases v with
            | VDelay body ρ_v =>
              have hstep : step (.ret (.force :: rest' ++ baseπ) (.VDelay body ρ_v)) =
                  .compute (rest' ++ baseπ) ρ_v body := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | VBuiltin b args ea =>
              -- step is a nested match on ea.head and ea.tail
              -- Establish the unfolded form via rfl
              have hstep_form : step (.ret (.force :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                  (match ea.head with
                   | .argQ => (match ea.tail with
                       | some r => (.ret (rest' ++ baseπ) (.VBuiltin b args r) : State)
                       | none => (match evalBuiltin b args with
                           | some v' => .ret (rest' ++ baseπ) v'
                           | none => .error))
                   | .argV => .error) := rfl
              -- Rewrite hs_next and h_not_err using hstep_form
              rw [hstep_form] at hs_next h_not_err
              -- Now case analyze
              cases heh : ea.head with
              | argV =>
                rw [heh] at h_not_err
                exact absurd rfl h_not_err
              | argQ =>
                rw [heh] at hs_next h_not_err
                cases het : ea.tail with
                | some r =>
                  rw [het] at hs_next h_not_err
                  have h_inv_next : hasSuffix baseπ
                      (.ret (rest' ++ baseπ) (.VBuiltin b args r)) := ⟨rest', rfl⟩
                  obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                    ih (.ret (rest' ++ baseπ) (.VBuiltin b args r)) v_halt hs_next h_inv_next
                  refine ⟨m + 1, by omega, v_inner, ?_⟩
                  show steps (m + 1) (.ret (.force :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                      .ret baseπ v_inner
                  simp only [steps]
                  rw [hstep_form, heh, het]
                  exact hm_steps
                | none =>
                  rw [het] at hs_next h_not_err
                  cases hev : evalBuiltin b args with
                  | none =>
                    rw [hev] at h_not_err
                    exact absurd rfl h_not_err
                  | some v' =>
                    rw [hev] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ (.ret (rest' ++ baseπ) v') := ⟨rest', rfl⟩
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.ret (rest' ++ baseπ) v') v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1) (.ret (.force :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, heh, het, hev]
                    exact hm_steps
            | VCon c =>
              exfalso; apply h_not_err
              show step (.ret (.force :: rest' ++ baseπ) (.VCon c)) = .error
              rfl
            | VLam body ρ_l =>
              exfalso; apply h_not_err
              show step (.ret (.force :: rest' ++ baseπ) (.VLam body ρ_l)) = .error
              rfl
            | VConstr tag fields =>
              exfalso; apply h_not_err
              show step (.ret (.force :: rest' ++ baseπ) (.VConstr tag fields)) = .error
              rfl
          | arg a ρ_a =>
            have hstep : step (.ret (.arg a ρ_a :: rest' ++ baseπ) v) =
                .compute (.funV v :: (rest' ++ baseπ)) ρ_a a := rfl
            have h_inv_next : hasSuffix baseπ
                (.compute (.funV v :: (rest' ++ baseπ)) ρ_a a) := by
              refine ⟨.funV v :: rest', ?_⟩
              simp
            exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
          | funV vf =>
            cases vf with
            | VLam body ρ_l =>
              have hstep : step (.ret (.funV (.VLam body ρ_l) :: rest' ++ baseπ) v) =
                  .compute (rest' ++ baseπ) (ρ_l.extend v) body := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | VBuiltin b args ea =>
              have hstep_form : step (.ret (.funV (.VBuiltin b args ea) :: rest' ++ baseπ) v) =
                  (match ea.head with
                   | .argV => (match ea.tail with
                       | some r => (.ret (rest' ++ baseπ) (.VBuiltin b (v :: args) r) : State)
                       | none => (match evalBuiltin b (v :: args) with
                           | some v' => .ret (rest' ++ baseπ) v'
                           | none => .error))
                   | .argQ => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases heh : ea.head with
              | argQ =>
                rw [heh] at h_not_err
                exact absurd rfl h_not_err
              | argV =>
                rw [heh] at hs_next h_not_err
                cases het : ea.tail with
                | some r =>
                  rw [het] at hs_next h_not_err
                  have h_inv_next : hasSuffix baseπ
                      (.ret (rest' ++ baseπ) (.VBuiltin b (v :: args) r)) := ⟨rest', rfl⟩
                  obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                    ih (.ret (rest' ++ baseπ) (.VBuiltin b (v :: args) r)) v_halt hs_next h_inv_next
                  refine ⟨m + 1, by omega, v_inner, ?_⟩
                  show steps (m + 1) (.ret (.funV (.VBuiltin b args ea) :: rest' ++ baseπ) v) =
                      .ret baseπ v_inner
                  simp only [steps]
                  rw [hstep_form, heh, het]
                  exact hm_steps
                | none =>
                  rw [het] at hs_next h_not_err
                  cases hev : evalBuiltin b (v :: args) with
                  | none =>
                    rw [hev] at h_not_err
                    exact absurd rfl h_not_err
                  | some v' =>
                    rw [hev] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ (.ret (rest' ++ baseπ) v') := ⟨rest', rfl⟩
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.ret (rest' ++ baseπ) v') v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1) (.ret (.funV (.VBuiltin b args ea) :: rest' ++ baseπ) v) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, heh, het, hev]
                    exact hm_steps
            | VCon c =>
              exfalso; apply h_not_err
              show step (.ret (.funV (.VCon c) :: rest' ++ baseπ) v) = .error
              rfl
            | VDelay body ρ_d =>
              exfalso; apply h_not_err
              show step (.ret (.funV (.VDelay body ρ_d) :: rest' ++ baseπ) v) = .error
              rfl
            | VConstr tag fields =>
              exfalso; apply h_not_err
              show step (.ret (.funV (.VConstr tag fields) :: rest' ++ baseπ) v) = .error
              rfl
          | applyArg vx =>
            cases v with
            | VLam body ρ_l =>
              have hstep : step (.ret (.applyArg vx :: rest' ++ baseπ) (.VLam body ρ_l)) =
                  .compute (rest' ++ baseπ) (ρ_l.extend vx) body := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | VBuiltin b args ea =>
              have hstep_form : step (.ret (.applyArg vx :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                  (match ea.head with
                   | .argV => (match ea.tail with
                       | some r => (.ret (rest' ++ baseπ) (.VBuiltin b (vx :: args) r) : State)
                       | none => (match evalBuiltin b (vx :: args) with
                           | some v' => .ret (rest' ++ baseπ) v'
                           | none => .error))
                   | .argQ => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases heh : ea.head with
              | argQ =>
                rw [heh] at h_not_err
                exact absurd rfl h_not_err
              | argV =>
                rw [heh] at hs_next h_not_err
                cases het : ea.tail with
                | some r =>
                  rw [het] at hs_next h_not_err
                  have h_inv_next : hasSuffix baseπ
                      (.ret (rest' ++ baseπ) (.VBuiltin b (vx :: args) r)) := ⟨rest', rfl⟩
                  obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                    ih (.ret (rest' ++ baseπ) (.VBuiltin b (vx :: args) r)) v_halt hs_next h_inv_next
                  refine ⟨m + 1, by omega, v_inner, ?_⟩
                  show steps (m + 1) (.ret (.applyArg vx :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                      .ret baseπ v_inner
                  simp only [steps]
                  rw [hstep_form, heh, het]
                  exact hm_steps
                | none =>
                  rw [het] at hs_next h_not_err
                  cases hev : evalBuiltin b (vx :: args) with
                  | none =>
                    rw [hev] at h_not_err
                    exact absurd rfl h_not_err
                  | some v' =>
                    rw [hev] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ (.ret (rest' ++ baseπ) v') := ⟨rest', rfl⟩
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.ret (rest' ++ baseπ) v') v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1) (.ret (.applyArg vx :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, heh, het, hev]
                    exact hm_steps
            | VCon c =>
              exfalso; apply h_not_err
              show step (.ret (.applyArg vx :: rest' ++ baseπ) (.VCon c)) = .error
              rfl
            | VDelay body ρ_d =>
              exfalso; apply h_not_err
              show step (.ret (.applyArg vx :: rest' ++ baseπ) (.VDelay body ρ_d)) = .error
              rfl
            | VConstr tag fields =>
              exfalso; apply h_not_err
              show step (.ret (.applyArg vx :: rest' ++ baseπ) (.VConstr tag fields)) = .error
              rfl
          | constrField tag done ms ρ_c =>
            cases ms with
            | nil =>
              have hstep : step (.ret (.constrField tag done [] ρ_c :: rest' ++ baseπ) v) =
                  .ret (rest' ++ baseπ) (.VConstr tag ((v :: done).reverse)) := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | cons m ms_rest =>
              have hstep : step (.ret (.constrField tag done (m :: ms_rest) ρ_c :: rest' ++ baseπ) v) =
                  .compute (.constrField tag (v :: done) ms_rest ρ_c :: (rest' ++ baseπ)) ρ_c m := rfl
              have h_inv_next : hasSuffix baseπ
                  (.compute (.constrField tag (v :: done) ms_rest ρ_c :: (rest' ++ baseπ)) ρ_c m) := by
                refine ⟨.constrField tag (v :: done) ms_rest ρ_c :: rest', ?_⟩
                simp
              exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
          | caseScrutinee alts ρ_cs =>
            cases v with
            | VConstr tag_v fields_v =>
              have hstep_form :
                  step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VConstr tag_v fields_v)) =
                  (match alts[tag_v]? with
                   | some alt => (.compute (fields_v.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt : State)
                   | none => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases halts : alts[tag_v]? with
              | none =>
                rw [halts] at h_not_err
                exact absurd rfl h_not_err
              | some alt =>
                rw [halts] at hs_next h_not_err
                have h_inv_next : hasSuffix baseπ
                    (.compute (fields_v.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt) := by
                  refine ⟨fields_v.map Frame.applyArg ++ rest', ?_⟩
                  simp
                obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                  ih (.compute (fields_v.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt)
                     v_halt hs_next h_inv_next
                refine ⟨m + 1, by omega, v_inner, ?_⟩
                show steps (m + 1)
                    (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VConstr tag_v fields_v)) =
                    .ret baseπ v_inner
                simp only [steps]
                rw [hstep_form, halts]
                exact hm_steps
            | VCon c =>
              -- Establish the unfolded form of step for this state
              have hstep_form : step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VCon c)) =
                  (match constToTagAndFields c with
                   | some (tag, numCtors, fields) =>
                     (if numCtors > 0 && alts.length > numCtors then .error
                      else match alts[tag]? with
                        | some alt => (.compute (fields.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt : State)
                        | none => .error)
                   | none => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases htag : constToTagAndFields c with
              | none =>
                rw [htag] at h_not_err
                exact absurd rfl h_not_err
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple
                -- `rw [htag]` substitutes constToTagAndFields c = some (tag, numCtors, fields);
                -- `dsimp only` reduces the outer match on `some`.
                rw [htag] at hs_next h_not_err
                dsimp only at hs_next h_not_err
                -- Now goal has: if ... then .error else match alts[tag]? ...
                cases hb : (numCtors > 0 && alts.length > numCtors : Bool) with
                | true =>
                  rw [hb] at h_not_err
                  exact absurd rfl h_not_err
                | false =>
                  rw [hb] at hs_next h_not_err
                  cases halts : alts[tag]? with
                  | none =>
                    rw [halts] at h_not_err
                    exact absurd rfl h_not_err
                  | some alt =>
                    rw [halts] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ
                        (.compute (fields.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt) := by
                      refine ⟨fields.map Frame.applyArg ++ rest', ?_⟩
                      simp
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.compute (fields.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt)
                         v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1)
                        (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VCon c)) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, htag]
                    dsimp only
                    rw [hb, halts]
                    exact hm_steps
            | VLam body ρ_l =>
              exfalso; apply h_not_err
              show step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VLam body ρ_l)) = .error
              rfl
            | VDelay body ρ_d =>
              exfalso; apply h_not_err
              show step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VDelay body ρ_d)) = .error
              rfl
            | VBuiltin b args ea =>
              exfalso; apply h_not_err
              show step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VBuiltin b args ea)) = .error
              rfl

--------------------------------------------------------------------------------
-- 5b. Stack-polymorphic purity: `isPure e` implies `t_rhs` reaches
--     `ret π v_rhs` from any initial stack without ever being `.error`.
--
-- This is the semantic substitute for the syntactic `isPure e` precondition
-- used by `uplc_dead_let_refines`. It lifts `Moist.Verified.Purity`'s
-- empty-stack results (`isPure_halts` + `isPure_no_error`) to arbitrary
-- stacks via `Moist.Verified.StepLift.steps_liftState`.
--
-- Complicating factor: `Moist.Verified.Semantics.steps` and
-- `Moist.VerifiedNewNew.Equivalence.steps` are two *syntactically distinct*
-- copies of the iterated CEK step. A small bridge lemma `vstep_eq` proves
-- them equal by induction so we can freely convert between them.
--------------------------------------------------------------------------------

/-- The two `steps` definitions (`Verified.Semantics` and
    `VerifiedNewNew.Equivalence`) both iterate `Moist.CEK.step`; they are
    propositionally equal by an induction on the step count. -/
private theorem vstep_eq : ∀ (n : Nat) (s : State),
    Moist.VerifiedNewNew.Equivalence.steps n s = Moist.Verified.Semantics.steps n s
  | 0, _ => rfl
  | n + 1, s => by
    show Moist.VerifiedNewNew.Equivalence.steps n (step s) =
         Moist.Verified.Semantics.steps n (step s)
    exact vstep_eq n (step s)

/-- Stack-polymorphic version of `isPure_halts + isPure_no_error`: for a
    pure MIR expression `e` lowered to UPLC term `t` under a well-sized
    environment, the trace `compute π ρ t` reaches `ret π v` (for some
    `v`) in a bounded number of steps and never passes through `.error`
    along the way, for *any* initial stack `π`. Obtained by locating the
    first inactive step of the empty-stack trace (which is either
    `ret [] v` or `halt v` — both lift to `ret π v` via `liftState`) and
    invoking `steps_liftState`. -/
theorem dead_let_pure_stack_poly
    (env : List Moist.MIR.VarId) (e : Moist.MIR.Expr) {t : Moist.Plutus.Term.Term}
    {ρ : CekEnv}
    (hpure : Moist.MIR.isPure e = true)
    (hlower : Moist.MIR.lowerTotal env e = some t)
    (hwf : Moist.Verified.Semantics.WellSizedEnv env.length ρ) :
    ∀ (π : Stack), ∃ (m : Nat) (v : CekValue),
      steps m (.compute π ρ t) = .ret π v ∧
      ∀ k ≤ m, steps k (.compute π ρ t) ≠ .error := by
  intro π
  -- Extract halt witness from `isPure_halts` (uses Verified.Semantics.steps).
  obtain ⟨v, n_halt, h_halt_v⟩ :=
    Moist.Verified.Purity.isPure_halts e t env ρ hpure hlower hwf
  -- No-error at every step, via `isPure_no_error`.
  have h_noerr_v : ∀ k, Moist.Verified.Semantics.steps k (.compute [] ρ t) ≠ .error := by
    intro k h_err
    exact Moist.Verified.Purity.isPure_no_error e t env ρ hpure hlower hwf ⟨k, h_err⟩
  -- The `halt v` state is inactive, so there's at least one inactive step
  -- within the bound `n_halt`. Use `firstInactive` to locate the earliest.
  have h_halt_inactive : Moist.Verified.StepLift.isActive
      (Moist.Verified.Semantics.steps n_halt (.compute [] ρ t)) = false := by
    rw [h_halt_v]; simp [Moist.Verified.StepLift.isActive]
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ := Moist.Verified.StepLift.firstInactive
    (.compute [] ρ t) n_halt ⟨n_halt, Nat.le_refl _, h_halt_inactive⟩
  -- At step K, the state is inactive and not error (isPure_no_error).
  -- So it's either `ret [] v'` or `halt v'` for some `v'` — and in both
  -- cases, `liftState π` produces `ret π v'`.
  have hK_not_err : Moist.Verified.Semantics.steps K (.compute [] ρ t) ≠ .error := h_noerr_v K
  -- Case-analyze the state at step K.
  have hK_state_ret_pi : ∃ v',
      Moist.Verified.StepLift.liftState π
        (Moist.Verified.Semantics.steps K (.compute [] ρ t)) = .ret π v' := by
    cases h_s : Moist.Verified.Semantics.steps K (.compute [] ρ t) with
    | compute _ _ _ =>
      rw [h_s] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact
    | ret π' v' =>
      cases π' with
      | nil =>
        refine ⟨v', ?_⟩
        simp [Moist.Verified.StepLift.liftState]
      | cons _ _ =>
        rw [h_s] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact
    | halt v' =>
      refine ⟨v', ?_⟩
      simp [Moist.Verified.StepLift.liftState]
    | error => exact absurd h_s hK_not_err
  obtain ⟨v_ret, h_lift_K⟩ := hK_state_ret_pi
  -- Lift via steps_liftState at step K (all j < K are active).
  have h_lift_start : (.compute π ρ t : State) =
      Moist.Verified.StepLift.liftState π (.compute [] ρ t) := by
    simp [Moist.Verified.StepLift.liftState]
  have h_steps_K : Moist.Verified.Semantics.steps K
      (Moist.Verified.StepLift.liftState π (.compute [] ρ t)) =
      Moist.Verified.StepLift.liftState π
        (Moist.Verified.Semantics.steps K (.compute [] ρ t)) :=
    Moist.Verified.StepLift.steps_liftState π K (.compute [] ρ t) hK_min
  rw [h_lift_K] at h_steps_K
  -- Translate to `VerifiedNewNew.Equivalence.steps`.
  have h_reach_ret : steps K (.compute π ρ t) = .ret π v_ret := by
    rw [vstep_eq, h_lift_start]; exact h_steps_K
  refine ⟨K, v_ret, h_reach_ret, ?_⟩
  intro k hk
  -- No-error for k ≤ K: for k < K, state at k is active (not error) and
  -- lifts to a non-error; for k = K, state is `ret π v_ret`, not error.
  by_cases hk_eq : k = K
  · rw [hk_eq, h_reach_ret]; exact State.noConfusion
  · have hk_lt : k < K := by omega
    have h_lift_k : Moist.Verified.Semantics.steps k
        (Moist.Verified.StepLift.liftState π (.compute [] ρ t)) =
        Moist.Verified.StepLift.liftState π
          (Moist.Verified.Semantics.steps k (.compute [] ρ t)) := by
      apply Moist.Verified.StepLift.steps_liftState
      intro j hj; exact hK_min j (by omega)
    have h_equiv_k : steps k (.compute π ρ t) =
        Moist.Verified.StepLift.liftState π
          (Moist.Verified.Semantics.steps k (.compute [] ρ t)) := by
      rw [vstep_eq, h_lift_start]; exact h_lift_k
    intro h_err
    rw [h_err] at h_equiv_k
    -- The active state at step k can't lift to `.error`, so we get a contradiction.
    have h_active_k : Moist.Verified.StepLift.isActive
        (Moist.Verified.Semantics.steps k (.compute [] ρ t)) = true := hK_min k hk_lt
    cases hs : Moist.Verified.Semantics.steps k (.compute [] ρ t) with
    | compute _ _ _ => rw [hs] at h_equiv_k; simp [Moist.Verified.StepLift.liftState] at h_equiv_k
    | ret π' v' =>
      cases π' with
      | nil =>
        rw [hs] at h_active_k
        simp [Moist.Verified.StepLift.isActive] at h_active_k
      | cons _ _ => rw [hs] at h_equiv_k; simp [Moist.Verified.StepLift.liftState] at h_equiv_k
    | halt v' =>
      rw [hs] at h_active_k
      simp [Moist.Verified.StepLift.isActive] at h_active_k
    | error =>
      rw [hs] at h_active_k
      simp [Moist.Verified.StepLift.isActive] at h_active_k

--------------------------------------------------------------------------------
-- 6. uplc_dead_let_refines — the main theorem (no preconditions on rhs)
--------------------------------------------------------------------------------

/-- Unidirectional dead-let refinement at the UPLC level. Takes a
    stack-polymorphic halts-without-error witness for `t_rhs` (the semantic
    substitute for the syntactic `isPure e` condition): for every stack and
    every environment `ρ` that is well-sized at depth `d`, `t_rhs` reaches
    `ret π v_rhs` in some number of steps `m` without passing through
    `.error` along the way. This is what prevents the unsound
    transformation `Let x = Error in body ⊑ body`, since `Error`'s lowering
    would fail the no-error conjunct. The user-facing MIR wrapper
    `dead_let_mirRefines` derives this from MIR's syntactic `isPure`
    predicate via `Moist.Verified.Purity.isPure_halts` +
    `Moist.Verified.Purity.isPure_no_error`. -/
theorem uplc_dead_let_refines {d : Nat} {t_body : Term} (t_rhs : Term)
    (hclosed : closedAt d t_body = true)
    (h_rhs_halts : ∀ (ρ : CekEnv),
      (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∀ (π : Stack), ∃ (m : Nat) (v_rhs : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v_rhs ∧
        ∀ k ≤ m, steps k (.compute π ρ t_rhs) ≠ .error) :
    ∀ (k : Nat) (j : Nat), j ≤ k → ∀ (ρ₁ ρ₂ : CekEnv), EnvRefinesK j d ρ₁ ρ₂ →
      ∀ (i : Nat), i ≤ j → ∀ (π₁ π₂ : Stack), StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁
             (.Apply (.Lam 0 (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_body)) t_rhs))
          (.compute π₂ ρ₂ t_body) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  let shifted := Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_body
  -- Extract ρ₁'s well-sizedness from EnvRefinesK
  have hwf_ρ₁ : ∀ n, 0 < n → n ≤ d → ∃ v, ρ₁.lookup n = some v := by
    intro n hn hnd
    obtain ⟨v_l, _, hl, _, _⟩ := henv n hn hnd
    exact ⟨v_l, hl⟩
  -- Get t_rhs's halts-without-error witness for the funV-extended stack
  obtain ⟨m_rhs, v_rhs, hm_steps_fv, hm_noerr_fv⟩ :=
    h_rhs_halts ρ₁ hwf_ρ₁ (.funV (.VLam shifted ρ₁) :: π₁)
  refine ⟨?_, ?_⟩
  -- ── Halt clause ──
  · intro v ⟨n, hn_le_i, hs⟩
    have h3 : steps 3 (.compute π₁ ρ₁ (.Apply (.Lam 0 shifted) t_rhs)) =
        .compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs := by
      simp [steps, step, shifted]
    have h_n_ge_3 : n ≥ 3 := by
      rcases n with _ | _ | _ | n''
      · simp only [steps] at hs
        exact absurd hs State.noConfusion
      · simp only [steps, step] at hs
        exact absurd hs State.noConfusion
      · simp only [steps, step] at hs
        exact absurd hs State.noConfusion
      · omega
    have hs' : steps (n - 3) (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) = .halt v := by
      have heq : n = 3 + (n - 3) := by omega
      rw [heq, steps_trans 3 (n - 3), h3] at hs
      exact hs
    have h_suffix : hasSuffix (.funV (.VLam shifted ρ₁) :: π₁)
        (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) := ⟨[], rfl⟩
    obtain ⟨m, hm_le, v_rhs, hm_steps⟩ :=
      halt_descends_to_baseπ (n - 3)
        (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) v hs' h_suffix
    have h_after_funV :
        steps (m + 1) (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) =
          .compute π₁ (ρ₁.extend v_rhs) shifted := by
      rw [steps_trans m 1, hm_steps]
      show step (.ret (.funV (.VLam shifted ρ₁) :: π₁) v_rhs) =
          .compute π₁ (ρ₁.extend v_rhs) shifted
      rfl
    have hm_rest : m + 1 ≤ n - 3 := by
      rcases Nat.lt_or_ge (n - 3) (m + 1) with hgt | hle
      · exfalso
        have hm_eq : m + 1 = (n - 3) + (m + 1 - (n - 3)) := by omega
        rw [hm_eq, steps_trans (n - 3) (m + 1 - (n - 3)), hs',
            steps_halt_fixed] at h_after_funV
        exact State.noConfusion h_after_funV
      · exact hle
    have h_remain_halt : steps (n - 3 - (m + 1))
        (.compute π₁ (ρ₁.extend v_rhs) shifted) = .halt v := by
      have heq : n - 3 = (m + 1) + (n - 3 - (m + 1)) := by omega
      rw [heq, steps_trans (m + 1) (n - 3 - (m + 1)), h_after_funV] at hs'
      exact hs'
    have h_shift_refines : ObsRefinesK i
        (.compute π₁ (ρ₁.extend v_rhs) shifted)
        (.compute π₂ ρ₂ t_body) := by
      exact shiftRefines 1 d (by omega) t_body hclosed i i (Nat.le_refl _)
        (ρ₁.extend v_rhs) ρ₂ (shiftEnvRefK_mono hi (envRefinesK_to_shiftEnvRefK henv))
        i (Nat.le_refl _) π₁ π₂ hπ
    apply h_shift_refines.1 v
    refine ⟨n - 3 - (m + 1), ?_, h_remain_halt⟩
    omega
  -- ── Error clause ──
  -- LHS errors ⇒ either (a) the initial Apply/Lam steps err (impossible),
  -- (b) `t_rhs`'s own evaluation errors (ruled out by the no-error conjunct
  -- of `h_rhs_halts`), or (c) after the funV→compute handoff, `shifted`'s
  -- evaluation errors — which we forward to `body` via `shiftRefines`'s
  -- error clause.
  · intro n hn_le_i hs
    have h3 : steps 3 (.compute π₁ ρ₁ (.Apply (.Lam 0 shifted) t_rhs)) =
        .compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs := by
      simp [steps, step, shifted]
    have h_n_ge_3 : n ≥ 3 := by
      rcases n with _ | _ | _ | n''
      · simp only [steps] at hs
        exact absurd hs State.noConfusion
      · simp only [steps, step] at hs
        exact absurd hs State.noConfusion
      · simp only [steps, step] at hs
        exact absurd hs State.noConfusion
      · omega
    have hs' : steps (n - 3) (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) = .error := by
      have heq : n = 3 + (n - 3) := by omega
      rw [heq, steps_trans 3 (n - 3), h3] at hs
      exact hs
    -- After `t_rhs` halts to `v_rhs` at step `m_rhs`, the next step dispatches
    -- the `funV` frame into `compute π₁ (ρ₁.extend v_rhs) shifted`.
    have h_after_funV :
        steps (m_rhs + 1) (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) =
          .compute π₁ (ρ₁.extend v_rhs) shifted := by
      rw [steps_trans m_rhs 1, hm_steps_fv]
      show step (.ret (.funV (.VLam shifted ρ₁) :: π₁) v_rhs) =
          .compute π₁ (ρ₁.extend v_rhs) shifted
      rfl
    -- Case split on whether `n - 3` is within `t_rhs`'s own eval, at the
    -- funV-dispatch step, or deep into `shifted`'s evaluation.
    by_cases hcase : n - 3 ≤ m_rhs
    · -- Within `t_rhs`'s eval — contradicts the no-error conjunct.
      exact absurd hs' (hm_noerr_fv (n - 3) hcase)
    · -- Past `t_rhs`'s halting step.
      have h_gt : n - 3 > m_rhs := Nat.gt_of_not_le hcase
      by_cases heq : n - 3 = m_rhs + 1
      · -- Exactly at the funV-dispatch step: state is `compute π₁ … shifted`.
        rw [heq, h_after_funV] at hs'
        exact absurd hs' State.noConfusion
      · -- Strictly past the funV dispatch: error is inside `shifted`'s eval.
        have hcase' : n - 3 > m_rhs + 1 := by omega
        have h_shifted_err : steps (n - 3 - (m_rhs + 1))
            (.compute π₁ (ρ₁.extend v_rhs) shifted) = .error := by
          have heq' : n - 3 = (m_rhs + 1) + (n - 3 - (m_rhs + 1)) := by omega
          rw [heq', steps_trans (m_rhs + 1) (n - 3 - (m_rhs + 1)), h_after_funV] at hs'
          exact hs'
        have h_shift_refines : ObsRefinesK i
            (.compute π₁ (ρ₁.extend v_rhs) shifted)
            (.compute π₂ ρ₂ t_body) := by
          exact shiftRefines 1 d (by omega) t_body hclosed i i (Nat.le_refl _)
            (ρ₁.extend v_rhs) ρ₂ (shiftEnvRefK_mono hi (envRefinesK_to_shiftEnvRefK henv))
            i (Nat.le_refl _) π₁ π₂ hπ
        exact h_shift_refines.2 (n - 3 - (m_rhs + 1)) (by omega) h_shifted_err

--------------------------------------------------------------------------------
-- 7. dead_let_mirRefines — MIR-level unidirectional dead-let refinement
--
-- Lifts `uplc_dead_let_refines` to the MIR level against the new unidirectional
-- `MIRRefines` relation (which drops `WellSizedEnv` because unidirectional
-- soundness doesn't need it).
--
-- Hypotheses:
--   * `x` is unused in `body` (so `Let`'s lowering of `body` under `(x :: env)`
--      is exactly the shifted `body` under `env`, via `lowerTotal_prepend_unused`)
--   * `isPure e = true` (semantic halt-without-error witness for the dropped RHS)
--
-- Reasoning goes through `expandFix e` / `expandFix body`, using
-- `isPure_expandFix` and `expandFix_freeVars_not_contains` to transfer the
-- hypotheses into the expanded form.
--------------------------------------------------------------------------------

open Moist.VerifiedNewNew.MIR
open Moist.VerifiedNewNew.DeadLet (lowerTotal_closedAt)
open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal
  lowerTotal_prepend_unused lowerTotal_prepend_unused_none
  freeVars)

/-- MIR-level dead-let refinement. Takes the unused-in-body and purity
    hypotheses; reasoning goes through `expandFix e` / `expandFix body`,
    using `isPure_expandFix` and `expandFix_freeVars_not_contains` to transfer
    the hypotheses. -/
theorem dead_let_mirRefines {x : VarId} {e body : Expr}
    (hunused : (Moist.MIR.freeVars body).contains x = false)
    (hsafe : Moist.MIR.isPure e = true) :
    MIRRefines (.Let [(x, e, false)] body) body := by
  -- Derive preservation of freshness and purity under expandFix
  have hunused' : (Moist.MIR.freeVars (Moist.MIR.expandFix body)).contains x = false :=
    Moist.MIR.expandFix_freeVars_not_contains body x hunused
  have hsafe' : Moist.MIR.isPure (Moist.MIR.expandFix e) = true :=
    Moist.Verified.Purity.isPure_expandFix e hsafe
  refine ⟨?_, ?_⟩
  · -- Compile preservation: if Let lowers, body lowers
    intro env h_let
    -- Unfold lowerTotalExpr to reveal lowerTotal on expandFix'd expression
    have hlet_eq : lowerTotalExpr env (.Let [(x, e, false)] body) =
        lowerTotal env (.Let [(x, Moist.MIR.expandFix e, false)] (Moist.MIR.expandFix body)) := by
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds]
    have hbody_eq : lowerTotalExpr env body = lowerTotal env (Moist.MIR.expandFix body) := by
      simp only [lowerTotalExpr]
    rw [hlet_eq] at h_let
    rw [hbody_eq]
    cases hb_env : lowerTotal env (Moist.MIR.expandFix body) with
    | some _ => rfl
    | none =>
      exfalso
      have h_xe : lowerTotal (x :: env) (Moist.MIR.expandFix body) = none :=
        lowerTotal_prepend_unused_none env x _ hunused' hb_env
      simp only [Moist.MIR.lowerTotal.eq_11, Moist.MIR.lowerTotalLet.eq_2,
        Moist.MIR.lowerTotalLet.eq_1, h_xe, Option.bind_eq_bind] at h_let
      cases he : lowerTotal env (Moist.MIR.expandFix e) with
      | none => rw [he] at h_let; simp at h_let
      | some e_t => rw [he] at h_let; simp at h_let
  · -- Semantic part: MIROpenRef at every depth d
    intro d k env hlen
    have hlet_eq : lowerTotalExpr env (.Let [(x, e, false)] body) =
        lowerTotal env (.Let [(x, Moist.MIR.expandFix e, false)] (Moist.MIR.expandFix body)) := by
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds]
    have hbody_eq : lowerTotalExpr env body = lowerTotal env (Moist.MIR.expandFix body) := by
      simp only [lowerTotalExpr]
    rw [hlet_eq, hbody_eq]
    simp only [Moist.MIR.lowerTotal.eq_11, Moist.MIR.lowerTotalLet.eq_2,
      Moist.MIR.lowerTotalLet.eq_1, Option.bind_eq_bind]
    cases he : lowerTotal env (Moist.MIR.expandFix e) with
    | none => simp
    | some e_t =>
      simp only [Option.bind_some]
      cases hb_env : lowerTotal env (Moist.MIR.expandFix body) with
      | none =>
        have := lowerTotal_prepend_unused_none env x _ hunused' hb_env
        rw [this]
        simp
      | some body_t =>
        have hshift := lowerTotal_prepend_unused env x _ hunused' body_t hb_env
        rw [hshift]
        simp only [Option.bind_some]
        intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
        have hclosed : closedAt d body_t = true := by
          have := lowerTotal_closedAt env _ body_t hb_env
          rw [hlen] at this; exact this
        -- Construct the stack-polymorphic halts-without-error witness for
        -- `e_t` from the MIR-level `isPure e` precondition, via the
        -- `Moist.Verified.Purity` suite (`isPure_halts` + `isPure_no_error`)
        -- combined with `Moist.Verified.StepLift.steps_liftState`.
        have h_rhs_halts : ∀ (ρ : CekEnv),
            (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
            ∀ (π : Stack), ∃ (m : Nat) (v_rhs : CekValue),
              steps m (.compute π ρ e_t) = .ret π v_rhs ∧
              ∀ k ≤ m, steps k (.compute π ρ e_t) ≠ .error := by
          intro ρ hwf_ρ
          have hwf_v : Moist.Verified.Semantics.WellSizedEnv env.length ρ := by
            show ∀ n, 0 < n → n ≤ env.length → ∃ v, ρ.lookup n = some v
            rw [hlen]; exact hwf_ρ
          exact dead_let_pure_stack_poly env (Moist.MIR.expandFix e) hsafe' he hwf_v
        exact uplc_dead_let_refines e_t hclosed h_rhs_halts k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ

end Moist.VerifiedNewNew.DeadLetRefines
