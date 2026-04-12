import Moist.VerifiedNewNew.MIR
import Moist.VerifiedNewNew.Rename
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity
import Moist.MIR.LowerTotal

/-! # Dead Let Elimination Soundness -/

namespace Moist.VerifiedNewNew.DeadLet

open Moist.CEK
open Moist.MIR (Expr VarId VarSet lowerTotalExpr lowerTotal lowerTotalLet
                 expandFix expandFixBinds fixCount fixCountBinds
                 freeVars freeVarsLet isPure
                 lowerTotalExpr_eq_lowerTotal expandFix_id expandFixBinds_id
                 lowerTotal_prepend_unused lowerTotal_prepend_unused_none)
open Moist.Plutus.Term (Term)
open Moist.VerifiedNewNew.MIR
open Moist.VerifiedNewNew.Equivalence
open Moist.VerifiedNewNew (closedAt closedAtList)

structure MIRDeadLetCond (x : VarId) (e body : Expr) : Prop where
  unused : (freeVars body).contains x = false
  safe : isPure e = true
  fixFree : fixCount e + fixCount body = 0

--------------------------------------------------------------------------------
-- 1. Shift-extend lookup
--------------------------------------------------------------------------------

theorem extend_lookup_shift (ρ : CekEnv) (v : CekValue) (n : Nat) :
    (ρ.extend v).lookup (Moist.Verified.shiftRename 1 n) = ρ.lookup n := by
  cases n with
  | zero =>
    simp [Moist.Verified.shiftRename, CekEnv.extend, CekEnv.lookup]; cases ρ <;> rfl
  | succ m => simp [Moist.Verified.shiftRename, CekEnv.extend, CekEnv.lookup]

--------------------------------------------------------------------------------
-- 2. ShiftEnvEqK
--------------------------------------------------------------------------------

/-- Shifted environment relation: `ρ₁.lookup (shiftRename c n)` relates to `ρ₂.lookup n`. -/
def ShiftEnvEqK (c k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (Moist.Verified.shiftRename c n), ρ₂.lookup n with
    | some v₁, some v₂ => ValueEqK k v₁ v₂
    | none, none => True
    | _, _ => False

theorem shiftEnvEqK_mono {c j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : ShiftEnvEqK c k d ρ₁ ρ₂) : ShiftEnvEqK c j d ρ₁ ρ₂ := by
  intro n hn hnd; have := h n hn hnd
  cases h₁ : ρ₁.lookup (Moist.Verified.shiftRename c n) <;> cases h₂ : ρ₂.lookup n <;> simp_all
  exact valueEqK_mono hjk _ _ this

theorem envEqK_to_shiftEnvEqK {k d : Nat} {ρ₁ ρ₂ : CekEnv} {w : CekValue}
    (h : EnvEqK k d ρ₁ ρ₂) : ShiftEnvEqK 1 k d (ρ₁.extend w) ρ₂ := by
  intro n hn hnd
  have heq := extend_lookup_shift ρ₁ w n
  have henv := h n hn hnd
  cases h₁ : ρ₁.lookup n <;> cases h₂ : ρ₂.lookup n <;> simp_all

theorem shiftEnvEqK_extend {c k d : Nat} (hc : c ≥ 1)
    {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : ShiftEnvEqK c k d ρ₁ ρ₂) (hv : ValueEqK k v₁ v₂) :
    ShiftEnvEqK (c + 1) k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1
    -- shiftRename (c+1) 1 = 1 since 1 < c+1
    have hsr : Moist.Verified.shiftRename (c + 1) 1 = 1 := by
      simp [Moist.Verified.shiftRename]; omega
    simp [hsr, CekEnv.extend, CekEnv.lookup]; exact hv
  · have hn2 : n ≥ 2 := by omega
    match n, hn2 with
    | n' + 2, _ =>
    -- Reduce to henv at index n'+1
    have henv' := henv (n' + 1) (by omega) (by omega)
    -- Case 1: n'+2 ≥ c+1 → shiftRename (c+1) (n'+2) = n'+3
    -- Case 2: n'+2 < c+1 → shiftRename (c+1) (n'+2) = n'+2
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
-- 3. Stepping infrastructure
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

private theorem obsEqK_of_step_left {k : Nat} {s₁ s₂ : State}
    (h₁ : ∀ v, s₁ ≠ .halt v) (h : ObsEqK k (step s₁) s₂) : ObsEqK k s₁ s₂ :=
  ⟨fun v ⟨n, hn, hs⟩ => match n with
    | 0 => absurd hs (h₁ v) | m + 1 => h.1 v ⟨m, by omega, hs⟩,
   fun v ⟨n, hn, hs⟩ => let ⟨v', m, hm⟩ := h.2 v ⟨n, hn, hs⟩; ⟨v', m + 1, hm⟩⟩

private theorem obsEqK_of_steps_left {k m : Nat} {s₁ s₂ : State}
    (h_no_halt : ∀ j, j ≤ m → ∀ v, steps j s₁ ≠ .halt v)
    (h : ObsEqK k (steps m s₁) s₂) : ObsEqK k s₁ s₂ := by
  induction m generalizing s₁ with
  | zero => exact h
  | succ m ih =>
    apply obsEqK_of_step_left (fun v hv => h_no_halt 0 (by omega) v (by simp [steps]; exact hv))
    apply ih (fun j hj v hv => h_no_halt (j + 1) (by omega) v (by simp [steps]; exact hv))
    simp [steps] at h ⊢; exact h

--------------------------------------------------------------------------------
-- 4. shiftEquiv (core shift simulation)
--------------------------------------------------------------------------------

private theorem shiftConstrField {c d tag k : Nat}
    {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ => ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftEnvEqK c j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRelK ValueEqK i π₁ π₂ →
      ObsEqK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      ShiftEnvEqK c j d ρ₁ ρ₂ → ListRel (ValueEqK j) done₁ done₂ →
      StackRelK ValueEqK j π₁ π₂ →
      StackRelK ValueEqK j (.constrField tag done₁ ms₁ ρ₁ :: π₁)
                            (.constrField tag done₂ ms₂ ρ₂ :: π₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
    cases ms₂ with
    | cons => exact absurd hfields id
    | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    | n + 1 =>
    apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    simp only [step]
    have hrev : ListRel (ValueEqK n) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hdone))
        ⟨valueEqK_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueEqK (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse)) (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
    exact obsEqK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m₁ ms₁' ih =>
    cases ms₂ with
    | nil => exact absurd hfields id
    | cons m₂ ms₂' =>
    have hm := hfields.1
    have hfs := hfields.2
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    | n + 1 =>
    apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (shiftEnvEqK_mono (by omega) henv)
      (show ListRel (ValueEqK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueEqK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hdone⟩)
      (stackRelK_mono (by omega) hπ)

mutual
  private def shiftEquiv (c d : Nat) (hc : c ≥ 1)
      (t : Term) (ht : closedAt d t = true) (k : Nat) :
      ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftEnvEqK c j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRelK ValueEqK i π₁ π₂ →
          ObsEqK i
            (.compute π₁ ρ₁ (Moist.Verified.renameTerm (Moist.Verified.shiftRename c) t))
            (.compute π₂ ρ₂ t) := by
    intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    match t with
    | .Var n =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      simp [closedAt] at ht
      by_cases hn : n = 0
      · subst hn
        have : Moist.Verified.shiftRename c 0 = 0 := by simp [Moist.Verified.shiftRename]; omega
        simp [this]
        have h1 : ρ₁.lookup 0 = none := by cases ρ₁ <;> rfl
        have h2 : ρ₂.lookup 0 = none := by cases ρ₂ <;> rfl
        simp [h1, h2]; exact obsEqK_error _
      · have h_n := henv n (by omega) ht
        revert h_n
        cases ρ₁.lookup (Moist.Verified.shiftRename c n) <;> cases ρ₂.lookup n <;> intro h_n
        · exact obsEqK_error _
        · exact absurd h_n id
        · exact absurd h_n id
        · exact hπ i' (by omega) _ _ (valueEqK_mono (by omega : i' ≤ j) _ _ h_n)
    | .Constant c' =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1] | succ => simp only [ValueEqK])
    | .Builtin b =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1] | succ => simp [ValueEqK, ListRel])
    | .Error =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp [step]; exact obsEqK_error _
    | .Lam name body =>
      simp only [Moist.Verified.renameTerm]
      rw [Moist.Verified.liftRename_shiftRename (by omega : c ≥ 1)]
      simp [closedAt] at ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1]
        | succ m =>
          simp only [ValueEqK]
          intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
          exact shiftEquiv (c + 1) (d + 1) (by omega) body ht j'
            j' (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
            (shiftEnvEqK_extend hc (shiftEnvEqK_mono (by omega) henv) hargs)
            ib hib π₁' π₂' hπ')
    | .Delay body =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1]
        | succ m =>
          simp only [ValueEqK]
          intro j' hj' ib hib π₁' π₂' hπ'
          exact shiftEquiv c d hc body ht j'
            j' (Nat.le_refl _) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv)
            ib hib π₁' π₂' hπ')
    | .Apply f x =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      -- Evaluate f with arg frame StackRelK
      apply shiftEquiv c d hc f hf (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) i' (by omega)
      -- StackRelK for arg frame
      intro i₁ hi₁ v₁ v₂ hv
      match i₁ with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | m₁ + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      -- Evaluate x with funV frame StackRelK
      apply shiftEquiv c d hc x hx (m₁+1)
        (m₁+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) m₁ (by omega)
      -- StackRelK for funV frame — dispatch on function value
      -- This is IDENTICAL to compat_app_k's funV dispatch since it only
      -- depends on ValueEqK of the function values
      intro i₂ hi₂ w₁ w₂ hw
      match i₂ with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | m₂ + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      match v₁, v₂ with
      | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
        simp only [step, ValueEqK] at hv ⊢
        exact hv m₂ (by omega) w₁ w₂ (valueEqK_mono (by omega) w₁ w₂ hw)
          m₂ (Nat.le_refl _) π₁ π₂ (stackRelK_mono (by omega) hπ)
      | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
        simp only [ValueEqK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv
        simp only [step]
        split
        · split
          · rename_i rest _
            have hval : ValueEqK (m₂ + 1)
                (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
              simp only [ValueEqK]; refine ⟨trivial, trivial, ?_⟩; simp only [ListRel]
              exact ⟨valueEqK_mono (by omega) w₁ w₂ hw,
                     listRel_mono (fun a b h => valueEqK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
            exact obsEqK_mono (by omega) (hπ (m₂ + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat
              (by simp only [ListRel]
                  exact ⟨valueEqK_mono (by omega) w₁ w₂ hw,
                    listRel_mono (fun a b h => valueEqK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩)
              (stackRelK_mono (by omega) hπ)
        · exact obsEqK_error _
      | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
      | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsEqK_error _
      | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv
    | .Force e =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      apply shiftEquiv c d hc e ht (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) i' (by omega)
      -- StackRelK for force frame — same dispatch as compat_force_k
      intro j' hj' v₁ v₂ hv
      match j' with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | m + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      match v₁, v₂ with
      | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
        simp only [step, ValueEqK] at hv ⊢
        exact hv m (by omega) m (by omega) π₁ π₂ (stackRelK_mono (by omega) hπ)
      | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
        simp only [ValueEqK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv; simp only [step]
        split
        · split
          · rename_i rest _
            have hval : ValueEqK (m + 1)
                (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
              simp only [ValueEqK]; exact ⟨trivial, trivial, hargs_rel⟩
            exact obsEqK_mono (by omega) (hπ (m + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat hargs_rel (stackRelK_mono (by omega) hπ)
        · exact obsEqK_error _
      | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
      | .VLam _ _, .VLam _ _ => simp only [step]; exact obsEqK_error _
      | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv
    | .Constr tag fields =>
      simp only [Moist.Verified.renameTerm]
      match fields with
      | [] =>
        simp [Moist.Verified.renameTermList]
        match i with
        | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | i' + 1 =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        have : ValueEqK i' (.VConstr tag []) (.VConstr tag []) := by
          cases i' with | zero => simp only [ValueEqK.eq_1] | succ => simp [ValueEqK, ListRel]
        exact hπ i' (by omega) _ _ this
      | m :: ms =>
        simp [closedAt] at ht
        have hm : closedAt d m = true := by
          have := ht; simp [closedAtList] at this; exact this.1
        have hms : closedAtList d ms = true := by
          have := ht; simp [closedAtList] at this; exact this.2
        simp [Moist.Verified.renameTermList]
        match i with
        | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | i' + 1 =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply shiftEquiv c d hc m hm (i'+1)
          (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) i' (by omega)
        exact shiftConstrField (shiftEquivList c d hc ms hms (i'+1))
          (by omega) (shiftEnvEqK_mono (by omega) henv) trivial (stackRelK_mono (by omega) hπ)
    | .Case scrut alts =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      -- Evaluate scrutinee with caseScrutinee frame
      apply shiftEquiv c d hc scrut hscrut (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) i' (by omega)
      -- StackRelK for caseScrutinee frames
      -- LHS: .caseScrutinee (renameTermList (shiftRename c) alts) ρ₁
      -- RHS: .caseScrutinee alts ρ₂
      intro j' hj' v₁ v₂ hv
      match j' with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | n + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      match v₁, v₂ with
      | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
        simp only [ValueEqK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
        simp only [step]
        -- LHS looks up (renameTermList σ alts)[tag₁]?, RHS looks up alts[tag₁]?
        split
        · -- LHS found an alt in the renamed list
          rename_i alt₁ halt₁
          -- Need to show RHS also finds an alt
          have hlen_eq : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length = alts.length :=
            Moist.Verified.renameTermList_length _ _
          have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
          have hi₁ : tag₁ < (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length := hsome₁.1
          have hi₂ : tag₁ < alts.length := by omega
          have halt₂ : alts[tag₁]? = some (alts[tag₁]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
          rw [halt₂]; simp only []
          -- alt₁ = (renameTermList σ alts)[tag₁] = renameTerm σ (alts[tag₁])
          have hidx : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts)[tag₁]'hi₁ =
              Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (alts[tag₁]) :=
            Moist.Verified.renameTermList_getElem _ _ _ hi₂
          have heq₁ : alt₁ = Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (alts[tag₁]) := by
            have := hsome₁.2; rw [hidx] at this; exact this.symm
          rw [heq₁]
          -- Get the shift relation for alts[tag₁]
          have haltsList := shiftEquivList c d hc alts halts (i'+1)
          have halt_shift := listRel_getElem haltsList (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
          rw [hidx] at halt_shift
          apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) n (by omega)
          exact applyArgFrames_stackRelK
            (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hfields_v)
            (stackRelK_mono (by omega) hπ)
        · -- LHS: none — alt not found in renamed list
          rename_i hnone₁
          -- RHS must also be none since lists have same length
          have hlen_eq : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length = alts.length :=
            Moist.Verified.renameTermList_length _ _
          have hnone₂ : alts[tag₁]? = none := by
            rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
          rw [hnone₂]; simp only []; exact obsEqK_error _
      | .VCon c₁, .VCon c₂ =>
        simp only [ValueEqK] at hv; subst hv
        simp only [step]
        have hlen_eq : (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length = alts.length :=
          Moist.Verified.renameTermList_length _ _
        split
        · rename_i tag numCtors fields htag
          -- The numCtors check: LHS uses renamed list length, RHS uses original
          -- Since lengths are equal, both branches match
          have hif_eq : (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList (Moist.Verified.shiftRename c) alts).length > numCtors)) =
              (decide (numCtors > 0) && decide (alts.length > numCtors)) := by
            rw [hlen_eq]
          split
          · -- LHS error from numCtors check
            rename_i h_check
            rw [hif_eq] at h_check; simp [h_check]; exact obsEqK_error _
          · -- LHS passed numCtors check
            rename_i h_check
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
              have haltsList := shiftEquivList c d hc alts halts (i'+1)
              have halt_shift := listRel_getElem haltsList (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
              rw [hidx] at halt_shift
              apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (shiftEnvEqK_mono (by omega) henv) n (by omega)
              have hfields_vcon := constToTagAndFields_fields_vcon c₁
              rw [htag] at hfields_vcon
              exact applyArgFrames_stackRelK
                (listRel_refl_vcon n fields hfields_vcon)
                (stackRelK_mono (by omega) hπ)
            · rename_i hnone₁
              have hnone₂ : alts[tag]? = none := by
                rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
              rw [hnone₂]; simp only []; exact obsEqK_error _
        · exact obsEqK_error _
      | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsEqK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv
  termination_by sizeOf t

  private def shiftEquivList (c d : Nat) (hc : c ≥ 1)
      (ts : List Term) (hts : closedAtList d ts = true) (k : Nat) :
      ListRel (fun t₁ t₂ =>
        ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftEnvEqK c j d ρ₁ ρ₂ →
          ∀ i ≤ j, ∀ π₁ π₂, StackRelK ValueEqK i π₁ π₂ →
            ObsEqK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) ts)
        ts := by
    match ts, hts with
    | [], _ => simp [Moist.Verified.renameTermList]; trivial
    | t :: rest, hts =>
      simp [closedAtList] at hts
      simp [Moist.Verified.renameTermList]
      exact ⟨shiftEquiv c d hc t hts.1 k, shiftEquivList c d hc rest hts.2 k⟩
  termination_by sizeOf ts
end

--------------------------------------------------------------------------------
-- 4b. isPure_stack_ret: pure expressions return to the caller's stack
--------------------------------------------------------------------------------

open Moist.MIR (envLookupT envLookupT_bound lowerTotalList lowerTotalLet
                isPureList isPureBinds isForceable) in
open Moist.CEK (expectedArgs ExpectedArgs ArgKind) in
mutual
  private theorem isPure_stack_ret (e : Expr) (t : Term) (env : List VarId) (ρ : CekEnv)
      (hpure : isPure e = true) (hlower : lowerTotal env e = some t)
      (hwf : WellSizedEnv env.length ρ) (π : Stack) :
      ∃ v, Reaches (.compute π ρ t) (.ret π v) := by
    match e with
    -- Excluded by isPure = false
    | .Error => exact absurd hpure (by unfold isPure; decide)
    | .Fix _ _ => simp [lowerTotal] at hlower
    | .Case _ _ => exact absurd hpure (by unfold isPure; decide)
    | .App _ _ => exact absurd hpure (by unfold isPure; decide)
    -- Value forms: 1 step each
    | .Var x =>
      simp only [lowerTotal.eq_1] at hlower
      split at hlower
      · rename_i idx hlook
        injection hlower with hlower; subst hlower
        have hbound := envLookupT_bound env x idx hlook
        have ⟨v, hv⟩ := hwf (idx + 1) (by omega) (by omega)
        exact ⟨v, 1, by simp [steps, step, hv]⟩
      · simp at hlower
    | .Lit (c, ty) =>
      simp [lowerTotal] at hlower; subst hlower
      exact ⟨.VCon c, 1, rfl⟩
    | .Builtin b =>
      simp [lowerTotal] at hlower; subst hlower
      exact ⟨.VBuiltin b [] (expectedArgs b), 1, rfl⟩
    | .Lam x body =>
      simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨body', _, heq⟩ := hlower
      injection heq with heq; subst heq
      exact ⟨.VLam body' ρ, 1, rfl⟩
    | .Delay inner =>
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨inner', _, heq⟩ := hlower
      injection heq with heq; subst heq
      exact ⟨.VDelay inner' ρ, 1, rfl⟩
    -- Force (Delay body): 3 steps + IH
    | .Force (.Delay body) =>
      have hpb : isPure body = true := by
        change isPure (.Force (.Delay body)) = true at hpure
        simp only [isPure] at hpure; exact hpure
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨inner', hinner, heq⟩ := hlower
      injection heq with heq; subst heq
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at hinner
      obtain ⟨body', hbody, heq⟩ := hinner
      injection heq with heq; subst heq
      have ⟨v, n, hn⟩ := isPure_stack_ret body body' env ρ hpb hbody hwf π
      exact ⟨v, n + 3, by
        rw [show n + 3 = 3 + n from by omega, steps_trans 3]
        simp [steps, step]; exact hn⟩
    -- Force (Builtin b): single type-force
    | .Force (.Builtin b) =>
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨inner', hinner, heq⟩ := hlower
      injection heq with heq; subst heq
      simp [lowerTotal] at hinner; subst hinner
      have hhead : ((expectedArgs b).head == .argQ) = true := by
        simp only [isPure, isForceable, Bool.and_true] at hpure; exact hpure
      cases hea : expectedArgs b with
      | more k rest =>
        cases k with
        | argQ =>
          exact ⟨.VBuiltin b [] rest, 3, by
            simp [steps, step, hea, ExpectedArgs.head, ExpectedArgs.tail]⟩
        | argV =>
          exfalso
          have : (ExpectedArgs.more ArgKind.argV rest).head = ArgKind.argV := rfl
          rw [hea, this] at hhead
          exact absurd hhead (by native_decide)
      | one k =>
        cases k with
        | argQ =>
          exfalso; cases b <;> (simp [expectedArgs] at hea; try exact absurd hea (by native_decide))
        | argV =>
          exact absurd hhead (by rw [hea]; native_decide)
    -- Force (Force (Builtin b)): double type-force
    | .Force (.Force (.Builtin b)) =>
      simp [lowerTotal] at hlower; subst hlower
      have hfc : isForceable (.Force (.Builtin b)) = true := by
        simp only [isPure, Bool.and_eq_true] at hpure; exact hpure.1
      have hfc' : (match expectedArgs b with
          | .more .argQ rest => rest.head == .argQ | _ => false) = true := by
        simp only [isForceable] at hfc; exact hfc
      cases hea : expectedArgs b with
      | more k rest =>
        cases k with
        | argQ =>
          rw [hea] at hfc'; simp at hfc'
          cases hrest : rest with
          | more k2 rest2 =>
            cases k2 with
            | argQ =>
              exact ⟨.VBuiltin b [] rest2, 5, by
                simp [steps, step, hea, hrest, ExpectedArgs.head, ExpectedArgs.tail]⟩
            | argV =>
              exfalso
              have : (ExpectedArgs.more ArgKind.argV rest2).head = ArgKind.argV := rfl
              rw [hrest, this] at hfc'
              exact absurd hfc' (by native_decide)
          | one k2 =>
            cases k2 with
            | argQ =>
              exfalso; rw [hrest] at hea
              cases b <;> (simp [expectedArgs] at hea; try exact absurd hea (by native_decide))
            | argV =>
              rw [hrest] at hfc'
              have : (ExpectedArgs.one ArgKind.argV).head = ArgKind.argV := rfl
              rw [this] at hfc'; exact absurd hfc' (by native_decide)
        | argV => rw [hea] at hfc'; simp at hfc'
      | one _ => rw [hea] at hfc'; simp at hfc'
    -- Force of other forms: excluded by isPure/isForceable = false
    | .Force (.Var _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Lit _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Lam _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Fix _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.App _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Constr _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Case _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Let _ _) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force .Error => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Var _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Lit _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Lam _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Fix _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.App _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Constr _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Case _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Let _ _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force .Error) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Delay _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    | .Force (.Force (.Force _)) => exact absurd hpure (by unfold isPure isForceable; simp)
    -- Constr with pure args
    | .Constr tag args =>
      have hpure' : isPureList args = true := by
        change isPure (.Constr tag args) = true at hpure
        simp only [isPure] at hpure; exact hpure
      simp only [lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨args', hargs, heq⟩ := hlower
      injection heq with heq; subst heq
      exact constr_stack_ret args args' env ρ tag hpure' hargs hwf π
    -- Let with pure bindings and body
    | .Let binds body =>
      have hpure' : isPureBinds binds = true ∧ isPure body = true := by
        change isPure (.Let binds body) = true at hpure
        simp only [isPure, Bool.and_eq_true] at hpure; exact hpure
      simp only [lowerTotal.eq_11] at hlower
      exact isPureBinds_stack_ret binds body t env ρ hpure'.1 hpure'.2 hlower hwf π
  termination_by sizeOf e

  private theorem constr_field_stack_ret (ρ : CekEnv) (tag : Nat)
      (done : List CekValue) (v : CekValue)
      (remaining : List Term) (remainingE : List Expr)
      (env : List VarId) (π : Stack)
      (hpure : isPureList remainingE = true)
      (hlower : lowerTotalList env remainingE = some remaining)
      (hwf : WellSizedEnv env.length ρ) :
      ∃ vfinal, Reaches (.ret (.constrField tag done remaining ρ :: π) v) (.ret π vfinal) := by
    match remainingE with
    | [] =>
      simp [lowerTotalList] at hlower; subst hlower
      exact ⟨.VConstr tag ((v :: done).reverse), 1, by simp [steps, step]⟩
    | re :: restE =>
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨t, ht, ts, hts, heq⟩ := hlower
      injection heq with heq; subst heq
      have hpure' : isPure re = true ∧ isPureList restE = true := by
        simp only [isPureList, Bool.and_eq_true] at hpure; exact hpure
      have ⟨v', n', hn'⟩ := isPure_stack_ret re t env ρ hpure'.1 ht hwf
        (.constrField tag (v :: done) ts ρ :: π)
      have ⟨vfinal, m', hm'⟩ := constr_field_stack_ret ρ tag (v :: done) v'
        ts restE env π hpure'.2 hts hwf
      exact ⟨vfinal, 1 + n' + m', by
        rw [show 1 + n' + m' = 1 + (n' + m') from by omega, steps_trans 1]
        simp [steps, step]
        rw [steps_trans n', hn', hm']⟩
  termination_by sizeOf remainingE

  private theorem constr_stack_ret (args : List Expr) (args' : List Term)
      (env : List VarId) (ρ : CekEnv) (tag : Nat)
      (hpure : isPureList args = true)
      (hlower : lowerTotalList env args = some args')
      (hwf : WellSizedEnv env.length ρ) (π : Stack) :
      ∃ v, Reaches (.compute π ρ (.Constr tag args')) (.ret π v) := by
    match args with
    | [] =>
      simp [lowerTotalList] at hlower; subst hlower
      exact ⟨.VConstr tag [], 1, by simp [steps, step]⟩
    | a :: rest =>
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨t, ht, ts, hts, heq⟩ := hlower
      injection heq with heq; subst heq
      have hpure' : isPure a = true ∧ isPureList rest = true := by
        simp only [isPureList, Bool.and_eq_true] at hpure; exact hpure
      have ⟨v, n, hn⟩ := isPure_stack_ret a t env ρ hpure'.1 ht hwf
        (.constrField tag [] ts ρ :: π)
      have ⟨vfinal, m, hm⟩ := constr_field_stack_ret ρ tag [] v ts rest env π
        hpure'.2 hts hwf
      exact ⟨vfinal, 1 + n + m, by
        rw [show 1 + n + m = 1 + (n + m) from by omega, steps_trans 1]
        simp [steps, step]
        rw [steps_trans n, hn, hm]⟩
  termination_by sizeOf args

  private theorem isPureBinds_stack_ret
      (binds : List (VarId × Expr × Bool)) (body : Expr)
      (t : Term) (env : List VarId) (ρ : CekEnv)
      (hpureBinds : isPureBinds binds = true) (hpureBody : isPure body = true)
      (hlower : lowerTotalLet env binds body = some t)
      (hwf : WellSizedEnv env.length ρ) (π : Stack) :
      ∃ v, Reaches (.compute π ρ t) (.ret π v) := by
    match binds with
    | [] =>
      simp [lowerTotalLet] at hlower
      exact isPure_stack_ret body t env ρ hpureBody hlower hwf π
    | (x, rhs, _) :: rest =>
      have hpure' : isPure rhs = true ∧ isPureBinds rest = true := by
        change isPureBinds ((x, rhs, _) :: rest) = true at hpureBinds
        simp only [isPureBinds, Bool.and_eq_true] at hpureBinds; exact hpureBinds
      simp only [lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlower
      obtain ⟨rhs', hrhs_lower, rest', hrest_lower, heq⟩ := hlower
      injection heq with heq; subst heq
      -- t = Apply (Lam 0 rest') rhs'
      -- Steps:
      --   compute π ρ (Apply (Lam 0 rest') rhs')
      --   → compute (arg rhs' ρ :: π) ρ (Lam 0 rest')        [1 step]
      --   → ret (arg rhs' ρ :: π) (VLam rest' ρ)               [1 step]
      --   → compute (funV (VLam rest' ρ) :: π) ρ rhs'          [1 step]
      --   → (by IH on rhs) ret (funV (VLam rest' ρ) :: π) vrhs [n steps]
      --   → compute π (ρ.extend vrhs) rest'                    [1 step]
      --   → (by IH on rest body) ret π v                       [m steps]
      have ⟨vrhs, nrhs, hnrhs⟩ := isPure_stack_ret rhs rhs' env ρ hpure'.1 hrhs_lower hwf
        (.funV (.VLam rest' ρ) :: π)
      have ⟨vrest, mrest, hmrest⟩ :=
        isPureBinds_stack_ret rest body rest' (x :: env) (ρ.extend vrhs)
          hpure'.2 hpureBody hrest_lower (wellSizedEnv_extend hwf vrhs) π
      exact ⟨vrest, 3 + nrhs + 1 + mrest, by
        rw [show 3 + nrhs + 1 + mrest = 3 + (nrhs + (mrest + 1)) from by omega,
            steps_trans 3,
            show steps 3 (.compute π ρ (.Apply (.Lam 0 rest') rhs')) =
              .compute (.funV (.VLam rest' ρ) :: π) ρ rhs' from by simp [steps, step],
            steps_trans nrhs, hnrhs,
            show mrest + 1 = 1 + mrest from by omega,
            steps_trans 1,
            show steps 1 (.ret (.funV (.VLam rest' ρ) :: π) vrhs) =
              .compute π (ρ.extend vrhs) rest' from rfl,
            hmrest]⟩
  termination_by sizeOf binds + sizeOf body
end

--------------------------------------------------------------------------------
-- 5. uplc_dead_let
--------------------------------------------------------------------------------

theorem uplc_dead_let {k d : Nat} {t_body t_rhs : Term}
    (hpure_rhs : ∀ (ρ : CekEnv), WellSizedEnv d ρ →
      ∀ (π : Stack), ∃ v, Reaches (.compute π ρ t_rhs) (.ret π v))
    (hclosed : closedAt d t_body = true) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, WellSizedEnv d ρ₁ → WellSizedEnv d ρ₂ →
      EnvEqK j d ρ₁ ρ₂ → BehEqK ValueEqK j ρ₁ ρ₂
        (.Apply (.Lam 0 (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_body)) t_rhs)
        t_body := by
  intro j hj ρ₁ ρ₂ hw₁ _hw₂ henv i hi π₁ π₂ hπ
  let shifted := Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_body
  obtain ⟨v_rhs, m_rhs, hm_rhs⟩ := hpure_rhs ρ₁ hw₁ (.funV (.VLam shifted ρ₁) :: π₁)
  -- Compute: Apply (Lam 0 shifted) t_rhs
  --   step 1: compute (.arg t_rhs ρ₁ :: π₁) ρ₁ (Lam 0 shifted)
  --   step 2: ret (.arg t_rhs ρ₁ :: π₁) (VLam shifted ρ₁)
  --   step 3: compute (.funV (VLam shifted ρ₁) :: π₁) ρ₁ t_rhs
  --   step 3 + m_rhs: ret (.funV (VLam shifted ρ₁) :: π₁) v_rhs
  --   step 3 + m_rhs + 1: compute π₁ (ρ₁.extend v_rhs) shifted
  -- First, step through the initial 3 steps
  have h3 : steps 3 (.compute π₁ ρ₁ (.Apply (.Lam 0 shifted) t_rhs)) =
      .compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs := by
    simp [steps, step, shifted]
  -- Then step through m_rhs evaluating t_rhs, then 1 more step for the function application
  have h_rest : steps (m_rhs + 1) (.compute (.funV (.VLam shifted ρ₁) :: π₁) ρ₁ t_rhs) =
      .compute π₁ (ρ₁.extend v_rhs) shifted := by
    rw [steps_trans m_rhs, hm_rhs]; simp [steps, step]
  have h_total : 3 + m_rhs + 1 = 3 + (m_rhs + 1) := by omega
  have h_overhead : steps (3 + m_rhs + 1) (.compute π₁ ρ₁ (.Apply (.Lam 0 shifted) t_rhs)) =
      .compute π₁ (ρ₁.extend v_rhs) shifted := by
    rw [h_total, steps_trans 3, h3, h_rest]
  have h_no_halt := no_halt_before_reach h_overhead (fun _ => State.noConfusion)
  have h_shifted : ObsEqK i
      (steps (3 + m_rhs + 1) (.compute π₁ ρ₁ (.Apply (.Lam 0 shifted) t_rhs)))
      (.compute π₂ ρ₂ t_body) := by
    rw [h_overhead]
    exact shiftEquiv 1 d (by omega) t_body hclosed i i (Nat.le_refl _)
      (ρ₁.extend v_rhs) ρ₂ (shiftEnvEqK_mono hi (envEqK_to_shiftEnvEqK henv))
      i (Nat.le_refl _) π₁ π₂ hπ
  exact obsEqK_of_steps_left h_no_halt h_shifted

--------------------------------------------------------------------------------
-- 6. Lowering & main theorem
--------------------------------------------------------------------------------

private theorem lowerExpr_eq (env : List VarId) (e : Expr)
    (h : fixCount e = 0) : lowerTotalExpr env e = lowerTotal env e :=
  lowerTotalExpr_eq_lowerTotal env e h

private theorem lowerTotal_body_of_extended {env : List VarId} {x : VarId} {body : Expr}
    (hunused : (freeVars body).contains x = false)
    (hext : (lowerTotal (x :: env) body).isSome) :
    (lowerTotal env body).isSome := by
  cases henv : lowerTotal env body with
  | some _ => simp
  | none => have := lowerTotal_prepend_unused_none env x body hunused henv; simp [this] at hext

--------------------------------------------------------------------------------
-- Bridge: lowerTotal_closedAt for VerifiedNewNew.closedAt
--------------------------------------------------------------------------------

open Moist.MIR (envLookupT_bound lowerTotalList) in
mutual
  private theorem lowerTotal_closedAt (env : List VarId) (e : Expr) (t : Term)
      (h : lowerTotal env e = some t) : closedAt env.length t = true := by
    match e with
    | .Var x =>
      simp only [lowerTotal.eq_1] at h; split at h
      · rename_i idx hlook; injection h with h; subst h; simp [closedAt]
        have := envLookupT_bound env x idx hlook; omega
      · injection h
    | .Lit (c, ty) =>
      simp only [lowerTotal.eq_2] at h; injection h with h; subst h; simp [closedAt]
    | .Builtin b =>
      simp only [lowerTotal.eq_3] at h; injection h with h; subst h; simp [closedAt]
    | .Error =>
      simp only [lowerTotal.eq_4] at h; injection h with h; subst h; simp [closedAt]
    | .Lam x body =>
      simp only [lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨body', hbody, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; have := lowerTotal_closedAt (x :: env) body body' hbody
      simp at this; exact this
    | .App f x =>
      simp only [lowerTotal.eq_6, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f', hf, x', hx, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env f f' hf, lowerTotal_closedAt env x x' hx⟩
    | .Force inner =>
      simp only [lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Delay inner =>
      simp only [lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Constr tag args =>
      simp only [lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨args', hargs, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotalList_closedAtList env args args' hargs
    | .Case scrut alts =>
      simp only [lowerTotal.eq_10, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨scrut', hscrut, alts', halts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env scrut scrut' hscrut,
             lowerTotalList_closedAtList env alts alts' halts⟩
    | .Let binds body =>
      simp only [lowerTotal.eq_11] at h; exact lowerTotalLet_closedAt env binds body t h
    | .Fix _ _ => simp only [lowerTotal.eq_12] at h; injection h
  termination_by sizeOf e

  private theorem lowerTotalList_closedAtList (env : List VarId) (es : List Expr)
      (ts : List Term) (h : lowerTotalList env es = some ts) :
      closedAtList env.length ts = true := by
    match es with
    | [] => simp only [lowerTotalList.eq_1] at h; injection h with h; subst h; simp [closedAtList]
    | e :: rest =>
      simp only [lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ts', hts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAtList, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env e t ht, lowerTotalList_closedAtList env rest ts' hts⟩
  termination_by sizeOf es

  private theorem lowerTotalLet_closedAt (env : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Term)
      (h : Moist.MIR.lowerTotalLet env binds body = some t) :
      closedAt env.length t = true := by
    match binds with
    | [] => simp only [Moist.MIR.lowerTotalLet.eq_1] at h; exact lowerTotal_closedAt env body t h
    | (x, rhs, _) :: rest =>
      simp only [Moist.MIR.lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rhs', hrhs, rest', hrest, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      have := lowerTotalLet_closedAt (x :: env) rest body rest' hrest
      simp at this; exact ⟨this, lowerTotal_closedAt env rhs rhs' hrhs⟩
  termination_by sizeOf binds + sizeOf body
end

--------------------------------------------------------------------------------
-- 7. Main theorem
--------------------------------------------------------------------------------

theorem dead_let_sound (x : VarId) (e body : Expr)
    (hsc : MIRDeadLetCond x e body) :
    .Let [(x, e, false)] body ⊑ᴹ body := by
  have hfc_e : fixCount e = 0 := by have := hsc.fixFree; omega
  have hfc_b : fixCount body = 0 := by have := hsc.fixFree; omega
  have hfc_let : fixCount (.Let [(x, e, false)] body) = 0 := by
    simp only [fixCount, fixCountBinds]; omega
  constructor
  · -- Part 1: Lowering preservation
    intro env h_let
    rw [lowerTotalExpr_eq_lowerTotal env body hfc_b]
    rw [lowerTotalExpr_eq_lowerTotal env (.Let [(x, e, false)] body) hfc_let] at h_let
    -- Decompose the let lowering
    have hlower_let : lowerTotal env (.Let [(x, e, false)] body) =
        (do let e' ← lowerTotal env e
            let b' ← lowerTotal (x :: env) body
            some (Term.Apply (Term.Lam 0 b') e')) := by
      rw [lowerTotal.eq_11, Moist.MIR.lowerTotalLet.eq_2, Moist.MIR.lowerTotalLet.eq_1]
    rw [hlower_let] at h_let
    -- The let lowers, so both lowerTotal env e and lowerTotal (x :: env) body succeed
    cases he : lowerTotal env e with
    | none => simp [he] at h_let
    | some _ =>
      cases hbx : lowerTotal (x :: env) body with
      | none => simp [he, hbx] at h_let
      | some _ => exact lowerTotal_body_of_extended hsc.unused (by simp [hbx])
  · -- Part 2: Behavioral equivalence (∀ d, MIROpenEq d LHS RHS)
    intro d k env hlen
    rw [lowerTotalExpr_eq_lowerTotal env (.Let [(x, e, false)] body) hfc_let,
        lowerTotalExpr_eq_lowerTotal env body hfc_b]
    -- Decompose the let lowering
    have hlower_let : lowerTotal env (.Let [(x, e, false)] body) =
        (do let e' ← lowerTotal env e
            let b' ← lowerTotal (x :: env) body
            some (Term.Apply (Term.Lam 0 b') e')) := by
      rw [lowerTotal.eq_11, Moist.MIR.lowerTotalLet.eq_2, Moist.MIR.lowerTotalLet.eq_1]
    cases hb : lowerTotal env body with
    | none =>
      -- body doesn't lower → match gives True for any LHS result
      rw [hlower_let]; simp only [Option.bind_eq_bind]; split <;> trivial
    | some body_t =>
      -- body_x = renameTerm (shiftRename 1) body_t
      have hbx := lowerTotal_prepend_unused env x body hsc.unused body_t hb
      cases he : lowerTotal env e with
      | none =>
        -- e doesn't lower → let doesn't lower → vacuous
        rw [hlower_let]; simp [he]
      | some rhs_t =>
        -- Both lower successfully
        rw [hlower_let]; simp [he, hbx]
        -- Goal: OpenEqK k d (Apply (Lam 0 (renameTerm (shiftRename 1) body_t)) rhs_t) body_t
        have hclosed : closedAt d body_t = true := by
          have := lowerTotal_closedAt env body body_t hb; rw [hlen] at this; exact this
        exact uplc_dead_let
          (fun ρ hwf π => isPure_stack_ret e rhs_t env ρ hsc.safe he (hlen ▸ hwf) π)
          hclosed

--------------------------------------------------------------------------------
-- 7a. shiftByN: shift by arbitrary amount
--------------------------------------------------------------------------------

private def shiftByN (a c : Nat) (n : Nat) : Nat :=
  if n ≥ c then n + a else n

private theorem shiftByN_zero_eq_id (c : Nat) : shiftByN 0 c = id := by
  funext n; simp [shiftByN, id]

private theorem shiftByN_one_eq_shiftRename (c : Nat) :
    shiftByN 1 c = Moist.Verified.shiftRename c := by
  funext n; simp [shiftByN, Moist.Verified.shiftRename]

private theorem liftRename_shiftByN {a c : Nat} (hc : c ≥ 1) :
    Moist.Verified.liftRename (shiftByN a c) = shiftByN a (c + 1) := by
  funext n; cases n with
  | zero => simp [Moist.Verified.liftRename, shiftByN]
  | succ m => cases m with
    | zero =>
      simp only [Moist.Verified.liftRename, shiftByN]
      have : ¬ (c ≤ 0) := by omega
      simp [this]
    | succ k =>
      simp only [Moist.Verified.liftRename, shiftByN]
      split <;> split <;> omega

private theorem shiftByN_comp (m n c : Nat) :
    ∀ k, shiftByN m c (shiftByN n c k) = shiftByN (m + n) c k := by
  intro k; unfold shiftByN
  by_cases hkc : k ≥ c
  · simp [hkc, show k + n ≥ c by omega]; omega
  · simp [show ¬(k ≥ c) from hkc]

--------------------------------------------------------------------------------
-- 7b. renameTerm composition: shiftByN m c ∘ shiftByN n c = shiftByN (m+n) c
--------------------------------------------------------------------------------

mutual
  private theorem renameTerm_shiftByN_comp (m n c : Nat) (hc : c ≥ 1) (t : Term) :
      Moist.Verified.renameTerm (shiftByN m c)
        (Moist.Verified.renameTerm (shiftByN n c) t) =
      Moist.Verified.renameTerm (shiftByN (m + n) c) t := by
    match t with
    | .Var k =>
      simp [Moist.Verified.renameTerm, shiftByN_comp]
    | .Constant _ | .Builtin _ | .Error =>
      simp [Moist.Verified.renameTerm]
    | .Lam name body =>
      simp only [Moist.Verified.renameTerm]
      rw [liftRename_shiftByN (by omega : c ≥ 1)]
      rw [liftRename_shiftByN (by omega : c ≥ 1)]
      rw [liftRename_shiftByN (by omega : c ≥ 1)]
      congr 1; exact renameTerm_shiftByN_comp m n (c + 1) (by omega) body
    | .Apply f x =>
      simp only [Moist.Verified.renameTerm]
      congr 1
      · exact renameTerm_shiftByN_comp m n c hc f
      · exact renameTerm_shiftByN_comp m n c hc x
    | .Force e =>
      simp only [Moist.Verified.renameTerm]
      exact congrArg _ (renameTerm_shiftByN_comp m n c hc e)
    | .Delay e =>
      simp only [Moist.Verified.renameTerm]
      exact congrArg _ (renameTerm_shiftByN_comp m n c hc e)
    | .Constr tag args =>
      simp only [Moist.Verified.renameTerm]
      congr 1; exact renameTermList_shiftByN_comp m n c hc args
    | .Case scrut alts =>
      simp only [Moist.Verified.renameTerm]
      congr 1
      · exact renameTerm_shiftByN_comp m n c hc scrut
      · exact renameTermList_shiftByN_comp m n c hc alts
  termination_by sizeOf t

  private theorem renameTermList_shiftByN_comp (m n c : Nat) (hc : c ≥ 1) (ts : List Term) :
      Moist.Verified.renameTermList (shiftByN m c)
        (Moist.Verified.renameTermList (shiftByN n c) ts) =
      Moist.Verified.renameTermList (shiftByN (m + n) c) ts := by
    match ts with
    | [] => simp [Moist.Verified.renameTermList]
    | t :: rest =>
      simp only [Moist.Verified.renameTermList]
      congr 1
      · exact renameTerm_shiftByN_comp m n c hc t
      · exact renameTermList_shiftByN_comp m n c hc rest
  termination_by sizeOf ts
end

--------------------------------------------------------------------------------
-- 7c. ShiftByNEnvEqK
--------------------------------------------------------------------------------

private def ShiftByNEnvEqK (a c k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (shiftByN a c n), ρ₂.lookup n with
    | some v₁, some v₂ => ValueEqK k v₁ v₂
    | none, none => True
    | _, _ => False

private theorem shiftByNEnvEqK_mono {a c j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : ShiftByNEnvEqK a c k d ρ₁ ρ₂) : ShiftByNEnvEqK a c j d ρ₁ ρ₂ := by
  intro n hn hnd; have := h n hn hnd
  cases h₁ : ρ₁.lookup (shiftByN a c n) <;> cases h₂ : ρ₂.lookup n <;> simp_all
  exact valueEqK_mono hjk _ _ this

private theorem extend_lookup_ge2 (ρ : CekEnv) (v : CekValue) (n : Nat) (hn : n ≥ 2) :
    (ρ.extend v).lookup n = ρ.lookup (n - 1) := by
  match n, hn with
  | n' + 2, _ => simp [CekEnv.extend, CekEnv.lookup]

private theorem shiftByNEnvEqK_extend {a c k d : Nat} (hc : c ≥ 1)
    {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : ShiftByNEnvEqK a c k d ρ₁ ρ₂) (hv : ValueEqK k v₁ v₂) :
    ShiftByNEnvEqK a (c + 1) k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1
    have hsr : shiftByN a (c + 1) 1 = 1 := by simp [shiftByN]; omega
    simp [hsr, CekEnv.extend, CekEnv.lookup]; exact hv
  · have hn2 : n ≥ 2 := by omega
    have henv' := henv (n - 1) (by omega) (by omega)
    -- Reduce RHS lookup: (ρ₂.extend v₂).lookup n = ρ₂.lookup (n - 1) for n ≥ 2
    rw [extend_lookup_ge2 ρ₂ v₂ n hn2]
    -- Reduce LHS: shiftByN a (c+1) n and (ρ₁.extend v₁).lookup
    by_cases hge : n ≥ c + 1
    · -- shiftByN a (c+1) n = n + a, so n + a ≥ c + 1 + a ≥ 2
      have hsr1 : shiftByN a (c + 1) n = n + a := by simp [shiftByN]; omega
      have hsr2 : shiftByN a c (n - 1) = (n - 1) + a := by simp [shiftByN]; omega
      rw [hsr1, extend_lookup_ge2 ρ₁ v₁ (n + a) (by omega)]
      rw [show n + a - 1 = (n - 1) + a from by omega]
      rw [hsr2] at henv'; exact henv'
    · -- shiftByN a (c+1) n = n, so n ≥ 2
      have hsr1 : shiftByN a (c + 1) n = n := by simp [shiftByN]; omega
      have hsr2 : shiftByN a c (n - 1) = n - 1 := by simp [shiftByN]; omega
      rw [hsr1, extend_lookup_ge2 ρ₁ v₁ n hn2]
      rw [show n - 1 = n - 1 from rfl]
      rw [hsr2] at henv'; exact henv'

--------------------------------------------------------------------------------
-- 7d. shiftByNEquiv (core shift simulation generalized to arbitrary shift)
--------------------------------------------------------------------------------

private theorem shiftByNConstrField {a c d tag k : Nat}
    {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ => ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftByNEnvEqK a c j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRelK ValueEqK i π₁ π₂ →
      ObsEqK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      ShiftByNEnvEqK a c j d ρ₁ ρ₂ → ListRel (ValueEqK j) done₁ done₂ →
      StackRelK ValueEqK j π₁ π₂ →
      StackRelK ValueEqK j (.constrField tag done₁ ms₁ ρ₁ :: π₁)
                            (.constrField tag done₂ ms₂ ρ₂ :: π₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
    cases ms₂ with
    | cons => exact absurd hfields id
    | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    | n + 1 =>
    apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    simp only [step]
    have hrev : ListRel (ValueEqK n) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hdone))
        ⟨valueEqK_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueEqK (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse)) (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
    exact obsEqK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m₁ ms₁' ih =>
    cases ms₂ with
    | nil => exact absurd hfields id
    | cons m₂ ms₂' =>
    have hm := hfields.1
    have hfs := hfields.2
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    | n + 1 =>
    apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (shiftByNEnvEqK_mono (by omega) henv)
      (show ListRel (ValueEqK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueEqK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hdone⟩)
      (stackRelK_mono (by omega) hπ)

mutual
  private def shiftByNEquiv (a c d : Nat) (hc : c ≥ 1)
      (t : Term) (ht : closedAt d t = true) (k : Nat) :
      ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftByNEnvEqK a c j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRelK ValueEqK i π₁ π₂ →
          ObsEqK i
            (.compute π₁ ρ₁ (Moist.Verified.renameTerm (shiftByN a c) t))
            (.compute π₂ ρ₂ t) := by
    intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    match t with
    | .Var n =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      simp [closedAt] at ht
      by_cases hn : n = 0
      · subst hn
        have : shiftByN a c 0 = 0 := by simp [shiftByN]; omega
        simp [this]
        have h1 : ρ₁.lookup 0 = none := by cases ρ₁ <;> rfl
        have h2 : ρ₂.lookup 0 = none := by cases ρ₂ <;> rfl
        simp [h1, h2]; exact obsEqK_error _
      · have h_n := henv n (by omega) ht
        revert h_n
        cases ρ₁.lookup (shiftByN a c n) <;> cases ρ₂.lookup n <;> intro h_n
        · exact obsEqK_error _
        · exact absurd h_n id
        · exact absurd h_n id
        · exact hπ i' (by omega) _ _ (valueEqK_mono (by omega : i' ≤ j) _ _ h_n)
    | .Constant c' =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1] | succ => simp only [ValueEqK])
    | .Builtin b =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1] | succ => simp [ValueEqK, ListRel])
    | .Error =>
      simp [Moist.Verified.renameTerm]
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp [step]; exact obsEqK_error _
    | .Lam name body =>
      simp only [Moist.Verified.renameTerm]
      rw [liftRename_shiftByN (by omega : c ≥ 1)]
      simp [closedAt] at ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1]
        | succ m =>
          simp only [ValueEqK]
          intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
          exact shiftByNEquiv a (c + 1) (d + 1) (by omega) body ht j'
            j' (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
            (shiftByNEnvEqK_extend hc (shiftByNEnvEqK_mono (by omega) henv) hargs)
            ib hib π₁' π₂' hπ')
    | .Delay body =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK.eq_1]
        | succ m =>
          simp only [ValueEqK]
          intro j' hj' ib hib π₁' π₂' hπ'
          exact shiftByNEquiv a c d hc body ht j'
            j' (Nat.le_refl _) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv)
            ib hib π₁' π₂' hπ')
    | .Apply f x =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      apply shiftByNEquiv a c d hc f hf (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) i' (by omega)
      intro i₁ hi₁ v₁ v₂ hv
      match i₁ with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | m₁ + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      apply shiftByNEquiv a c d hc x hx (m₁+1)
        (m₁+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) m₁ (by omega)
      intro i₂ hi₂ w₁ w₂ hw
      match i₂ with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | m₂ + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      match v₁, v₂ with
      | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
        simp only [step, ValueEqK] at hv ⊢
        exact hv m₂ (by omega) w₁ w₂ (valueEqK_mono (by omega) w₁ w₂ hw)
          m₂ (Nat.le_refl _) π₁ π₂ (stackRelK_mono (by omega) hπ)
      | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
        simp only [ValueEqK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv
        simp only [step]
        split
        · split
          · rename_i rest _
            have hval : ValueEqK (m₂ + 1)
                (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
              simp only [ValueEqK]; refine ⟨trivial, trivial, ?_⟩; simp only [ListRel]
              exact ⟨valueEqK_mono (by omega) w₁ w₂ hw,
                     listRel_mono (fun a b h => valueEqK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
            exact obsEqK_mono (by omega) (hπ (m₂ + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat
              (by simp only [ListRel]
                  exact ⟨valueEqK_mono (by omega) w₁ w₂ hw,
                    listRel_mono (fun a b h => valueEqK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩)
              (stackRelK_mono (by omega) hπ)
        · exact obsEqK_error _
      | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
      | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsEqK_error _
      | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv
    | .Force e =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      apply shiftByNEquiv a c d hc e ht (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) i' (by omega)
      intro j' hj' v₁ v₂ hv
      match j' with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | m + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      match v₁, v₂ with
      | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
        simp only [step, ValueEqK] at hv ⊢
        exact hv m (by omega) m (by omega) π₁ π₂ (stackRelK_mono (by omega) hπ)
      | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
        simp only [ValueEqK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv; simp only [step]
        split
        · split
          · rename_i rest _
            have hval : ValueEqK (m + 1)
                (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
              simp only [ValueEqK]; exact ⟨trivial, trivial, hargs_rel⟩
            exact obsEqK_mono (by omega) (hπ (m + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat hargs_rel (stackRelK_mono (by omega) hπ)
        · exact obsEqK_error _
      | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
      | .VLam _ _, .VLam _ _ => simp only [step]; exact obsEqK_error _
      | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv
    | .Constr tag fields =>
      simp only [Moist.Verified.renameTerm]
      match fields with
      | [] =>
        simp [Moist.Verified.renameTermList]
        match i with
        | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | i' + 1 =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        have : ValueEqK i' (.VConstr tag []) (.VConstr tag []) := by
          cases i' with | zero => simp only [ValueEqK.eq_1] | succ => simp [ValueEqK, ListRel]
        exact hπ i' (by omega) _ _ this
      | m :: ms =>
        simp [closedAt] at ht
        have hm : closedAt d m = true := by
          have := ht; simp [closedAtList] at this; exact this.1
        have hms : closedAtList d ms = true := by
          have := ht; simp [closedAtList] at this; exact this.2
        simp [Moist.Verified.renameTermList]
        match i with
        | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        | i' + 1 =>
        apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
        simp only [step]
        apply shiftByNEquiv a c d hc m hm (i'+1)
          (i'+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) i' (by omega)
        exact shiftByNConstrField (shiftByNEquivList a c d hc ms hms (i'+1))
          (by omega) (shiftByNEnvEqK_mono (by omega) henv) trivial (stackRelK_mono (by omega) hπ)
    | .Case scrut alts =>
      simp only [Moist.Verified.renameTerm]
      simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
      match i with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | i' + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      simp only [step]
      apply shiftByNEquiv a c d hc scrut hscrut (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) i' (by omega)
      intro j' hj' v₁ v₂ hv
      match j' with
      | 0 => exact obsEqK_zero_nonhalt (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      | n + 1 =>
      apply obsEqK_of_step (fun _ => State.noConfusion) (fun _ => State.noConfusion)
      match v₁, v₂ with
      | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
        simp only [ValueEqK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
        simp only [step]
        split
        · rename_i alt₁ halt₁
          have hlen_eq : (Moist.Verified.renameTermList (shiftByN a c) alts).length = alts.length :=
            Moist.Verified.renameTermList_length _ _
          have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
          have hi₁ : tag₁ < (Moist.Verified.renameTermList (shiftByN a c) alts).length := hsome₁.1
          have hi₂ : tag₁ < alts.length := by omega
          have halt₂ : alts[tag₁]? = some (alts[tag₁]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
          rw [halt₂]; simp only []
          have hidx : (Moist.Verified.renameTermList (shiftByN a c) alts)[tag₁]'hi₁ =
              Moist.Verified.renameTerm (shiftByN a c) (alts[tag₁]) :=
            Moist.Verified.renameTermList_getElem _ _ _ hi₂
          have heq₁ : alt₁ = Moist.Verified.renameTerm (shiftByN a c) (alts[tag₁]) := by
            have := hsome₁.2; rw [hidx] at this; exact this.symm
          rw [heq₁]
          have haltsList := shiftByNEquivList a c d hc alts halts (i'+1)
          have halt_shift := listRel_getElem haltsList (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
          rw [hidx] at halt_shift
          apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) n (by omega)
          exact applyArgFrames_stackRelK
            (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hfields_v)
            (stackRelK_mono (by omega) hπ)
        · rename_i hnone₁
          have hlen_eq : (Moist.Verified.renameTermList (shiftByN a c) alts).length = alts.length :=
            Moist.Verified.renameTermList_length _ _
          have hnone₂ : alts[tag₁]? = none := by
            rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
          rw [hnone₂]; simp only []; exact obsEqK_error _
      | .VCon c₁, .VCon c₂ =>
        simp only [ValueEqK] at hv; subst hv
        simp only [step]
        have hlen_eq : (Moist.Verified.renameTermList (shiftByN a c) alts).length = alts.length :=
          Moist.Verified.renameTermList_length _ _
        split
        · rename_i tag numCtors fields htag
          have hif_eq : (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList (shiftByN a c) alts).length > numCtors)) =
              (decide (numCtors > 0) && decide (alts.length > numCtors)) := by
            rw [hlen_eq]
          split
          · rename_i h_check
            rw [hif_eq] at h_check; simp [h_check]; exact obsEqK_error _
          · rename_i h_check
            rw [hif_eq] at h_check; simp [h_check]
            split
            · rename_i alt₁ halt₁
              have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
              have hi₁ : tag < (Moist.Verified.renameTermList (shiftByN a c) alts).length := hsome₁.1
              have hi₂ : tag < alts.length := by omega
              have halt₂ : alts[tag]? = some (alts[tag]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
              rw [halt₂]; simp only []
              have hidx : (Moist.Verified.renameTermList (shiftByN a c) alts)[tag]'hi₁ =
                  Moist.Verified.renameTerm (shiftByN a c) (alts[tag]) :=
                Moist.Verified.renameTermList_getElem _ _ _ hi₂
              have heq₁ : alt₁ = Moist.Verified.renameTerm (shiftByN a c) (alts[tag]) := by
                have := hsome₁.2; rw [hidx] at this; exact this.symm
              rw [heq₁]
              have haltsList := shiftByNEquivList a c d hc alts halts (i'+1)
              have halt_shift := listRel_getElem haltsList (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
              rw [hidx] at halt_shift
              apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (shiftByNEnvEqK_mono (by omega) henv) n (by omega)
              have hfields_vcon := constToTagAndFields_fields_vcon c₁
              rw [htag] at hfields_vcon
              exact applyArgFrames_stackRelK
                (listRel_refl_vcon n fields hfields_vcon)
                (stackRelK_mono (by omega) hπ)
            · rename_i hnone₁
              have hnone₂ : alts[tag]? = none := by
                rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
              rw [hnone₂]; simp only []; exact obsEqK_error _
        · exact obsEqK_error _
      | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsEqK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv
  termination_by sizeOf t

  private def shiftByNEquivList (a c d : Nat) (hc : c ≥ 1)
      (ts : List Term) (hts : closedAtList d ts = true) (k : Nat) :
      ListRel (fun t₁ t₂ =>
        ∀ j ≤ k, ∀ ρ₁ ρ₂, ShiftByNEnvEqK a c j d ρ₁ ρ₂ →
          ∀ i ≤ j, ∀ π₁ π₂, StackRelK ValueEqK i π₁ π₂ →
            ObsEqK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
        (Moist.Verified.renameTermList (shiftByN a c) ts)
        ts := by
    match ts, hts with
    | [], _ => simp [Moist.Verified.renameTermList]; trivial
    | t :: rest, hts =>
      simp [closedAtList] at hts
      simp [Moist.Verified.renameTermList]
      exact ⟨shiftByNEquiv a c d hc t hts.1 k, shiftByNEquivList a c d hc rest hts.2 k⟩
  termination_by sizeOf ts
end

--------------------------------------------------------------------------------
-- 7e. Multi-extend infrastructure
--------------------------------------------------------------------------------

private def multiExtend (ρ : CekEnv) : List CekValue → CekEnv
  | [] => ρ
  | v :: vs => multiExtend (ρ.extend v) vs

private theorem multiExtend_lookup_shift (ρ : CekEnv) (vs : List CekValue) (m : Nat) (hm : m ≥ 1) :
    (multiExtend ρ vs).lookup (m + vs.length) = ρ.lookup m := by
  induction vs generalizing ρ m with
  | nil => simp [multiExtend]
  | cons v rest ih =>
    simp only [multiExtend, List.length_cons]
    rw [show m + (rest.length + 1) = (m + 1) + rest.length from by omega]
    rw [ih (ρ.extend v) (m + 1) (by omega)]
    exact extend_lookup_ge2 ρ v (m + 1) (by omega)

private theorem multiExtend_wellSized {d : Nat} {ρ : CekEnv} (h : WellSizedEnv d ρ)
    (vs : List CekValue) : WellSizedEnv (d + vs.length) (multiExtend ρ vs) := by
  induction vs generalizing d ρ with
  | nil => simp [multiExtend]; exact h
  | cons v rest ih =>
    simp only [multiExtend, List.length_cons]
    rw [show d + (rest.length + 1) = (d + 1) + rest.length from by omega]
    exact ih (wellSizedEnv_extend h v)

private theorem envEqK_to_multiShiftByNEnvEqK {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvEqK k d ρ₁ ρ₂) (vs : List CekValue) :
    ShiftByNEnvEqK vs.length 1 k d (multiExtend ρ₁ vs) ρ₂ := by
  intro n hn hnd
  have hshift : shiftByN vs.length 1 n = n + vs.length := by
    simp [shiftByN]; omega
  rw [hshift, multiExtend_lookup_shift ρ₁ vs n (by omega)]
  exact h n hn hnd

--------------------------------------------------------------------------------
-- 7f. Multi-prepend unused: lowerTotal with multiple prepended unused vars
--------------------------------------------------------------------------------

private theorem lowerTotal_multi_prepend_unused
    (xs : List VarId) (env : List VarId) (body : Expr)
    (hunused : ∀ x ∈ xs, (freeVars body).contains x = false)
    (body_t : Term) (hbody : lowerTotal env body = some body_t) :
    lowerTotal (xs ++ env) body =
      some (Moist.Verified.renameTerm (shiftByN xs.length 1) body_t) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [show shiftByN 0 1 = id from shiftByN_zero_eq_id 1]
    simp [Moist.Verified.renameTerm_id, hbody]
  | cons x rest ih =>
    have hx := hunused x (List.Mem.head _)
    have hrest := fun y hy => hunused y (List.Mem.tail _ hy)
    have ih' := ih hrest
    show lowerTotal (x :: (rest ++ env)) body =
      some (Moist.Verified.renameTerm (shiftByN (rest.length + 1) 1) body_t)
    have hprepend := lowerTotal_prepend_unused (rest ++ env) x body hx
      (Moist.Verified.renameTerm (shiftByN rest.length 1) body_t) ih'
    rw [hprepend]
    congr 1
    rw [← shiftByN_one_eq_shiftRename 1]
    have := renameTerm_shiftByN_comp 1 rest.length 1 (by omega) body_t
    rw [show 1 + rest.length = rest.length + 1 from by omega] at this
    exact this

--------------------------------------------------------------------------------
-- 7g. AllDeadLetCond definition and helpers
--------------------------------------------------------------------------------

/-- All dead-let conditions for a binding list, checked left-to-right.
    Each binding `(x, e, false)` must satisfy `MIRDeadLetCond x e tail_body`
    where `tail_body = Let rest body` is the expression AFTER that binding. -/
inductive AllDeadLetCond : List (VarId × Expr × Bool) → Expr → Prop where
  | nil : AllDeadLetCond [] body
  | cons {x e rest body} :
      MIRDeadLetCond x e (.Let rest body) →
      AllDeadLetCond rest body →
      AllDeadLetCond ((x, e, false) :: rest) body

open Moist.MIR (VarSet) in
private theorem freeVarsLet_not_contains_body
    (binds : List (VarId × Expr × Bool)) (body : Expr) (x : VarId)
    (h : (freeVarsLet binds body).contains x = false)
    (hall : ∀ (y : VarId) (ey : Expr) (b : Bool),
      (y, ey, b) ∈ binds → (freeVars body).contains y = false) :
    (freeVars body).contains x = false := by
  induction binds with
  | nil => simp [freeVarsLet] at h; exact h
  | cons bind rest ih =>
    obtain ⟨y, ey, b⟩ := bind
    simp only [freeVarsLet] at h
    have ⟨_, hrest_erase⟩ := VarSet.union_not_contains' _ _ _ h
    have hall_rest : ∀ (z : VarId) (ez : Expr) (bz : Bool),
        (z, ez, bz) ∈ rest → (freeVars body).contains z = false :=
      fun z ez bz hmem => hall z ez bz (List.Mem.tail _ hmem)
    cases VarSet.erase_not_contains_imp' _ y x hrest_erase with
    | inl hfvl => exact ih hfvl hall_rest
    | inr heq =>
      have hy_unused := hall y ey b (List.Mem.head _)
      -- heq : (y == x) = true, so y.uid = x.uid
      -- VarSet.contains checks BEq which compares uid
      -- So contains s x = contains s y when y == x
      have hyx : y.uid = x.uid := of_decide_eq_true heq
      have : ∀ (w : VarId), (w == x) = (w == y) := by
        intro w; show decide (w.uid = x.uid) = decide (w.uid = y.uid); rw [hyx]
      unfold VarSet.contains at hy_unused ⊢
      rw [show (· == x) = (· == y) from funext this]
      exact hy_unused

private theorem allDeadLetCond_unused_in_body :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
    AllDeadLetCond binds body →
    ∀ x e b, (x, e, b) ∈ binds → (freeVars body).contains x = false := by
  intro binds body hsc
  induction hsc with
  | nil => intro _ _ _ h; simp at h
  | @cons x e rest body' hcond _ ih =>
    intro x' e' b' hmem
    cases hmem with
    | head =>
      have hunused_let := hcond.unused
      -- freeVars (.Let rest body') = freeVarsLet rest body'
      rw [show freeVars (.Let rest body') = freeVarsLet rest body' from by
        simp [freeVars]] at hunused_let
      exact freeVarsLet_not_contains_body _ body' x hunused_let (fun y ey by' hy => ih y ey by' hy)
    | tail _ hmem' => exact ih x' e' b' hmem'

--------------------------------------------------------------------------------
-- 7h. Binding list variable extraction and multi-step through bindings
--------------------------------------------------------------------------------

private def bindVars : List (VarId × Expr × Bool) → List VarId
  | [] => []
  | (x, _, _) :: rest => x :: bindVars rest

private theorem bindVars_length (binds : List (VarId × Expr × Bool)) :
    (bindVars binds).length = binds.length := by
  induction binds with
  | nil => rfl
  | cons b rest ih => simp [bindVars, ih]

private theorem bindVars_mem {binds : List (VarId × Expr × Bool)} {x : VarId}
    (h : x ∈ bindVars binds) : ∃ e b, (x, e, b) ∈ binds := by
  induction binds with
  | nil => simp [bindVars] at h
  | cons bind rest ih =>
    obtain ⟨y, ey, by'⟩ := bind
    simp [bindVars] at h
    cases h with
    | inl heq => exact ⟨ey, by', heq ▸ List.Mem.head _⟩
    | inr hmem => obtain ⟨e, b, he⟩ := ih hmem; exact ⟨e, b, List.Mem.tail _ he⟩

--------------------------------------------------------------------------------
-- 7i. allDeadLetCond_fixCount: extract fixCount constraints
--------------------------------------------------------------------------------

private theorem allDeadLetCond_cons_fixCount_body
    {x : VarId} {e : Expr} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (hsc : AllDeadLetCond ((x, e, false) :: rest) body) :
    fixCount body = 0 := by
  cases hsc with
  | cons hcond _ => have := hcond.fixFree; simp [fixCount] at this; omega

private theorem allDeadLetCond_cons_fixCount_binds
    {x : VarId} {e : Expr} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (hsc : AllDeadLetCond ((x, e, false) :: rest) body) :
    fixCountBinds ((x, e, false) :: rest) = 0 := by
  cases hsc with
  | cons hcond hsc_rest =>
    have hff := hcond.fixFree
    simp only [fixCount] at hff
    simp only [fixCountBinds]; omega

private theorem allDeadLetCond_cons_fixCount_let
    {x : VarId} {e : Expr} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (hsc : AllDeadLetCond ((x, e, false) :: rest) body) :
    fixCount (.Let ((x, e, false) :: rest) body) = 0 := by
  have h1 := allDeadLetCond_cons_fixCount_binds hsc
  have h2 := allDeadLetCond_cons_fixCount_body hsc
  simp only [fixCount, fixCountBinds] at h1 ⊢; omega

private theorem allDeadLetCond_isPure_binds
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hsc : AllDeadLetCond binds body) : Moist.MIR.isPureBinds binds = true := by
  induction hsc with
  | nil => simp [Moist.MIR.isPureBinds]
  | cons hcond _ ih =>
    simp [Moist.MIR.isPureBinds, Bool.and_eq_true]
    exact ⟨hcond.safe, ih⟩

--------------------------------------------------------------------------------
-- 7j. Multi-step through pure bindings
--------------------------------------------------------------------------------

open Moist.MIR (envLookupT envLookupT_bound lowerTotalList lowerTotalLet
                isPureList isPureBinds isForceable) in
private def multiStepBindings :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
    AllDeadLetCond binds body →
    ∀ (env : List VarId) (ρ : CekEnv),
    WellSizedEnv env.length ρ → ∀ (π : Stack)
    (t : Term), lowerTotalLet env binds body = some t →
    ∀ (body_t : Term), lowerTotal env body = some body_t →
    ∃ (vs : List CekValue) (M : Nat),
      vs.length = binds.length ∧
      steps M (.compute π ρ t) =
        .compute π (multiExtend ρ vs)
          (Moist.Verified.renameTerm (shiftByN binds.length 1) body_t) ∧
      (∀ j, j ≤ M → ∀ v, steps j (.compute π ρ t) ≠ .halt v) := by
  intro binds body hsc
  induction hsc with
  | nil =>
    intro env ρ hwf π t hlet body_t hbody
    simp only [lowerTotalLet.eq_1] at hlet
    rw [hlet] at hbody; injection hbody with hbody; subst hbody
    refine ⟨[], 0, rfl, ?_, fun j hj v => ?_⟩
    · simp only [multiExtend, List.length_nil]
      rw [show shiftByN 0 1 = id from shiftByN_zero_eq_id 1]
      simp [Moist.Verified.renameTerm_id, steps]
    · have : j = 0 := by omega
      subst this; simp [steps]; exact fun _ => State.noConfusion
  | @cons x e rest body' hcond _hrest_sc ih =>
    intro env ρ hwf π t hlet body_t hbody
    simp only [lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlet
    obtain ⟨e_t, he, rest_t, hrest, heq⟩ := hlet
    injection heq with heq; subst heq
    -- t = Apply (Lam 0 rest_t) e_t
    -- Step through: compute π ρ (Apply (Lam 0 rest_t) e_t)
    --   3 steps → compute (funV (VLam rest_t ρ) :: π) ρ e_t
    --   m₁ steps → ret (funV (VLam rest_t ρ) :: π) v_rhs  (by isPure_stack_ret)
    --   1 step → compute π (ρ.extend v_rhs) rest_t
    have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 rest_t) e_t)) =
        .compute (.funV (.VLam rest_t ρ) :: π) ρ e_t := by
      simp [steps, step]
    have ⟨v_rhs, m₁, hm₁⟩ := isPure_stack_ret e e_t env ρ hcond.safe he hwf
      (.funV (.VLam rest_t ρ) :: π)
    have h_app : steps (m₁ + 1) (.compute (.funV (.VLam rest_t ρ) :: π) ρ e_t) =
        .compute π (ρ.extend v_rhs) rest_t := by
      rw [steps_trans m₁, hm₁]; simp [steps, step]
    have h_prefix : steps (3 + m₁ + 1) (.compute π ρ (.Apply (.Lam 0 rest_t) e_t)) =
        .compute π (ρ.extend v_rhs) rest_t := by
      rw [show 3 + m₁ + 1 = 3 + (m₁ + 1) from by omega, steps_trans 3, h3, h_app]
    -- x is unused in body', so lowerTotal (x::env) body' = shift(lowerTotal env body')
    have hunused_body : (freeVars body').contains x = false :=
      allDeadLetCond_unused_in_body ((x, e, false) :: rest) body'
        (AllDeadLetCond.cons hcond _hrest_sc) x e false (List.Mem.head _)
    have hbody_shifted := lowerTotal_prepend_unused env x body' hunused_body body_t hbody
    -- Apply IH: rest body' _hrest_sc (x::env) (ρ.extend v_rhs)
    have hwf' : WellSizedEnv (x :: env).length (ρ.extend v_rhs) := by
      simp only [List.length_cons]
      exact wellSizedEnv_extend hwf v_rhs
    have ⟨vs_rest, M_rest, hvs_len, hsteps_rest, hno_halt_rest⟩ :=
      ih (x :: env) (ρ.extend v_rhs) hwf' π rest_t hrest
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) body_t) hbody_shifted
    -- Compose: vs = v_rhs :: vs_rest
    refine ⟨v_rhs :: vs_rest, (3 + m₁ + 1) + M_rest, ?_, ?_, ?_⟩
    · -- vs.length = binds.length
      simp [hvs_len]
    · -- steps ((3 + m₁ + 1) + M_rest) ... = compute π (multiExtend ρ (v_rhs :: vs_rest)) ...
      rw [steps_trans (3 + m₁ + 1), h_prefix, hsteps_rest]
      simp only [multiExtend, List.length_cons]
      -- Need: renameTerm (shiftByN rest.length 1) (renameTerm (shiftRename 1) body_t)
      --      = renameTerm (shiftByN (rest.length + 1) 1) body_t
      congr 1
      rw [← shiftByN_one_eq_shiftRename 1]
      rw [renameTerm_shiftByN_comp rest.length 1 1 (by omega) body_t]
      congr 1; omega
    · -- no halt in any prefix
      intro j hj v hv
      by_cases hjp : j ≤ 3 + m₁ + 1 - 1
      · -- j < 3 + m₁ + 1 : in the prefix phase
        have h_no_halt_prefix := no_halt_before_reach h_prefix (fun _ => State.noConfusion)
        exact h_no_halt_prefix j (by omega) v hv
      · -- j ≥ 3 + m₁ + 1 : in the IH phase
        have hjge : j ≥ 3 + m₁ + 1 := by omega
        rw [show j = (3 + m₁ + 1) + (j - (3 + m₁ + 1)) from by omega,
            steps_trans (3 + m₁ + 1), h_prefix] at hv
        exact hno_halt_rest (j - (3 + m₁ + 1)) (by omega) v hv

--------------------------------------------------------------------------------
-- 7k. Lowering preservation for multi-binding dead let
--------------------------------------------------------------------------------

private theorem allDeadLetCond_lowerPres :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
    AllDeadLetCond binds body → ∀ (env : List VarId),
    (lowerTotalLet env binds body).isSome →
    (lowerTotal env body).isSome := by
  intro binds body hsc
  induction hsc with
  | nil => intro env h_let; simp [lowerTotalLet] at h_let; exact h_let
  | @cons x e rest body' hcond _ ih =>
    intro env h_let
    simp only [lowerTotalLet.eq_2, Option.bind_eq_bind] at h_let
    cases he : lowerTotal env e with
    | none => simp [he] at h_let
    | some _ =>
      cases hrest : lowerTotalLet (x :: env) rest body' with
      | none => simp [he, hrest] at h_let
      | some _ =>
        -- lowerTotalLet (x::env) rest body' = lowerTotal (x::env) (.Let rest body')
        have hlet_x : (lowerTotal (x :: env) (.Let rest body')).isSome := by
          rw [lowerTotal.eq_11]; simp [hrest]
        -- By lowerTotal_body_of_extended for (.Let rest body'):
        have hlet_env : (lowerTotal env (.Let rest body')).isSome :=
          lowerTotal_body_of_extended hcond.unused hlet_x
        -- lowerTotal env (.Let rest body') = lowerTotalLet env rest body'
        rw [lowerTotal.eq_11] at hlet_env
        exact ih env hlet_env

--------------------------------------------------------------------------------
-- 7l. uplc_dead_let_multi: the UPLC-level multi-binding theorem
--------------------------------------------------------------------------------

private theorem uplc_dead_let_multi {k d : Nat}
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hsc : AllDeadLetCond binds body)
    (env : List VarId) (hlen : env.length = d)
    (let_t body_t : Term)
    (hlet : lowerTotalLet env binds body = some let_t)
    (hbody : lowerTotal env body = some body_t)
    (hclosed : closedAt d body_t = true) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, WellSizedEnv d ρ₁ → WellSizedEnv d ρ₂ →
      EnvEqK j d ρ₁ ρ₂ → BehEqK ValueEqK j ρ₁ ρ₂ let_t body_t := by
  intro j hj ρ₁ ρ₂ hw₁ _hw₂ henv i hi π₁ π₂ hπ
  -- Step through all bindings on the LHS
  have ⟨vs, M, hvs_len, hsteps, hno_halt⟩ :=
    multiStepBindings binds body hsc env ρ₁ (hlen ▸ hw₁) π₁ let_t hlet body_t hbody
  -- After M steps: compute π₁ (multiExtend ρ₁ vs) (renameTerm (shiftByN n 1) body_t)
  -- where n = binds.length = vs.length
  -- Build the ShiftByNEnvEqK relation
  have hshift_env : ShiftByNEnvEqK vs.length 1 j d (multiExtend ρ₁ vs) ρ₂ :=
    envEqK_to_multiShiftByNEnvEqK henv vs
  -- Apply shiftByNEquiv
  rw [hvs_len] at hshift_env
  have h_shifted : ObsEqK i
      (steps M (.compute π₁ ρ₁ let_t))
      (.compute π₂ ρ₂ body_t) := by
    rw [hsteps]
    exact shiftByNEquiv binds.length 1 d (by omega) body_t hclosed i i (Nat.le_refl _)
      (multiExtend ρ₁ vs) ρ₂ (shiftByNEnvEqK_mono hi hshift_env) i (Nat.le_refl _) π₁ π₂ hπ
  exact obsEqK_of_steps_left hno_halt h_shifted

--------------------------------------------------------------------------------
-- 8. Multi-binding dead let elimination
--------------------------------------------------------------------------------

/-- Removing all dead pure bindings from a Let is a valid refinement. -/
theorem dead_let_multi_sound (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hsc : AllDeadLetCond binds body) :
    .Let binds body ⊑ᴹ body := by
  cases binds with
  | nil =>
    -- .Let [] body ⊑ᴹ body: lowerings are identical
    have heq : ∀ env, lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
      intro env
      simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal.eq_11, lowerTotalLet.eq_1]
    constructor
    · -- Lowering preservation
      intro env h; rw [heq] at h; exact h
    · -- Behavioral equivalence
      intro d k env hlen
      rw [heq]
      cases h : lowerTotalExpr env body with
      | none => simp
      | some t =>
        simp only []
        intro j hj ρ₁ ρ₂ hw₁ hw₂ henv_eq
        have hclosed : closedAt d t = true := by
          simp only [lowerTotalExpr] at h
          have := lowerTotal_closedAt env (expandFix body) t h
          rw [hlen] at this; exact this
        exact openEq_refl d t hclosed j j (Nat.le_refl _) ρ₁ ρ₂ henv_eq
  | cons bind rest =>
    obtain ⟨x, e, b⟩ := bind
    -- AllDeadLetCond ((x,e,b) :: rest) body
    -- From AllDeadLetCond, b = false
    cases hsc with
    | cons hcond hsc_rest =>
    -- (x, e, false) :: rest
    have hfc_let := allDeadLetCond_cons_fixCount_let (AllDeadLetCond.cons hcond hsc_rest)
    have hfc_body := allDeadLetCond_cons_fixCount_body (AllDeadLetCond.cons hcond hsc_rest)
    constructor
    · -- Part 1: Lowering preservation
      intro env h_let
      rw [lowerTotalExpr_eq_lowerTotal env body hfc_body]
      rw [lowerTotalExpr_eq_lowerTotal env (.Let ((x, e, false) :: rest) body) hfc_let] at h_let
      rw [lowerTotal.eq_11] at h_let
      exact allDeadLetCond_lowerPres ((x, e, false) :: rest) body
        (AllDeadLetCond.cons hcond hsc_rest) env h_let
    · -- Part 2: Behavioral equivalence
      intro d k env hlen
      rw [lowerTotalExpr_eq_lowerTotal env (.Let ((x, e, false) :: rest) body) hfc_let,
          lowerTotalExpr_eq_lowerTotal env body hfc_body]
      rw [lowerTotal.eq_11]
      cases hb : lowerTotal env body with
      | none =>
        -- body doesn't lower → match gives True for any LHS result
        cases lowerTotalLet env ((x, e, false) :: rest) body <;> simp
      | some body_t =>
        cases hlet : lowerTotalLet env ((x, e, false) :: rest) body with
        | none => simp
        | some let_t =>
          simp only []
          have hclosed : closedAt d body_t = true := by
            have := lowerTotal_closedAt env body body_t hb; rw [hlen] at this; exact this
          exact uplc_dead_let_multi ((x, e, false) :: rest) body
            (AllDeadLetCond.cons hcond hsc_rest) env hlen let_t body_t hlet hb hclosed

end Moist.VerifiedNewNew.DeadLet
