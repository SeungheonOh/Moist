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
  rhs_halts : ∀ env t, lowerTotal env e = some t →
    ∀ (ρ : CekEnv) (π : Stack), ∃ v, Reaches (.compute π ρ t) (.ret π v)

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
-- 5. uplc_dead_let
--------------------------------------------------------------------------------

theorem uplc_dead_let {k d : Nat} {t_body t_rhs : Term}
    (hpure_rhs : ∀ (ρ : CekEnv) (π : Stack),
      ∃ v, Reaches (.compute π ρ t_rhs) (.ret π v))
    (hclosed : closedAt d t_body = true) :
    OpenEqK k d
      (.Apply (.Lam 0 (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_body)) t_rhs)
      t_body := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  let shifted := Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_body
  obtain ⟨v_rhs, m_rhs, hm_rhs⟩ := hpure_rhs ρ₁ (.funV (.VLam shifted ρ₁) :: π₁)
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
          (fun ρ π => hsc.rhs_halts env rhs_t he ρ π)
          hclosed

end Moist.VerifiedNewNew.DeadLet
