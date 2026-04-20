import Moist.Verified.SubstBisim
import Moist.Verified.DeadLet
import Moist.Verified.FundamentalRefines
import Moist.Verified.BetaValueRefines

/-! # UPLC-level β-substitution refinement

Bridges the state-level `ObsRefines` provided by `SubstBisim` to a UPLC-level
`CtxRefines` for the β-substitution pair:

  `Apply (Lam 0 body) rhs  ⊑  substTerm 1 rhs body`

under a "halts-no-error" hypothesis on `rhs`.

The construction:
1. Given a closing context `C`, CEK evaluates the outer structure identically
   on both sides until reaching the hole, at which point LHS runs
   `Apply (Lam 0 body) rhs` and RHS runs `substTerm 1 rhs body`.
2. LHS takes `3 + M` CEK steps to reach `compute π_C (ρ_C.extend v_rhs) body`
   (where `M` is the number of steps `rhs` takes to halt).
3. At that point, `SubstBisim` relates LHS's post-step state with RHS's
   initial-context-reaching state.
4. `substBisimState_to_obsRefines` gives `ObsRefines`.
5. The outer context lifting is handled by chaining through intermediate
   states using `obsRefinesK_of_steps_left` + `obsRefinesK_of_steps_right`.
-/

namespace Moist.Verified.InlineSoundness.UplcBeta

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.BetaValueRefines
open Moist.Verified.SubstBisim
open Moist.Verified.FundamentalRefines

--------------------------------------------------------------------------------
-- 1. Composition of ObsRefinesK with ObsRefines
--------------------------------------------------------------------------------

/-- Compose an `ObsRefinesK` (step-indexed) with an `ObsRefines` (unbounded) on
    the right. The step-index bound transfers cleanly because `ObsRefinesK`
    already has unbounded conclusions. -/
theorem obsRefinesK_trans_obsRefines {i : Nat} {A B C : State}
    (h₁ : ObsRefinesK i A B) (h₂ : ObsRefines B C) :
    ObsRefinesK i A C := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨n, hn, hs⟩
    have hReachesB : ∃ v', Reaches B (.halt v') := h₁.1 v ⟨n, hn, hs⟩
    exact h₂.halt hReachesB
  · intro n hn herr
    have hReachesErrB : Reaches B .error := h₁.2 n hn herr
    exact h₂.error hReachesErrB

/-- Steps on the right propagate ObsRefines to the pre-step state. -/
theorem obsRefines_of_steps_right {n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefines s₁ s₂') :
    ObsRefines s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro hhalt
    obtain ⟨v', m, hm⟩ := h.halt hhalt
    refine ⟨v', n + m, ?_⟩
    rw [show (n + m) = n + m from rfl]
    rw [Moist.Verified.BetaValueRefines.steps_trans n m s₂, h_steps]
    exact hm
  · intro herr
    obtain ⟨m, hm⟩ := h.error herr
    refine ⟨n + m, ?_⟩
    rw [Moist.Verified.BetaValueRefines.steps_trans n m s₂, h_steps]
    exact hm

/-- Steps on the left propagate ObsRefines to the pre-step state. -/
theorem obsRefines_of_steps_left {n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁') (h : ObsRefines s₁' s₂) :
    ObsRefines s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨v, m, hs⟩
    by_cases hmn : m ≤ n
    · -- steps m s₁ = halt v with m ≤ n. Then steps n s₁ = halt v too.
      have hsteps_n : steps n s₁ = .halt v := by
        have hsplit : n = m + (n - m) := by omega
        rw [hsplit, Moist.Verified.BetaValueRefines.steps_trans m (n - m), hs]
        -- steps (n - m) (halt v) = halt v
        induction (n - m) with
        | zero => rfl
        | succ k ih => simp [steps, step, ih]
      -- So s₁' = halt v
      have : s₁' = .halt v := by rw [← h_steps]; exact hsteps_n
      rw [this] at h
      exact h.halt ⟨v, 0, rfl⟩
    · -- m > n. Then steps (m - n) s₁' = halt v.
      have hsteps_s₁' : steps (m - n) s₁' = .halt v := by
        have hsplit : m = n + (m - n) := by omega
        rw [← h_steps, ← Moist.Verified.BetaValueRefines.steps_trans n (m - n), ← hsplit]
        exact hs
      exact h.halt ⟨v, m - n, hsteps_s₁'⟩
  · rintro ⟨m, hs⟩
    by_cases hmn : m ≤ n
    · have hsteps_n : steps n s₁ = .error := by
        have hsplit : n = m + (n - m) := by omega
        rw [hsplit, Moist.Verified.BetaValueRefines.steps_trans m (n - m), hs]
        induction (n - m) with
        | zero => rfl
        | succ k ih => simp [steps, step, ih]
      have : s₁' = .error := by rw [← h_steps]; exact hsteps_n
      rw [this] at h
      exact h.error ⟨0, rfl⟩
    · have hsteps_s₁' : steps (m - n) s₁' = .error := by
        have hsplit : m = n + (m - n) := by omega
        rw [← h_steps, ← Moist.Verified.BetaValueRefines.steps_trans n (m - n), ← hsplit]
        exact hs
      exact h.error ⟨m - n, hsteps_s₁'⟩

--------------------------------------------------------------------------------
-- 2. Reflexivity of SubstBisimStack for well-formed stacks
--------------------------------------------------------------------------------

/-- Extend a well-formed value with an empty list. -/
private theorem foldrExtend_nil_eq (ρ : CekEnv) : foldrExtend ρ [] = ρ := rfl

/-- Reflexivity of `SubstBisimFrame` for well-formed frames. -/
private theorem substBisimFrame_refl_wf : ∀ {f : Frame},
    FrameWellFormed f → SubstBisimFrame f f
  | .force, _ => SubstBisimFrame.force
  | .arg t ρ, h => by
    cases h with
    | @arg _ _ k hρ hρ_len hct =>
      have : SubstBisimFrame (.arg t (foldrExtend ρ [])) (.arg t (foldrExtend ρ [])) :=
        SubstBisimFrame.argRefl hρ hρ_len SubstBisimValueList.nil (by simp; exact hct)
          ValueListWellFormed.nil
      exact this
  | .funV v, h => by
    cases h with
    | funV hv => exact SubstBisimFrame.funV (SubstBisimValue.refl hv)
  | .applyArg v, h => by
    cases h with
    | applyArg hv => exact SubstBisimFrame.applyArg (SubstBisimValue.refl hv)
  | .constrField tag done todo ρ, h => by
    cases h with
    | @constrField _ _ _ _ k hdone hρ hρ_len hct =>
      have : SubstBisimFrame
          (.constrField tag done todo (foldrExtend ρ []))
          (.constrField tag done todo (foldrExtend ρ [])) :=
        SubstBisimFrame.constrFieldRefl tag hdone hρ hρ_len SubstBisimValueList.nil
          (by simp; exact hct) ValueListWellFormed.nil
      exact this
  | .caseScrutinee alts ρ, h => by
    cases h with
    | @caseScrutinee _ _ k hρ hρ_len hct =>
      have : SubstBisimFrame
          (.caseScrutinee alts (foldrExtend ρ []))
          (.caseScrutinee alts (foldrExtend ρ [])) :=
        SubstBisimFrame.caseScrutineeRefl hρ hρ_len SubstBisimValueList.nil
          (by simp; exact hct) ValueListWellFormed.nil
      exact this

/-- Reflexivity of `SubstBisimStack` for well-formed stacks. -/
theorem substBisimStack_refl_wf : ∀ {π : Stack},
    StackWellFormed π → SubstBisimStack π π
  | [], _ => SubstBisimStack.nil
  | f :: π, h => by
    cases h with
    | cons hf hπ =>
      exact SubstBisimStack.cons (substBisimFrame_refl_wf hf) (substBisimStack_refl_wf hπ)

--------------------------------------------------------------------------------
-- 3. The main UPLC β-substitution ObsRefines theorem (under concrete envs)
--
-- Given specific well-formed `ρ`, `π`, and a halt witness for `rhs` in `ρ`
-- producing `v_rhs`, the Apply-Lam state ObsRefines-refines the substituted
-- state directly. No env refinement (EnvRefinesK) — the two envs are literally
-- equal.
--
-- This lifts directly to the context case: when a closing context C evaluates
-- to reach the hole at some (π_C, ρ_C), both sides have reached (compute π_C
-- ρ_C t_i) — and SAME π_C, ρ_C because context evaluation is deterministic.
-- Then this theorem gives the ObsRefines on those hole-reaching states.
--------------------------------------------------------------------------------

/-- Main state-level ObsRefines theorem for the β-substitution pair.
    Both sides use the SAME base env `ρ` and SAME stack `π`. -/
theorem uplc_beta_obsRefines_same_env (d : Nat) (body rhs : Term)
    (hb : closedAt (d + 1) body = true)
    (hr : closedAt d rhs = true)
    {ρ : CekEnv} (hρ : EnvWellFormed d ρ) (hρ_len : d ≤ ρ.length)
    {π : Stack} (hπ : StackWellFormed π)
    {v_rhs : CekValue} (hv_rhs_wf : ValueWellFormed v_rhs)
    (h_rhs_halts : ∀ (π' : Stack), ∃ (m : Nat),
      steps m (.compute π' ρ rhs) = .ret π' v_rhs ∧
      ∀ k ≤ m, steps k (.compute π' ρ rhs) ≠ .error) :
    ObsRefines
      (.compute π ρ (.Apply (.Lam 0 body) rhs))
      (.compute π ρ (substTerm 1 rhs body)) := by
  -- CEK steps for LHS:
  -- compute π ρ (Apply (Lam 0 body) rhs)
  -- → step 1: compute (arg rhs ρ :: π) ρ (Lam 0 body)
  -- → step 2: ret (arg rhs ρ :: π) (VLam body ρ)
  -- → step 3: compute (funV (VLam body ρ) :: π) ρ rhs
  -- Then rhs evaluates to v_rhs in M steps with no error.
  -- → step 3+M: ret (funV (VLam body ρ) :: π) v_rhs
  -- → step 3+M+1: compute π (ρ.extend v_rhs) body
  have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 body) rhs)) =
      .compute (.funV (.VLam body ρ) :: π) ρ rhs := by
    simp [steps, step]
  obtain ⟨M, hM_steps, hM_noerr⟩ := h_rhs_halts (.funV (.VLam body ρ) :: π)
  have h3M : steps (3 + M) (.compute π ρ (.Apply (.Lam 0 body) rhs)) =
      .ret (.funV (.VLam body ρ) :: π) v_rhs := by
    rw [Moist.Verified.BetaValueRefines.steps_trans 3 M, h3]
    exact hM_steps
  have h3M1 : steps (3 + M + 1) (.compute π ρ (.Apply (.Lam 0 body) rhs)) =
      .compute π (ρ.extend v_rhs) body := by
    rw [show 3 + M + 1 = (3 + M) + 1 from rfl,
        Moist.Verified.BetaValueRefines.steps_trans (3 + M) 1, h3M]
    rfl
  -- Now build SubstBisimState between LHS_post = compute π (ρ.extend v_rhs) body
  -- and RHS = compute π ρ (substTerm 1 rhs body).
  -- Use SubstBisimState.compute with pos=1, vs₁=vs₂=[].
  have hbisim_env : SubstBisimEnv 1 rhs v_rhs (d + 1) (ρ.extend v_rhs) ρ :=
    substBisimEnv_initial d rhs v_rhs ρ hr hρ
  have h_halts_at : SubstHaltsAt rhs v_rhs ρ d := by
    refine ⟨hρ, hρ_len, hr, hv_rhs_wf, ?_⟩
    intro π'
    obtain ⟨m, hm_steps, hm_noerr⟩ := h_rhs_halts π'
    exact ⟨m, hm_steps, hm_noerr⟩
  have hπ_bisim : SubstBisimStack π π := substBisimStack_refl_wf hπ
  have hbody_closed : closedAt (d + 1 + ([] : List CekValue).length) body = true := by
    show closedAt (d + 1 + 0) body = true
    simpa using hb
  -- Apply SubstBisimState.compute constructor.
  have hstate_bisim : SubstBisimState
      (.compute π (foldrExtend (ρ.extend v_rhs) ([] : List CekValue)) body)
      (.compute π (foldrExtend ρ ([] : List CekValue))
        (substTerm (1 + ([] : List CekValue).length)
          (iteratedShift ([] : List CekValue).length rhs) body)) := by
    exact SubstBisimState.compute (d := d) (pos := 1) (replacement := rhs) (v_repl := v_rhs)
      (by omega) (by omega) hr hbisim_env SubstBisimValueList.nil
      hbody_closed h_halts_at ValueListWellFormed.nil hπ hπ_bisim
  -- Simplify foldrExtend and iteratedShift for empty list.
  have hlhs_eq : (State.compute π (foldrExtend (ρ.extend v_rhs) ([] : List CekValue)) body) =
      (State.compute π (ρ.extend v_rhs) body) := by
    rfl
  have hrhs_eq : (State.compute π (foldrExtend ρ ([] : List CekValue))
        (substTerm (1 + ([] : List CekValue).length)
          (iteratedShift ([] : List CekValue).length rhs) body)) =
      (State.compute π ρ (substTerm 1 rhs body)) := by
    show State.compute π ρ (substTerm (1 + 0) rhs body) = State.compute π ρ (substTerm 1 rhs body)
    rfl
  rw [hlhs_eq, hrhs_eq] at hstate_bisim
  -- Get ObsRefines on LHS_post and RHS.
  have hobs_post : ObsRefines
      (.compute π (ρ.extend v_rhs) body)
      (.compute π ρ (substTerm 1 rhs body)) :=
    substBisimState_to_obsRefines hstate_bisim
  -- Propagate back through 3+M+1 steps on LHS.
  exact obsRefines_of_steps_left h3M1 hobs_post

--------------------------------------------------------------------------------
-- 4. OpenRefines-style β-substitution refinement
--
-- Extends the above from same-env to general EnvRefinesK-related envs, by
-- composing FTLR (for the LHS → Mid intermediate state) with the same-env
-- theorem (for Mid → RHS).
--
-- Extra hypotheses: EnvWellFormed d ρ₂, d ≤ ρ₂.length, StackWellFormed π₂.
-- These are discharged by the downstream `ctxRefines_from_uplc_beta` bridge
-- that specializes ρ₂ = dummyEnv d (which is well-formed).
--------------------------------------------------------------------------------

/-- Universal halt-no-error + value-uniformity hypothesis: for every
    well-formed env, rhs halts in a UNIFORM way (same value across stacks). -/
def UniformHaltsAt (rhs : Term) (d : Nat) : Prop :=
  ∀ (ρ : CekEnv), EnvWellFormed d ρ → d ≤ ρ.length →
    ∃ (v : CekValue), ValueWellFormed v ∧
      ∀ (π : Stack), ∃ (m : Nat),
        steps m (.compute π ρ rhs) = .ret π v ∧
        ∀ k ≤ m, steps k (.compute π ρ rhs) ≠ .error

/-- OpenRefines-style β-substitution refinement.

    Bridges from `uplc_beta_obsRefines_same_env` (state-level ObsRefines at
    a single `ρ`) to the step-indexed `ObsRefinesK` under arbitrary
    `EnvRefinesK`-related envs, via FTLR-based transit.

    The extra `EnvWellFormed` / `StackWellFormed` hypotheses on ρ₂/π₂ are
    required to invoke SubstBisim. They are discharged downstream at the
    CtxRefines bridge by specializing ρ₂ = dummyEnv d. -/
theorem uplc_beta_openRefinesK (d : Nat) (body rhs : Term)
    (hb : closedAt (d + 1) body = true)
    (hr : closedAt d rhs = true)
    (h_halts : UniformHaltsAt rhs d) :
    ∀ (k : Nat) (j : Nat), j ≤ k →
      ∀ (ρ₁ ρ₂ : CekEnv), EnvRefinesK j d ρ₁ ρ₂ →
        EnvWellFormed d ρ₂ → d ≤ ρ₂.length →
      ∀ (i : Nat), i ≤ j → ∀ (π₁ π₂ : Stack),
        StackRefK ValueRefinesK i π₁ π₂ → StackWellFormed π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (.Apply (.Lam 0 body) rhs))
          (.compute π₂ ρ₂ (substTerm 1 rhs body)) := by
  intro k j hj ρ₁ ρ₂ henv hρ₂_wf hρ₂_len i hi π₁ π₂ hπ hπ₂_wf
  -- Closedness of Apply (Lam 0 body) rhs at depth d.
  have hclosed_apply : closedAt d (.Apply (.Lam 0 body) rhs) = true := by
    simp [closedAt, hb, hr]
  -- Step 1: FTLR relates LHS to Mid (same term, refinement-related envs).
  have h_lhs_mid : ObsRefinesK i
      (.compute π₁ ρ₁ (.Apply (.Lam 0 body) rhs))
      (.compute π₂ ρ₂ (.Apply (.Lam 0 body) rhs)) :=
    Moist.Verified.FundamentalRefines.ftlr d (.Apply (.Lam 0 body) rhs) hclosed_apply k
      j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  -- Step 2: ObsRefines on Mid → RHS via same-env theorem.
  obtain ⟨v_rhs, hv_rhs_wf, h_halts_uni⟩ := h_halts ρ₂ hρ₂_wf hρ₂_len
  have h_mid_rhs : ObsRefines
      (.compute π₂ ρ₂ (.Apply (.Lam 0 body) rhs))
      (.compute π₂ ρ₂ (substTerm 1 rhs body)) :=
    uplc_beta_obsRefines_same_env d body rhs hb hr hρ₂_wf hρ₂_len hπ₂_wf hv_rhs_wf h_halts_uni
  -- Step 3: Compose.
  exact obsRefinesK_trans_obsRefines h_lhs_mid h_mid_rhs

--------------------------------------------------------------------------------
-- 5. Bridge to CtxRefines via dummyEnv + locality
--
-- Uses `dummyEnv d` (which is trivially well-formed) + the existing
-- `locality_obsRefinesK` infrastructure from Soundness.lean.
--------------------------------------------------------------------------------

/-- `VCon .Unit` is always well-formed. -/
private theorem valueWellFormed_vcon_unit : ValueWellFormed (.VCon Moist.Plutus.Term.Const.Unit) :=
  ValueWellFormed.vcon _

/-- `dummyEnv n` has length exactly `n`. -/
private theorem dummyEnv_length_eq (n : Nat) :
    (Moist.Verified.Contextual.Soundness.dummyEnv n).length = n :=
  Moist.Verified.Contextual.Soundness.dummyEnv_length n

/-- Lookups in `dummyEnv n` at any valid position return `VCon .Unit`. -/
private theorem dummyEnv_lookup : ∀ (n m : Nat), 1 ≤ m → m ≤ n →
    (Moist.Verified.Contextual.Soundness.dummyEnv n).lookup m =
    some (.VCon Moist.Plutus.Term.Const.Unit) := by
  intro n
  induction n with
  | zero => intro m hm1 hmn; omega
  | succ n' ih =>
    intro m hm1 hmn
    by_cases hm_eq : m = 1
    · subst hm_eq
      show ((Moist.Verified.Contextual.Soundness.dummyEnv n').extend
             (.VCon Moist.Plutus.Term.Const.Unit)).lookup 1 = _
      rfl
    · have hm_ge : m ≥ 2 := by omega
      match m, hm_ge with
      | m' + 2, _ =>
        have hm'_ge : m' + 1 ≥ 1 := by omega
        have hm'_le : m' + 1 ≤ n' := by omega
        have ih_res := ih (m' + 1) hm'_ge hm'_le
        show ((Moist.Verified.Contextual.Soundness.dummyEnv n').extend
               (.VCon Moist.Plutus.Term.Const.Unit)).lookup (m' + 2) = _
        show (CekEnv.cons (.VCon Moist.Plutus.Term.Const.Unit)
               (Moist.Verified.Contextual.Soundness.dummyEnv n')).lookup (m' + 2) = _
        show (Moist.Verified.Contextual.Soundness.dummyEnv n').lookup (m' + 1) = _
        exact ih_res

/-- `dummyEnv n` is well-formed at any depth `k ≤ n`. -/
theorem envWellFormed_dummyEnv : ∀ (k n : Nat), k ≤ n →
    EnvWellFormed k (Moist.Verified.Contextual.Soundness.dummyEnv n) := by
  intro k n hkn
  induction k with
  | zero => exact EnvWellFormed.zero
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have ihm := ih hmn
    have hlen : m + 1 ≤ (Moist.Verified.Contextual.Soundness.dummyEnv n).length := by
      rw [dummyEnv_length_eq]; exact hkn
    have hlookup : (Moist.Verified.Contextual.Soundness.dummyEnv n).lookup (m + 1) =
        some (.VCon Moist.Plutus.Term.Const.Unit) :=
      dummyEnv_lookup n (m + 1) (by omega) hkn
    exact EnvWellFormed.succ ihm hlen hlookup valueWellFormed_vcon_unit

end Moist.Verified.InlineSoundness.UplcBeta
