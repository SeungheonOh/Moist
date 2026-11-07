import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.AdvancedRefinement

/-! # Beta reduction at the evaluation frontier

`beta_ctxRefines_of_errorFrontier` is the single UPLC beta rule used by the
inliner: `(λ. body) rhs` refines `body[rhs/1]` whenever an `rhs` that errors
makes the substituted body error too. A halting `rhs` discharges the
hypothesis vacuously (`beta_ctxRefines_of_halts`). -/

namespace Moist.Verified.InlineSoundness.Frontier

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.InlineSoundness.StrictOcc

theorem outcome_of_terminal {environment : CekEnv} {stack : Stack} {term : Term} {terminal : State}
    (isTerminal : terminal = .error ∨ ∃ value, terminal = .halt value)
    (terminates : Reaches (.compute stack environment term) terminal) :
    (∃ value, Reaches (.compute [] environment term) (.halt value)) ∨
      Reaches (.compute [] environment term) .error := by
  obtain ⟨fuel, terminates⟩ := terminates
  rw [vstep_eq] at terminates
  let initial : State := .compute [] environment term
  have inactive : ∃ index, index ≤ fuel ∧ StepLift.isActive (Semantics.steps index initial) = false := by
    apply Classical.byContradiction
    intro noneInactive
    have active : ∀ index, index ≤ fuel → StepLift.isActive (Semantics.steps index initial) = true := by
      intro index bound
      cases selected : StepLift.isActive (Semantics.steps index initial) with
      | true => rfl
      | false => exact False.elim (noneInactive ⟨index, bound, selected⟩)
    have lifted := StepLift.steps_liftState stack fuel initial (fun index bound => active index (by omega))
    change Semantics.steps fuel (.compute stack environment term) = _ at lifted
    rw [terminates] at lifted
    rcases isTerminal with rfl | ⟨value, rfl⟩
    · have innerError := StepLift.liftState_eq_error stack _ lifted.symm
      have stillActive := active fuel (Nat.le_refl _)
      rw [innerError] at stillActive
      contradiction
    · exact StepLift.liftState_ne_halt stack _ value lifted.symm
  obtain ⟨index, _, inactive, _⟩ := StepLift.firstInactive initial fuel inactive
  cases reached : Semantics.steps index initial with
  | compute _ _ _ => rw [reached] at inactive; contradiction
  | error => exact .inr ⟨index, by rw [vstep_eq]; exact reached⟩
  | halt value => exact .inl ⟨value, index, by rw [vstep_eq]; exact reached⟩
  | ret pending value =>
    cases pending with
    | cons _ _ => rw [reached] at inactive; contradiction
    | nil =>
      exact .inl ⟨value, index + 1, by
        rw [vstep_eq, Semantics.steps_trans, reached]; rfl⟩

private theorem beta_rhs_outcome {environment : CekEnv} {stack : Stack}
    {body rhs : Term} {terminal : State}
    (isTerminal : terminal = .error ∨ ∃ value, terminal = .halt value)
    (terminates : Reaches (.compute stack environment (.Apply (.Lam 0 body) rhs)) terminal) :
    (∃ value, Reaches (.compute [] environment rhs) (.halt value)) ∨
      Reaches (.compute [] environment rhs) .error := by
  have fixed : step terminal = terminal := by
    rcases isTerminal with rfl | ⟨value, rfl⟩ <;> rfl
  exact outcome_of_terminal isTerminal ((AdvancedRefinement.reaches_after_prefix 3 fixed).mp terminates)

private theorem beta_of_rhs_halts {depth : Nat} {body rhs : Term}
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (stack : Stack)
    (environmentWellFormed : EnvWellFormed depth environment)
    (environmentLength : depth ≤ environment.length)
    (stackWellFormed : StackWellFormed stack)
    (halts : ∃ value, Reaches (.compute [] environment rhs) (.halt value)) :
    ObsRefines (.compute stack environment (.Apply (.Lam 0 body) rhs))
      (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) :=
  same_env_beta_of_halts bodyClosed rhsClosed environment stack
    environmentWellFormed environmentLength stackWellFormed halts

/-- Same-environment beta: the redex is refined by the substituted body as
    long as an erroring `rhs` makes the substituted body error. -/
theorem same_env_beta_errorFrontier {depth : Nat} {body rhs : Term}
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (stack : Stack)
    (environmentWellFormed : EnvWellFormed depth environment)
    (environmentLength : depth ≤ environment.length)
    (stackWellFormed : StackWellFormed stack)
    (errorFrontier : Reaches (.compute [] environment rhs) .error →
      Reaches (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) .error) :
    ObsRefines (.compute stack environment (.Apply (.Lam 0 body) rhs))
      (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) := by
  have fromHalts := beta_of_rhs_halts bodyClosed rhsClosed environment stack
    environmentWellFormed environmentLength stackWellFormed
  constructor
  · rintro ⟨value, halts⟩
    rcases beta_rhs_outcome (.inr ⟨value, rfl⟩) halts with rhsHalts | rhsErrors
    · exact (fromHalts rhsHalts).halt ⟨value, halts⟩
    · obtain ⟨errorFuel, errors⟩ := error_on_all_stacks rhsErrors (.funV (.VLam body environment) :: stack)
      exact (halt_excludes_error halts ⟨3 + errorFuel, by rw [steps_trans]; exact errors⟩).elim
  · intro errors
    rcases beta_rhs_outcome (.inl rfl) errors with rhsHalts | rhsErrors
    · exact (fromHalts rhsHalts).error errors
    · exact errorFrontier rhsErrors

theorem same_env_beta_frontier_refines {depth : Nat} {body rhs : Term}
    (_single : SingleOcc 1 body)
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (stack : Stack)
    (environmentWellFormed : EnvWellFormed depth environment)
    (environmentLength : depth ≤ environment.length)
    (stackWellFormed : StackWellFormed stack)
    (errorFrontier : Reaches (.compute [] environment rhs) .error →
      Reaches (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) .error) :
    ObsRefines (.compute stack environment (.Apply (.Lam 0 body) rhs))
      (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) :=
  same_env_beta_errorFrontier bodyClosed rhsClosed environment stack
    environmentWellFormed environmentLength stackWellFormed errorFrontier

/-- The UPLC beta rule used for every inlining decision. -/
theorem beta_ctxRefines_of_errorFrontier {depth : Nat} {body rhs : Term}
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (errorFrontier : ∀ environment stack, EnvWellFormed depth environment →
      depth ≤ environment.length → StackWellFormed stack →
      Reaches (.compute [] environment rhs) .error →
      Reaches (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) .error) :
    CtxRefines (.Apply (.Lam 0 body) rhs) (Moist.Verified.substTerm 1 rhs body) :=
  AdvancedRefinement.contextual_of_wf_refinement (by simp [closedAt, bodyClosed, rhsClosed])
    (fun depth closed => by
      simp only [closedAt, Bool.and_eq_true] at closed
      exact closedAt_substTerm 1 rhs body depth (by omega) (by omega) closed.2 closed.1)
    (fun environment stack wellFormed length stackWellFormed =>
      same_env_beta_errorFrontier bodyClosed rhsClosed environment stack wellFormed length
        stackWellFormed (errorFrontier environment stack wellFormed length stackWellFormed))

theorem beta_frontier_ctxRefines {depth : Nat} {body rhs : Term}
    (_single : SingleOcc 1 body)
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (errorFrontier : ∀ environment stack, EnvWellFormed depth environment →
      depth ≤ environment.length → StackWellFormed stack →
      Reaches (.compute [] environment rhs) .error →
      Reaches (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) .error) :
    CtxRefines (.Apply (.Lam 0 body) rhs) (Moist.Verified.substTerm 1 rhs body) :=
  beta_ctxRefines_of_errorFrontier bodyClosed rhsClosed errorFrontier

/-- Beta with an `rhs` that halts in every well-formed environment. -/
theorem beta_ctxRefines_of_halts {depth : Nat} {body rhs : Term}
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (halts : ∀ environment, EnvWellFormed depth environment → depth ≤ environment.length →
      ∃ value, Reaches (.compute [] environment rhs) (.halt value)) :
    CtxRefines (.Apply (.Lam 0 body) rhs) (Moist.Verified.substTerm 1 rhs body) :=
  beta_ctxRefines_of_errorFrontier bodyClosed rhsClosed
    fun environment _ wellFormed length _ errors =>
      let ⟨_, halted⟩ := halts environment wellFormed length
      (halt_excludes_error halted errors).elim

end Moist.Verified.InlineSoundness.Frontier

namespace Moist.Verified.InlineSoundness.SubstCommute

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

/-- The UPLC lowering of a recursive lambda returns a value in 17 steps. -/
theorem fixLamWrapUplc_halts (body : Term) (environment : CekEnv) :
    ∃ value, Reaches (.compute [] environment (Moist.MIR.fixLamWrapUplc body)) (.halt value) :=
  ⟨_, 17, rfl⟩

theorem uplc_beta_multi_pure_openRefines {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (h_rhs_halts : ∀ (ρ : CekEnv),
      (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∀ (π : Stack), ∃ (m : Nat) (v : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v ∧
        ∀ k ≤ m, steps k (.compute π ρ t_rhs) ≠ .error) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) :=
  Frontier.beta_ctxRefines_of_halts hclosed_body hclosed_rhs fun ρ wellFormed _ => by
    obtain ⟨m, v, returns, _⟩ := h_rhs_halts ρ (fun n hn hnd =>
      let ⟨v, hv, _⟩ := envWellFormed_lookup d wellFormed hn hnd; ⟨v, hv⟩) []
    exact ⟨v, m + 1, by rw [steps_trans, returns]; rfl⟩

theorem uplc_beta_single_pure_openRefines {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (_h_single : StrictOcc.SingleOcc 1 t_body)
    (h_rhs_halts : ∀ (ρ : CekEnv),
      (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∀ (π : Stack), ∃ (m : Nat) (v : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v ∧
        ∀ k ≤ m, steps k (.compute π ρ t_rhs) ≠ .error) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) :=
  uplc_beta_multi_pure_openRefines hclosed_body hclosed_rhs h_rhs_halts

end Moist.Verified.InlineSoundness.SubstCommute
