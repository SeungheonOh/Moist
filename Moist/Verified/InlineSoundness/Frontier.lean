import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.AdvancedRefinement

namespace Moist.Verified.InlineSoundness.Frontier

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.InlineSoundness.StrictOcc

private theorem steps_bridge (fuel : Nat) (state : State) :
    steps fuel state = Semantics.steps fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis => exact inductionHypothesis (step state)

theorem outcome_of_terminal {environment : CekEnv} {stack : Stack} {term : Term} {terminal : State}
    (isTerminal : terminal = .error ∨ ∃ value, terminal = .halt value)
    (terminates : Reaches (.compute stack environment term) terminal) :
    (∃ value, Reaches (.compute [] environment term) (.halt value)) ∨
      Reaches (.compute [] environment term) .error := by
  obtain ⟨fuel, terminates⟩ := terminates
  rw [steps_bridge] at terminates
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
  | error => exact .inr ⟨index, by rw [steps_bridge]; exact reached⟩
  | halt value => exact .inl ⟨value, index, by rw [steps_bridge]; exact reached⟩
  | ret pending value =>
    cases pending with
    | cons _ _ => rw [reached] at inactive; contradiction
    | nil =>
      exact .inl ⟨value, index + 1, by
        rw [steps_bridge, Semantics.steps_trans, reached]; rfl⟩

private theorem beta_rhs_outcome {environment : CekEnv} {stack : Stack}
    {body rhs : Term} {terminal : State}
    (isTerminal : terminal = .error ∨ ∃ value, terminal = .halt value)
    (terminates : Reaches (.compute stack environment (.Apply (.Lam 0 body) rhs)) terminal) :
    (∃ value, Reaches (.compute [] environment rhs) (.halt value)) ∨
      Reaches (.compute [] environment rhs) .error := by
  have fixed : step terminal = terminal := by
    rcases isTerminal with rfl | ⟨value, rfl⟩ <;> rfl
  apply outcome_of_terminal isTerminal
  have afterPrefix := (AdvancedRefinement.reaches_after_prefix 3 fixed).mp terminates
  exact afterPrefix

private theorem beta_of_rhs_halts {depth : Nat} {body rhs : Term}
    (single : SingleOcc 1 body)
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (stack : Stack)
    (environmentWellFormed : EnvWellFormed depth environment)
    (environmentLength : depth ≤ environment.length)
    (stackWellFormed : StackWellFormed stack)
    (halts : ∃ value, Reaches (.compute [] environment rhs) (.halt value)) :
    ObsRefines (.compute stack environment (.Apply (.Lam 0 body) rhs))
      (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) := by
  obtain ⟨value, fuel, reaches⟩ := halts
  obtain ⟨returnFuel, _, returned, returns⟩ :=
    halt_descends_to_baseπ fuel (.compute [] environment rhs) value reaches ⟨[], rfl⟩
  apply same_env_beta_single_obsRefines single bodyClosed rhsClosed environment stack
    environmentWellFormed environmentLength stackWellFormed
  intro continuation
  obtain ⟨fuel, returns⟩ := ret_on_all_stacks returns continuation
  refine ⟨fuel, returned, returns, ?_⟩
  intro earlier bound errors
  have split : fuel = earlier + (fuel - earlier) := by omega
  rw [split, steps_trans, errors, steps_error_fixed] at returns
  contradiction

theorem same_env_beta_frontier_refines {depth : Nat} {body rhs : Term}
    (single : SingleOcc 1 body)
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
  have fromHalts := beta_of_rhs_halts single bodyClosed rhsClosed environment stack
    environmentWellFormed environmentLength stackWellFormed
  constructor
  · rintro ⟨value, halts⟩
    rcases beta_rhs_outcome (.inr ⟨value, rfl⟩) halts with rhsHalts | rhsErrors
    · exact (fromHalts rhsHalts).halt ⟨value, halts⟩
    · obtain ⟨errorFuel, errors⟩ := error_on_all_stacks rhsErrors (.funV (.VLam body environment) :: stack)
      have sourceErrors : Reaches (.compute stack environment (.Apply (.Lam 0 body) rhs)) .error :=
        ⟨3 + errorFuel, by rw [steps_trans]; exact errors⟩
      obtain ⟨fuel, halts⟩ := halts
      have afterHalt := (AdvancedRefinement.reaches_after_prefix fuel rfl).mp sourceErrors
      rw [halts] at afterHalt
      obtain ⟨remaining, impossible⟩ := afterHalt
      rw [steps_halt_fixed] at impossible
      contradiction
  · intro errors
    rcases beta_rhs_outcome (.inl rfl) errors with rhsHalts | rhsErrors
    · exact (fromHalts rhsHalts).error errors
    · exact errorFrontier rhsErrors

theorem beta_frontier_ctxRefines {depth : Nat} {body rhs : Term}
    (single : SingleOcc 1 body)
    (bodyClosed : closedAt (depth + 1) body = true)
    (rhsClosed : closedAt depth rhs = true)
    (errorFrontier : ∀ environment stack, EnvWellFormed depth environment →
      depth ≤ environment.length → StackWellFormed stack →
      Reaches (.compute [] environment rhs) .error →
      Reaches (.compute stack environment (Moist.Verified.substTerm 1 rhs body)) .error) :
    CtxRefines (.Apply (.Lam 0 body) rhs) (Moist.Verified.substTerm 1 rhs body) := by
  apply TermObsRefinesWF.soundness_refinesWF (d := depth)
  · intro budget index indexBound leftEnv rightEnv environments leftWellFormed leftLength
      rightWellFormed rightLength observation observationBound leftStack rightStack
      leftStackWellFormed rightStackWellFormed stacks
    have sourceClosed : closedAt depth (.Apply (.Lam 0 body) rhs) = true := by
      simp [closedAt, bodyClosed, rhsClosed]
    have selfRefinement := FundamentalRefinesWF.ftlr_wf depth _ sourceClosed
      budget index indexBound leftEnv rightEnv environments leftWellFormed leftLength
      rightWellFormed rightLength observation observationBound leftStack rightStack
      leftStackWellFormed rightStackWellFormed stacks
    exact SubstRefinesExt.obsRefinesK_compose_obsRefines_right selfRefinement
      (same_env_beta_frontier_refines single bodyClosed rhsClosed rightEnv rightStack
        rightWellFormed rightLength rightStackWellFormed
        (errorFrontier rightEnv rightStack rightWellFormed rightLength rightStackWellFormed))
  · intro context sourceContextClosed
    obtain ⟨contextClosed, sourceClosed⟩ :=
      (fill_closedAt_iff context (.Apply (.Lam 0 body) rhs) 0).mp sourceContextClosed
    simp only [closedAt, Bool.and_eq_true, Nat.zero_add] at sourceClosed
    apply (fill_closedAt_iff context _ 0).mpr
    refine ⟨contextClosed, ?_⟩
    simpa only [Nat.zero_add] using closedAt_substTerm 1 rhs body context.binders (by omega) (by omega)
      sourceClosed.2 sourceClosed.1

end Moist.Verified.InlineSoundness.Frontier
