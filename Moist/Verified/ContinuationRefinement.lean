import Moist.Verified.InlineSoundness.Frontier
import Moist.Verified.Purity

namespace Moist.Verified.ContinuationRefinement

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence
open Moist.Verified.Contextual Moist.Verified.InlineSoundness.StrictOcc

def Terminal (state : State) : Prop :=
  state = .error ∨ ∃ value, state = .halt value

def TerminalRefines (source target : State) : Prop :=
  ∀ terminal, Terminal terminal → Reaches source terminal → Reaches target terminal

theorem Terminal.fixed {state : State} (terminal : Terminal state) : step state = state := by
  rcases terminal with rfl | ⟨value, rfl⟩ <;> rfl

theorem TerminalRefines.refl (state : State) : TerminalRefines state state := by
  intro terminal _ reaches
  exact reaches

theorem TerminalRefines.trans {first second third : State}
    (left : TerminalRefines first second) (right : TerminalRefines second third) :
    TerminalRefines first third := by
  intro terminal final reaches
  exact right terminal final (left terminal final reaches)

theorem TerminalRefines.obs {source target : State} (refines : TerminalRefines source target) :
    ObsRefines source target := by
  constructor
  · rintro ⟨value, reaches⟩
    exact ⟨value, refines _ (.inr ⟨value, rfl⟩) reaches⟩
  · exact refines _ (.inl rfl)

theorem TerminalRefines.prefix {source target : State} (sourceFuel targetFuel : Nat)
    (refines : TerminalRefines (steps sourceFuel source) (steps targetFuel target)) :
    TerminalRefines source target := by
  intro terminal final reaches
  apply (AdvancedRefinement.reaches_after_prefix targetFuel final.fixed).mpr
  exact refines terminal final
    ((AdvancedRefinement.reaches_after_prefix sourceFuel final.fixed).mp reaches)

theorem compute_of_returns (sourceStack targetStack : Stack)
    (continuations : ∀ value, TerminalRefines (.ret sourceStack value) (.ret targetStack value))
    (environment : CekEnv) (term : Term) :
    TerminalRefines (.compute sourceStack environment term) (.compute targetStack environment term) := by
  intro terminal final reaches
  rcases InlineSoundness.Frontier.outcome_of_terminal final reaches with halts | errors
  · obtain ⟨value, fuel, halts⟩ := halts
    have semanticSteps : ∀ fuel state, steps fuel state = Semantics.steps fuel state := by
      intro fuel state
      induction fuel generalizing state with
      | zero => rfl
      | succ fuel inductionHypothesis => exact inductionHypothesis (step state)
    obtain ⟨sourceFuel, sourceReturns⟩ := Purity.compute_to_ret_from_halt environment term value
      sourceStack ⟨fuel, by rw [← semanticSteps]; exact halts⟩
    obtain ⟨targetFuel, targetReturns⟩ := Purity.compute_to_ret_from_halt environment term value
      targetStack ⟨fuel, by rw [← semanticSteps]; exact halts⟩
    rw [← semanticSteps] at sourceReturns targetReturns
    apply (AdvancedRefinement.reaches_after_prefix targetFuel final.fixed).mpr
    rw [targetReturns]
    apply continuations value terminal final
    have afterSource := (AdvancedRefinement.reaches_after_prefix sourceFuel final.fixed).mp reaches
    rwa [sourceReturns] at afterSource
  · have sourceErrors := errors
    obtain ⟨fuel, errors⟩ := InlineSoundness.StrictOcc.error_on_all_stacks errors sourceStack
    have afterError := (AdvancedRefinement.reaches_after_prefix fuel final.fixed).mp reaches
    rw [errors] at afterError
    obtain ⟨remaining, terminalEqual⟩ := afterError
    have errorFixed : steps remaining (.error : State) = .error := by
      clear terminalEqual
      induction remaining with
      | zero => rfl
      | succ remaining inductionHypothesis => exact inductionHypothesis
    rw [errorFixed] at terminalEqual
    subst terminal
    exact InlineSoundness.StrictOcc.error_on_all_stacks sourceErrors targetStack

end Moist.Verified.ContinuationRefinement
