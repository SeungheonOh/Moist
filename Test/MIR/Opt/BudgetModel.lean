import Moist.Verified.Definitions

namespace Test.MIR.Opt.BudgetModel

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Equivalence

private def selfApply : Term := .Apply (.Var 1) (.Var 1)
private def closure : CekValue := .VLam selfApply .nil
private def environment : CekEnv := .cons closure .nil

def loopState : State := .compute [] environment selfApply

private inductive InCycle : State → Prop where
  | start : InCycle loopState
  | functionLookup : InCycle (.compute [.arg (.Var 1) environment] environment (.Var 1))
  | functionReturn : InCycle (.ret [.arg (.Var 1) environment] closure)
  | argumentLookup : InCycle (.compute [.funV closure] environment (.Var 1))
  | argumentReturn : InCycle (.ret [.funV closure] closure)

private theorem cycle_step {state : State} (member : InCycle state) : InCycle (step state) := by
  cases member with
  | start => exact InCycle.functionLookup
  | functionLookup => exact InCycle.functionReturn
  | functionReturn => exact InCycle.argumentLookup
  | argumentLookup => exact InCycle.argumentReturn
  | argumentReturn => exact InCycle.start

private theorem cycle_steps (fuel : Nat) {state : State} (member : InCycle state) :
    InCycle (steps fuel state) := by
  induction fuel generalizing state with
  | zero => exact member
  | succ fuel inductionHypothesis => exact inductionHypothesis (cycle_step member)

theorem loop_never_halts (value : CekValue) : ¬Reaches loopState (.halt value) := by
  intro ⟨fuel, reaches⟩
  have member := cycle_steps fuel InCycle.start
  rw [reaches] at member
  cases member

theorem loop_never_errors : ¬Reaches loopState .error := by
  intro ⟨fuel, reaches⟩
  have member := cycle_steps fuel InCycle.start
  rw [reaches] at member
  cases member

theorem unbounded_budget_exhaustion_is_false :
    ¬(∀ state : State, (∀ value, ¬Reaches state (.halt value)) → Reaches state .error) := by
  intro exhaustion
  exact loop_never_errors (exhaustion loopState loop_never_halts)

end Test.MIR.Opt.BudgetModel
