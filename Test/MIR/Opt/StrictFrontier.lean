import Moist.Verified.AdvancedRefinement
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.InlineSoundness.FrontierError

namespace Test.MIR.Opt.StrictFrontier

open Moist.CEK Moist.Plutus.Term Moist.Verified
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.InlineSoundness.StrictOcc

private def selfApply : Term := .Apply (.Var 1) (.Var 1)
private def closure : CekValue := .VLam selfApply .nil
private def environment : CekEnv := .cons closure .nil
private def pending : Stack := [.arg .Error .nil]
private def looping : State := .compute pending environment selfApply

def divergent : Term := .Apply (.Lam 0 selfApply) (.Lam 0 selfApply)
def body : Term := .Apply divergent (.Var 1)
def before : State := .compute [] .nil (.Apply (.Lam 0 body) .Error)
def after : State := .compute [] .nil (Moist.Verified.substTerm 1 .Error body)

private inductive InCycle : State → Prop where
  | start : InCycle looping
  | functionLookup : InCycle (.compute (.arg (.Var 1) environment :: pending) environment (.Var 1))
  | functionReturn : InCycle (.ret (.arg (.Var 1) environment :: pending) closure)
  | argumentLookup : InCycle (.compute (.funV closure :: pending) environment (.Var 1))
  | argumentReturn : InCycle (.ret (.funV closure :: pending) closure)

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

theorem legacy_occurrence_accepts_divergent_predecessor : StrictSingleOcc 1 body := by
  apply StrictSingleOcc.apply_r
  · simp [divergent, selfApply, freeOf]
  · exact StrictSingleOcc.var

theorem before_errors : Reaches before .error := by
  exact ⟨4, rfl⟩

theorem after_never_errors : ¬Reaches after .error := by
  intro reaches
  have entered : steps 6 after = looping := by
    simp [after, body, divergent, selfApply, Moist.Verified.substTerm]
    rfl
  have afterEntry := (AdvancedRefinement.reaches_after_prefix 6 rfl).mp reaches
  rw [entered] at afterEntry
  obtain ⟨fuel, terminates⟩ := afterEntry
  have member := cycle_steps fuel InCycle.start
  rw [terminates] at member
  cases member

theorem strict_occurrence_alone_does_not_refine : ¬ObsRefines before after := by
  intro refines
  exact after_never_errors (refines.error before_errors)

theorem evaluation_path_rejects_divergent_predecessor :
    ¬InlineSoundness.Frontier.EvaluationPath 1 body := by
  intro path
  have errors := InlineSoundness.Frontier.evaluationPath_subst_errors (depth := 0) (rhs := .Error)
    path legacy_occurrence_accepts_divergent_predecessor (by omega) (by omega)
    (by simp [body, divergent, selfApply, closedAt]) (by simp [closedAt]) .nil
    .zero (by simp [CekEnv.length]) ⟨1, rfl⟩ []
  exact after_never_errors errors

end Test.MIR.Opt.StrictFrontier
