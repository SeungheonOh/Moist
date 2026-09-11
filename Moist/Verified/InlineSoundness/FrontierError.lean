import Moist.Verified.InlineSoundness.EvaluationPath
import Moist.Verified.InlineSoundness.Frontier

set_option maxHeartbeats 800000

namespace Moist.Verified.InlineSoundness.Frontier

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.BetaValueRefines
open Moist.Verified.InlineSoundness.Totality

private theorem semantic_steps (fuel : Nat) (state : State) :
    steps fuel state = Semantics.steps fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis => exact inductionHypothesis (step state)

private theorem total_returns {term rhs : Term} (total : TotalTerm term)
    {position depth : Nat} (positive : 1 ≤ position) (bound : position ≤ depth + 1)
    (absent : StrictOcc.freeOf position term = true)
    (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length) :
    ∃ value, ValueWellFormed value ∧ ∀ stack, ∃ fuel,
      steps fuel (.compute stack environment (substTerm position rhs term)) = .ret stack value := by
  have sized : Semantics.WellSizedEnv depth environment := by
    intro index positive bound
    obtain ⟨value, lookup, _⟩ := envWellFormed_lookup depth wellFormed positive bound
    exact ⟨value, lookup⟩
  obtain ⟨value, fuel, halts⟩ := total.subst_halts positive bound absent closed rhsClosed environment sized
  have halts' : steps fuel (.compute [] environment (substTerm position rhs term)) = .halt value := by
    rw [semantic_steps]; exact halts
  have valueWellFormed := StepWellFormed.halt_value_wf
    (StepWellFormed.StateWellFormed.compute .nil wellFormed length
      (closedAt_substTerm position rhs term depth positive bound rhsClosed closed)) halts'
  refine ⟨value, valueWellFormed, ?_⟩
  intro stack
  obtain ⟨returnFuel, returned⟩ := Purity.compute_to_ret_from_halt environment _ value stack ⟨fuel, halts⟩
  exact ⟨returnFuel, by rw [semantic_steps]; exact returned⟩

private theorem error_before {source target : State} (fuel : Nat)
    (prefixSteps : steps fuel source = target) (errors : Reaches target .error) :
    Reaches source .error := by
  obtain ⟨remaining, errors⟩ := errors
  exact ⟨fuel + remaining, by rw [steps_trans, prefixSteps]; exact errors⟩

mutual
  theorem CheckedPath.errors {position depth : Nat} {term rhs : Term}
      (path : CheckedPath position term) (positive : 1 ≤ position) (bound : position ≤ depth + 1)
      (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
      (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
      (length : depth ≤ environment.length)
      (rhsErrors : ∀ stack, Reaches (.compute stack environment rhs) .error)
      (stack : Stack) :
      Reaches (.compute stack environment (substTerm position rhs term)) .error := by
    cases path with
    | var => simpa only [substTerm, if_pos rfl] using rhsErrors stack
    | applyLeft inner =>
      simp only [substTerm]
      simp only [closedAt, Bool.and_eq_true] at closed
      apply error_before 1 rfl
      exact inner.errors positive bound closed.1 rhsClosed environment wellFormed length rhsErrors _
    | applyRight total absent inner =>
      simp only [substTerm]
      simp only [closedAt, Bool.and_eq_true] at closed
      obtain ⟨value, _, returns⟩ := total_returns total positive bound absent closed.1 rhsClosed
        environment wellFormed length
      obtain ⟨fuel, returns⟩ := returns (.arg (substTerm position rhs _) environment :: stack)
      apply error_before 1 rfl
      apply error_before fuel returns
      apply error_before 1 rfl
      exact inner.errors positive bound closed.2 rhsClosed environment wellFormed length rhsErrors _
    | force inner =>
      simp only [substTerm]
      apply error_before 1 rfl
      exact inner.errors positive bound (by simpa only [closedAt] using closed) rhsClosed
        environment wellFormed length rhsErrors _
    | caseScrutinee inner =>
      simp only [substTerm]
      simp only [closedAt, Bool.and_eq_true] at closed
      apply error_before 1 rfl
      exact inner.errors positive bound closed.1 rhsClosed environment wellFormed length rhsErrors _
    | constr fields =>
      rename_i terms tag
      cases terms with
      | nil => cases fields
      | cons head tail =>
        simp only [substTerm, substTermList]
        apply error_before 1 rfl
        exact fields.errors positive bound (by simpa only [closedAt] using closed) rhsClosed
          environment wellFormed length rhsErrors tag [] stack
    | letBody total absent inner =>
      rename_i rhsTerm body
      simp only [substTerm]
      simp only [closedAt, Bool.and_eq_true] at closed
      obtain ⟨value, valueWellFormed, returns⟩ := total_returns total positive bound absent closed.2 rhsClosed
        environment wellFormed length
      obtain ⟨fuel, returns⟩ := returns
        (.funV (.VLam (substTerm (position + 1) (renameTerm (shiftRename 1) rhs) body) environment) :: stack)
      apply error_before 3 rfl
      apply error_before fuel returns
      apply error_before 1 rfl
      exact inner.errors (by omega) (by omega) closed.1 (closedAt_shift rhsClosed)
        (environment.extend value) (envWellFormed_extend depth wellFormed length valueWellFormed)
        (by simp [CekEnv.extend, CekEnv.length]; omega)
        (StrictOcc.shift_rhs_reaches_error rhsClosed wellFormed rhsErrors value) stack
  termination_by sizeOf term
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega

  theorem CheckedPaths.errors {position depth : Nat} {head rhs : Term} {tail : List Term}
      (path : CheckedPaths position (head :: tail)) (positive : 1 ≤ position) (bound : position ≤ depth + 1)
      (closed : closedAtList (depth + 1) (head :: tail) = true) (rhsClosed : closedAt depth rhs = true)
      (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
      (length : depth ≤ environment.length)
      (rhsErrors : ∀ stack, Reaches (.compute stack environment rhs) .error)
      (tag : Nat) (done : List CekValue) (stack : Stack) :
      Reaches (.compute (.constrField tag done (substTermList position rhs tail) environment :: stack)
        environment (substTerm position rhs head)) .error := by
    simp only [closedAtList, Bool.and_eq_true] at closed
    cases path with
    | head inner => exact inner.errors positive bound closed.1 rhsClosed environment wellFormed length rhsErrors _
    | tail total absent inner =>
      obtain ⟨value, _, returns⟩ := total_returns total positive bound absent closed.1 rhsClosed
        environment wellFormed length
      obtain ⟨fuel, returns⟩ := returns (.constrField tag done (substTermList position rhs tail) environment :: stack)
      apply error_before fuel returns
      cases tail with
      | nil => cases inner
      | cons next rest =>
        simp only [substTermList]
        apply error_before 1 rfl
        exact inner.errors positive bound closed.2 rhsClosed environment wellFormed length rhsErrors
          tag (value :: done) stack
  termination_by sizeOf (head :: tail)
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega
end

theorem evaluationPath_subst_errors {position depth : Nat} {term rhs : Term}
    (path : EvaluationPath position term) (single : StrictOcc.StrictSingleOcc position term)
    (positive : 1 ≤ position) (bound : position ≤ depth + 1)
    (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length)
    (rhsErrors : Reaches (.compute [] environment rhs) .error) (stack : Stack) :
    Reaches (.compute stack environment (substTerm position rhs term)) .error :=
  path.checked single |>.errors positive bound closed rhsClosed environment wellFormed length
    (StrictOcc.error_on_all_stacks rhsErrors) stack

theorem beta_evaluationPath_ctxRefines {depth : Nat} {body rhs : Term}
    (path : EvaluationPath 1 body) (single : StrictOcc.StrictSingleOcc 1 body)
    (bodyClosed : closedAt (depth + 1) body = true) (rhsClosed : closedAt depth rhs = true) :
    Contextual.CtxRefines (.Apply (.Lam 0 body) rhs) (substTerm 1 rhs body) := by
  apply beta_frontier_ctxRefines single.toSingleOcc bodyClosed rhsClosed
  intro environment stack wellFormed length _ errors
  exact evaluationPath_subst_errors path single (by omega) (by omega) bodyClosed rhsClosed
    environment wellFormed length errors stack

end Moist.Verified.InlineSoundness.Frontier
