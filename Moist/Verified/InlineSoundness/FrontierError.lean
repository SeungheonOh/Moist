import Moist.Verified.InlineSoundness.EvaluationPath
import Moist.Verified.InlineSoundness.Frontier


namespace Moist.Verified.InlineSoundness.Frontier

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.BetaValueRefines
open Moist.Verified.InlineSoundness.Totality

/-- Evaluation from the empty stack halts or errors. -/
private def Terminates (state : State) : Prop :=
  (∃ value, Reaches state (.halt value)) ∨ Reaches state .error

private theorem terminates_of_steps {source target : State} (fuel : Nat)
    (prefixSteps : steps fuel source = target) (terminates : Terminates target) :
    Terminates source := by
  rcases terminates with ⟨value, more, halts⟩ | ⟨more, errors⟩
  · exact .inl ⟨value, fuel + more, by rw [steps_trans, prefixSteps]; exact halts⟩
  · exact .inr ⟨fuel + more, by rw [steps_trans, prefixSteps]; exact errors⟩

private theorem terminates_then {environment : CekEnv} {term : Term} {stack : Stack}
    (terminates : Terminates (.compute [] environment term))
    (andThen : ∀ value, Reaches (.compute [] environment term) (.halt value) →
      Terminates (.ret stack value)) :
    Terminates (.compute stack environment term) := by
  rcases terminates with ⟨value, halts⟩ | errors
  · obtain ⟨fuel, returns⟩ := StrictOcc.halt_on_all_stacks halts stack
    exact terminates_of_steps fuel returns (andThen value halts)
  · exact .inr (StrictOcc.error_on_all_stacks errors stack)

private theorem constrFields_terminate {environment : CekEnv} {tag : Nat} :
    ∀ (terms : List Term) (done : List CekValue) (value : CekValue),
      (∀ term ∈ terms, Terminates (.compute [] environment term)) →
      Terminates (.ret [.constrField tag done terms environment] value)
  | [], _, _, _ => .inl ⟨_, 2, rfl⟩
  | term :: rest, done, value, terminate =>
    terminates_of_steps 1 rfl <| terminates_then (terminate term (.head _)) fun next _ =>
      constrFields_terminate rest (value :: done) next fun other member =>
        terminate other (.tail _ member)

mutual
/-- Substituting an erroring `rhs` into a total term cannot diverge. -/
private theorem subst_terminates {rhs : Term} {position depth : Nat}
    (positive : 1 ≤ position) (bound : position ≤ depth + 1) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length)
    (rhsErrors : ∀ stack, Reaches (.compute stack environment rhs) .error) :
    ∀ {term : Term}, TotalTerm term → closedAt (depth + 1) term = true →
      Terminates (.compute [] environment (substTerm position rhs term))
  | _, .var nonzero, closed => by
    rename_i index
    simp only [closedAt, decide_eq_true_eq] at closed
    simp only [substTerm]
    split
    · exact .inr (rhsErrors [])
    · have lookup : ∀ index, 1 ≤ index → index ≤ depth →
          Terminates (.compute [] environment (.Var index)) := fun index low high =>
        let ⟨value, found, _⟩ := envWellFormed_lookup depth wellFormed low high
        .inl ⟨value, 2, by simp [steps, step, found]⟩
      split
      · exact lookup _ (by omega) (by omega)
      · exact lookup _ nonzero (by omega)
  | _, .constant, _ | _, .builtin, _ => by simp only [substTerm]; exact .inl ⟨_, 2, rfl⟩
  | _, .lam, _ | _, .delay, _ => by simp only [substTerm]; exact .inl ⟨_, 2, rfl⟩
  | _, .forceBuiltin signature, _ => by
    simp only [substTerm]
    exact .inl ⟨_, 4, by simp [steps, step, signature, ExpectedArgs.head, ExpectedArgs.tail]; rfl⟩
  | _, .forceForceBuiltin signature, _ => by
    simp only [substTerm]
    exact .inl ⟨_, 6, by simp [steps, step, signature, ExpectedArgs.head, ExpectedArgs.tail]; rfl⟩
  | _, .forceDelay inner, closed => by
    simp only [substTerm]
    exact terminates_of_steps 3 rfl
      (subst_terminates positive bound rhsClosed environment wellFormed length rhsErrors inner
        (by simpa [closedAt] using closed))
  | _, .constr fields, closed => by
    rename_i terms tag
    simp only [closedAt] at closed
    simp only [substTerm]
    have each := substList_terminates positive bound rhsClosed environment wellFormed length
      rhsErrors fields closed
    generalize substTermList position rhs terms = substituted at each
    cases substituted with
    | nil => exact .inl ⟨_, 2, rfl⟩
    | cons head tail =>
      exact terminates_of_steps 1 rfl <| terminates_then (each head (.head _)) fun value _ =>
        constrFields_terminate tail [] value fun other member => each other (.tail _ member)
  | _, .letBody rhsTotal bodyTotal, closed => by
    rename_i rhsTerm body _
    simp only [closedAt, Bool.and_eq_true] at closed
    simp only [substTerm]
    refine terminates_of_steps 3 rfl <| terminates_then
      (subst_terminates positive bound rhsClosed environment wellFormed length rhsErrors rhsTotal
        closed.2) fun value halts => terminates_of_steps 1 rfl ?_
    obtain ⟨fuel, halts⟩ := halts
    have valueWellFormed := StepWellFormed.halt_value_wf
      (StepWellFormed.StateWellFormed.compute .nil wellFormed length
        (closedAt_substTerm position rhs rhsTerm depth positive bound rhsClosed closed.2)) halts
    exact subst_terminates (by omega) (by omega) (closedAt_shift rhsClosed)
      (environment.extend value) (envWellFormed_extend depth wellFormed length valueWellFormed)
      (by simp [CekEnv.extend, CekEnv.length]; omega)
      (StrictOcc.shift_rhs_reaches_error rhsClosed wellFormed rhsErrors value) bodyTotal closed.1

private theorem substList_terminates {rhs : Term} {position depth : Nat}
    (positive : 1 ≤ position) (bound : position ≤ depth + 1) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length)
    (rhsErrors : ∀ stack, Reaches (.compute stack environment rhs) .error) :
    ∀ {terms : List Term}, TotalTerms terms → closedAtList (depth + 1) terms = true →
      ∀ term ∈ substTermList position rhs terms, Terminates (.compute [] environment term)
  | _, .nil, _ => by simp [substTermList]
  | _, .cons headTotal tailTotal, closed => by
    simp only [closedAtList, Bool.and_eq_true] at closed
    simp only [substTermList]
    intro term member
    cases member with
    | head =>
      exact subst_terminates positive bound rhsClosed environment wellFormed length rhsErrors
        headTotal closed.1
    | tail _ member =>
      exact substList_terminates positive bound rhsClosed environment wellFormed length rhsErrors
        tailTotal closed.2 term member
end

/-- Substituting an erroring `rhs` into a total term returns a well-formed
    value on every stack, or errors on every stack. -/
private theorem subst_returns_or_errors {term rhs : Term} (total : TotalTerm term)
    {position depth : Nat} (positive : 1 ≤ position) (bound : position ≤ depth + 1)
    (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length)
    (rhsErrors : ∀ stack, Reaches (.compute stack environment rhs) .error) :
    (∃ value, ValueWellFormed value ∧ ∀ stack, ∃ fuel,
      steps fuel (.compute stack environment (substTerm position rhs term)) = .ret stack value) ∨
    ∀ stack, Reaches (.compute stack environment (substTerm position rhs term)) .error := by
  rcases subst_terminates positive bound rhsClosed environment wellFormed length rhsErrors total closed
    with ⟨value, fuel, halts⟩ | errors
  · refine .inl ⟨value, StepWellFormed.halt_value_wf
      (StepWellFormed.StateWellFormed.compute .nil wellFormed length
        (closedAt_substTerm position rhs term depth positive bound rhsClosed closed)) halts,
      StrictOcc.halt_on_all_stacks ⟨fuel, halts⟩⟩
  · exact .inr (StrictOcc.error_on_all_stacks errors)

private theorem error_before {source target : State} (fuel : Nat)
    (prefixSteps : steps fuel source = target) (errors : Reaches target .error) :
    Reaches source .error := by
  obtain ⟨remaining, errors⟩ := errors
  exact ⟨fuel + remaining, by rw [steps_trans, prefixSteps]; exact errors⟩

mutual
  /-- An erroring `rhs` substituted at the evaluation frontier makes the
      whole term error. -/
  theorem EvaluationPath.errors {position depth : Nat} {term rhs : Term}
      (path : EvaluationPath position term) (positive : 1 ≤ position) (bound : position ≤ depth + 1)
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
    | applyRight total inner =>
      simp only [substTerm]
      simp only [closedAt, Bool.and_eq_true] at closed
      apply error_before 1 rfl
      rcases subst_returns_or_errors total positive bound closed.1 rhsClosed environment wellFormed
        length rhsErrors with ⟨value, _, returns⟩ | errors
      · obtain ⟨fuel, returns⟩ := returns (.arg (substTerm position rhs _) environment :: stack)
        apply error_before fuel returns
        apply error_before 1 rfl
        exact inner.errors positive bound closed.2 rhsClosed environment wellFormed length rhsErrors _
      · exact errors _
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
    | letBody total inner =>
      rename_i rhsTerm body
      simp only [substTerm]
      simp only [closedAt, Bool.and_eq_true] at closed
      apply error_before 3 rfl
      rcases subst_returns_or_errors total positive bound closed.2 rhsClosed environment wellFormed
        length rhsErrors with ⟨value, valueWellFormed, returns⟩ | errors
      · obtain ⟨fuel, returns⟩ := returns
          (.funV (.VLam (substTerm (position + 1) (renameTerm (shiftRename 1) rhs) body) environment) :: stack)
        apply error_before fuel returns
        apply error_before 1 rfl
        exact inner.errors (by omega) (by omega) closed.1 (closedAt_shift rhsClosed)
          (environment.extend value) (envWellFormed_extend depth wellFormed length valueWellFormed)
          (by simp [CekEnv.extend, CekEnv.length]; omega)
          (StrictOcc.shift_rhs_reaches_error rhsClosed wellFormed rhsErrors value) stack
      · exact errors _
  termination_by sizeOf term
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega

  theorem EvaluationPaths.errors {position depth : Nat} {head rhs : Term} {tail : List Term}
      (path : EvaluationPaths position (head :: tail)) (positive : 1 ≤ position)
      (bound : position ≤ depth + 1)
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
    | tail total inner =>
      rcases subst_returns_or_errors total positive bound closed.1 rhsClosed environment wellFormed
        length rhsErrors with ⟨value, _, returns⟩ | errors
      · obtain ⟨fuel, returns⟩ := returns
          (.constrField tag done (substTermList position rhs tail) environment :: stack)
        apply error_before fuel returns
        cases tail with
        | nil => cases inner
        | cons next rest =>
          simp only [substTermList]
          apply error_before 1 rfl
          exact inner.errors positive bound closed.2 rhsClosed environment wellFormed length rhsErrors
            tag (value :: done) stack
      · exact errors _
  termination_by sizeOf (head :: tail)
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega
end

theorem CheckedPath.errors {position depth : Nat} {term rhs : Term}
    (path : CheckedPath position term) (positive : 1 ≤ position) (bound : position ≤ depth + 1)
    (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length)
    (rhsErrors : ∀ stack, Reaches (.compute stack environment rhs) .error)
    (stack : Stack) :
    Reaches (.compute stack environment (substTerm position rhs term)) .error :=
  path.toEvaluationPath.errors positive bound closed rhsClosed environment wellFormed length
    rhsErrors stack

theorem evaluationPath_subst_errors {position depth : Nat} {term rhs : Term}
    (path : EvaluationPath position term) (_single : StrictOcc.StrictSingleOcc position term)
    (positive : 1 ≤ position) (bound : position ≤ depth + 1)
    (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (wellFormed : EnvWellFormed depth environment)
    (length : depth ≤ environment.length)
    (rhsErrors : Reaches (.compute [] environment rhs) .error) (stack : Stack) :
    Reaches (.compute stack environment (substTerm position rhs term)) .error :=
  path.errors positive bound closed rhsClosed environment wellFormed length
    (StrictOcc.error_on_all_stacks rhsErrors) stack

/-- Frontier beta without an occurrence-count premise. -/
theorem beta_evaluationPath_refines {depth : Nat} {body rhs : Term} (path : EvaluationPath 1 body)
    (bodyClosed : closedAt (depth + 1) body = true) (rhsClosed : closedAt depth rhs = true) :
    Contextual.CtxRefines (.Apply (.Lam 0 body) rhs) (substTerm 1 rhs body) :=
  beta_ctxRefines_of_errorFrontier bodyClosed rhsClosed
    fun environment stack wellFormed length _ errors =>
      path.errors (by omega) (by omega) bodyClosed rhsClosed environment wellFormed length
        (StrictOcc.error_on_all_stacks errors) stack

/-- Beta with a total (pure) `rhs`. -/
theorem beta_total_ctxRefines {depth : Nat} {body rhs : Term} (total : TotalTerm rhs)
    (bodyClosed : closedAt (depth + 1) body = true) (rhsClosed : closedAt depth rhs = true) :
    Contextual.CtxRefines (.Apply (.Lam 0 body) rhs) (substTerm 1 rhs body) :=
  beta_ctxRefines_of_halts bodyClosed rhsClosed fun environment wellFormed _ => by
    obtain ⟨value, fuel, halts⟩ := total.halts depth environment rhsClosed fun index positive bound =>
      let ⟨value, lookup, _⟩ := envWellFormed_lookup depth wellFormed positive bound; ⟨value, lookup⟩
    exact ⟨value, fuel, by rw [vstep_eq]; exact halts⟩

theorem beta_evaluationPath_ctxRefines {depth : Nat} {body rhs : Term}
    (path : EvaluationPath 1 body) (_single : StrictOcc.StrictSingleOcc 1 body)
    (bodyClosed : closedAt (depth + 1) body = true) (rhsClosed : closedAt depth rhs = true) :
    Contextual.CtxRefines (.Apply (.Lam 0 body) rhs) (substTerm 1 rhs body) :=
  beta_evaluationPath_refines path bodyClosed rhsClosed

end Moist.Verified.InlineSoundness.Frontier
