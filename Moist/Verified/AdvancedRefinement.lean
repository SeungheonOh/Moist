import Moist.Verified.AdvancedRedexes
import Moist.Verified.FundamentalRefinesWF
import Moist.Verified.InlineSoundness.SubstRefinesExt

namespace Moist.Verified.AdvancedRefinement

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual

theorem advance_eq_steps (fuel : Nat) (state : State) :
    AdvancedRedexes.advance fuel state = steps fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis => exact inductionHypothesis (step state)

private theorem steps_add (prefixFuel suffix : Nat) (state : State) :
    steps (prefixFuel + suffix) state = steps suffix (steps prefixFuel state) := by
  induction prefixFuel generalizing state with
  | zero => simp [steps]
  | succ prefixFuel inductionHypothesis =>
    simpa only [Nat.succ_add, steps] using inductionHypothesis (step state)

private theorem steps_fixed (fuel : Nat) {state : State} (fixed : step state = state) :
    steps fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis => simpa only [steps, fixed] using inductionHypothesis

theorem reaches_after_prefix (prefixFuel : Nat) {source target : State}
    (fixed : step target = target) :
    Reaches source target ↔ Reaches (steps prefixFuel source) target := by
  constructor
  · rintro ⟨fuel, reaches⟩
    by_cases before : fuel ≤ prefixFuel
    · refine ⟨0, ?_⟩
      have split : prefixFuel = fuel + (prefixFuel - fuel) := by omega
      change steps prefixFuel source = target
      rw [split, steps_add, reaches]
      exact steps_fixed _ fixed
    · refine ⟨fuel - prefixFuel, ?_⟩
      rw [← steps_add, Nat.add_sub_of_le (by omega)]
      exact reaches
  · rintro ⟨fuel, reaches⟩
    exact ⟨prefixFuel + fuel, by rw [steps_add]; exact reaches⟩

theorem finite_join_refines {left right : State} {leftFuel rightFuel : Nat}
    (join : AdvancedRedexes.advance leftFuel left =
      AdvancedRedexes.advance rightFuel right) : ObsRefines left right := by
  simp only [advance_eq_steps] at join
  constructor
  · rintro ⟨value, reaches⟩
    refine ⟨value, (reaches_after_prefix rightFuel rfl).mpr ?_⟩
    rw [← join]
    exact (reaches_after_prefix leftFuel rfl).mp reaches
  · intro reaches
    apply (reaches_after_prefix rightFuel rfl).mpr
    rw [← join]
    exact (reaches_after_prefix leftFuel rfl).mp reaches

theorem contextual_of_uniform_refinement {depth : Nat} {source target : Term}
    (sourceClosed : closedAt depth source = true)
    (closedPreserved : ∀ depth, closedAt depth source = true → closedAt depth target = true)
    (localRefinement : ∀ environment stack,
      ObsRefines (.compute stack environment source) (.compute stack environment target)) :
    CtxRefines source target := by
  apply TermObsRefinesWF.soundness_refinesWF (d := depth)
  · intro budget index indexBound leftEnv rightEnv environments leftWellFormed leftLength
      rightWellFormed rightLength observation observationBound leftStack rightStack
      leftStackWellFormed rightStackWellFormed stacks
    have selfRefinement := FundamentalRefinesWF.ftlr_wf depth source sourceClosed
      budget index indexBound leftEnv rightEnv environments leftWellFormed leftLength
      rightWellFormed rightLength observation observationBound leftStack rightStack
      leftStackWellFormed rightStackWellFormed stacks
    exact InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
      selfRefinement (localRefinement rightEnv rightStack)
  · intro context sourceContextClosed
    obtain ⟨contextClosed, termClosed⟩ :=
      (fill_closedAt_iff context source 0).mp sourceContextClosed
    exact (fill_closedAt_iff context target 0).mpr
      ⟨contextClosed, closedPreserved _ termClosed⟩

theorem contextual_of_uniform_join {depth : Nat} {source target : Term}
    (sourceClosed : closedAt depth source = true)
    (closedPreserved : ∀ depth, closedAt depth source = true → closedAt depth target = true)
    (join : ∀ environment stack, ∃ leftFuel rightFuel,
      AdvancedRedexes.advance leftFuel (.compute stack environment source) =
        AdvancedRedexes.advance rightFuel (.compute stack environment target)) :
    CtxRefines source target := by
  apply contextual_of_uniform_refinement sourceClosed closedPreserved
  intro environment stack
  obtain ⟨leftFuel, rightFuel, joined⟩ := join environment stack
  exact finite_join_refines joined

theorem fold_mkCons_generic_data (head : Moist.Plutus.Data)
    (tail : List Moist.Plutus.Data) :
    CtxRefines
      (.Apply (.Apply (.Force (.Builtin .MkCons))
        (.Constant (.Data head, .AtomicType .TypeData)))
        (.Constant (.ConstList (tail.map Const.Data),
          .TypeOperator (.TypeList (.AtomicType .TypeData)))))
      (.Constant (.ConstList ((head :: tail).map Const.Data),
        .TypeOperator (.TypeList (.AtomicType .TypeData)))) := by
  apply contextual_of_uniform_join (depth := 0) (by simp [closedAt]) (by intros; simp [closedAt])
  intro environment stack
  exact ⟨11, 1, rfl⟩

theorem fold_mkCons_specialized_data (head : Moist.Plutus.Data)
    (tail : List Moist.Plutus.Data) :
    CtxRefines
      (.Apply (.Apply (.Force (.Builtin .MkCons))
        (.Constant (.Data head, .AtomicType .TypeData)))
        (.Constant (.ConstDataList tail,
          .TypeOperator (.TypeList (.AtomicType .TypeData)))))
      (.Constant (.ConstDataList (head :: tail),
        .TypeOperator (.TypeList (.AtomicType .TypeData)))) := by
  apply contextual_of_uniform_join (depth := 0) (by simp [closedAt]) (by intros; simp [closedAt])
  intro environment stack
  exact ⟨11, 1, rfl⟩

theorem fold_binary_builtin (builtin : BuiltinFun) (first second result : Const)
    (firstType secondType resultType : BuiltinType)
    (signature : expectedArgs builtin = .more .argV (.one .argV))
    (evaluated : evalBuiltin builtin [.VCon second, .VCon first] = some (.VCon result)) :
    CtxRefines
      (.Apply (.Apply (.Builtin builtin) (.Constant (first, firstType)))
        (.Constant (second, secondType)))
      (.Constant (result, resultType)) := by
  apply contextual_of_uniform_join (depth := 0) (by simp [closedAt]) (by intros; simp [closedAt])
  intro environment stack
  exact ⟨9, 1, AdvancedRedexes.fold_binary_builtin builtin first second result
    firstType secondType resultType environment stack signature evaluated⟩

theorem boolean_choice (depth : Nat) (condition : Bool) (whenFalse whenTrue : Term)
    (falseClosed : closedAt depth whenFalse = true)
    (trueClosed : closedAt depth whenTrue = true) :
    CtxRefines
      (.Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse))
        (.Constant (.Bool condition, .AtomicType .TypeBool))) (.Delay whenTrue))
        (.Delay whenFalse)))
      (.Case (.Constant (.Bool condition, .AtomicType .TypeBool)) [whenFalse, whenTrue]) := by
  apply contextual_of_uniform_join (depth := depth)
  · simp [closedAt, falseClosed, trueClosed]
  · intro scope sourceClosed
    simpa [closedAt, closedAtList, Bool.and_comm] using sourceClosed
  · intro environment stack
    exact ⟨17, 3, AdvancedRedexes.boolean_choice condition whenFalse whenTrue environment stack⟩

theorem force_case_delay (depth : Nat) (condition : Bool) (whenFalse whenTrue : Term)
    (falseClosed : closedAt depth whenFalse = true)
    (trueClosed : closedAt depth whenTrue = true) :
    CtxRefines
      (.Force (.Case (.Constant (.Bool condition, .AtomicType .TypeBool))
        [.Delay whenFalse, .Delay whenTrue]))
      (.Case (.Constant (.Bool condition, .AtomicType .TypeBool)) [whenFalse, whenTrue]) := by
  apply contextual_of_uniform_join (depth := depth)
  · simp [closedAt, closedAtList, falseClosed, trueClosed]
  · intro scope sourceClosed
    simpa [closedAt, closedAtList] using sourceClosed
  · intro environment stack
    exact ⟨6, 3, AdvancedRedexes.force_case_delay condition whenFalse whenTrue environment stack⟩

theorem delayed_list_choice_variable (depth : Nat) (nonempty empty : Term)
    (variableClosed : 1 ≤ depth)
    (nonemptyClosed : closedAt depth nonempty = true)
    (emptyClosed : closedAt depth empty = true) :
    CtxRefines
      (.Force (.Apply (.Apply (.Apply (.Force (.Force (.Builtin .ChooseList)))
        (.Var 1)) (.Delay empty)) (.Delay nonempty)))
      (.Case (.Apply (.Force (.Builtin .NullList)) (.Var 1)) [nonempty, empty]) := by
  apply contextual_of_uniform_join (depth := depth)
  · simp [closedAt, variableClosed, nonemptyClosed, emptyClosed]
  · intro scope sourceClosed
    simpa [closedAt, closedAtList, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
      using sourceClosed
  · intro environment stack
    cases environment with
    | nil => exact ⟨19, 9, rfl⟩
    | cons value environment =>
      exact ⟨19, 9, AdvancedRedexes.delayed_list_choice_value value nonempty empty environment stack⟩

end Moist.Verified.AdvancedRefinement
