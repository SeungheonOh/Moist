import Moist.Verified.DataFoldingSoundness

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Plutus.Term Moist.CEK
open Moist.Verified.Equivalence Moist.Verified.BetaValueRefines

def ClosedConstantEvaluation (expression : Expr) (value : CekValue) : Prop :=
  ∃ term, (∀ environment, lowerTotalExpr environment expression = some term) ∧
    Moist.Verified.closedAt 0 term = true ∧
    ∀ environment stack, ∃ fuel, steps fuel (.compute stack environment term) = .ret stack value

private theorem closedEvaluation_force {inner : Expr} {builtin : BuiltinFun}
    {arguments : List CekValue} {remaining rest : ExpectedArgs}
    (evaluates : ClosedConstantEvaluation inner (.VBuiltin builtin arguments remaining))
    (head : remaining.head = .argQ) (tail : remaining.tail = some rest) :
    ClosedConstantEvaluation (.Force inner) (.VBuiltin builtin arguments rest) := by
  obtain ⟨term, lowering, closed, evaluation⟩ := evaluates
  refine ⟨.Force term, ?_, ?_, ?_⟩
  · intro environment; rw [lowerTotalExpr_force, lowering]; rfl
  · simpa [Moist.Verified.closedAt] using closed
  · intro environment stack
    obtain ⟨fuel, returns⟩ := evaluation environment (.force :: stack)
    refine ⟨1 + fuel + 1, ?_⟩
    rw [show 1 + fuel + 1 = 1 + (fuel + 1) by omega, steps_trans]
    change steps (fuel + 1) (.compute (.force :: stack) environment term) = _
    rw [steps_trans, returns]
    simp [steps, step, head, tail]

private theorem closedEvaluation_app {function argument : Expr} {functionValue argumentValue result : CekValue}
    (functionEvaluates : ClosedConstantEvaluation function functionValue)
    (argumentEvaluates : ClosedConstantEvaluation argument argumentValue)
    (applies : ∀ stack, step (.ret (.funV functionValue :: stack) argumentValue) = .ret stack result) :
    ClosedConstantEvaluation (.App function argument) result := by
  obtain ⟨functionTerm, functionLowering, functionClosed, functionEvaluation⟩ := functionEvaluates
  obtain ⟨argumentTerm, argumentLowering, argumentClosed, argumentEvaluation⟩ := argumentEvaluates
  refine ⟨.Apply functionTerm argumentTerm, ?_, ?_, ?_⟩
  · intro environment; rw [lowerTotalExpr_app, functionLowering, argumentLowering]; rfl
  · simp [Moist.Verified.closedAt, functionClosed, argumentClosed]
  · intro environment stack
    obtain ⟨functionFuel, functionReturns⟩ := functionEvaluation environment (.arg argumentTerm environment :: stack)
    obtain ⟨argumentFuel, argumentReturns⟩ := argumentEvaluation environment (.funV functionValue :: stack)
    refine ⟨1 + (functionFuel + (1 + (argumentFuel + 1))), ?_⟩
    rw [steps_trans]
    change steps (functionFuel + (1 + (argumentFuel + 1)))
      (.compute (.arg argumentTerm environment :: stack) environment functionTerm) = _
    rw [steps_trans, functionReturns, steps_trans]
    change steps (argumentFuel + 1) (.compute (.funV functionValue :: stack) environment argumentTerm) = _
    rw [steps_trans, argumentReturns]
    exact applies stack

theorem constantValue_evaluates (expression : Expr) (value : CekValue)
    (accepted : constantValue expression = some value) : ClosedConstantEvaluation expression value := by
  cases expression with
  | Lit literal =>
    obtain ⟨constant, annotation⟩ := literal
    simp only [constantValue] at accepted
    split at accepted
    · cases accepted
      refine ⟨.Constant (constant, annotation), ?_, ?_, ?_⟩
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack; exact ⟨1, rfl⟩
    · contradiction
  | Builtin builtin =>
    simp only [constantValue] at accepted
    split at accepted
    · cases accepted
      refine ⟨.Builtin builtin, ?_, ?_, ?_⟩
      · intro environment; simp [lowerTotalExpr, expandFix, lowerTotal]
      · simp [Moist.Verified.closedAt]
      · intro environment stack; exact ⟨1, rfl⟩
    · contradiction
  | Force inner =>
    simp only [constantValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨innerValue, innerAccepted, result⟩ := accepted
    cases innerValue <;> try contradiction
    rename_i builtin arguments remaining
    dsimp only at result
    split at result
    · contradiction
    · rename_i head
      simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at result
      obtain ⟨rest, tail, rfl⟩ := result
      apply closedEvaluation_force (constantValue_evaluates inner _ innerAccepted) _ tail
      cases headValue : remaining.head with
      | argQ => rfl
      | argV => exact False.elim (head (by rw [headValue]; rfl))
  | App function argument =>
    simp only [constantValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨functionValue, functionAccepted, result⟩ := accepted
    cases functionValue <;> try contradiction
    rename_i builtin arguments remaining
    simp only [Option.bind_eq_some_iff] at result
    obtain ⟨argumentValue, argumentAccepted, result⟩ := result
    split at result
    · contradiction
    · rename_i head
      have headEqual : remaining.head = .argV := by
        cases headValue : remaining.head with
        | argV => rfl
        | argQ => exact False.elim (head (by rw [headValue]; rfl))
      split at result
      · rename_i rest tail
        cases result
        apply closedEvaluation_app (constantValue_evaluates function _ functionAccepted)
          (constantValue_evaluates argument _ argumentAccepted)
        intro stack; simp [step, headEqual, tail]
      · rename_i tail
        simp only [Option.bind_eq_some_iff] at result
        obtain ⟨evaluated, evaluation, result⟩ := result
        cases evaluated <;> try contradiction
        rename_i constant
        dsimp only at result
        split at result
        · cases result
          apply closedEvaluation_app (constantValue_evaluates function _ functionAccepted)
            (constantValue_evaluates argument _ argumentAccepted)
          intro stack; simp [step, headEqual, tail, evaluation]
        · contradiction
  | Var _ | Error | Lam _ _ | Fix _ _ | Delay _ | Constr _ _ | Case _ _ | Let _ _ =>
    simp [constantValue] at accepted
termination_by sizeOf expression

theorem foldConstant_refines (expression : Expr) :
    MIRCtxRefines expression (foldConstant expression) := by
  unfold foldConstant
  split
  · exact mirCtxRefines_refl _
  · split
    · rename_i constant accepted
      split
      · obtain ⟨term, lowering, closed, evaluates⟩ := constantValue_evaluates expression _ accepted
        apply literal_join_refines expression _ term lowering closed
        intro environment stack
        obtain ⟨fuel, returns⟩ := evaluates environment stack
        exact ⟨fuel, by rw [AdvancedRefinement.advance_eq_steps]; exact returns⟩
      · exact mirCtxRefines_refl _
    · exact mirCtxRefines_refl _

theorem constantFold_refines (expression : Expr) :
    MIRCtxRefines expression (constantFold expression) := by
  apply rewriteBottomUp_refines foldConstant foldConstant_refines
  intro binder body
  simp [foldConstant, Expr.isAtom, constantValue]

theorem constantFoldingSegment_refines (expression : Expr) :
    MIRCtxRefines expression (foldDataConstructors (constantFold expression)) :=
  mirCtxRefines_trans (constantFold_refines expression)
    (foldDataConstructors_refines (constantFold expression))

end Moist.Verified.MIR
