import Moist.SMT.Soundness.SolverBoundary

namespace Test.SMT.SolverBoundary

open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

/-! The production input grammar permits a symbolic constructor whose field
is itself a direct symbolic `Val`.  These regressions exercise the successful
composition and the two validity failures that used to be hidden behind a
caller-supplied final environment decoder. -/

private def directValDeclaration : SymDecl :=
  symVal "nested_value"

private def constructorDeclaration : SymDecl :=
  symConstr "outer_tag" [.dyn (.sym directValDeclaration.name)]

private def composedDeclarations : List SymDecl :=
  [constructorDeclaration, directValDeclaration]

private def positiveModel : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind
    (Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
      constructorDeclaration.name (.int 2))
    directValDeclaration.name (.val (.constr 4 [.int 7]))

private def negativeTagModel : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind
    (Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
      constructorDeclaration.name (.int (-1)))
    directValDeclaration.name (.val (.constr 4 [.int 7]))

private def invalidValModel : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind
    (Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
      constructorDeclaration.name (.int 2))
    directValDeclaration.name (.val (.constr (-1) []))

private def assumptionsHold (model : Moist.SMT.Semantics.Model) : Bool :=
  (composedDeclarations.flatMap SymDecl.assumptions).all fun expression =>
    Moist.SMT.Semantics.evalBoolIs model expression true

example : (SupportedDeclarations.check composedDeclarations).isSome = true := by
  native_decide

example :
    SExpr.ge (.sym constructorDeclaration.name) (.int 0) ∈
      constructorDeclaration.assumptions := by
  apply SymDecl.constrTagNonnegative_mem constructorDeclaration
  · exact symDeclInputSafe_checkedWellFormed
      (declarations := composedDeclarations) (by native_decide)
  · rfl
  · rfl
  · rfl

example :
    (.app "val_valid" [.sym directValDeclaration.name] : SExpr) ∈
      directValDeclaration.assumptions := by
  apply SymDecl.valValid_mem_of_sort directValDeclaration
  · exact symDeclInputSafe_checkedWellFormed
      (declarations := composedDeclarations) (by native_decide)
  · rfl

example : (scriptWith composedDeclarations []).assertions =
    composedDeclarations.flatMap SymDecl.assumptions := by
  simpa using scriptWith_assertions composedDeclarations []

example : assumptionsHold positiveModel = true := by
  native_decide

example :
    (symEnvToCek? positiveModel (envOf composedDeclarations)).isSome = true := by
  native_decide

/-- A concrete model bridge supplies only the two declared atoms.  Composite
expression evaluation is not a field of this certificate. -/
private theorem positiveBridge :
    SolverInputModel composedDeclarations positiveModel := by
  constructor
  intro declaration hdeclaration
  simp [composedDeclarations] at hdeclaration
  rcases hdeclaration with rfl | rfl
  · refine ⟨.int 2, ?_, .intVal 2⟩
    rfl
  · refine ⟨.val (.constr 4 [.int 7]), ?_,
      .valVal (.constr 4 [.int 7])⟩
    rfl

private def wrongSortDeclaration : SymDecl :=
  symInt "wrong_sort"

private def wrongSortModel : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
    wrongSortDeclaration.name (.bool true)

/-- A model assigning the wrong runtime sort to a declared atom cannot satisfy
the only external bridge premise. -/
example : ¬ SolverInputModel [wrongSortDeclaration] wrongSortModel := by
  intro bridge
  obtain ⟨value, hvalue, hsort⟩ :=
    bridge.declaredSymbolValue wrongSortDeclaration (by simp)
  simp [wrongSortModel, Moist.SMT.Semantics.Model.bind] at hvalue
  subst value
  cases hsort

/-- The internal lifting theorem handles a nested tester, arithmetic
application, conditional, and declared symbols without any composite bridge
premise. -/
example : ∃ value,
    Moist.SMT.Semantics.eval positiveModel
      (.ite
        (.app "(_ is VConstr)" [.sym directValDeclaration.name])
        (.app "+" [.sym constructorDeclaration.name, .int 5])
        (.int 0)) = some value ∧
      SValHasSort value .int := by
  apply positiveBridge.expressionEvaluates
  · native_decide
  · native_decide

/-- With only declared-symbol typing supplied externally, the checked input
facts and the exact generated declaration assertions derive the complete CEK
environment in the kernel. -/
example :
    ∃ environment,
      symEnvToCek? positiveModel (envOf composedDeclarations) =
        some environment := by
  apply declarationsInputSafe_decodes positiveBridge
  · native_decide
  · native_decide
  · intro declaration hdeclaration expression hexpression
    have hall :
        (composedDeclarations.flatMap SymDecl.assumptions).all
          (fun candidate =>
            Moist.SMT.Semantics.evalBoolIs positiveModel candidate true) =
          true := by
      native_decide
    apply List.all_eq_true.mp hall expression
    simp only [List.mem_flatMap]
    exact ⟨declaration, hdeclaration, hexpression⟩

example : assumptionsHold negativeTagModel = false := by
  native_decide

example :
    (symEnvToCek? negativeTagModel (envOf composedDeclarations)).isSome =
      false := by
  native_decide

example : assumptionsHold invalidValModel = false := by
  native_decide

example :
    (symEnvToCek? invalidValModel (envOf composedDeclarations)).isSome =
      false := by
  native_decide

end Test.SMT.SolverBoundary
