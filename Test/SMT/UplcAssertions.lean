import Moist.SMT.Soundness.ResultQueries
import Test.SMT.SupportedQueries

/-!
# Granular UPLC assertion regressions

These tests exercise the production assertion API, its ordinary UPLC/CEK
semantics, fail-closed builtin coverage, exact script accounting, and the
strong public theorem.  Real solver-process tests live separately in
`UplcAssertionsZ3`.
-/

namespace Test.SMT.UplcAssertions

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

private abbrev tyInt : BuiltinType := .AtomicType .TypeInteger
private abbrev tyBool : BuiltinType := .AtomicType .TypeBool

private def int (value : Int) : Term :=
  .Constant (.Integer value, tyInt)

private def bool (value : Bool) : Term :=
  .Constant (.Bool value, tyBool)

private def app (function argument : Term) : Term :=
  .Apply function argument

private def app2 (builtin : BuiltinFun) (left right : Term) : Term :=
  app (app (.Builtin builtin) left) right

private def forceBuiltin (builtin : BuiltinFun) : Term :=
  .Force (.Builtin builtin)

private def lazyIf (condition thenBranch elseBranch : Term) : Term :=
  .Force <| app (app (app (forceBuiltin .IfThenElse) condition)
    (.Delay thenBranch)) (.Delay elseBranch)

private def runCek : Nat → Moist.CEK.State → Moist.CEK.CekResult
  | _, .halt value => .success value
  | _, .error => .failure
  | 0, _ => .outOfBudget
  | fuel + 1, state => runCek fuel (Moist.CEK.step state)

private def cekBoolTrue (environment : Moist.CEK.CekEnv)
    (term : Term) : Bool :=
  match runCek 1000 (.compute [] environment term) with
  | .success (.VCon (.Bool true)) => true
  | _ => false

private def cekSucceeds (environment : Moist.CEK.CekEnv)
    (term : Term) : Bool :=
  match runCek 1000 (.compute [] environment term) with
  | .success _ => true
  | _ => false

private def cekBoolEq (environment : Moist.CEK.CekEnv)
    (term : Term) (expected : Bool) : Bool :=
  match runCek 1000 (.compute [] environment term) with
  | .success (.VCon (.Bool actual)) => actual == expected
  | _ => false

private def cekIntEq (environment : Moist.CEK.CekEnv)
    (term : Term) (expected : Int) : Bool :=
  match runCek 1000 (.compute [] environment term) with
  | .success (.VCon (.Integer actual)) => actual == expected
  | _ => false

private def cekErrors (environment : Moist.CEK.CekEnv)
    (term : Term) : Bool :=
  match runCek 1000 (.compute [] environment term) with
  | .failure => true
  | _ => false

private def assertionHolds (model : Moist.SMT.Semantics.Model)
    (declarations : List SymDecl) (assertion : UplcAssertion) : Bool :=
  Moist.SMT.Semantics.evalBoolIs model
    (assertion.condition declarations) true

private def assertionsHold (model : Moist.SMT.Semantics.Model)
    (declarations : List SymDecl) (assertions : List UplcAssertion) : Bool :=
  assertions.all (assertionHolds model declarations)

/-! The target and assertion APIs share one dispatcher.  Handcrafted outcome
lists keep these tests independent of `evalSym`, so a target-selection bug
cannot be hidden by evaluator behavior. -/

private def outcomeBool (path : SExpr) (value : Bool) : Outcome :=
  .ok path (.const (.bool (.bool value)))

private def outcomeInt (path : SExpr) (value : Int) : Outcome :=
  .ok path (.const (.integer (.int value)))

private def targetConditionHolds (expectation : UplcAssertionExpectation)
    (outcomes : List Outcome) : Bool :=
  Moist.SMT.Semantics.evalBoolIs Moist.SMT.Semantics.Model.empty
    (Moist.SMT.Compiler.queryCondition expectation outcomes) true

example : targetConditionHolds .succeeds
    [outcomeBool .trueE false] = true := by
  native_decide

example : targetConditionHolds .succeeds
    [.ok .trueE (.lam (.Var 1) [])] = true := by
  native_decide

example : targetConditionHolds .succeeds
    [.error .trueE, .timeout .trueE, outcomeBool .falseE true] = false := by
  native_decide

example : targetConditionHolds (.boolEq false)
    [outcomeBool .trueE false] = true := by
  native_decide

example : targetConditionHolds (.boolEq false)
    [outcomeBool .trueE true, outcomeInt .trueE 0,
      .error .trueE, .timeout .trueE] = false := by
  native_decide

example : targetConditionHolds (.intEq (-7))
    [outcomeInt .trueE (-7)] = true := by
  native_decide

example : targetConditionHolds (.intEq (-7))
    [outcomeInt .trueE 7, outcomeBool .trueE true,
      .error .trueE, .timeout .trueE] = false := by
  native_decide

example : targetConditionHolds .error [.error .trueE] = true := by
  native_decide

example : targetConditionHolds .error
    [.error .falseE, outcomeBool .trueE true, .timeout .trueE] = false := by
  native_decide

example (expectation : UplcAssertionExpectation)
    (outcomes : List Outcome) :
    Moist.SMT.Compiler.queryCondition expectation outcomes =
      expectation.condition outcomes := rfl

example : Moist.SMT.Compiler.QueryKind.boolTrue =
    (UplcAssertionExpectation.boolEq true) := rfl

private def trueAssertion : UplcAssertion :=
  { fuel := 10, term := bool true }

private def falseAssertion : UplcAssertion :=
  { fuel := 10, term := bool false }

private def errorAssertion : UplcAssertion :=
  { fuel := 10, term := .Error }

private def nonBooleanAssertion : UplcAssertion :=
  { fuel := 10, term := int 1 }

private def timeoutAssertion : UplcAssertion :=
  { fuel := 0, term := bool true }

private def outOfRangeAssertion : UplcAssertion :=
  { fuel := 10, term := .Var 1 }

/-! The source-compatible default still requires actual `Bool true`. -/

example : trueAssertion.expectation = .boolEq true := rfl

example : trueAssertion.condition [] =
    okBoolTrueCond (evalSym trueAssertion.fuel [] trueAssertion.term) := rfl

example : assertionHolds Moist.SMT.Semantics.Model.empty [] trueAssertion = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] falseAssertion = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] errorAssertion = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] nonBooleanAssertion = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] timeoutAssertion = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] outOfRangeAssertion = false := by
  native_decide

/-! Explicit expectations distinguish any value, typed exact values, and runtime
error, while fuel timeout is rejected by every expectation.  In particular,
general success includes higher-order CEK values which have no first-order SMT
value encoding. -/

private def succeedsInt : UplcAssertion :=
  UplcAssertion.succeeds 10 (int 7)

private def succeedsFalse : UplcAssertion :=
  UplcAssertion.succeeds 10 (bool false)

private def succeedsLambda : UplcAssertion :=
  UplcAssertion.succeeds 10 (.Lam 0 (.Var 1))

private def succeedsError : UplcAssertion :=
  UplcAssertion.succeeds 10 .Error

private def zeroFuelSuccess : UplcAssertion :=
  UplcAssertion.succeeds 0 (bool true)

private def returnsFalse : UplcAssertion :=
  UplcAssertion.returnsBool 10 false (bool false)

private def returnsFalseFromInteger : UplcAssertion :=
  UplcAssertion.returnsBool 10 false (int 1)

private def returnsSeven : UplcAssertion :=
  UplcAssertion.returnsInt 10 7 (int 7)

private def returnsWrongInteger : UplcAssertion :=
  UplcAssertion.returnsInt 10 8 (int 7)

private def returnsSevenFromBoolean : UplcAssertion :=
  UplcAssertion.returnsInt 10 7 (bool true)

private def expectsError : UplcAssertion :=
  UplcAssertion.errors 10 .Error

private def expectsErrorFromValue : UplcAssertion :=
  UplcAssertion.errors 10 (int 7)

private def zeroFuelError : UplcAssertion :=
  UplcAssertion.errors 0 .Error

example : assertionHolds Moist.SMT.Semantics.Model.empty [] succeedsInt = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] succeedsFalse = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] succeedsLambda = true := by
  native_decide

example : cekSucceeds .nil succeedsLambda.term = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] succeedsError = false := by
  native_decide

example : cekSucceeds .nil zeroFuelSuccess.term = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    zeroFuelSuccess = false := by
  native_decide

#guard succeedsInt.condition [] == (.bool true : SExpr)
#guard succeedsError.condition [] == (.bool false : SExpr)

example : assertionHolds Moist.SMT.Semantics.Model.empty [] returnsFalse = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    returnsFalseFromInteger = false := by
  native_decide

example : cekBoolEq .nil returnsFalse.term false = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] returnsSeven = true := by
  native_decide

#guard returnsFalse.condition [] == (.bool true : SExpr)

example : cekIntEq .nil returnsSeven.term 7 = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    returnsWrongInteger = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    returnsSevenFromBoolean = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] expectsError = true := by
  native_decide

#guard expectsError.condition [] == (.bool true : SExpr)

example : cekErrors .nil expectsError.term = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    expectsErrorFromValue = false := by
  native_decide

/- The underlying CEK term errors, but zero symbolic fuel produces only a
timeout outcome.  Timeout therefore satisfies neither success nor error. -/
example : cekErrors .nil zeroFuelError.term = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty [] zeroFuelError = false := by
  native_decide

/- A caller can refine any successful result with an arbitrary ordinary UPLC
program.  This constructor works for structured values without adding an
unproved generic SMT equality operation. -/
private def constructorZero : Term := .Constr 0 []

private def isConstructorZero : Term :=
  .Lam 0 (.Case (.Var 1) [bool true, bool false])

private def constructorResultSatisfies : UplcAssertion :=
  UplcAssertion.resultSatisfies 30 constructorZero isConstructorZero

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    constructorResultSatisfies = true := by
  native_decide

example : cekBoolTrue .nil constructorResultSatisfies.term = true := by
  native_decide

/-! Source-attached assertions are host metadata around an ordinary UPLC
term. Every metadata combinator preserves exact erasure. Result matching is a
separate `UplcQuery`, so it cannot silently replace the deployable term. -/

private def attachedSource : AssertedTerm :=
  (constructorZero.withAssertion trueAssertion).assertingAll
    [succeedsInt]

private def attachedBinaryPredicate : Term :=
  .Lam 0 (.Lam 0 (bool true))

example : attachedSource.erase = constructorZero := rfl

example : attachedSource.assertions = [trueAssertion, succeedsInt] := rfl

example : (constructorZero.withAssertions
    [trueAssertion, succeedsInt]).erase = constructorZero := rfl

example : (constructorZero.withParameterAssertion
    30 isConstructorZero 1).erase = constructorZero := rfl

example : (constructorZero.withParameterAssertions
    30 attachedBinaryPredicate [1, 2]).erase = constructorZero := rfl

private def attachedResultQuery : UplcQuery :=
  attachedSource.resultSatisfies isConstructorZero

example : attachedSource.erase = constructorZero := rfl

example : attachedResultQuery.target =
    .Apply isConstructorZero constructorZero := rfl

example : attachedResultQuery.source.assertions =
    [trueAssertion, succeedsInt] := rfl

example : attachedResultQuery.expectation = .boolEq true := rfl

example : attachedResultQuery.erase = constructorZero := rfl

private def attachedSuccessQuery : UplcQuery :=
  attachedSource.succeeds

example : attachedSuccessQuery.target = constructorZero := rfl

example : attachedSuccessQuery.expectation = .succeeds := rfl

private def identityFunction : Term :=
  .Lam 0 (.Var 1)

private def attachedApplicationQuery : UplcQuery :=
  (AssertedTerm.ofTerm identityFunction).appliedWith (.intEq 9) [int 9]

example : attachedApplicationQuery.target =
    .Apply identityFunction (int 9) := rfl

example : attachedApplicationQuery.expectation = .intEq 9 := rfl

example : attachedApplicationQuery.erase = identityFunction := rfl

private def attachedApplicationResultQuery : UplcQuery :=
  (AssertedTerm.ofTerm identityFunction).appliedResultSatisfiesWith
    (.intEq 9) [int 9] identityFunction

example : attachedApplicationResultQuery.target =
    .Apply identityFunction (.Apply identityFunction (int 9)) := rfl

example : attachedApplicationResultQuery.expectation = .intEq 9 := rfl

example : attachedApplicationResultQuery.erase = identityFunction := rfl

private def incrementFunction : Term :=
  .Lam 0 (app2 .AddInteger (.Var 1) (int 1))

/- This plan deliberately composes consumer/application/consumer rather than
using only a convenience constructor. Its target remains structurally rooted
at the deployable source, while erasure returns that source exactly. -/
private def composedTargetPlan : UplcQueryTarget :=
  .consumed incrementFunction
    (.applied (.consumed identityFunction .source) [int 9])

private def composedRootedQuery : UplcQuery :=
  { source := (AssertedTerm.ofTerm identityFunction).asserting trueAssertion
    targetPlan := composedTargetPlan
    expectation := .intEq 10 }

example : composedTargetPlan.resolve identityFunction =
    .Apply incrementFunction
      (.Apply (.Apply identityFunction identityFunction) (int 9)) := rfl

example : composedRootedQuery.target =
    .Apply incrementFunction
      (.Apply (.Apply identityFunction identityFunction) (int 9)) := rfl

example : composedRootedQuery.erase = identityFunction := rfl

example : composedRootedQuery.source.assertions = [trueAssertion] := rfl

example : composedRootedQuery.expectation = .intEq 10 := rfl

private def mismatchingIntegerConsumerQuery : UplcQuery :=
  (AssertedTerm.ofTerm (int 7)).resultSatisfiesWith
    (.intEq 8) identityFunction

example : mismatchingIntegerConsumerQuery.target =
    .Apply identityFunction (int 7) := rfl

example : mismatchingIntegerConsumerQuery.expectation = .intEq 8 := rfl

example : cekIntEq .nil mismatchingIntegerConsumerQuery.target 8 = false := by
  native_decide

private def consumerFirstErrorQuery : UplcQuery :=
  (AssertedTerm.ofTerm (int 7)).resultSatisfiesWith .error .Error

example : consumerFirstErrorQuery.target = .Apply .Error (int 7) := rfl

example : cekErrors .nil consumerFirstErrorQuery.target = true := by
  native_decide

private def exactAppliedResultQuery : UplcQuery :=
  (AssertedTerm.ofTerm identityFunction).appliedResultSatisfiesWith
    (.intEq 10) [int 9] incrementFunction

example : exactAppliedResultQuery.target =
    .Apply incrementFunction (.Apply identityFunction (int 9)) := rfl

example : exactAppliedResultQuery.expectation = .intEq 10 := rfl

example : cekIntEq .nil exactAppliedResultQuery.target 10 = true := by
  native_decide

example : exactAppliedResultQuery.erase = identityFunction := rfl

private def firstOfTwoFunction : Term :=
  .Lam 0 (.Lam 0 (.Var 2))

private def declarationBoundQuery : UplcQuery :=
  let declarations := [symInt "contract_x", symInt "contract_y"]
  (AssertedTerm.ofTerm firstOfTwoFunction).appliedToDeclarationsWith
    (.intEq 4) declarations

example : AssertedTerm.declarationArguments
    [symInt "contract_x", symInt "contract_y"] = [.Var 1, .Var 2] := by
  native_decide

example : declarationBoundQuery.target =
    .Apply (.Apply firstOfTwoFunction (.Var 1)) (.Var 2) := rfl

example : declarationBoundQuery.erase = firstOfTwoFunction := rfl

example : cekIntEq
    (.cons (.VCon (.Integer 4)) (.cons (.VCon (.Integer 9)) .nil))
    declarationBoundQuery.target 4 = true := by
  native_decide

/- The source-attached query facade is definitionally the existing checked compiler
on exactly the source fields. -/
example (fuel : Nat) (declarations : List SymDecl) (query : UplcQuery) :
    Moist.SMT.Compiler.compileUplcQuery? fuel declarations query =
      Moist.SMT.Compiler.compileWithAssertions?
        query.expectation fuel declarations query.source.assertions
          query.target := rfl

example (fuel : Nat) (declarations : List SymDecl) (query : UplcQuery) :
    Moist.SMT.Compiler.compileUplcQueryQueries? fuel declarations query =
      Moist.SMT.Compiler.compileAssertionQueries?
        query.expectation fuel declarations query.source.assertions
          query.target := rfl

example (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    Moist.SMT.Compiler.compileAssertedTerm? kind fuel declarations source =
      Moist.SMT.Compiler.compileWithAssertions?
        kind fuel declarations source.assertions source.term := rfl

example (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm)
    (consumer : Term) :
    Moist.SMT.Compiler.compileResultProgramWithAssertions?
        expectation fuel declarations source.assertions source.term consumer =
      Moist.SMT.Compiler.compileWithAssertions?
        expectation fuel declarations source.assertions
          (.Apply consumer source.term) := rfl

/- Multi-parameter and result/input helpers preserve source application order.
The predicate is applied left-to-right to the listed one-based variables. -/
example : (UplcAssertion.onParameters
    40 attachedBinaryPredicate [1, 2]).term =
      .Apply (.Apply attachedBinaryPredicate (.Var 1)) (.Var 2) := rfl

example : (UplcAssertion.onParametersWith 40 (.intEq 7)
    attachedBinaryPredicate [2, 1]).term =
      .Apply (.Apply attachedBinaryPredicate (.Var 2)) (.Var 1) := rfl

example : (UplcAssertion.resultAndParametersSatisfy
    40 constructorZero attachedBinaryPredicate [2, 1]).term =
      .Apply (.Apply (.Apply attachedBinaryPredicate constructorZero)
        (.Var 2)) (.Var 1) := rfl

example : (UplcAssertion.resultAndParametersSatisfyWith
    40 .succeeds constructorZero attachedBinaryPredicate [1, 2]).expectation =
      .succeeds := rfl

example (environment : Moist.CEK.CekEnv) (fuel : Nat) (term : Term) :
    CekAssertionHolds environment (UplcAssertion.succeeds fuel term) =
      (∃ value, CekHaltsValue environment term value) := rfl

example (environment : Moist.CEK.CekEnv) (fuel : Nat) (term : Term)
    (expected : Bool) :
    CekAssertionHolds environment
        (UplcAssertion.returnsBool fuel expected term) =
      CekHaltsValue environment term (.VCon (.Bool expected)) := rfl

example (environment : Moist.CEK.CekEnv) (fuel : Nat) (term : Term)
    (expected : Int) :
    CekAssertionHolds environment
        (UplcAssertion.returnsInt fuel expected term) =
      CekHaltsInteger environment term expected := rfl

example (environment : Moist.CEK.CekEnv) (fuel : Nat) (term : Term) :
    CekAssertionHolds environment (UplcAssertion.errors fuel term) =
      CekHaltsError environment term := rfl

/-! Ground builtins use the same static-folding path as the target. -/

private def foldedAssertion : UplcAssertion :=
  { fuel := 20
    term := app2 .EqualsInteger
      (app2 .AddInteger (int 2) (int 3)) (int 5) }

example : assertionHolds Moist.SMT.Semantics.Model.empty [] foldedAssertion = true := by
  native_decide

#guard foldedAssertion.condition [] == (.bool true : SExpr)

example : cekBoolTrue .nil foldedAssertion.term = true := by
  native_decide

/-! Lazy branches preserve ordinary CEK strictness/laziness. -/

private def unselectedErrorAssertion : UplcAssertion :=
  { fuel := 30, term := lazyIf (bool true) (bool true) .Error }

private def selectedErrorAssertion : UplcAssertion :=
  { fuel := 30, term := lazyIf (bool false) (bool true) .Error }

private def strictArgumentErrorAssertion : UplcAssertion :=
  { fuel := 30, term := app2 .EqualsInteger .Error (int 0) }

private def positiveOrErrorAssertion : UplcAssertion :=
  { fuel := 40
    term := lazyIf (app2 .LessThanInteger (int 0) (.Var 1))
      (bool true) .Error }

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    unselectedErrorAssertion = true := by
  native_decide

example : cekBoolTrue .nil unselectedErrorAssertion.term = true := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    selectedErrorAssertion = false := by
  native_decide

example : assertionHolds Moist.SMT.Semantics.Model.empty []
    strictArgumentErrorAssertion = false := by
  native_decide

/-! Symbolic predicates and parameter ordering. -/

private def x : SymDecl := symInt "assert_x"
private def y : SymDecl := symInt "assert_y"
private def symbolicBool : SymDecl := symBool "assert_bool"

private def intModel (declaration : SymDecl) (value : Int) :
    Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
    declaration.name (.int value)

private def xyModel (xValue yValue : Int) : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind
    (Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
      x.name (.int xValue))
    y.name (.int yValue)

private def boolModel (value : Bool) : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.bind Moist.SMT.Semantics.Model.empty
    symbolicBool.name (.bool value)

private def symbolicFalse : UplcAssertion :=
  UplcAssertion.returnsBool 20 false (.Var 1)

example : assertionHolds (boolModel false) [symbolicBool]
    symbolicFalse = true := by
  native_decide

example : assertionHolds (boolModel true) [symbolicBool]
    symbolicFalse = false := by
  native_decide

private def symbolicFalseQuery : UplcQuery :=
  (AssertedTerm.ofTerm (.Var 1)).returnsBool false

example : symbolicFalseQuery.expectation = .boolEq false := rfl

example : cekBoolEq (.cons (.VCon (.Bool false)) .nil)
    symbolicFalseQuery.target false = true := by
  native_decide

example : cekBoolEq (.cons (.VCon (.Bool true)) .nil)
    symbolicFalseQuery.target false = false := by
  native_decide

private def positivePredicate : Term :=
  .Lam 0 (app2 .LessThanInteger (int 0) (.Var 1))

private def positiveX : UplcAssertion :=
  UplcAssertion.onParameter 30 positivePredicate 1

example : (UplcAssertion.onParameterChecked?
    [x] 30 positivePredicate 1).isSome = true := by
  native_decide

example : (UplcAssertion.onParameterChecked?
    [x] 30 positivePredicate 0).isSome = false := by
  native_decide

example : (UplcAssertion.onParameterChecked?
    [x] 30 positivePredicate 2).isSome = false := by
  native_decide

example : (UplcAssertion.onParametersChecked?
    [x, y] 30 attachedBinaryPredicate [1, 2]).isSome = true := by
  native_decide

example : (UplcAssertion.onParametersChecked?
    [x, y] 30 attachedBinaryPredicate [1, 3]).isSome = false := by
  native_decide

example : assertionHolds (intModel x 4) [x] positiveX = true := by
  native_decide

example : assertionHolds (intModel x (-1)) [x] positiveX = false := by
  native_decide

private def symbolicSeven : UplcAssertion :=
  UplcAssertion.returnsInt 20 7 (.Var 1)

example : assertionHolds (intModel x 7) [x] symbolicSeven = true := by
  native_decide

example : assertionHolds (intModel x 8) [x] symbolicSeven = false := by
  native_decide

private def mixedExpectations : List UplcAssertion :=
  [ UplcAssertion.succeeds 20 (.Var 1)
  , UplcAssertion.returnsInt 20 7 (.Var 1)
  , UplcAssertion.returnsBool 20 false (bool false)
  , UplcAssertion.errors 20 .Error
  ]

example : assertionsHold (intModel x 7) [x] mixedExpectations = true := by
  native_decide

example : assertionsHold (intModel x 8) [x] mixedExpectations = false := by
  native_decide

example : assertionHolds (intModel x 4) [x]
    positiveOrErrorAssertion = true := by
  native_decide

example : assertionHolds (intModel x (-1)) [x]
    positiveOrErrorAssertion = false := by
  native_decide

private def xLessThanY : UplcAssertion :=
  { fuel := 30, term := app2 .LessThanInteger (.Var 1) (.Var 2) }

private def yLessThanX : UplcAssertion :=
  { fuel := 30, term := app2 .LessThanInteger (.Var 2) (.Var 1) }

private def binaryLessPredicate : Term :=
  .Lam 0 (.Lam 0 (app2 .LessThanInteger (.Var 2) (.Var 1)))

private def appliedXLessThanY : UplcAssertion :=
  UplcAssertion.applied 40 binaryLessPredicate [.Var 1, .Var 2]

example : assertionHolds (xyModel 2 5) [x, y] xLessThanY = true := by
  native_decide

example : assertionHolds (xyModel 2 5) [x, y] yLessThanX = false := by
  native_decide

example : assertionHolds (xyModel 2 5) [x, y] appliedXLessThanY = true := by
  native_decide

private def xyEnvironment : Moist.CEK.CekEnv :=
  .cons (.VCon (.Integer 2))
    (.cons (.VCon (.Integer 5)) .nil)

example : cekBoolTrue xyEnvironment xLessThanY.term = true := by
  native_decide

/- Inside the lambda, `Var 1` is its argument and `Var 2` remains the first
query declaration.  Applying it to the second declaration must still mean
`x < y`. -/
private def capturedRelation : UplcAssertion :=
  { fuel := 30
    term := app
      (.Lam 0 (app2 .LessThanInteger (.Var 2) (.Var 1)))
      (.Var 2) }

example : assertionHolds (xyModel 2 5) [x, y] capturedRelation = true := by
  native_decide

example : assertionHolds (xyModel 5 2) [x, y] capturedRelation = false := by
  native_decide

example : cekBoolTrue xyEnvironment capturedRelation.term = true := by
  native_decide

/-! Production gates preserve exactly the existing supported-builtin policy
inside assertion terms as well as target terms. -/

private def assertionUsing (builtin : BuiltinFun) : UplcAssertion :=
  { fuel := 1, term := .Builtin builtin }

private def allSupportedAssertionsAccepted : Bool :=
  Test.SMT.SupportedQueries.certifiedBuiltins.all fun builtin =>
    (Moist.SMT.Compiler.compileBoolTrueWithAssertions?
      3 [] [assertionUsing builtin] (bool true)).isSome

private def allUnsupportedAssertionsRejected : Bool :=
  Test.SMT.SupportedQueries.unsupportedBuiltins.all fun builtin =>
    !(Moist.SMT.Compiler.compileBoolTrueWithAssertions?
      3 [] [assertionUsing builtin] (bool true)).isSome

example : allSupportedAssertionsAccepted = true := by
  native_decide

example : allUnsupportedAssertionsRejected = true := by
  native_decide

example :
    (Moist.SMT.Compiler.compileBoolTrueWithAssertions?
      3 [] [{ fuel := 3, term := .Delay (.Builtin .Sha2_256) }]
      (bool true)).isSome = false := by
  native_decide

example :
    (Moist.SMT.Compiler.compileAssertionsSatisfiable? []
      [trueAssertion, assertionUsing .Sha2_256, foldedAssertion]).isSome =
      false := by
  native_decide

example :
    (Moist.SMT.Compiler.compileBoolTrueWithAssertions?
      3 [] [trueAssertion] (.Builtin .SerializeData)).isSome = false := by
  native_decide

/-! Empty assertion lists preserve the legacy low-level scripts exactly. -/

example : scriptForBoolTrueWithAssertions 20 [] [] (bool true) =
    scriptForBoolTrue 20 [] (bool true) := rfl

example : scriptForIntEqWithAssertions 20 [] [] (int 7) (.int 7) =
    scriptForIntEq 20 [] (int 7) (.int 7) := rfl

example : scriptForErrorWithAssertions 20 [] [] .Error =
    scriptForError 20 [] .Error := rfl

/- The shared two-query constructor remains definitionally identical to every
canonical standalone script while evaluating assertion conditions once. -/
example (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) :
    (Moist.SMT.Compiler.scriptsForWithAssertions
      kind fuel declarations assertions term).satisfiability =
      scriptForAssertionsSatisfiable declarations assertions := by
  rfl

example (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    (Moist.SMT.Compiler.scriptsForWithAssertions
      .boolTrue fuel declarations assertions term).target =
      scriptForBoolTrueWithAssertions fuel declarations assertions term := by
  rfl

example (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) (expected : Int) :
    (Moist.SMT.Compiler.scriptsForWithAssertions
      (.intEq expected) fuel declarations assertions term).target =
      scriptForIntEqWithAssertions fuel declarations assertions term
        (.int expected) := by
  rfl

example (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    (Moist.SMT.Compiler.scriptsForWithAssertions
      .error fuel declarations assertions term).target =
      scriptForErrorWithAssertions fuel declarations assertions term := by
  rfl

/- Exact accounting includes every source predicate before the target and
then explicitly passes through solver-oriented grouping. -/
example (assertions : List UplcAssertion) :
    (scriptForBoolTrueWithAssertions 20 [x] assertions (bool true)).assertions =
      [x].flatMap SymDecl.assumptions ++ groupedAssertions
        (uplcAssertionConditions [x] assertions ++
          [okBoolTrueCond (evalSym 20 (envOf [x]) (bool true))]) := by
  exact scriptForBoolTrueWithAssertions_assertions _ _ _ _

/- A nonconstant 100-predicate context remains one solver assertion command.
Unlike a replicated ground `true`, every source condition here depends on the
symbolic parameter, so this guards the intended large-context representation. -/
private def symbolicLowerBounds : List UplcAssertion :=
  (List.range 100).map fun bound =>
    { fuel := 30
      term := app2 .LessThanInteger (int (Int.ofNat bound)) (.Var 1) }

example : symbolicLowerBounds.length = 100 := by
  native_decide

example : (scriptForAssertionsSatisfiable [x]
    symbolicLowerBounds).assertions.length = 1 := by
  native_decide

/-! Every generalized target expectation and the assertion-only query use the
fully checked production API. -/

example : (Moist.SMT.Compiler.compileSucceeds?
    20 [] (.Lam 0 (.Var 1))).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileBoolEq?
    20 [] (bool false) false).isSome = true := by
  native_decide

example : Moist.SMT.Compiler.compileSucceeds?
    20 [] (.Lam 0 (.Var 1)) =
      Moist.SMT.Compiler.compile? .succeeds
        20 [] (.Lam 0 (.Var 1)) := rfl

example : Moist.SMT.Compiler.compileBoolEq?
    20 [] (bool false) false =
      Moist.SMT.Compiler.compile? (.boolEq false)
        20 [] (bool false) := rfl

example : (AssertedQuery.compileBoolTrue?
    20 [] [trueAssertion] (bool true)).isSome = true := by
  native_decide

example : (AssertedQuery.compileSucceeds?
    20 [] [trueAssertion] (.Lam 0 (.Var 1))).isSome = true := by
  native_decide

example : (AssertedQuery.compileBoolEq?
    20 [] [trueAssertion] (bool false) false).isSome = true := by
  native_decide

example : (AssertedQuery.compileUplcQuery?
    50 [] attachedResultQuery).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileUplcQuery?
    50 [] attachedResultQuery).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileUplcQuery?
    50 [] ((Term.Builtin .Sha2_256).withAssertion trueAssertion).succeeds).isSome =
      false := by
  native_decide

private def safeIgnoringConsumer : Term :=
  .Lam 0 (bool true)

private def unsupportedSourceBehindSafeConsumer : UplcQuery :=
  (AssertedTerm.ofTerm (.Builtin .Sha2_256)).resultSatisfies
    safeIgnoringConsumer

/- Even a consumer whose body is statically `true` cannot conceal an
unsupported source. The source-rooted target remains subject to the same
fail-closed builtin gate as direct queries. -/
example : unsupportedSourceBehindSafeConsumer.target =
    .Apply safeIgnoringConsumer (.Builtin .Sha2_256) := rfl

example : unsupportedSourceBehindSafeConsumer.erase =
    .Builtin .Sha2_256 := rfl

example : Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness
    unsupportedSourceBehindSafeConsumer.target = true := by
  native_decide

example : (Moist.SMT.Compiler.compileUplcQuery?
    50 [] unsupportedSourceBehindSafeConsumer).isSome = false := by
  native_decide

example : (AssertedQuery.compileIntEq?
    20 [] [trueAssertion] (int 7) 7).isSome = true := by
  native_decide

example : (AssertedQuery.compileError?
    20 [] [trueAssertion] .Error).isSome = true := by
  native_decide

example : (AssertionSatisfiabilityQuery.compile?
    [] [trueAssertion, foldedAssertion]).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileErrorAssertionQueries?
    20 [] [trueAssertion] .Error).isSome = true := by
  native_decide

example : (AssertionQueryBundle.compileError?
    20 [] [trueAssertion] .Error).isSome = true := by
  native_decide

example : (Moist.SMT.Compiler.compileBoolTrueAssertionQueries?
    20 [] [trueAssertion, assertionUsing .Sha2_256]
      (bool true)).isSome = false := by
  native_decide

/- Proof-carrying compilation erases to the exact proof-free script. -/
example (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) :
    (AssertedQuery.compile? kind fuel declarations assertions term).map
        (·.script) =
      Moist.SMT.Compiler.compileWithAssertions?
        kind fuel declarations assertions term := by
  exact AssertedQuery.compile_map_script _ _ _ _ _

example (fuel : Nat) (declarations : List SymDecl) (query : UplcQuery) :
    (AssertedQuery.compileUplcQuery? fuel declarations query).map
        (·.script) =
      Moist.SMT.Compiler.compileUplcQuery?
        fuel declarations query := by
  exact AssertedQuery.compileUplcQuery_map_script _ _ _

example (fuel : Nat) (declarations : List SymDecl) (query : UplcQuery) :
    (AssertionQueryBundle.compileUplcQuery?
        fuel declarations query).map (·.scripts) =
      Moist.SMT.Compiler.compileUplcQueryQueries?
        fuel declarations query := by
  exact AssertionQueryBundle.compileUplcQuery_map_scripts _ _ _

example (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (ResultQuery.compile? kind fuel declarations term).map (·.script) =
      Moist.SMT.Compiler.compile? kind fuel declarations term := by
  exact ResultQuery.compile_map_script _ _ _ _

example (declarations : List SymDecl)
    (assertions : List UplcAssertion) :
    (AssertionSatisfiabilityQuery.compile? declarations assertions).map
        (·.script) =
      Moist.SMT.Compiler.compileAssertionsSatisfiable?
        declarations assertions := by
  exact AssertionSatisfiabilityQuery.compile_map_script _ _

example (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) :
    (AssertionQueryBundle.compile?
      kind fuel declarations assertions term).map (·.scripts) =
      Moist.SMT.Compiler.compileAssertionQueries?
        kind fuel declarations assertions term := by
  exact AssertionQueryBundle.compile_map_scripts _ _ _ _ _

/- The public theorem is genuinely stronger than target-only soundness: the
same `cekEnv` occurs in both conjuncts. -/
example (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekAssertionsHold (AssertedQuery.cekEnv query z3) query.assertions ∧
      CekQueryResult kind (AssertedQuery.cekEnv query z3)
        query.program.term := by
  exact AssertedQuery.sound query z3

example {fuel : Nat} {declarations : List SymDecl} {query : UplcQuery}
    {certified : AssertedQuery query.expectation}
    (hcompile : AssertedQuery.compileUplcQuery?
      fuel declarations query = some certified)
    (z3 : CertifiedZ3Model certified.inputs certified.script) :
    CekAssertionsHold (AssertedQuery.cekEnv certified z3)
        query.source.assertions ∧
      CekExpectationHolds query.expectation
        (AssertedQuery.cekEnv certified z3) query.target := by
  exact AssertedQuery.compileUplcQuery_sound hcompile z3

example (query : ResultQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekQueryResult kind (ResultQuery.cekEnv query z3)
      query.program.term := by
  exact ResultQuery.sound query z3

example (query : AssertionSatisfiabilityQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekAssertionsHold
      (AssertionSatisfiabilityQuery.cekEnv query z3) query.assertions := by
  exact AssertionSatisfiabilityQuery.sound query z3

example (bundle : AssertionQueryBundle kind)
    (z3 : CertifiedZ3Model bundle.inputs bundle.scripts.target) :
    CekAssertionsHold
        (AssertionQueryBundle.targetCekEnv bundle z3) bundle.assertions ∧
      CekQueryResult kind
        (AssertionQueryBundle.targetCekEnv bundle z3)
        bundle.program.term := by
  exact AssertionQueryBundle.target_sound bundle z3

example (bundle : AssertionQueryBundle kind)
    (z3 : CertifiedZ3Model bundle.inputs bundle.scripts.satisfiability) :
    CekAssertionsHold
      (AssertionQueryBundle.satisfiabilityCekEnv bundle z3)
      bundle.assertions := by
  exact AssertionQueryBundle.satisfiability_sound bundle z3

end Test.SMT.UplcAssertions
