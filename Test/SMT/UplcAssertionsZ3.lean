import Moist.SMT.Soundness.Assertions
import Moist.SMT.Compiler.Operational

/-!
# Real-Z3 differential tests for UPLC assertions

Every script is produced through the fully checked proof-free production API.
Each expected solver status is paired with an independent CEK or executable
semantic oracle.  Both reference and DAG renderings are submitted to Z3.
-/

namespace Test.SMT.UplcAssertionsZ3

set_option maxRecDepth 10000

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC

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

private def lazyIf (condition thenBranch elseBranch : Term) : Term :=
  .Force <| app
    (app (app (.Force (.Builtin .IfThenElse)) condition)
      (.Delay thenBranch))
    (.Delay elseBranch)

private def runCek : Nat → Moist.CEK.State → Moist.CEK.CekResult
  | _, .halt value => .success value
  | _, .error => .failure
  | 0, _ => .outOfBudget
  | fuel + 1, state => runCek fuel (Moist.CEK.step state)

private def cekBoolTrue (environment : Moist.CEK.CekEnv)
    (term : Term) : Bool :=
  match runCek 2000 (.compute [] environment term) with
  | .success (.VCon (.Bool true)) => true
  | _ => false

private def cekSucceeds (environment : Moist.CEK.CekEnv)
    (term : Term) : Bool :=
  match runCek 2000 (.compute [] environment term) with
  | .success _ => true
  | _ => false

private def cekBool (environment : Moist.CEK.CekEnv)
    (term : Term) (expected : Bool) : Bool :=
  match runCek 2000 (.compute [] environment term) with
  | .success (.VCon (.Bool actual)) => actual == expected
  | _ => false

private def cekInteger (environment : Moist.CEK.CekEnv)
    (term : Term) (expected : Int) : Bool :=
  match runCek 2000 (.compute [] environment term) with
  | .success (.VCon (.Integer actual)) => actual == expected
  | _ => false

private def cekError (environment : Moist.CEK.CekEnv)
    (term : Term) : Bool :=
  match runCek 2000 (.compute [] environment term) with
  | .failure => true
  | _ => false

private def trueAssertion : UplcAssertion :=
  { fuel := 20, term := bool true }

private def falseAssertion : UplcAssertion :=
  { fuel := 20, term := bool false }

private def errorAssertion : UplcAssertion :=
  { fuel := 20, term := .Error }

private def nonBooleanAssertion : UplcAssertion :=
  { fuel := 20, term := int 1 }

private def timeoutAssertion : UplcAssertion :=
  { fuel := 0, term := bool true }

private def succeedsInt : UplcAssertion :=
  UplcAssertion.succeeds 20 (int 7)

private def succeedsFalse : UplcAssertion :=
  UplcAssertion.succeeds 20 (bool false)

private def succeedsLambda : UplcAssertion :=
  UplcAssertion.succeeds 20 (.Lam 0 (.Var 1))

private def succeedsError : UplcAssertion :=
  UplcAssertion.succeeds 20 .Error

private def zeroFuelSuccess : UplcAssertion :=
  UplcAssertion.succeeds 0 (bool true)

private def returnsFalse : UplcAssertion :=
  UplcAssertion.returnsBool 20 false (bool false)

private def returnsFalseFromTrue : UplcAssertion :=
  UplcAssertion.returnsBool 20 false (bool true)

private def returnsFalseFromInteger : UplcAssertion :=
  UplcAssertion.returnsBool 20 false (int 1)

private def returnsSeven : UplcAssertion :=
  UplcAssertion.returnsInt 20 7 (int 7)

private def returnsEightFromSeven : UplcAssertion :=
  UplcAssertion.returnsInt 20 8 (int 7)

private def returnsSevenFromBoolean : UplcAssertion :=
  UplcAssertion.returnsInt 20 7 (bool true)

private def expectsError : UplcAssertion :=
  UplcAssertion.errors 20 .Error

private def expectsErrorFromValue : UplcAssertion :=
  UplcAssertion.errors 20 (int 7)

private def zeroFuelError : UplcAssertion :=
  UplcAssertion.errors 0 .Error

private def constructorResultSatisfies : UplcAssertion :=
  UplcAssertion.resultSatisfies 40 (.Constr 0 [])
    (.Lam 0 (.Case (.Var 1) [bool true, bool false]))

private def structuredSeven : Term :=
  .Constr 0 [int 7]

private def structuredEight : Term :=
  .Constr 0 [int 8]

private def constructorFieldIsSeven : Term :=
  .Lam 0 <| .Case (.Var 1)
    [ .Lam 0 (app2 .EqualsInteger (.Var 1) (int 7))
    , bool false
    ]

private def identity : Term :=
  .Lam 0 (.Var 1)

private def increment : Term :=
  .Lam 0 (app2 .AddInteger (.Var 1) (int 1))

private def exactAppliedResultQuery : UplcQuery :=
  (AssertedTerm.ofTerm identity).appliedResultSatisfiesWith
    (.intEq 10) [int 9] increment

private def mismatchingIntegerConsumerQuery : UplcQuery :=
  (AssertedTerm.ofTerm (int 7)).resultSatisfiesWith
    (.intEq 8) identity

private def composedRootedQuery : UplcQuery :=
  { source := (AssertedTerm.ofTerm identity).asserting trueAssertion
    targetPlan := .consumed increment
      (.applied (.consumed identity .source) [int 9])
    expectation := .intEq 10 }

private def foldedAssertion : UplcAssertion :=
  { fuel := 30
    term := app2 .EqualsInteger
      (app2 .AddInteger (int 2) (int 3)) (int 5) }

private def unselectedErrorAssertion : UplcAssertion :=
  { fuel := 40, term := lazyIf (bool true) (bool true) .Error }

private def selectedErrorAssertion : UplcAssertion :=
  { fuel := 40, term := lazyIf (bool false) (bool true) .Error }

private def fixedInt (name : String) (value : Int) : SymDecl :=
  let declaration := symInt name
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.int value)]

private def fixedBool (name : String) (value : Bool) : SymDecl :=
  let declaration := symBool name
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.bool value)]

private def x4 : SymDecl := fixedInt "assert_z3_x4" 4
private def xNeg : SymDecl := fixedInt "assert_z3_xneg" (-1)
private def x2 : SymDecl := fixedInt "assert_z3_x" 2
private def y5 : SymDecl := fixedInt "assert_z3_y" 5
private def x5 : SymDecl := fixedInt "assert_z3_x5" 5
private def y2 : SymDecl := fixedInt "assert_z3_y2" 2
private def x7 : SymDecl := fixedInt "assert_z3_x7" 7
private def x8 : SymDecl := fixedInt "assert_z3_x8" 8
private def freeX : SymDecl := symInt "assert_z3_free_x"
private def freeDivisor : SymDecl := symInt "assert_z3_free_divisor"
private def boolFalse : SymDecl :=
  fixedBool "assert_z3_bool_false" false
private def boolTrue : SymDecl :=
  fixedBool "assert_z3_bool_true" true

private def positivePredicate : Term :=
  .Lam 0 (app2 .LessThanInteger (int 0) (.Var 1))

private def positiveParameter : UplcAssertion :=
  UplcAssertion.onParameter 40 positivePredicate 1

private def positiveOrError : UplcAssertion :=
  { fuel := 50
    term := lazyIf (app2 .LessThanInteger (int 0) (.Var 1))
      (bool true) .Error }

private def yLessThanX : UplcAssertion :=
  { fuel := 40, term := app2 .LessThanInteger (.Var 2) (.Var 1) }

private def binaryLessPredicate : Term :=
  .Lam 0 (.Lam 0 (app2 .LessThanInteger (.Var 2) (.Var 1)))

private def appliedXLessThanY : UplcAssertion :=
  UplcAssertion.applied 50 binaryLessPredicate [.Var 1, .Var 2]

private def capturedRelation : UplcAssertion :=
  { fuel := 40
    term := app
      (.Lam 0 (app2 .LessThanInteger (.Var 2) (.Var 1)))
      (.Var 2) }

private def notZeroDivisor : UplcAssertion :=
  { fuel := 50
    term := lazyIf (app2 .EqualsInteger (.Var 1) (int 0))
      (bool false) (bool true) }

private def divideByParameter : Term :=
  app2 .DivideInteger (int 10) (.Var 1)

private def fixedConstructorValue (name : String) (tag : Int) : SymDecl :=
  let declaration := symVal name
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name)
      (.app "VConstr" [.int tag, .app "VNil" []])]

private def constructor0 : SymDecl :=
  fixedConstructorValue "assert_z3_constructor0" 0

private def constructor1 : SymDecl :=
  fixedConstructorValue "assert_z3_constructor1" 1

private def constructorIsZero : UplcAssertion :=
  { fuel := 40, term := .Case (.Var 1) [bool true, bool false] }

private def symbolicSeven : UplcAssertion :=
  UplcAssertion.returnsInt 30 7 (.Var 1)

private def mixedExpectations : List UplcAssertion :=
  [ UplcAssertion.succeeds 30 (.Var 1)
  , UplcAssertion.returnsInt 30 7 (.Var 1)
  , UplcAssertion.returnsBool 30 false (bool false)
  , UplcAssertion.errors 20 .Error
  ]

private def integerEnvironment (value : Int) : Moist.CEK.CekEnv :=
  .cons (.VCon (.Integer value)) .nil

private def booleanEnvironment (value : Bool) : Moist.CEK.CekEnv :=
  .cons (.VCon (.Bool value)) .nil

private def xyEnvironment : Moist.CEK.CekEnv :=
  .cons (.VCon (.Integer 2))
    (.cons (.VCon (.Integer 5)) .nil)

private def yxEnvironment : Moist.CEK.CekEnv :=
  .cons (.VCon (.Integer 5))
    (.cons (.VCon (.Integer 2)) .nil)

private def constructorEnvironment (tag : Nat) : Moist.CEK.CekEnv :=
  .cons (.VConstr tag []) .nil

private def compileAssertions (name : String) (declarations : List SymDecl)
    (assertions : List UplcAssertion) : IO Script :=
  match Moist.SMT.Compiler.compileAssertionsSatisfiable?
      declarations assertions with
  | some script => pure script
  | none => throw <| IO.userError s!"{name}: assertion query was rejected"

private def compileBool (name : String) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) : IO Script :=
  match Moist.SMT.Compiler.compileBoolTrueWithAssertions?
      50 declarations assertions term with
  | some script => pure script
  | none => throw <| IO.userError s!"{name}: Boolean query was rejected"

private def compileInt (name : String) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term)
    (expected : Int) : IO Script :=
  match Moist.SMT.Compiler.compileIntEqWithAssertions?
      50 declarations assertions term expected with
  | some script => pure script
  | none => throw <| IO.userError s!"{name}: integer query was rejected"

private def compileError (name : String) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) : IO Script :=
  match Moist.SMT.Compiler.compileErrorWithAssertions?
      50 declarations assertions term with
  | some script => pure script
  | none => throw <| IO.userError s!"{name}: error query was rejected"

private def compileQuery (name : String) (fuel : Nat)
    (declarations : List SymDecl) (query : UplcQuery) : IO Script :=
  match Moist.SMT.Compiler.compileUplcQuery? fuel declarations query with
  | some script => pure script
  | none => throw <| IO.userError s!"{name}: UPLC query was rejected"

private def compileErrorBundle (name : String)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : IO Moist.SMT.Compiler.AssertionQueryScripts :=
  match Moist.SMT.Compiler.compileErrorAssertionQueries?
      50 declarations assertions term with
  | some scripts => pure scripts
  | none => throw <| IO.userError
      s!"{name}: coupled assertion/error queries were rejected"

private def statusOnly (name renderer expected text : String) : IO Unit := do
  IO.FS.withTempFile fun handle path => do
    handle.putStr text
    handle.flush
    let result ← IO.Process.output
      { cmd := "z3", args := #["-T:30", "-smt2", path.toString] }
    let status := (result.stdout.splitOn "\n").head?.getD ""
    unless result.exitCode == 0 && result.stderr.isEmpty &&
        (result.stdout.splitOn "(error").length == 1 && status == expected do
      throw <| IO.userError
        s!"{name}/{renderer}: expected {expected}, got:\n{result.stdout}{result.stderr}"

private def withoutModelRequest (name : String) (script : Script) : IO Script :=
  match script.commands.reverse with
  | .getModel :: reversed => pure ⟨reversed.reverse⟩
  | _ => throw <| IO.userError
      s!"{name}: production script no longer ends with get-model"

private unsafe def check (name expected : String) (oracle : Bool)
    (script : Script) : IO Unit := do
  unless oracle do
    throw <| IO.userError s!"{name}: independent CEK/semantic oracle failed"
  -- SAT cases exercise the exact production suffix, including `get-model`.
  -- UNSAT has no model, so omit only that final request to keep Z3's expected
  -- "model is not available" diagnostic from obscuring the status check.
  let solverScript ←
    if expected == "sat" then pure script else withoutModelRequest name script
  statusOnly name "reference" expected solverScript.render
  statusOnly name "dag" expected solverScript.renderDag

private def timeoutConditionIsFalse : Bool :=
  Moist.SMT.Semantics.evalBoolIs Moist.SMT.Semantics.Model.empty
    (timeoutAssertion.condition []) true == false

private def zeroFuelErrorConditionIsFalse : Bool :=
  Moist.SMT.Semantics.evalBoolIs Moist.SMT.Semantics.Model.empty
    (zeroFuelError.condition []) true == false

private def zeroFuelSuccessConditionIsFalse : Bool :=
  Moist.SMT.Semantics.evalBoolIs Moist.SMT.Semantics.Model.empty
    (zeroFuelSuccess.condition []) true == false

unsafe def main : IO Unit := do
  check "assertion-true" "sat"
    (cekBoolTrue .nil trueAssertion.term)
    (← compileAssertions "assertion-true" [] [trueAssertion])
  check "assertion-false" "unsat"
    (!cekBoolTrue .nil falseAssertion.term)
    (← compileAssertions "assertion-false" [] [falseAssertion])
  check "assertion-error" "unsat"
    (cekError .nil errorAssertion.term)
    (← compileAssertions "assertion-error" [] [errorAssertion])
  check "assertion-non-bool" "unsat"
    (!cekBoolTrue .nil nonBooleanAssertion.term)
    (← compileAssertions "assertion-non-bool" [] [nonBooleanAssertion])
  -- Fuel exhaustion is deliberately one-way incomplete: CEK eventually
  -- returns true, while this zero-fuel assertion cannot certify that fact.
  check "assertion-timeout" "unsat"
    (cekBoolTrue .nil timeoutAssertion.term && timeoutConditionIsFalse)
    (← compileAssertions "assertion-timeout" [] [timeoutAssertion])
  check "assertion-succeeds-int" "sat"
    (cekSucceeds .nil succeedsInt.term)
    (← compileAssertions "assertion-succeeds-int" [] [succeedsInt])
  check "assertion-succeeds-false" "sat"
    (cekSucceeds .nil succeedsFalse.term)
    (← compileAssertions "assertion-succeeds-false" [] [succeedsFalse])
  -- This value is intentionally higher-order and has no first-order SMT
  -- equality encoding; general success must still certify the CEK halt.
  check "assertion-succeeds-lambda" "sat"
    (cekSucceeds .nil succeedsLambda.term)
    (← compileAssertions "assertion-succeeds-lambda" [] [succeedsLambda])
  check "assertion-succeeds-error" "unsat"
    (!cekSucceeds .nil succeedsError.term)
    (← compileAssertions "assertion-succeeds-error" [] [succeedsError])
  check "assertion-succeeds-timeout" "unsat"
    (cekSucceeds .nil zeroFuelSuccess.term &&
      zeroFuelSuccessConditionIsFalse)
    (← compileAssertions "assertion-succeeds-timeout" []
      [zeroFuelSuccess])
  check "assertion-returns-false" "sat"
    (cekBool .nil returnsFalse.term false)
    (← compileAssertions "assertion-returns-false" [] [returnsFalse])
  check "assertion-returns-false-mismatch" "unsat"
    (!cekBool .nil returnsFalseFromTrue.term false)
    (← compileAssertions "assertion-returns-false-mismatch" []
      [returnsFalseFromTrue])
  check "assertion-returns-false-wrong-sort" "unsat"
    (!cekBool .nil returnsFalseFromInteger.term false)
    (← compileAssertions "assertion-returns-false-wrong-sort" []
      [returnsFalseFromInteger])
  check "assertion-returns-int" "sat"
    (cekInteger .nil returnsSeven.term 7)
    (← compileAssertions "assertion-returns-int" [] [returnsSeven])
  check "assertion-returns-int-mismatch" "unsat"
    (!cekInteger .nil returnsEightFromSeven.term 8)
    (← compileAssertions "assertion-returns-int-mismatch" []
      [returnsEightFromSeven])
  check "assertion-returns-int-wrong-sort" "unsat"
    (!cekInteger .nil returnsSevenFromBoolean.term 7)
    (← compileAssertions "assertion-returns-int-wrong-sort" []
      [returnsSevenFromBoolean])
  check "assertion-expects-error" "sat"
    (cekError .nil expectsError.term)
    (← compileAssertions "assertion-expects-error" [] [expectsError])
  check "assertion-expects-error-from-value" "unsat"
    (!cekError .nil expectsErrorFromValue.term)
    (← compileAssertions "assertion-expects-error-from-value" []
      [expectsErrorFromValue])
  -- Even when the source term really reaches CEK error, symbolic fuel
  -- exhaustion is not evidence for the error expectation.
  check "assertion-error-timeout" "unsat"
    (cekError .nil zeroFuelError.term && zeroFuelErrorConditionIsFalse)
    (← compileAssertions "assertion-error-timeout" [] [zeroFuelError])
  check "assertion-result-predicate" "sat"
    (cekBoolTrue .nil constructorResultSatisfies.term)
    (← compileAssertions "assertion-result-predicate" []
      [constructorResultSatisfies])
  -- General target expectations use the source-attached `UplcQuery` facade rather
  -- than only the assertion-side constructors.
  let succeedsLambdaQuery :=
    UplcQuery.ofTerm (.Lam 0 (.Var 1)) .succeeds
  check "target-succeeds-lambda" "sat"
    (cekSucceeds .nil succeedsLambdaQuery.target)
    (← compileQuery "target-succeeds-lambda" 30 [] succeedsLambdaQuery)
  let succeedsErrorQuery := UplcQuery.ofTerm .Error .succeeds
  check "target-succeeds-error" "unsat"
    (!cekSucceeds .nil succeedsErrorQuery.target)
    (← compileQuery "target-succeeds-error" 30 [] succeedsErrorQuery)
  let succeedsZeroFuelQuery := UplcQuery.ofTerm (bool true) .succeeds
  check "target-succeeds-zero-fuel" "unsat"
    (cekSucceeds .nil succeedsZeroFuelQuery.target)
    (← compileQuery "target-succeeds-zero-fuel" 0 []
      succeedsZeroFuelQuery)
  let returnsFalseQuery :=
    (AssertedTerm.ofTerm (bool false)).returnsBool false
  check "target-bool-false" "sat"
    (cekBool .nil returnsFalseQuery.target false)
    (← compileQuery "target-bool-false" 30 [] returnsFalseQuery)
  let falseMismatchQuery :=
    (AssertedTerm.ofTerm (bool true)).returnsBool false
  check "target-bool-false-mismatch" "unsat"
    (!cekBool .nil falseMismatchQuery.target false)
    (← compileQuery "target-bool-false-mismatch" 30 []
      falseMismatchQuery)
  -- Exercise the false branch with a genuine symbolic Boolean rather than a
  -- statically folded constant.
  let symbolicFalseQuery :=
    (AssertedTerm.ofTerm (.Var 1)).returnsBool false
  check "target-symbolic-bool-false" "sat"
    (cekBool (booleanEnvironment false) symbolicFalseQuery.target false)
    (← compileQuery "target-symbolic-bool-false" 30 [boolFalse]
      symbolicFalseQuery)
  check "target-symbolic-bool-false-mismatch" "unsat"
    (!cekBool (booleanEnvironment true) symbolicFalseQuery.target false)
    (← compileQuery "target-symbolic-bool-false-mismatch" 30 [boolTrue]
      symbolicFalseQuery)
  -- The source remains deployable as the constructor while only the
  -- verification target applies the structured-value matcher.
  let structuredQuery :=
    (structuredSeven.withAssertion trueAssertion).resultSatisfies
      constructorFieldIsSeven
  check "target-attached-structured-result" "sat"
    (cekBoolTrue .nil trueAssertion.term &&
      cekBoolTrue .nil structuredQuery.target)
    (← compileQuery "target-attached-structured-result" 80 []
      structuredQuery)
  let structuredMismatchQuery :=
    (structuredEight.withAssertion trueAssertion).resultSatisfies
      constructorFieldIsSeven
  check "target-attached-structured-mismatch" "unsat"
    (cekBoolTrue .nil trueAssertion.term &&
      !cekBoolTrue .nil structuredMismatchQuery.target)
    (← compileQuery "target-attached-structured-mismatch" 80 []
      structuredMismatchQuery)
  -- A result consumer need not return Boolean: the same API can select any
  -- shared result expectation.
  let integerConsumerQuery :=
    (AssertedTerm.ofTerm (int 7)).resultSatisfiesWith (.intEq 7) identity
  check "target-general-result-consumer" "sat"
    (cekInteger .nil integerConsumerQuery.target 7)
    (← compileQuery "target-general-result-consumer" 40 []
      integerConsumerQuery)
  check "target-general-result-consumer-mismatch" "unsat"
    (!cekInteger .nil mismatchingIntegerConsumerQuery.target 8)
    (← compileQuery "target-general-result-consumer-mismatch" 40 []
      mismatchingIntegerConsumerQuery)
  -- General error expectations name the exact UPLC application. CEK evaluates
  -- this erroring consumer before its source argument.
  let consumerFirstErrorQuery :=
    (AssertedTerm.ofTerm (int 7)).resultSatisfiesWith .error .Error
  check "target-consumer-first-error" "sat"
    (cekError .nil consumerFirstErrorQuery.target)
    (← compileQuery "target-consumer-first-error" 40 []
      consumerFirstErrorQuery)
  -- The exact expectation applies after both the source call and the result
  -- consumer; this catches accidental expectation placement on either
  -- intermediate value.
  check "target-exact-applied-result" "sat"
    (cekInteger .nil exactAppliedResultQuery.target 10)
    (← compileQuery "target-exact-applied-result" 80 []
      exactAppliedResultQuery)
  -- Direct target-plan composition remains rooted at the source even when a
  -- consumer occurs below an application and another consumer occurs above.
  check "target-composed-root-plan" "sat"
    (cekBoolTrue .nil trueAssertion.term &&
      cekInteger .nil composedRootedQuery.target 10)
    (← compileQuery "target-composed-root-plan" 100 []
      composedRootedQuery)
  -- Source-attached parameter contracts compose with an explicit application
  -- target. The same external declaration supplies the assertion and call.
  let assertedIdentity :=
    identity.withParameterAssertion 40 positivePredicate 1
  let appliedPositiveQuery :=
    assertedIdentity.declarationResultSatisfiesWith
      (.intEq 4) [x4] identity
  check "target-applied-parameter-contract" "sat"
    (cekBoolTrue (integerEnvironment 4) positiveParameter.term &&
      cekInteger (integerEnvironment 4) appliedPositiveQuery.target 4)
    (← compileQuery "target-applied-parameter-contract" 80 [x4]
      appliedPositiveQuery)
  let appliedNegativeQuery :=
    assertedIdentity.declarationResultSatisfiesWith
      (.intEq (-1)) [xNeg] identity
  check "target-applied-parameter-contract-rejects" "unsat"
    (!cekBoolTrue (integerEnvironment (-1)) positiveParameter.term &&
      cekInteger (integerEnvironment (-1)) appliedNegativeQuery.target (-1))
    (← compileQuery "target-applied-parameter-contract-rejects" 80 [xNeg]
      appliedNegativeQuery)
  check "assertion-static-fold" "sat"
    (cekBoolTrue .nil foldedAssertion.term)
    (← compileAssertions "assertion-static-fold" [] [foldedAssertion])
  check "assertion-contradictory" "unsat"
    (cekBoolTrue .nil trueAssertion.term &&
      !cekBoolTrue .nil falseAssertion.term)
    (← compileAssertions "assertion-contradictory" []
      [trueAssertion, falseAssertion])
  check "target-bool-with-true" "sat"
    (cekBoolTrue .nil trueAssertion.term && cekBoolTrue .nil (bool true))
    (← compileBool "target-bool-with-true" [] [trueAssertion] (bool true))
  -- Paired with the preceding case: dropping compiler-owned assertions would
  -- incorrectly turn this query into SAT.
  check "target-bool-with-false" "unsat"
    (!cekBoolTrue .nil falseAssertion.term && cekBoolTrue .nil (bool true))
    (← compileBool "target-bool-with-false" [] [falseAssertion] (bool true))
  check "target-bool-with-timeout" "unsat"
    (cekBoolTrue .nil timeoutAssertion.term && timeoutConditionIsFalse &&
      cekBoolTrue .nil (bool true))
    (← compileBool "target-bool-with-timeout" [] [timeoutAssertion] (bool true))
  check "target-int" "sat"
    (cekBoolTrue .nil trueAssertion.term && cekInteger .nil (int 7) 7)
    (← compileInt "target-int" [] [trueAssertion] (int 7) 7)
  check "target-int-with-false" "unsat"
    (!cekBoolTrue .nil falseAssertion.term && cekInteger .nil (int 7) 7)
    (← compileInt "target-int-with-false" [] [falseAssertion] (int 7) 7)
  check "target-error" "sat"
    (cekBoolTrue .nil trueAssertion.term && cekError .nil .Error)
    (← compileError "target-error" [] [trueAssertion] .Error)
  check "target-error-with-false" "unsat"
    (!cekBoolTrue .nil falseAssertion.term && cekError .nil .Error)
    (← compileError "target-error-with-false" [] [falseAssertion] .Error)
  check "symbolic-positive" "sat"
    (cekBoolTrue (integerEnvironment 4) positiveParameter.term)
    (← compileAssertions "symbolic-positive" [x4] [positiveParameter])
  check "symbolic-negative" "unsat"
    (!cekBoolTrue (integerEnvironment (-1)) positiveParameter.term)
    (← compileAssertions "symbolic-negative" [xNeg] [positiveParameter])
  check "symbolic-exact-int" "sat"
    (cekInteger (integerEnvironment 7) symbolicSeven.term 7)
    (← compileAssertions "symbolic-exact-int" [x7] [symbolicSeven])
  check "symbolic-exact-int-mismatch" "unsat"
    (!cekInteger (integerEnvironment 8) symbolicSeven.term 7)
    (← compileAssertions "symbolic-exact-int-mismatch" [x8]
      [symbolicSeven])
  -- A genuinely free declaration must be restricted by the exact-result
  -- assertion, and the target must use that identical solver/CEK value.
  check "symbolic-exact-int-free-witness" "sat"
    (cekInteger (integerEnvironment 7) symbolicSeven.term 7)
    (← compileAssertions "symbolic-exact-int-free-witness" [freeX]
      [symbolicSeven])
  check "symbolic-exact-int-free-target" "sat"
    (cekInteger (integerEnvironment 7) symbolicSeven.term 7 &&
      cekInteger (integerEnvironment 7) (.Var 1) 7)
    (← compileInt "symbolic-exact-int-free-target" [freeX]
      [symbolicSeven] (.Var 1) 7)
  check "symbolic-exact-int-free-restricted" "unsat"
    (!cekInteger (integerEnvironment 8) symbolicSeven.term 7 &&
      cekInteger (integerEnvironment 8) (.Var 1) 8)
    (← compileInt "symbolic-exact-int-free-restricted" [freeX]
      [symbolicSeven] (.Var 1) 8)
  check "mixed-expectations" "sat"
    (cekSucceeds (integerEnvironment 7) (.Var 1) &&
      cekInteger (integerEnvironment 7) (.Var 1) 7 &&
      cekBool (integerEnvironment 7) (bool false) false &&
      cekError (integerEnvironment 7) .Error)
    (← compileAssertions "mixed-expectations" [x7] mixedExpectations)
  check "mixed-expectations-mismatch" "unsat"
    (cekSucceeds (integerEnvironment 8) (.Var 1) &&
      !cekInteger (integerEnvironment 8) (.Var 1) 7 &&
      cekBool (integerEnvironment 8) (bool false) false &&
      cekError (integerEnvironment 8) .Error)
    (← compileAssertions "mixed-expectations-mismatch" [x8]
      mixedExpectations)
  check "symbolic-path-positive" "sat"
    (cekBoolTrue (integerEnvironment 4) positiveOrError.term)
    (← compileAssertions "symbolic-path-positive" [x4] [positiveOrError])
  check "symbolic-path-error" "unsat"
    (cekError (integerEnvironment (-1)) positiveOrError.term)
    (← compileAssertions "symbolic-path-error" [xNeg] [positiveOrError])
  -- The target and predicate share one genuinely free symbolic parameter.
  -- The baseline permits x = -1, the compatible case permits x = 4, and the
  -- predicate must rule the same x = -1 target out.
  check "shared-parameter-baseline" "sat"
    (cekInteger (integerEnvironment (-1)) (.Var 1) (-1))
    (← compileInt "shared-parameter-baseline" [freeX] [] (.Var 1) (-1))
  check "shared-parameter-compatible" "sat"
    (cekBoolTrue (integerEnvironment 4) positiveParameter.term &&
      cekInteger (integerEnvironment 4) (.Var 1) 4)
    (← compileInt "shared-parameter-compatible"
      [freeX] [positiveParameter] (.Var 1) 4)
  check "shared-parameter-restricted" "unsat"
    (!cekBoolTrue (integerEnvironment (-1)) positiveParameter.term &&
      cekInteger (integerEnvironment (-1)) (.Var 1) (-1))
    (← compileInt "shared-parameter-restricted"
      [freeX] [positiveParameter] (.Var 1) (-1))
  -- Refinement-style partiality check: division by a free parameter can
  -- error, the not-zero predicate is itself satisfiable, and together they
  -- make the error target impossible without vacuous preconditions.
  let divisionQueries ← compileErrorBundle "divide-under-not-zero"
    [freeDivisor] [notZeroDivisor] divideByParameter
  check "not-zero-satisfiable" "sat"
    (cekBoolTrue (integerEnvironment 2) notZeroDivisor.term)
    divisionQueries.satisfiability
  check "divide-error-baseline" "sat"
    (cekError (integerEnvironment 0) divideByParameter)
    (← compileError "divide-error-baseline" [freeDivisor] [] divideByParameter)
  check "divide-error-under-not-zero" "unsat"
    (cekError (integerEnvironment 0) divideByParameter &&
      !cekBoolTrue (integerEnvironment 0) notZeroDivisor.term &&
      !cekError (integerEnvironment 2) divideByParameter &&
      cekBoolTrue (integerEnvironment 2) notZeroDivisor.term)
    divisionQueries.target
  check "declaration-order-positive" "sat"
    (cekBoolTrue xyEnvironment appliedXLessThanY.term)
    (← compileAssertions "declaration-order-positive"
      [x2, y5] [appliedXLessThanY])
  check "declaration-order-negative" "unsat"
    (!cekBoolTrue xyEnvironment yLessThanX.term)
    (← compileAssertions "declaration-order-negative" [x2, y5] [yLessThanX])
  check "lambda-capture" "sat"
    (cekBoolTrue xyEnvironment capturedRelation.term)
    (← compileAssertions "lambda-capture" [x2, y5] [capturedRelation])
  check "lambda-capture-negative" "unsat"
    (!cekBoolTrue yxEnvironment capturedRelation.term)
    (← compileAssertions "lambda-capture-negative" [x5, y2] [capturedRelation])
  check "symbolic-constructor-positive" "sat"
    (cekBoolTrue (constructorEnvironment 0) constructorIsZero.term)
    (← compileAssertions "symbolic-constructor-positive"
      [constructor0] [constructorIsZero])
  check "symbolic-constructor-negative" "unsat"
    (!cekBoolTrue (constructorEnvironment 1) constructorIsZero.term)
    (← compileAssertions "symbolic-constructor-negative"
      [constructor1] [constructorIsZero])
  check "lazy-unselected-error" "sat"
    (cekBoolTrue .nil unselectedErrorAssertion.term)
    (← compileAssertions "lazy-unselected-error" [] [unselectedErrorAssertion])
  check "lazy-selected-error" "unsat"
    (cekError .nil selectedErrorAssertion.term)
    (← compileAssertions "lazy-selected-error" [] [selectedErrorAssertion])
  IO.println "UPLC assertion SMT/CEK differential passed (70 cases, 2 renderers)"

end Test.SMT.UplcAssertionsZ3

unsafe def main : IO Unit := Test.SMT.UplcAssertionsZ3.main
