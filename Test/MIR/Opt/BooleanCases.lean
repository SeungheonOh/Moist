import Test.MIR.Opt.Soundness
import Moist.MIR.Compile

/-- Tests evaluate under semantics variant E (the conformance-suite variant). -/
private local instance testSemVariant : Moist.CEK.SemVariant := .E


namespace Test.MIR.Opt.BooleanCases

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def helper := sourceVar 900
private def parameter := sourceVar 901
private def recursive := sourceVar 902
private def input := sourceVar 903
private def list := sourceVar 904
private def head := sourceVar 905
private def tail := sourceVar 906
private def extra := sourceVar 907
private def bound := sourceVar 908

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message,.AtomicType .TypeString))) body

private def equalsZero (value : Expr) : Expr :=
  .App (.App (.Builtin .EqualsInteger) value) (intLit 0)

private def booleanConsumer (condition : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) condition)
    (.Delay (trace "yes" (intLit 11)))) (.Delay (trace "no" (intLit 22))))

private def integerList (values : List Int) : Expr :=
  .Lit (.ConstList (.AtomicType .TypeInteger) (values.map .Integer),.TypeOperator (.TypeList (.AtomicType .TypeInteger)))

private def lowerChecked (expression : Expr) : IO Term :=
  match lowerExpr expression with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

private def nativeObservation (term : Term) : IO String := do
  match ← Moist.Plutus.Eval.evalTerm term
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return Moist.Plutus.Pretty.prettyTerm result.term
  | .error (kind,_,message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid observation: {kind}: {message}")
    | _ => return "failure"

/-- The checked simplifier and the whole pipeline agree with the source on
    the native evaluator and on Lean CEK traces. -/
private def compare (label : String) (expression : Expr) : IO Unit := do
  let baseline ← nativeObservation (← lowerChecked expression)
  let baselineTrace ← Soundness.tracedObservation expression
  for (name,candidate) in [("summaries",Advanced.shapeDCE expression),
      ("combined",prepareForLowering expression)] do
    checkEq s!"{label}/{name}/native" (← nativeObservation (← lowerChecked candidate)) baseline
    check s!"{label}/{name}/trace" ((← Soundness.tracedObservation candidate) == baselineTrace)

/-- `true` when no lazy `ifThenElse` remains. -/
partial def lazyChoices : Expr → Nat
  | .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay a)) (.Delay b)) =>
    1 + lazyChoices c + lazyChoices a + lazyChoices b
  | .Let bindings body => bindings.foldl (fun n (_, rhs, _) => n + lazyChoices rhs) (lazyChoices body)
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => lazyChoices body
  | .App function argument => lazyChoices function + lazyChoices argument
  | .Constr _ fields => fields.foldl (fun n field => n + lazyChoices field) 0
  | .Case scrutinee alternatives =>
    alternatives.foldl (fun n alternative => n + lazyChoices alternative) (lazyChoices scrutinee)
  | _ => 0

/-- Number of cases whose scrutinee is itself a case. -/
partial def nestedCases : Expr → Nat
  | .Case scrutinee alternatives =>
    let here := match scrutinee with | .Case _ _ => 1 | _ => 0
    alternatives.foldl (fun n alternative => n + nestedCases alternative) (here + nestedCases scrutinee)
  | .Let bindings body => bindings.foldl (fun n (_, rhs, _) => n + nestedCases rhs) (nestedCases body)
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => nestedCases body
  | .App function argument => nestedCases function + nestedCases argument
  | .Constr _ fields => fields.foldl (fun n field => n + nestedCases field) 0
  | _ => 0

def tests : TestTree := suite "boolean cases" do
  test "let_bound_helper_results" do
    let isZero : Expr := .Lam parameter (equalsZero (.Var parameter))
    let environment := [(helper, isZero)]
    check "saturated helper call is Boolean"
      (Advanced.knownBooleanResult 64 environment (.App (.Var helper) (intLit 3)))
    check "partial helper call is not Boolean"
      (!Advanced.knownBooleanResult 64 [(helper, .Lam parameter isZero)] (.App (.Var helper) (intLit 3)))
    check "overapplied helper call is not Boolean"
      (!Advanced.knownBooleanResult 64 environment (.App (.App (.Var helper) (intLit 3)) (intLit 4)))
    check "helper returning its parameter is not Boolean"
      (!Advanced.knownBooleanResult 64 [(helper, .Lam parameter (.Var parameter))]
        (.App (.Var helper) (boolLit true)))
    check "helper returning an integer is not Boolean"
      (!Advanced.knownBooleanResult 64 [(helper, .Lam parameter (intLit 1))] (.App (.Var helper) (intLit 3)))
    let loop : Expr := .Fix recursive (.Lam parameter
      (.Case (equalsZero (.Var parameter))
        [.App (.Var recursive) (.App (.App (.Builtin .SubtractInteger) (.Var parameter)) (intLit 1)),
         boolLit true]))
    check "let-bound recursive helper is Boolean"
      (Advanced.knownBooleanResult 64 [(helper, loop)] (.App (.Var helper) (intLit 3)))
    for value in [0, 1, 5] do
      compare s!"helper/{value}" (.Let [(helper, isZero, false)]
        (booleanConsumer (.App (.Var helper) (trace "argument" (intLit value)))))
      compare s!"recursive helper/{value}" (.Let [(helper, loop, false)]
        (booleanConsumer (.App (.Var helper) (intLit value))))
      compare s!"integer helper/{value}" (.Let [(helper, .Lam parameter (.Var parameter), false)]
        (booleanConsumer (.App (.Var helper) (intLit value))))
    let rewritten := Advanced.shapeDCE (.Let [(helper, isZero, false)]
      (booleanConsumer (.App (.Var helper) (.Var input))))
    checkEq "helper condition becomes a case" (lazyChoices rewritten) 0
    let kept := Advanced.shapeDCE (.Let [(helper, .Lam parameter (.Var parameter), false)]
      (booleanConsumer (.App (.Var helper) (.Var input))))
    checkEq "non-Boolean helper condition kept" (lazyChoices kept) 1
  test "case_alternatives_with_fields" do
    let consCase (alternative : Expr) (scrutinee : Expr) : Expr :=
      .Case scrutinee [alternative, boolLit false]
    let tailOf : Expr := .App (.Force (.Builtin .TailList)) (.Var list)
    let environment := [(list, integerList [1, 2, 3])]
    check "list alternative binding both fields is Boolean"
      (Advanced.knownBooleanResult 64 environment
        (consCase (.Lam head (.Lam tail (equalsZero (.Var head)))) tailOf))
    check "list alternative binding one field is Boolean"
      (Advanced.knownBooleanResult 64 environment (consCase (.Lam head (boolLit true)) tailOf))
    check "list alternative binding three fields is not Boolean"
      (!Advanced.knownBooleanResult 64 environment
        (consCase (.Lam head (.Lam tail (.Lam extra (boolLit true)))) tailOf))
    check "unknown scrutinee does not supply fields"
      (!Advanced.knownBooleanResult 64 [] (consCase (.Lam head (.Lam tail (boolLit true))) (.Var list)))
    check "field facts are not assumed"
      (!Advanced.knownBooleanResult 64 environment (consCase (.Lam head (.Lam tail (.Var head))) tailOf))
    let pairCase : Expr := .Case (.App (.Builtin .UnConstrData) (.Var input))
      [.Lam head (.Lam tail (equalsZero (.Var head)))]
    check "constructor pair alternative is Boolean" (Advanced.knownBooleanResult 64 [] pairCase)
    for values in [[], [0], [5, 0], [0, 0, 0]] do
      for alternative in [Expr.Lam head (.Lam tail (equalsZero (.Var head))), .Lam head (boolLit true),
          .Lam head (.Lam tail (.Lam extra (boolLit true))), .Lam head (.Lam tail (.Var head))] do
        compare s!"list/{values}" (.Let [(list, integerList values, false)]
          (booleanConsumer (consCase alternative tailOf)))
  test "boolean_case_of_case" do
    let condition := equalsZero (.Var input)
    let inner : Expr := .Case condition
      [boolLit false, .Let [(bound, trace "inner" (intLit 4), false)] (equalsZero (.Var bound))]
    let outer : Expr := .Case inner [.Error, .Lit (.Unit, .AtomicType .TypeUnit)]
    let rewritten := Advanced.shapeDCE (.Let [(input, intLit 0, false)] outer)
    checkEq "outer case moved into the Boolean case tree" (nestedCases rewritten) 0
    for value in [0, 1] do
      compare s!"case of case/{value}" (.Let [(input, trace "input" (intLit value), false)] outer)
      compare s!"identity/{value}" (.Let [(input, intLit value, false)]
        (.Case condition [boolLit false, boolLit true]))
    let integerScrutinee : Expr := .Case (intLit 0) [boolLit false, boolLit true]
    check "identity on an integer scrutinee kept"
      (alphaEq (Advanced.shapeDCE integerScrutinee) integerScrutinee)
    compare "identity on an integer scrutinee" integerScrutinee
    let unknownInner : Expr := .Case (.Case (.Var input) [boolLit false, boolLit true]) [.Error, intLit 1]
    for value in [Expr.Lit (.Unit, .AtomicType .TypeUnit), intLit 1, .Constr 1 [intLit 2], boolLit true] do
      compare "case of case on an unknown scrutinee" (.Let [(input, value, false)] unknownInner)

end Test.MIR.Opt.BooleanCases
