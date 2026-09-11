import Test.MIR.Opt.Soundness
import Moist.MIR.Optimize.Advanced.Recursion
import Moist.MIR.Compile

namespace Test.MIR.Opt.Recursion

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def recursive := sourceVar 800
private def invariant := sourceVar 801
private def counter := sourceVar 802
private def temporary := sourceVar 803

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message,.AtomicType .TypeString))) body

private def loop (base next : Expr) : Expr :=
  .Fix recursive (.Lam invariant (.Lam counter
    (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Var counter)) (intLit 0))
      [.App (.App (.Var recursive) next)
        (.App (.App (.Builtin .SubtractInteger) (.Var counter)) (intLit 1)),base])))

private def booleanConsumer (condition : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) condition)
    (.Delay (trace "yes" (intLit 11)))) (.Delay (trace "no" (intLit 22))))

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

private def compare (label : String) (expression : Expr) : IO Unit := do
  let baseline ← nativeObservation (← lowerChecked expression)
  let baselineTrace ← Soundness.tracedObservation expression
  for (name,candidate) in [("static",Advanced.staticArguments expression),
      ("summaries",Advanced.shapeDCE expression),
      ("combined",prepareForLowering (Advanced.staticArguments expression))] do
    checkEq s!"{label}/{name}/native" (← nativeObservation (← lowerChecked candidate)) baseline
    check s!"{label}/{name}/trace" ((← Soundness.tracedObservation candidate) == baselineTrace)

def tests : TestTree := suite "recursion" do
  test "static_arguments_preserve_effects_and_partial_applications" do
    let worker := loop (trace "base" (.Var invariant)) (.Var invariant)
    check "invariant transformed" (!alphaEq worker (Advanced.staticArguments worker))
    for count in [0,1,4] do
      compare s!"effects/{count}" (.App (.App worker (trace "argument" (intLit 7))) (trace "count" (intLit count)))
    compare "deferred partial" (.Let [(temporary,.App worker (trace "argument" (intLit 7)),false)] (intLit 9))
    compare "forced partial fails" (.Force (.App worker (intLit 7)))
    let returned := loop (.Lam temporary (.Var invariant)) (.Var invariant)
    compare "overapplication" (.App (.App (.App returned (intLit 7)) (intLit 3)) (trace "extra" (intLit 8)))
    let partialUse : Expr := .Fix recursive (.Lam invariant (.Lam counter
      (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Var counter)) (intLit 0))
        [.App (.App (.Var recursive) (.Var invariant)) (intLit 0),.App (.Var recursive) (.Var invariant)])))
    compare "partial recursive result discarded" (.Let [(temporary,.App (.App partialUse (intLit 7)) (intLit 0),false)] (intLit 1))
  test "static_argument_guards_and_hygiene" do
    for next in [intLit 4,trace "next" (.Var invariant),.App (.Builtin .UnIData) (.Var invariant)] do
      let worker := loop (boolLit true) next
      check "changed or effectful argument rejected" (alphaEq worker (Advanced.staticArguments worker))
    for body in [Expr.Var recursive,.Let [(temporary,.Var recursive,false)] (.Var temporary),
        .Lam invariant (.App (.Var recursive) (.Var invariant))] do
      let worker : Expr := .Fix recursive (.Lam invariant (.Lam counter body))
      check "escaping and shadowed recursion rejected" (alphaEq worker (Advanced.staticArguments worker))
    let shadowed : Expr := .Fix recursive (.Lam recursive (.Lam counter (.Var recursive)))
    compare "recursive binder shadowed" (.App (.App shadowed (intLit 5)) (intLit 0))
    let originVariant : VarId := { invariant with origin := .gen }
    let worker : Expr := .Lam originVariant (loop (.Var originVariant) (.Var invariant))
    compare "origin collision" (.App (.App (.App worker (intLit 19)) (intLit 7)) (intLit 2))
  test "boolean_summary_rejects_parameter_specialization_and_arity" do
    let identityLoop := loop (.Var invariant) (intLit 0)
    let application : Expr := .App (.App identityLoop (boolLit true)) (intLit 1)
    check "recursive parameter type remains unknown" (!Advanced.knownBooleanResult 64 [] application)
    check "shadowed parameter facts are hidden" (!Advanced.knownBooleanResult 64 [(invariant,boolLit true)] application)
    compare "changed recursive result type" (booleanConsumer application)
    let booleanLoop := loop (boolLit true) (.Var invariant)
    check "saturated Boolean recursion recognized" (Advanced.knownBooleanResult 64 [] (.App (.App booleanLoop (intLit 0)) (intLit 1)))
    check "partial application not Boolean" (!Advanced.knownBooleanResult 64 [] (.App booleanLoop (intLit 0)))
    check "overapplication not Boolean" (!Advanced.knownBooleanResult 64 [] (.App (.App (.App booleanLoop (intLit 0)) (intLit 1)) (intLit 2)))
    compare "partial application used as Boolean" (booleanConsumer (.App booleanLoop (intLit 0)))
  test "generated_recursive_return_shapes" do
    let dataValue := Expr.Lit (.Data (.I 3),.AtomicType .TypeData)
    let bases := [boolLit true,boolLit false,.Var invariant,intLit 0,intLit 1,
      dataValue,.Constr 0 [],.Delay (boolLit true),.Lam temporary (boolLit true),
      .Error,trace "base" (boolLit true),
      .App (.App (.Builtin .EqualsInteger) (.App (.Builtin .UnIData) (.Var invariant))) (intLit 3)]
    for (base,baseIndex) in bases.zipIdx do
      for (next,nextIndex) in [Expr.Var invariant,boolLit true,intLit 0,dataValue].zipIdx do
        for (argument,argumentIndex) in [boolLit false,intLit 0,dataValue].zipIdx do
          for count in [0,1,3] do
            compare s!"generated/{baseIndex}/{nextIndex}/{argumentIndex}/{count}"
              (booleanConsumer (.App (.App (loop base next) argument) (intLit count)))
  test "divergent_workers_remain_divergent" do
    let forever : Expr := .Fix recursive (.Lam invariant (.Lam counter
      (.App (.App (.Var recursive) (.Var invariant)) (.Var counter))))
    let application := booleanConsumer (.App (.App forever (boolLit true)) (intLit 0))
    for candidate in [application,Advanced.staticArguments application,prepareForLowering application] do
      let result ← Moist.Plutus.Eval.evalTerm (← lowerChecked candidate) 1000000 1000000
      match result with
      | .error (.outOfBudget,_,_) => pure ()
      | _ => throw (IO.userError "Divergent recursion unexpectedly completed")

end Test.MIR.Opt.Recursion
