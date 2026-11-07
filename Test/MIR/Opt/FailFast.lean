import Test.MIR.OpportunityBench

namespace Test.MIR.Opt.FailFast

open Moist.MIR Moist.Plutus.Term Test.Framework

private def requireTerm (result : Except String Term) : IO Term :=
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

private def observe (term : Term) : IO (String × UInt64 × UInt64) := do
  match ← Moist.Plutus.Eval.evalTerm term
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return (Moist.Plutus.Pretty.prettyTerm result.term, result.budget.cpu, result.budget.mem)
  | .error (kind, budget, message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .encodeError | .decodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid fail-fast observation: {kind}: {message}")
    | _ => return ("failure", budget.cpu, budget.mem)

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def dataLiteral (datum : Moist.Plutus.Data) : Expr :=
  .Lit (.Data datum, .AtomicType .TypeData)

private def unI (e : Expr) : Expr := .App (.Builtin .UnIData) e
private def eqI (a b : Expr) : Expr := .App (.App (.Builtin .EqualsInteger) a) b
private def addI (a b : Expr) : Expr := .App (.App (.Builtin .AddInteger) a) b

private def inputs : List Expr :=
  [dataLiteral (.I 1), dataLiteral (.I 2), dataLiteral (.B ⟨#[1]⟩), dataLiteral (.Constr 0 [])]

/-- Every transformation agrees with the source on results and traces. -/
private def compareScript (label : String) (script : Expr) (arguments : List (List Expr)) : IO Unit := do
  let baseline ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.failFast, Advanced.structural].mapM
    fun transform => requireTerm (lowerExpr (transform script))
  let compiled ← requireTerm (compileOptimized script)
  for (arguments, inputIndex) in arguments.zipIdx do
    let values ← arguments.mapM fun argument => requireTerm (lowerExpr argument)
    let original := values.foldl Term.Apply baseline
    let expected ← observe original
    let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
    for (candidate, variant) in (candidates ++ [compiled]).zipIdx do
      let result := values.foldl Term.Apply candidate
      checkEq s!"{label}/{inputIndex}/{variant}" (← observe result).1 expected.1
      check s!"{label}/{inputIndex}/{variant}/trace"
        ((← Soundness.tracedObservation (liftUPLC result)) == expectedTrace)

private def pairs : List (List Expr) :=
  inputs.flatMap fun a => inputs.map fun b => [a, b]

private def values := sourceVar 300
private def flag := sourceVar 301
private def total := sourceVar 302
private def other := sourceVar 303

/-- `let total = e in if flag == 1 then total else error` -/
private def guarded (rhs : Expr) (check : Expr) (alternatives : List Expr) : Expr :=
  .Lam values (.Lam flag (.Let [(total, rhs, false)] (.Case check alternatives)))

def tests : TestTree := suite "fail_fast" do
  test "binding_moves_below_terminating_check" do
    let script := guarded (addI (unI (.Var values)) (intLit 5)) (eqI (unI (.Var flag)) (intLit 1))
      [.Error, .Var total]
    let moved := Advanced.failFastWalk script
    check "binding moved into the accepting alternative" (match moved with
      | .Lam _ (.Lam _ (.Case _ [.Error, .Let [_] _])) => true
      | _ => false)
    compareScript "guarded" script pairs
  test "reject_path_skips_the_binding" do
    let script := guarded (addI (unI (.Var values)) (intLit 5)) (eqI (unI (.Var flag)) (intLit 1))
      [.Error, .Var total]
    let before ← requireTerm (lowerExpr script)
    let after ← requireTerm (lowerExpr (Advanced.failFast script))
    let arguments ← [dataLiteral (.I 7), dataLiteral (.I 2)].mapM fun a => requireTerm (lowerExpr a)
    let original ← observe (arguments.foldl Term.Apply before)
    let optimized ← observe (arguments.foldl Term.Apply after)
    checkEq "both reject" optimized.1 original.1
    check "reject CPU drops" (optimized.2.1 < original.2.1)
  test "nested_checks_receive_the_binding" do
    let script := guarded (addI (unI (.Var values)) (intLit 5)) (eqI (unI (.Var flag)) (intLit 1))
      [.Error, .Case (eqI (unI (.Var flag)) (intLit 2)) [.Var total, .Error]]
    check "moved twice" (match Advanced.failFastWalk script with
      | .Lam _ (.Lam _ (.Case _ [.Error, .Case _ [.Let [_] _, .Error]])) => true
      | _ => false)
    compareScript "nested" script pairs
  test "check_mentioning_the_binding_stays" do
    let script := guarded (unI (.Var values)) (eqI (.Var total) (intLit 1)) [.Error, .Var total]
    check "unchanged" (alphaEq (Advanced.failFastWalk script) script)
    compareScript "dependent" script pairs
  test "unknown_calls_are_not_checks" do
    let script := Expr.Lam other (guarded (unI (.Var values)) (.App (.Var other) (.Var flag))
      [.Error, .Var total])
    check "unchanged" (alphaEq (Advanced.failFastWalk script) script)
  test "over_applied_builtins_are_not_checks" do
    let ite := Expr.App (.App (.App (.Force (.Builtin .IfThenElse)) (boolLit true)) (.Var other))
      (.Var other)
    let script := Expr.Lam other (guarded (unI (.Var values)) (.App ite (intLit 0))
      [.Error, .Var total])
    check "unchanged" (alphaEq (Advanced.failFastWalk script) script)
  test "traces_are_not_moved" do
    let traced := guarded (trace "decode" (unI (.Var values))) (eqI (unI (.Var flag)) (intLit 1))
      [.Error, .Var total]
    check "traced binding stays" (alphaEq (Advanced.failFastWalk traced) traced)
    compareScript "traced binding" traced pairs
    let tracedCheck := guarded (unI (.Var values)) (trace "check" (eqI (unI (.Var flag)) (intLit 1)))
      [.Error, .Var total]
    check "traced check stays" (alphaEq (Advanced.failFastWalk tracedCheck) tracedCheck)
    compareScript "traced check" tracedCheck pairs
  test "two_live_alternatives_keep_the_binding" do
    let script := guarded (addI (unI (.Var values)) (intLit 5)) (eqI (unI (.Var flag)) (intLit 1))
      [.Var total, addI (.Var total) (intLit 1)]
    check "unchanged" (alphaEq (Advanced.failFastWalk script) script)
  test "if_then_else_checks" do
    let check' := Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
      (eqI (unI (.Var flag)) (intLit 1))) (.Delay (boolLit true))) (.Delay (boolLit false)))
    let script := guarded (addI (unI (.Var values)) (intLit 5)) check' [.Error, .Var total]
    check "moved" (!alphaEq (Advanced.failFastWalk script) script)
    compareScript "ite check" script pairs

end Test.MIR.Opt.FailFast
