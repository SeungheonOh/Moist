import Test.MIR.OpportunityBench

namespace Test.MIR.Opt.ChecksFirst

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
      throw (IO.userError s!"Invalid checks-first observation: {kind}: {message}")
    | _ => return ("failure", budget.cpu, budget.mem)

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def dataLiteral (datum : Moist.Plutus.Data) : Expr :=
  .Lit (.Data datum, .AtomicType .TypeData)

private def unI (e : Expr) : Expr := .App (.Builtin .UnIData) e
private def eqI (a b : Expr) : Expr := .App (.App (.Builtin .EqualsInteger) a) b
private def addI (a b : Expr) : Expr := .App (.App (.Builtin .AddInteger) a) b

/-- `force (ifThenElse c (delay body) (delay error))` -/
private def require (c body : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay body)) (.Delay .Error))

private def inputs : List Expr :=
  [dataLiteral (.I 1), dataLiteral (.I 2), dataLiteral (.B ⟨#[1]⟩), dataLiteral (.Constr 0 [])]

/-- Every transformation agrees with the source on results and traces. -/
private def compareScript (label : String) (script : Expr) (arguments : List (List Expr)) : IO Unit := do
  let baseline ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.checksFirst, Advanced.structural].mapM
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

private def value := sourceVar 400
private def flag := sourceVar 401
private def decoded := sourceVar 402
private def other := sourceVar 403

/-- `λ value flag. let decoded = rhs in require check body` -/
private def decodeThenCheck (rhs check body : Expr) : Expr :=
  .Lam value (.Lam flag (.Let [(decoded, rhs, false)] (require check body)))

private def flagIsOne : Expr := eqI (unI (.Var flag)) (intLit 1)

def tests : TestTree := suite "checks_first" do
  test "binding_moves_below_the_check" do
    let script := decodeThenCheck (unI (.Var value)) flagIsOne (addI (.Var decoded) (intLit 5))
    check "check first" (match Advanced.checksFirst script with
      | .Lam _ (.Lam _ (.Force (.App (.App (.App _ _) (.Delay (.Let [_] _))) (.Delay .Error)))) => true
      | _ => false)
    compareScript "decode then check" script pairs
  test "reject_path_skips_the_decoding" do
    let script := decodeThenCheck (unI (.Var value)) flagIsOne (addI (.Var decoded) (intLit 5))
    let before ← requireTerm (lowerExpr script)
    let after ← requireTerm (lowerExpr (Advanced.checksFirst script))
    let arguments ← [dataLiteral (.I 7), dataLiteral (.I 2)].mapM fun a => requireTerm (lowerExpr a)
    let original ← observe (arguments.foldl Term.Apply before)
    let optimized ← observe (arguments.foldl Term.Apply after)
    checkEq "both reject" optimized.1 original.1
    check "reject CPU drops" (optimized.2.1 < original.2.1)
  test "binding_moves_below_consecutive_checks" do
    let script := decodeThenCheck (unI (.Var value)) flagIsOne
      (require (eqI (unI (.Var flag)) (unI (.Var flag))) (.Var decoded))
    check "below both checks" (match Advanced.checksFirst script with
      | .Lam _ (.Lam _ (.Force (.App (.App (.App _ _)
          (.Delay (.Force (.App (.App (.App _ _) (.Delay (.Let [_] _))) (.Delay .Error))))) (.Delay .Error)))) => true
      | _ => false)
    compareScript "two checks" script pairs
  test "checks_keep_their_order" do
    let script := Expr.Lam value (.Lam flag
      (require (eqI (unI (.Var value)) (intLit 1)) (require flagIsOne (.Var flag))))
    check "unchanged" (alphaEq (Advanced.checksFirst script) script)
    compareScript "ordered checks" script pairs
  test "check_mentioning_the_binding_stays" do
    let script := decodeThenCheck (unI (.Var value)) (eqI (.Var decoded) (intLit 1)) (.Var decoded)
    check "unchanged" (alphaEq (Advanced.checksFirst script) script)
    compareScript "dependent" script pairs
  test "unknown_calls_are_not_crossed" do
    let script := Expr.Lam other (decodeThenCheck (unI (.Var value)) (.App (.Var other) (.Var flag))
      (.Var decoded))
    check "unchanged" (alphaEq (Advanced.checksFirst script) script)
  test "traces_are_not_moved" do
    let traced := decodeThenCheck (trace "decode" (unI (.Var value))) flagIsOne (.Var decoded)
    check "traced binding stays" (alphaEq (Advanced.checksFirst traced) traced)
    compareScript "traced binding" traced pairs
    let tracedCheck := decodeThenCheck (unI (.Var value)) (trace "check" flagIsOne) (.Var decoded)
    check "traced check stays" (alphaEq (Advanced.checksFirst tracedCheck) tracedCheck)
    compareScript "traced check" tracedCheck pairs

end Test.MIR.Opt.ChecksFirst
