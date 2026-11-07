import Test.MIR.OpportunityBench
import Moist.MIR.Optimize.Advanced.Placement

namespace Test.MIR.Opt.LowSharing

open Moist.MIR Moist.Plutus.Term Test.Framework

/-! Sharing at the lowest dominating node (`Advanced.shareLow`): placement
below branches, the guard that keeps every successful run as fast, and
observational equality of every shared program on concrete inputs. -/

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
      throw (IO.userError s!"Invalid low-sharing observation: {kind}: {message}")
    | _ => return ("failure", budget.cpu, budget.mem)

private def dataList (values : List Int) : Expr :=
  .Lit (.Data (.List (values.map .I)), .AtomicType .TypeData)

private def inputs : List Expr :=
  [dataList [], dataList [4], dataList [4, 5], dataList [1, 2, 3],
   .Lit (.Data (.I 3), .AtomicType .TypeData), intLit 0]

private def input : VarId := sourceVar 7000
private def list : VarId := sourceVar 7001

private def headOf (expression : Expr) : Expr :=
  .App (.Builtin .UnIData) (.App (.Force (.Builtin .HeadList)) expression)

private def add (left right : Expr) : Expr :=
  .App (.App (.Builtin .AddInteger) left) right

/-- `λd. let l = unListData d in case (nullList l) [nonEmpty, empty]`. -/
private def onList (nonEmpty empty : Expr) : Expr :=
  .Lam input (.Let [(list, .App (.Builtin .UnListData) (.Var input), false)]
    (.Case (.App (.Force (.Builtin .NullList)) (.Var list)) [nonEmpty, empty]))

/-- Nine reads of the head: a shared `force headList` pays for its binding in
    steps (four) and in size (at least eight uses of its 15 bits). -/
private def nineHeads : Expr :=
  (List.replicate 8 ()).foldl (fun sum _ => add (headOf (.Var list)) sum) (headOf (.Var list))

private def caseAlternatives : Expr → Option (List Expr)
  | .Lam _ (.Let _ (.Case _ alternatives)) => some alternatives
  | _ => none

private def bindsForcedHead : Expr → Bool
  | .Let [(_, .Force (.Builtin .HeadList), _)] _ => true
  | _ => false

private def topBindsForcedHead : Expr → Bool
  | .Lam _ (.Let [(_, .Force (.Builtin .HeadList), _)] _) => true
  | .Lam _ (.Let _ (.Let [(_, .Force (.Builtin .HeadList), _)] _)) => true
  | _ => false

/-- Same observation on every input; with `guarded`, no successful run costs
    more. -/
private def compareRuns (label : String) (before after : Expr) (guarded : Bool) : IO Unit := do
  let beforeTerm ← requireTerm (lowerExpr before)
  let afterTerm ← requireTerm (lowerExpr after)
  for (argument, index) in inputs.zipIdx do
    let argumentTerm ← requireTerm (lowerExpr argument)
    let (expected, cpuBefore, memBefore) ← observe (.Apply beforeTerm argumentTerm)
    let (actual, cpuAfter, memAfter) ← observe (.Apply afterTerm argumentTerm)
    checkEq s!"{label}/{index}/result" actual expected
    if guarded && expected != "failure" then
      check s!"{label}/{index}/cpu {cpuAfter} > {cpuBefore}" (cpuAfter <= cpuBefore)
      check s!"{label}/{index}/mem {memAfter} > {memBefore}" (memAfter <= memBefore)

def tests : TestTree := suite "low-sharing" do
  test "binding_is_placed_in_the_branch_that_uses_it" do
    let script := onList nineHeads (intLit 0)
    let shared := Advanced.shareLow {} script
    check "the top level binds nothing new" (!topBindsForcedHead shared)
    match caseAlternatives shared with
    | some (nonEmpty :: _) => check "the non-empty branch binds force headList" (bindsForcedHead nonEmpty)
    | _ => throw (IO.userError "unexpected shape after low sharing")
    compareRuns "branch placement" script shared true

  test "bindings that slow a successful path are rejected" do
    -- The empty branch reads a head once; a binding above both branches
    -- would cost four steps there and save one.
    let script := onList nineHeads (headOf (.Lit (.ConstDataList [.I 1], Advanced.dataListType)))
    let shared := Advanced.shareLow {} script
    check "unchanged" (alphaEq shared script)
    let unguarded := Advanced.shareLow { guardPaths := false } script
    check "the unguarded plan shares" (!alphaEq unguarded script)
    compareRuns "unguarded" script unguarded false

  test "closed values are shared without the guard" do
    let y := sourceVar 7002
    let increment := Expr.Lam y (add (.Var y) (intLit 1))
    let script := onList (.App increment (headOf (.Var list))) (.App increment (intLit 41))
    check "guarded: a value binding never pays for itself"
      (alphaEq (Advanced.shareLow {} script) script)
    let shared := Advanced.shareLow { guardPaths := false } script
    check "unguarded: the lambda is bound once" (!alphaEq shared script)
    compareRuns "values" script shared false

  test "lifted fixed points are shared and still run" do
    let n := sourceVar 7003
    let factorial := sourceVar 7004
    let fix := Expr.Fix factorial (.Lam n
      (.Case (.App (.App (.Builtin .EqualsInteger) (.Var n)) (intLit 0))
        [.App (.App (.Builtin .MultiplyInteger) (.Var n))
           (.App (.Var factorial) (.App (.App (.Builtin .SubtractInteger) (.Var n)) (intLit 1))),
         intLit 1]))
    let script := onList (.App fix (headOf (.Var list))) (.App fix (intLit 5))
    let lifted := liftUPLC (← requireTerm (lowerExpr script))
    check "the lowered fixed point is a lifted Z combinator"
      ((Advanced.occurrencesOf Advanced.isFixValue lifted).size == 2)
    let shared := Advanced.shareLow { guardPaths := false } lifted
    check "shared" (!alphaEq shared lifted)
    compareRuns "fixed point" lifted shared false

  test "default compilation shares only when no successful run is slower" do
    for script in [onList nineHeads (intLit 0),
        onList nineHeads (headOf (.Lit (.ConstDataList [.I 1], Advanced.dataListType)))] do
      let compiled ← requireTerm (compileOptimized script)
      let reference ← requireTerm (compileOptimized script 1000 5000 { shareLow := false })
      compareRuns "compiled" (liftUPLC reference) (liftUPLC compiled) true

end Test.MIR.Opt.LowSharing
