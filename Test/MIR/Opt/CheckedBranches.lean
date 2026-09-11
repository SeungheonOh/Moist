import Test.MIR.Opt.Soundness
import Moist.MIR.Compile
import Moist.MIR.Optimize.Advanced.CheckedBranches

namespace Test.MIR.Opt.CheckedBranches

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def input := sourceVar 850
private def headBinder := sourceVar 851
private def tailBinder := sourceVar 852
private def alias := sourceVar 853
private def temporary := sourceVar 854
private def recursive := sourceVar 855

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message,.AtomicType .TypeString))) body

private def head (value : Expr) : Expr := .App (.Force (.Builtin .HeadList)) value
private def tail (value : Expr) : Expr := .App (.Force (.Builtin .TailList)) value
private def null (value : Expr) : Expr := .App (.Force (.Builtin .NullList)) value

private def choose (value empty nonempty : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Force (.Builtin .ChooseList))) value)
    (.Delay empty)) (.Delay nonempty))

private def projections (value body : Expr) : Expr :=
  .Let [(headBinder,head value,false),(tailBinder,tail value,false)] body

private def inputs : List Expr :=
  [intLit (-1),intLit 0,intLit 1,boolLit false,boolLit true,
   .Lit (.Unit,.AtomicType .TypeUnit),.Lit (.Data (.List [.I 3]),.AtomicType .TypeData),
   .Lit (.Pair (.Integer 3,.Integer 4),.TypeOperator (.TypePair
     (.AtomicType .TypeInteger) (.AtomicType .TypeInteger))),
   .Constr 0 [],.Constr 1 [],.Constr 0 [intLit 3,intLit 4],
   .Delay (intLit 3),.Lam temporary (.Var temporary)] ++
  [[],[Moist.Plutus.Data.I 3],[.I 3,.I 4]].map
    (fun fields => .Lit (.ConstDataList fields,.TypeOperator (.TypeList (.AtomicType .TypeData)))) ++
  [[],[Const.Integer 3],[.Integer 3,.Integer 4]].map
    (fun fields => .Lit (.ConstList fields,.TypeOperator (.TypeList (.AtomicType .TypeInteger)))) ++
  [[],[(Moist.Plutus.Data.I 3,Moist.Plutus.Data.I 4)]].map
    (fun fields => .Lit (.ConstPairDataList fields,.TypeOperator (.TypeList
      (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData))))))

private def requireTerm (result : Except String Term) : IO Term :=
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

private def observe (term : Term) : IO String := do
  match ← Moist.Plutus.Eval.evalTerm term
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return Moist.Plutus.Pretty.prettyTerm result.term
  | .error (kind,_,message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid observation: {kind}: {message}")
    | _ => return "failure"

private def compare (label : String) (script : Expr) (arguments : List Expr := inputs) : IO Unit := do
  let raw ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.fuseCheckedListBranches,Advanced.lowerDelayedListChoices,
    Advanced.optimizeCheckedBranches].mapM fun transform => requireTerm (lowerExpr (transform script))
  let compiled ← requireTerm (compileOptimized script)
  let sizeCompiled ← requireTerm (compileOptimized script 0 0
    { shareBuiltinStates := true, poolConstants := true })
  for (argument,index) in arguments.zipIdx do
    let value ← requireTerm (lowerExpr argument)
    let original := Term.Apply raw value
    let expected ← observe original
    let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
    for (candidate,variant) in (candidates ++ [compiled,sizeCompiled]).zipIdx do
      let applied := Term.Apply candidate value
      checkEq s!"{label}/{index}/{variant}/native" (← observe applied) expected
      check s!"{label}/{index}/{variant}/trace"
        ((← Soundness.tracedObservation (liftUPLC applied)) == expectedTrace)

def tests : TestTree := suite "checked-branches" do
  test "unknown_inputs_keep_runtime_validation" do
    let body := projections (.Var input) (.Constr 0 [.Var headBinder,.Var tailBinder])
    let choices := [choose (.Var input) (intLit 7) body,
      .Case (null (.Var input)) [body,intLit 7]]
    for (choice,index) in choices.zipIdx do
      let script := Expr.Lam input choice
      check "nonempty deconstruction transformed" (!alphaEq script (Advanced.fuseCheckedListBranches script))
      compare s!"runtime shapes/{index}" script
    compare "empty projection still fails" (.Lam input
      (choose (.Var input) body (intLit 7)))
    compare "null empty projection still fails" (.Lam input
      (.Case (null (.Var input)) [intLit 7,body]))
  test "strict_arguments_and_builtin_protocol" do
    let selector := Expr.Force (.Force (.Builtin .ChooseList))
    let eager := projections (.Var input) (.Delay (intLit 3))
    for (empty,nonempty) in [(Expr.Delay (intLit 7),eager),
        (trace "empty argument" (.Delay (intLit 7)),trace "nonempty argument" (.Delay (intLit 3))),
        (.Error,.Delay (intLit 3)),(.Delay (intLit 7),.Error)] do
      let script := Expr.Lam input (.Force (.App (.App (.App selector (.Var input)) empty) nonempty))
      check "eager arguments not delayed" (alphaEq
        (liftUPLC (← requireTerm (lowerExpr script)))
        (liftUPLC (← requireTerm (lowerExpr (Advanced.optimizeCheckedBranches script)))))
      compare "strict selector arguments" script
    for selector in [Expr.Builtin .ChooseList,.Force (.Builtin .ChooseList),
        .Force (.Force (.Force (.Builtin .ChooseList))),.Force (.Builtin .IfThenElse)] do
      let script := Expr.Lam input (.Force (.App (.App (.App selector (.Var input))
        (.Delay (intLit 7))) (.Delay (intLit 3))))
      check "wrong selector protocol untouched" (alphaEq script (Advanced.optimizeCheckedBranches script))
      compare "selector protocol" script
  test "effects_failures_and_projection_order" do
    let bodies := [projections (.Var input) (trace "body" (.Var headBinder)),
      .Let [(headBinder,trace "head" (head (.Var input)),false),
        (tailBinder,trace "tail" (tail (.Var input)),false)] (intLit 1),
      .Let [(headBinder,head (.Var input),false),(temporary,trace "between" (intLit 0),false),
        (tailBinder,tail (.Var input),false)] (.Var headBinder),
      .Let [(headBinder,head (.Var input),false),(temporary,.Error,false),
        (tailBinder,tail (.Var input),false)] (intLit 1),
      .Let [(tailBinder,tail (.Var input),false),(headBinder,head (.Var input),false)] (.Var headBinder)]
    for (body,index) in bodies.zipIdx do
      compare s!"projection order/{index}" (.Lam input
        (choose (.Var input) (trace "empty" (intLit 7)) body))
      compare s!"selector input effects/{index}" (.Lam input
        (choose (trace "input" (.Var input)) (trace "empty" (intLit 7)) body))
    compare "failing discriminator" (.Lam input
      (choose (trace "input" .Error) (trace "empty" (intLit 7)) (trace "nonempty" (intLit 3))))
  test "aliases_shadowing_and_captured_facts" do
    let body := projections (.Var input) (.Var headBinder)
    let originVariant : VarId := { input with origin := .gen }
    let bodies := [
      Expr.Let [(alias,.Var input,false)] (projections (.Var alias) (.Var headBinder)),
      .Let [(alias,.Force (.Builtin .HeadList),false),(temporary,.Force (.Builtin .TailList),false)]
        (.Let [(headBinder,.App (.Var alias) (.Var input),false),
          (tailBinder,.App (.Var temporary) (.Var input),false)] (.Var headBinder)),
      .App (.Lam input body) (intLit 0),
      .Let [(input,intLit 0,false)] body,
      .Let [(originVariant,intLit 0,false)] (projections (.Var originVariant) (.Var headBinder)),
      .Force (.Delay body),.App (.Lam temporary body) (intLit 0)]
    for (body,index) in bodies.zipIdx do
      compare s!"scope/{index}" (.Lam input (choose (.Var input) (intLit 7) body))
    compare "aliased selector" (.Lam input (.Let
      [(alias,.Force (.Force (.Builtin .ChooseList)),false)]
      (.Force (.App (.App (.App (.Var alias) (.Var input)) (.Delay (intLit 7))) (.Delay body)))))
    compare "aliased null selector" (.Lam input (.Let
      [(alias,.Force (.Builtin .NullList),false)]
      (.Case (.App (.Var alias) (.Var input)) [body,intLit 7])))
    compare "selected delay escapes before force" (.Lam input
      (.Force (.Force (choose (.Var input) (.Delay (.Delay (intLit 7))) (.Delay (.Delay body))))))
  test "recursive_traversals" do
    let worker := Expr.Fix recursive (.Lam input (choose (.Var input) (intLit 0)
      (projections (.Var input)
        (.App (.App (.Builtin .AddInteger) (.App (.Builtin .UnIData) (.Var headBinder)))
          (.App (.Var recursive) (.Var tailBinder))))))
    let lists := (List.range 33).map fun count => Expr.Lit
      (.ConstDataList ((List.range count).map fun number => .I (Int.ofNat number)),
        .TypeOperator (.TypeList (.AtomicType .TypeData)))
    compare "recursive sum" worker (inputs ++ lists)
  test "delays_partial_selectors_and_divergence" do
    let forever := Expr.Fix recursive (.Lam temporary (.App (.Var recursive) (.Var temporary)))
    let diverging := Expr.App forever (intLit 0)
    let emptyList := Expr.Lit (.ConstDataList [],.TypeOperator (.TypeList (.AtomicType .TypeData)))
    let nonemptyList := Expr.Lit (.ConstDataList [.I 3],.TypeOperator (.TypeList (.AtomicType .TypeData)))
    compare "unselected divergence" (.Lam input (choose (.Var input) (intLit 7) diverging)) [emptyList]
    compare "discarded delayed selector" (.Lam input (.Let [(temporary,
      .App (.App (.App (.Force (.Force (.Builtin .ChooseList))) (.Var input))
        (.Delay diverging)) (.Delay (projections (.Var input) diverging)),false)] (intLit 7)))
    compare "partial selector applied later" (.Lam input (.Let [(alias,
      .App (.App (.Force (.Force (.Builtin .ChooseList))) (.Var input)) (.Delay (intLit 7)),false)]
      (.Force (.App (.Var alias) (.Delay (projections (.Var input) (.Var headBinder)))))))
    let script := Expr.Lam input (choose (.Var input) (intLit 7) (projections (.Var input) diverging))
    for candidate in [script,Advanced.optimizeCheckedBranches script,prepareForLowering script] do
      let applied := Expr.App candidate nonemptyList
      match ← Moist.Plutus.Eval.evalTerm (← requireTerm (lowerExpr applied)) 1000000 1000000 with
      | .error (.outOfBudget,_,_) => pure ()
      | _ => throw (IO.userError "Selected divergence unexpectedly completed")

end Test.MIR.Opt.CheckedBranches
