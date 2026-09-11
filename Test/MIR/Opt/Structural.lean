import Test.MIR.OpportunityBench

namespace Test.MIR.Opt.Structural

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
      throw (IO.userError s!"Invalid structural observation: {kind}: {message}")
    | _ => return ("failure", budget.cpu, budget.mem)

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def dataLiteral (datum : Moist.Plutus.Data) : Expr :=
  .Lit (.Data datum, .AtomicType .TypeData)

private def inputs : List Expr :=
  [intLit 0, boolLit true, .Lit (.Unit, .AtomicType .TypeUnit),
   dataLiteral (.I 7), dataLiteral (.B ⟨#[1]⟩), dataLiteral (.Map []),
   dataLiteral (.Constr 0 []), dataLiteral (.Constr 1 [.I 4]),
   dataLiteral (.List []), dataLiteral (.List [.I 4]), dataLiteral (.List [.I 4, .B ⟨#[1]⟩])]

private def compareScript (label : String) (script : Expr) (arguments : List (List Expr)) : IO Unit := do
  let baseline ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.destructureProducts, Advanced.fuseListChoices, Advanced.structural].mapM
    fun transform => requireTerm (lowerExpr (transform script))
  let compiled ← (List.range 8).mapM fun mask => requireTerm (compileOptimized script 0 0 {
    packApplications := mask % 2 == 1
    shareBuiltinStates := (mask / 2) % 2 == 1
    poolConstants := mask / 4 == 1 })
  for (arguments, inputIndex) in arguments.zipIdx do
    let values ← arguments.mapM fun argument => requireTerm (lowerExpr argument)
    let original := values.foldl Term.Apply baseline
    let expected ← observe original
    let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
    for (candidate, variant) in (candidates ++ compiled).zipIdx do
      let result := values.foldl Term.Apply candidate
      checkEq s!"{label}/{inputIndex}/{variant}" (← observe result).1 expected.1
      check s!"{label}/{inputIndex}/{variant}/trace"
        ((← Soundness.tracedObservation (liftUPLC result)) == expectedTrace)

private def first (pair : Expr) : Expr := .App (.Force (.Force (.Builtin .FstPair))) pair
private def second (pair : Expr) : Expr := .App (.Force (.Force (.Builtin .SndPair))) pair
private def head (list : Expr) : Expr := .App (.Force (.Builtin .HeadList)) list
private def tail (list : Expr) : Expr := .App (.Force (.Builtin .TailList)) list
private def null (list : Expr) : Expr := .App (.Force (.Builtin .NullList)) list

def tests : TestTree := suite "structural" do
  test "pair_projection_runtime_types" do
    let input := sourceVar 200
    for project in [first, second] do
      let raw := Expr.Lam input (project (.Var input))
      check "unknown pair is not assumed" (alphaEq (Advanced.destructureProducts raw) raw)
      compareScript "unknown pair" raw (inputs.map fun value => [value])
      let script := Expr.Lam input (project (.App (.Builtin .UnConstrData) (trace "decode" (.Var input))))
      check "known pair projection changes" (!alphaEq (Advanced.destructureProducts script) script)
      compareScript "known pair" script (inputs.map fun value => [value])
  test "pair_unboxing_scope_and_effects" do
    let input := sourceVar 210
    let pair := sourceVar 211
    let projected := sourceVar 212
    let flag := sourceVar 213
    let bodies := [
      Expr.Constr 0 [first (.Var pair), trace "second" (second (.Var pair))],
      .Let [(projected, first (.Var pair), false)]
        (.Constr 0 [.Var projected, second (.Var pair), .Var projected]),
      .Constr 0 [first (.Var pair), .Var pair],
      .Force (.Delay (first (.Var pair))),
      .Case (.Var flag) [intLit 7, first (.Var pair)],
      .App (.Lam pair (first (.Var pair))) (boolLit true)]
    for (body, index) in bodies.zipIdx do
      let script := Expr.Lam input (.Lam flag (.Let
        [(pair, .App (.Builtin .UnConstrData) (trace "producer" (.Var input)), false)] body))
      compareScript s!"pair scope/{index}" script
        (inputs.flatMap fun value => [[value, boolLit false], [value, boolLit true]])
  test "pair_builtin_aliases_and_mkpair" do
    let input := sourceVar 220
    let pair := sourceVar 221
    let alias := sourceVar 222
    let script := Expr.Lam input (.Let
      [(alias, .Force (.Force (.Builtin .SndPair)), false),
       (pair, .App (.App (.Builtin .MkPairData) (trace "left" (.Var input)))
         (trace "right" (dataLiteral (.I 2))), false)]
      (.Constr 0 [first (.Var pair), .App (.Var alias) (.Var pair)]))
    compareScript "builtin aliases" script (inputs.map fun value => [value])
  test "shared_pair_functions_do_not_gain_allocation_cost" do
    let input := sourceVar 225
    let pair := sourceVar 226
    let cached := sourceVar 227
    let script := Expr.Lam input (.Let
      [(cached, .Force (.Force (.Builtin .FstPair)), false),
       (pair, .App (.Builtin .UnConstrData) (.Var input), false)]
      (.Constr 0 [.App (.Var cached) (.Var pair), .App (.Var cached) (.Var pair)]))
    let before ← requireTerm (lowerExpr script)
    let after ← requireTerm (lowerExpr (Advanced.destructureProducts script))
    for input in inputs do
      let argument ← requireTerm (lowerExpr input)
      let original ← observe (.Apply before argument)
      let optimized ← observe (.Apply after argument)
      checkEq "cached projection result" optimized.1 original.1
      check "cached projection CPU" (optimized.2.1 <= original.2.1)
      check "cached projection memory" (optimized.2.2 <= original.2.2)
  test "list_branch_fusion_runtime_types" do
    let input := sourceVar 230
    let list := sourceVar 231
    let body := Expr.Case (null (.Var list))
      [.Constr 0 [trace "head" (head (.Var list)), tail (.Var list)], intLit 7]
    let raw := Expr.Lam list body
    check "unknown list is not assumed" (alphaEq (Advanced.fuseListChoices raw) raw)
    compareScript "unknown list" raw (inputs.map fun value => [value])
    let script := Expr.Lam input (.Let
      [(list, .App (.Builtin .UnListData) (trace "list" (.Var input)), false)] body)
    check "known list branch changes" (!alphaEq (Advanced.fuseListChoices script) script)
    compareScript "known list" script (inputs.map fun value => [value])
  test "list_branch_fusion_preserves_empty_errors_and_shadowing" do
    let input := sourceVar 240
    let list := sourceVar 241
    let rest := sourceVar 242
    let bodies := [
      Expr.Case (null (.Var list)) [head (.Var list), head (.Var list)],
      .Case (null (.Var list)) [head (.Var list), intLit 1, .Error],
      .Case (null (.Var list))
        [.App (.Lam list (head (.Var list))) (intLit 1), intLit 2],
      .Case (null (.Var list))
        [.Let [(rest, tail (.Var list), false)]
          (.Case (null (.Var rest)) [head (.Var rest), intLit 3]), intLit 4],
      .Case (null (.Var list)) [trace "nonempty" (head (.Var list)), trace "empty" (intLit 1)]]
    for (body, index) in bodies.zipIdx do
      let script := Expr.Lam input (.Let
        [(list, .App (.Builtin .UnListData) (.Var input), false)] body)
      compareScript s!"list guards/{index}" script (inputs.map fun value => [value])
  test "frozen_validator_results_and_resource_costs" do
    let fixtures ← OpportunityBench.snapshotFixtures
    checkEq "frozen workload/input rows" fixtures.length 32
    for fixture in fixtures do
      let baseline ← requireTerm (lowerExpr fixture.script)
      let optimized ← requireTerm (lowerExpr (Advanced.structural fixture.script))
      let compiled ← requireTerm (compileOptimized fixture.script)
      for arguments in fixture.arguments do
        let before ← observe (arguments.foldl Term.Apply baseline)
        for (candidate, variant) in [optimized, compiled].zipIdx do
          let after ← observe (arguments.foldl Term.Apply candidate)
          checkEq s!"{fixture.name}/{variant}/result" after.1 before.1
          check s!"{fixture.name}/{variant}/CPU" (after.2.1 <= before.2.1)
          check s!"{fixture.name}/{variant}/memory" (after.2.2 <= before.2.2)
  test "frozen_policies_reject_malformed_runtime_shapes" do
    let fixtures := (← OpportunityBench.snapshotFixtures).filter
      (fun fixture => fixture.name.startsWith "policy/" && fixture.name.endsWith "/0")
    checkEq "policy designs" fixtures.length 5
    let values := [Moist.Plutus.Data.I 0, .B ⟨#[]⟩, .List [], .Map [], .Constr 0 []] ++
      (List.range 7).flatMap fun tag => (List.range 5).map fun count =>
        Moist.Plutus.Data.Constr 0 [.Constr 0 [], .List [.B ⟨#[1]⟩, .I 0],
          .Constr (Int.ofNat tag) (List.replicate count (.I 0))]
    for fixture in fixtures do
      let baseline ← requireTerm (lowerExpr fixture.script)
      let candidates ← [Advanced.destructureProducts, Advanced.fuseListChoices, Advanced.structural].mapM
        fun transform => requireTerm (lowerExpr (transform fixture.script))
      let compiled ← requireTerm (compileOptimized fixture.script)
      let arguments := fixture.arguments.head!
      for (value, index) in values.zipIdx do
        let supplied := arguments.take (arguments.length - 1) ++
          [Term.Constant (.Data value, .AtomicType .TypeData)]
        let expected ← observe (supplied.foldl Term.Apply baseline)
        for candidate in candidates ++ [compiled] do
          checkEq s!"{fixture.name}/malformed/{index}" (← observe (supplied.foldl Term.Apply candidate)).1 expected.1
  test "partial_builtin_inlining_retains_protocol_and_effects" do
    let input := sourceVar 250
    let partialState := sourceVar 251
    let binding := Expr.App (.Builtin .EqualsData) (.Var input)
    let script := Expr.Lam input (.Let [(partialState, binding, false)]
      (.App (.Lam (sourceVar 252) (.App (.Var partialState) (dataLiteral (.I 2))))
        (trace "before call" (intLit 0))))
    check "total partial state does not need a binding"
      (exprSize (preLowerInlineExpr script) < exprSize script)
    compareScript "partial builtin" script (inputs.map fun value => [value])
    for rhs in [Expr.App (.Builtin .EqualsData) (.Var input),
        .App (.Builtin .VerifyEd25519Signature) (.Var input),
        .App (.Builtin .UnIData) (.Var input),
        .Force (.Builtin .EqualsData),
        .App (.Builtin .EqualsData) (trace "captured" (.Var input))] do
      let script := Expr.Lam input (.Let [(partialState, rhs, false)] (trace "after" (intLit 7)))
      compareScript "strict or invalid partial state" script (inputs.map fun value => [value])
  test "generated_structural_compositions" do
    for seed in List.range 256 do
      let expression := (Differential.generate 4 [] |>.run (seed + 811)).1
      for context in Differential.contexts expression do
        let before ← Soundness.tracedObservation context
        for transform in [Advanced.destructureProducts, Advanced.fuseListChoices, Advanced.structural] do
          check s!"generated/{seed}" ((← Soundness.tracedObservation (transform context)) == before)

end Test.MIR.Opt.Structural
