import Test.MIR.OpportunityBench
import Moist.Verified.AdvancedRedexes
import Moist.Ptah.Prelude

namespace Test.MIR.Opt.Production

open Moist.MIR
open Moist.Plutus.Term
open Test.Framework

private def profiles : List Advanced.Options :=
  (List.range 8).map fun mask => {
    packApplications := mask % 2 == 1
    shareBuiltinStates := (mask / 2) % 2 == 1
    poolConstants := mask / 4 == 1 }

@[onchain]
private def sharedTextProgram (flag : Bool) (suffix : String) : String :=
  let text := "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
  if flag then Moist.Onchain.Prelude.appendString text suffix
  else Moist.Onchain.Prelude.appendString suffix text

private def ordinaryText : Term := compile! sharedTextProgram

set_option moist.optimize.poolConstants true in
private def pooledText : Term := compile! sharedTextProgram

open Moist.Ptah in
private def ptahText : Moist.Ptah.Term (PBool → PString → PString) :=
  plam fun (flag : Moist.Ptah.Term PBool) (suffix : Moist.Ptah.Term PString) =>
    let text : Moist.Ptah.Term PString := pconstant (String.mk (List.replicate 128 'x'))
    pif flag (pappendString # text # suffix) (pappendString # suffix # text)

private def nativeObservation (term : Term) : IO String := do
  match ← Moist.Plutus.Eval.evalTerm term
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return Moist.Plutus.Pretty.prettyTerm result.term
  | .error (kind, _, message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid soundness observation: {kind}: {message}")
    | _ => return "failure"

private def requireTerm (result : Except String Term) : IO Term :=
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError s!"Compilation failed: {message}")

private def observeProfiles (label : String) (expression : Expr) : IO Unit := do
  let baseline ← requireTerm (lowerExpr expression)
  let expected ← nativeObservation baseline
  let traced ← Soundness.tracedObservation expression
  for (profile, index) in profiles.zipIdx do
    let compiled ← requireTerm (compileOptimized expression 0 0 profile)
    checkEq s!"{label}/native/{index}" (← nativeObservation compiled) expected
    let after ← Soundness.tracedObservation (liftUPLC compiled)
    check s!"{label}/trace/{index}: {repr traced} != {repr after}" (traced == after)

private def traceExpression (message : String) (result : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace))
    (.Lit (.String message, .AtomicType .TypeString))) result

private def observeRuntimeInputs (label : String) (script : Expr)
    (arguments : List Expr) : IO Unit := do
  let baseline ← requireTerm (lowerExpr script)
  let checked ← requireTerm (lowerExpr (Advanced.shapeDCE script))
  let compiled ← profiles.mapM fun profile => requireTerm (compileOptimized script 0 0 profile)
  for (argument, inputIndex) in arguments.zipIdx do
    let input ← requireTerm (lowerExpr argument)
    let expected ← nativeObservation (.Apply baseline input)
    let expectedTrace ← Soundness.tracedObservation (liftUPLC (.Apply baseline input))
    for (candidate, profileIndex) in (checked :: compiled).zipIdx do
      let actual := Term.Apply candidate input
      checkEq s!"{label}/{inputIndex}/{profileIndex}/native"
        (← nativeObservation actual) expected
      let actualTrace ← Soundness.tracedObservation (liftUPLC actual)
      check s!"{label}/{inputIndex}/{profileIndex}/trace"
        (expectedTrace == actualTrace)

private def dataInputs : List Expr :=
  [intLit 0, boolLit true, .Lit (.Unit, .AtomicType .TypeUnit)] ++
  ([Moist.Plutus.Data.I (-7), .B ⟨#[0xFF]⟩, .List [], .List [.I 2, .I 3],
    .Constr 0 [], .Constr 4 [.I 5], .Map [(.I 0, .I 1)]].map
      fun datum => .Lit (.Data datum, .AtomicType .TypeData))

private def dataConsumers : List Expr :=
  let input := sourceVar 10
  let pair := sourceVar 11
  let tag := sourceVar 12
  let fields := sourceVar 13
  let head := sourceVar 14
  let tail := sourceVar 15
  let first := Expr.App (.Force (.Force (.Builtin .FstPair))) (.Var pair)
  let second := Expr.App (.Force (.Force (.Builtin .SndPair))) (.Var pair)
  let compare := Expr.App (.App (.Builtin .EqualsInteger) (.Var tag)) (intLit 0)
  let inspect := fun suffix => Expr.Lam input (.Let
    [(pair, .App (.Builtin .UnConstrData) (.Var input), false),
     (tag, first, false), (fields, second, false)] suffix)
  [inspect (.Case compare [intLit 7, intLit 7]),
   inspect (.Case compare [traceExpression "false" (intLit 1), traceExpression "true" (intLit 2)]),
   inspect (.Let [(head, .App (.Force (.Builtin .HeadList)) (.Var fields), false),
     (tail, .App (.Force (.Builtin .TailList)) (.Var fields), false)]
       (.Constr 0 [.Var head, .Var tail])),
   .Lam input (.Let [(fields, .App (.Builtin .UnListData) (.Var input), false),
     (head, .App (.Force (.Builtin .HeadList)) (.Var fields), false),
     (tail, .App (.Force (.Builtin .TailList)) (.Var fields), false)]
       (.Constr 0 [.Var head, .Var tail]))]

def tests : TestTree := suite "production" do
  test "benchmark_profiles_use_the_production_compiler" do
    let encode := fun term => (Moist.Plutus.Encode.encode_program
      (.Program (.Version 1 1 0) term)).toHexString
    for (name, options) in Opportunities.productionProfiles do
      let some (_, compile) := Opportunities.productionCandidates.find? (fun entry => entry.1 == name)
        | throw (IO.userError s!"Missing benchmark profile: {name}")
      for expression in [Test.MIR.factorialMIR, .Lam (sourceVar 9930) (.Var (sourceVar 9930))] do
        let expected ← requireTerm (compileOptimized expression 1000 5000 options)
        let actual ← requireTerm (compile expression)
        checkEq s!"{name}/exact production UPLC" (encode actual) (encode expected)
      check s!"{name}/invalid input is not silently optimized away"
        (match compile (.Let [(sourceVar 9930, .Var (sourceVar 9931), false)] (intLit 0)) with
         | .error _ => true
         | .ok _ => false)

  test "checked_arithmetic_runtime_inputs" do
    let input := sourceVar 100
    let checked := sourceVar 101
    let forms : List (BuiltinFun × Int × Bool) :=
      [(.AddInteger, 0, false), (.AddInteger, 0, true),
       (.SubtractInteger, 0, false), (.MultiplyInteger, 1, false),
       (.MultiplyInteger, 1, true), (.MultiplyInteger, 0, false),
       (.MultiplyInteger, 0, true), (.DivideInteger, 1, false),
       (.QuotientInteger, 1, false), (.RemainderInteger, 1, false), (.ModInteger, 1, false)]
    let inputs := dataInputs ++ [intLit (-5), intLit 1,
      .Lit (.Data (.I 0), .AtomicType .TypeData),
      .Lit (.Data (.I (2 ^ 300)), .AtomicType .TypeData),
      .Lit (.Data (.I (-(2 ^ 300))), .AtomicType .TypeData)]
    for (builtin, literal, reversed) in forms do
      let operation := fun value => if reversed then
        Expr.App (.App (.Builtin builtin) (intLit literal)) value
        else Expr.App (.App (.Builtin builtin) value) (intLit literal)
      let raw := Expr.Lam input (operation (.Var input))
      check s!"no source-type assumptions/{repr builtin}/{reversed}"
        (alphaEq (Advanced.shapeDCE raw) raw)
      observeRuntimeInputs "unvalidated arithmetic" raw inputs
      let script := Expr.Lam input (.Let
        [(checked, .App (.Builtin .UnIData) (.Var input), false)] (operation (.Var checked)))
      check s!"checked identity changes/{repr builtin}/{reversed}"
        (!alphaEq (Advanced.shapeDCE script) script)
      observeRuntimeInputs "checked arithmetic" script inputs
    for builtin in [BuiltinFun.SubtractInteger, .EqualsInteger,
        .LessThanInteger, .LessThanEqualsInteger] do
      let script := Expr.Lam input (.Let
        [(checked, .App (.Builtin .UnIData) (.Var input), false)]
        (.App (.App (.Builtin builtin) (.Var checked)) (.Var checked)))
      check "checked self comparison changes" (!alphaEq (Advanced.shapeDCE script) script)
      observeRuntimeInputs "self comparison" script inputs
  test "checked_data_round_trips_runtime_inputs" do
    let input := sourceVar 110
    let checked := sourceVar 111
    let alias := sourceVar 112
    let builtinAlias := sourceVar 113
    let conversions : List (BuiltinFun × BuiltinFun) :=
      [(.IData, .UnIData), (.UnIData, .IData), (.BData, .UnBData),
       (.UnBData, .BData), (.ListData, .UnListData), (.MapData, .UnMapData)]
    for (outer, inner) in conversions do
      let script := Expr.Lam input (.Let
        [(builtinAlias, .Builtin inner, false),
         (checked, .App (.Var builtinAlias) (.Var input), false),
         (alias, .Var checked, false)] (.App (.Builtin outer) (.Var alias)))
      check s!"round trip changes/{repr outer}" (!alphaEq (Advanced.shapeDCE script) script)
      observeRuntimeInputs s!"round trip/{repr outer}" script
        (dataInputs ++ [.Lit (.ByteString ⟨#[0, 255]⟩, .AtomicType .TypeByteString),
          .Lit (.Data (.B ⟨#[]⟩), .AtomicType .TypeData),
          .Lit (.Data (.Map []), .AtomicType .TypeData)])
  test "arithmetic_annihilators_preserve_strict_effects" do
    let input := sourceVar 120
    let producing := Expr.App (.App (.Builtin .AddInteger)
      (traceExpression "first" (.Var input))) (traceExpression "second" (intLit 1))
    for (builtin, literal) in [(BuiltinFun.MultiplyInteger, 0), (.RemainderInteger, 1), (.ModInteger, 1)] do
      let script := Expr.Lam input (.App (.App (.Builtin builtin) producing) (intLit literal))
      check "annihilator changes" (!alphaEq (Advanced.shapeDCE script) script)
      observeRuntimeInputs "strict annihilator" script
        (dataInputs ++ [traceExpression "input" (intLit 2), .Error])
  test "checked_value_facts_respect_shadowing" do
    let input := sourceVar 130
    let checked := sourceVar 131
    let inner := Expr.Lam checked (.App (.App (.Builtin .AddInteger) (.Var checked)) (intLit 0))
    let script := Expr.Lam input (.Let
      [(checked, .App (.Builtin .UnIData) (.Var input), false)] (.App inner (boolLit false)))
    observeRuntimeInputs "shadowed integer evidence" script dataInputs
    let nested := Expr.Lam checked (.App (.Builtin .IData) (.Var checked))
    let script := Expr.Lam input (.Let
      [(checked, .App (.Builtin .UnIData) (.Var input), false)] (.App nested (boolLit false)))
    observeRuntimeInputs "shadowed conversion evidence" script dataInputs
  test "boolean_facts_remain_branch_local" do
    let input := sourceVar 140
    let checked := sourceVar 141
    let comparison := Expr.App (.App (.Builtin .EqualsInteger)
      (.App (.Builtin .UnIData) (.Var input))) (intLit 0)
    let repeated := Expr.Case (.Var checked)
      [.Case (.Var checked) [traceExpression "false" (intLit 7), .Error],
       .Case (.Var checked) [.Error, traceExpression "true" (intLit 9)]]
    let script := Expr.Lam input (.Let [(checked, comparison, false)] repeated)
    check "branch facts remove nested checks"
      (exprSize (Advanced.shapeDCE script) < exprSize script)
    observeRuntimeInputs "branch facts" script
      (dataInputs ++ [.Lit (.Data (.I 0), .AtomicType .TypeData)])
    let shadowed := Expr.Lam checked (.Case (.Var checked) [intLit 4, intLit 5])
    let body := Expr.Constr 0 [repeated, .Case (.Var checked) [intLit 1, intLit 2],
      .App shadowed (boolLit true)]
    let script := Expr.Lam input (.Let [(checked, comparison, false)] body)
    observeRuntimeInputs "branch scope and shadowing" script
      (dataInputs ++ [.Lit (.Data (.I 0), .AtomicType .TypeData)])
    let raw := Expr.Lam checked repeated
    check "unvalidated scrutinees do not supply Boolean facts"
      (alphaEq (Advanced.shapeDCE raw) raw)
    observeRuntimeInputs "unvalidated branch facts" raw dataInputs
  test "checked_optimizations_reduce_runtime_cost" do
    let names := ["synthetic/checked-arithmetic", "synthetic/checked-data-round-trip",
      "synthetic/repeated-boolean-case"]
    let fixtures := OpportunityBench.fixtures.filter (fun fixture => names.contains fixture.name)
    checkEq "all cost fixtures are present" fixtures.length 3
    let evaluate := fun term => do
      match ← Moist.Plutus.Eval.evalTerm term
          Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
      | .ok result => pure result
      | .error failure => throw (IO.userError s!"Expected successful cost fixture: {repr failure}")
    let size := fun term => (Moist.Plutus.Encode.encode_program
      (.Program (.Version 1 1 0) term)).toByteList.length
    for fixture in fixtures do
      let baseline ← requireTerm (lowerExpr fixture.script)
      let checked ← requireTerm (lowerExpr (Advanced.shapeDCE fixture.script))
      let compiled ← requireTerm (compileOptimized fixture.script)
      for candidate in [checked, compiled] do
        check s!"{fixture.name}/smaller script" (size candidate < size baseline)
        for arguments in fixture.arguments.take 2 do
          let before ← evaluate (arguments.foldl Term.Apply baseline)
          let after ← evaluate (arguments.foldl Term.Apply candidate)
          checkEq s!"{fixture.name}/result" (Moist.Plutus.Pretty.prettyTerm after.term)
            (Moist.Plutus.Pretty.prettyTerm before.term)
          check s!"{fixture.name}/less CPU" (after.budget.cpu < before.budget.cpu)
          check s!"{fixture.name}/less memory" (after.budget.mem < before.budget.mem)
  test "adversarial_guards" do
    OpportunityBench.validateGuards
  test "native_builtin_and_projection_conformance" do
    OpportunityBench.validateNativeBuiltins
  test "native_policy_shape_matrix" do
    OpportunityBench.validatePolicyShapes
  test "generated_production_and_pass_compositions" do
    OpportunityBench.validateCandidates
  test "all_profiles_checked_data_and_traces" do
    for (consumer, consumerIndex) in dataConsumers.zipIdx do
      for (argument, argumentIndex) in dataInputs.zipIdx do
        observeProfiles s!"data/{consumerIndex}/{argumentIndex}" (.App consumer argument)
  test "typed_data_constructors_and_empty_lists" do
    let listType : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeData))
    for fields in [[], [.Data (.I 0)], [.Data (.List [])]] do
      let literal := Expr.Lit (.ConstList fields, listType)
      observeProfiles "data/list" (.App (.Builtin .ListData) literal)
      observeProfiles "data/constr" (.App (.App (.Builtin .ConstrData) (intLit 0)) literal)
    let wrongList := Expr.Lit (.ConstList [], .TypeOperator (.TypeList (.AtomicType .TypeInteger)))
    check "folding retains the empty list element type"
      (alphaEq (Advanced.foldDataConstructors (.App (.Builtin .ListData) wrongList))
        (.App (.Builtin .ListData) wrongList))
  test "recursive_and_shadowed_functions" do
    let self := sourceVar 30
    let argument := sourceVar 31
    let identity := Expr.Fix self (.Lam argument (.Var argument))
    observeProfiles "dead fix" (.App identity (intLit 7))
    let shadowed := Expr.Fix self (.Lam self (.Var self))
    observeProfiles "shadowed self" (.App shadowed (intLit 7))
    let lowered ← requireTerm (lowerExpr (.App shadowed (intLit 7)))
    checkEq "shadowed Fix parameter denotes its argument" (← nativeObservation lowered)
      (← nativeObservation (.Constant (.Integer 7, .AtomicType .TypeInteger)))
    let condition := Expr.App (.App (.Builtin .LessThanEqualsInteger) (.Var argument)) (intLit 0)
    let recur := Expr.App (.Var self) (.App (.App (.Builtin .SubtractInteger) (.Var argument)) (intLit 1))
    let countdown := Expr.Fix self (.Lam argument (.Case condition
      [traceExpression "recur" recur, intLit 0]))
    for value in [0, 1, 5] do
      observeProfiles s!"countdown/{value}" (.App countdown (intLit value))
  test "case_specialization_preserves_composite_types" do
    let first := sourceVar 70
    let second := sourceVar 71
    let integerType : BuiltinType := .AtomicType .TypeInteger
    let integerListType : BuiltinType := .TypeOperator (.TypeList integerType)
    let nestedListType : BuiltinType := .TypeOperator (.TypeList integerListType)
    let tail := Expr.Lam first (.Lam second (.Var second))
    let list := Expr.Lit (.ConstList [.Integer 1, .Integer 2], integerListType)
    observeProfiles "integer list tail" (.Case list [tail, .Error])
    let singleton := Expr.Lit (.ConstList [.Integer 1], integerListType)
    observeProfiles "empty integer list tail" (.Case singleton [tail, .Error])
    let nested := Expr.Lit (.ConstList [.ConstList []], nestedListType)
    observeProfiles "nested empty integer list" (.Case nested
      [.Lam first (.Lam second (.Var first)), .Error])
    let pairType : BuiltinType := .TypeOperator (.TypePair integerType integerListType)
    let pair := Expr.Lit (.Pair (.Integer 1, .ConstList []), pairType)
    observeProfiles "pair empty integer list" (.Case pair [tail])
  test "trace_matches_actual_optimizer" do
    for seed in List.range 64 do
      let expression := (Differential.generate 4 [] |>.run (seed + 4721)).1
      let steps := optimizeTraceExpr expression
      let some last := steps.back? | throw (IO.userError "Empty optimizer trace")
      check s!"trace result/{seed}" (alphaEq last.expr (optimizeExpr expression))
    let steps := optimizeTraceExpr (intLit 42)
    let anfSteps := steps.filter (fun step => step.pass == "ANF" || step.pass.endsWith ": ANF")
    check "trace includes ANF stages" (!anfSteps.isEmpty)
    check "unchanged ANF stages do not report a rewrite" (anfSteps.all (fun step => !step.changed))
  test "late_passes_survive_lowering" do
    let parameter := sourceVar 80
    let large := Expr.Lit (.String (String.mk (List.replicate 128 'x')), .AtomicType .TypeString)
    let script := Expr.Lam parameter (.Case (.Var parameter)
      [.Constr 0 [large], .Constr 1 [large]])
    let plain ← requireTerm (compileOptimized script 0 0 { packApplications := false })
    let pooled ← requireTerm (compileOptimized script 0 0 { poolConstants := true })
    let size := fun term => (Moist.Plutus.Encode.encode_program
      (.Program (.Version 1 1 0) term)).toByteList.length
    check "late constant pooling survives lowering" (size pooled < size plain)
    for flag in [false, true] do
      let input := Term.Constant (.Bool flag, .AtomicType .TypeBool)
      checkEq "pooled script result" (← nativeObservation (.Apply pooled input))
        (← nativeObservation (.Apply plain input))
  test "frontend_options_reach_final_lowering" do
    let size := fun term => (Moist.Plutus.Encode.encode_program
      (.Program (.Version 1 1 0) term)).toByteList.length
    check "compile! honors the size option" (size pooledText < size ordinaryText)
    let plainPtah ← match Moist.Ptah.compile ptahText with
      | .ok (.Program _ term) => pure term
      | .error message => throw (IO.userError message)
    let pooledPtah ← match Moist.Ptah.compile ptahText (options := { poolConstants := true }) with
      | .ok (.Program _ term) => pure term
      | .error message => throw (IO.userError message)
    check "Ptah honors the size option" (size pooledPtah < size plainPtah)
    for flag in [false, true] do
      let apply := fun term => Term.Apply
        (.Apply term (.Constant (.Bool flag, .AtomicType .TypeBool)))
        (.Constant (.String "suffix", .AtomicType .TypeString))
      let expected ← nativeObservation (apply ordinaryText)
      checkEq "compile! option result" (← nativeObservation (apply pooledText)) expected
      checkEq "Ptah ordinary result" (← nativeObservation (apply plainPtah)) expected
      checkEq "Ptah option result" (← nativeObservation (apply pooledPtah)) expected
  test "free_variables_remain_compilation_errors" do
    let missing := sourceVar 9999
    let unused := sourceVar 9998
    let invalid : List Expr := [
      .Var missing,
      .Let [(unused, .Var missing, false)] (intLit 7),
      .App (.Lam unused (intLit 7)) (.Delay (.Var missing)),
      .Case (boolLit true) [.Var missing, intLit 7],
      .Let [(unused, .Var unused, false)] (intLit 7),
      .Let [(unused, .Var missing, false), (missing, intLit 1, false)] (intLit 7)]
    for profile in profiles do
      for (expression, index) in invalid.zipIdx do
        check s!"unbound variable is not silently accepted/{index}"
          (match compileOptimized expression 0 0 profile with
            | .error _ => true
            | .ok _ => false)
  test "invalid_fix_bodies_remain_compilation_errors" do
    let self := sourceVar 9997
    let malformed := Expr.Fix self (intLit 7)
    for profile in profiles do
      for expression in [malformed, .Case (boolLit true) [malformed, intLit 7],
          .Let [(self, .Delay malformed, false)] (intLit 7)] do
        check "malformed Fix is not silently accepted"
          (match compileOptimized expression 0 0 profile with
            | .error _ => true
            | .ok _ => false)
  test "recursive_divergence_does_not_become_error_or_value" do
    let self := sourceVar 90
    let parameter := sourceVar 91
    let loop := Expr.App (.Fix self (.Lam parameter (.App (.Var self) (.Var parameter)))) (intLit 0)
    let checkDiverges := fun term => do
      match ← Moist.Plutus.Eval.evalTerm term 1000000 1000000 with
      | .error (.outOfBudget, _, _) => pure ()
      | outcome => throw (IO.userError s!"Expected recursive budget exhaustion: {repr outcome}")
    checkDiverges (← requireTerm (lowerExpr loop))
    for profile in profiles do
      checkDiverges (← requireTerm (compileOptimized loop 0 0 profile))

end Test.MIR.Opt.Production
