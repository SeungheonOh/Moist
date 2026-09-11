import Test.MIR.Opt.Soundness
import Test.MIR.Opt.SoundnessAudit
import Moist.MIR.Compile

namespace Test.MIR.Opt.FormalCoverage

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private partial def referenceDataFold (expression : Expr) : Expr :=
  Advanced.foldDataConstructor (Advanced.mapChildren referenceDataFold expression)

private partial def referenceScalarFold (expression : Expr) : Expr :=
  if expression.isAtom then expression else
    Advanced.foldConstant (Advanced.mapChildren referenceScalarFold expression)

private partial def referenceDeadFix (expression : Expr) : Expr :=
  Advanced.eliminateDeadFixRoot (Advanced.mapChildren referenceDeadFix expression)

private partial def referencePacking (minimum : Nat) (expression : Expr) : Expr :=
  match expression with
  | .App _ _ =>
    let (function, arguments) := Advanced.applicationSpine expression
    let function' := referencePacking minimum function
    let arguments' := arguments.map (referencePacking minimum)
    if arguments'.length >= minimum && arguments'.all isPure then
      .Case (.Constr 0 arguments') [function']
    else arguments'.foldl Expr.App function'
  | _ => Advanced.mapChildren (referencePacking minimum) expression

private def checkTraversal (expression : Expr) : IO Unit := do
  check "total data traversal preserves the original rewrite output"
    (Advanced.foldDataConstructors expression == referenceDataFold expression)
  check "total scalar traversal preserves the original rewrite output"
    (Advanced.constantFold expression == referenceScalarFold expression)
  check "total dead-Fix traversal preserves the original rewrite output"
    (Advanced.eliminateDeadFix expression == referenceDeadFix expression)
  for minimum in [0, 1, 2, 3, 8] do
    check "total packing traversal preserves the original spine rewrite output"
      (Advanced.packApplications minimum expression == referencePacking minimum expression)
  for environment in [[], [sourceVar 0, sourceVar 1, sourceVar 2],
      [sourceVar 9900, sourceVar 9901, sourceVar 9902]] do
    check "binder freshening preserves exact total lowering"
      (reprStr (lowerTotalExpr environment (uniqueOptimizationBinders expression)) ==
        reprStr (lowerTotalExpr environment expression))

def tests : TestTree := suite "formal-coverage" do
  test "shared_analysis_preserves_scope_and_evaluation_boundaries" do
    let alias := sourceVar 9930
    let target := sourceVar 9931
    let environment := [(alias, .Var target), (target, Expr.Builtin .AddInteger)]
    check "zero fuel leaves an alias unresolved"
      (Advanced.resolveHead 0 environment (.Var alias) == .Var alias)
    check "one step follows exactly one alias"
      (Advanced.resolveHead 1 environment (.Var alias) == .Var target)
    check "the nearest binding wins"
      (Advanced.resolveHead 8 ((alias, intLit 7) :: environment) (.Var alias) == intLit 7)
    check "head resolution does not evaluate or substitute arguments"
      (Advanced.resolveHead 8 environment (.App (.Var alias) (.Var alias)) ==
        .App (.Builtin .AddInteger) (.Var alias))
    check "cyclic aliases stop at the fuel limit"
      (Advanced.resolveHead 64 [(alias, .Var target), (target, .Var alias)] (.Var alias) == .Var alias)
    let fallibleArgument := Expr.App (.Builtin .AddInteger) .Error
    check "post-success protocol is not a totality certificate"
      ((Advanced.builtinProtocolAfterSuccess fallibleArgument).isSome &&
        (builtinRemainder fallibleArgument).isNone)
    for invalid in [Expr.Force (.Builtin .AddInteger),
        .App (.Builtin .HeadList) (intLit 0),
        .Force (.Force (.Builtin .HeadList))] do
      check "post-success protocol still rejects invalid force/application order"
        ((Advanced.builtinProtocolAfterSuccess invalid).isNone)
    let arguments := (List.range 128).map (fun index => intLit (Int.ofNat index))
    let application := arguments.foldl Expr.App (.Var alias)
    check "application spines preserve left-to-right arguments"
      (Advanced.applicationSpine application == (.Var alias, arguments))

  test "certified_traversals_preserve_generated_rewrites" do
    for seed in List.range 512 do
      let expression := ((Differential.generate 5 []).run (seed + 991)).1
      checkTraversal expression

  test "certified_traversals_reach_deep_children" do
    let arithmetic := Expr.App (.App (.Builtin .AddInteger) (intLit 20)) (intLit 22)
    let datum := Expr.App (.Builtin .IData) (intLit 42)
    let wrappers : List (Expr → Expr) :=
      [fun body => .Lam (sourceVar 9900) body,
       Expr.Delay, fun body => .Force (.Delay body),
       fun body => .Let [(sourceVar 9900, body, false)] (intLit 0),
       fun body => .Constr 0 [intLit 0, body],
       fun body => .Case (boolLit true) [intLit 0, body],
       fun body => .Fix (sourceVar 9900) (.Lam (sourceVar 9901) body)]
    for wrapper in wrappers do
      for root in [arithmetic, datum, Expr.Fix (sourceVar 9902) (.Lam (sourceVar 9903) (intLit 42)),
          Expr.App (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)) (intLit 3)] do
        let expression := (List.range 64).foldl (fun body _ => wrapper body) root
        checkTraversal expression

  test "production_inline_rejects_divergent_predecessor" do
    let binder := sourceVar 9900
    let argument := sourceVar 9901
    let selfApply := Expr.Lam argument (.App (.Var argument) (.Var argument))
    let body := Expr.App (.App selfApply selfApply) (.Var binder)
    check "strict occurrence alone would accept this use" (!occursInDeferred binder body)
    check "evaluation frontier rejects a diverging predecessor" (!firstEvaluationUse binder body)
    let expression := Expr.Let [(binder,.Error,false)] body
    SoundnessAudit.compare "divergent-predecessor" expression

  test "certified_dead_fix_preserves_scope_and_deferred_effects" do
    let recursive := sourceVar 9900
    let parameter := sourceVar 9901
    let captured := sourceVar 9902
    let identity := Expr.Fix recursive (.Lam parameter (.Var parameter))
    let shadowed := Expr.Fix recursive (.Lam recursive (.Var recursive))
    let failing := Expr.Fix recursive (.Lam parameter .Error)
    let captures := Expr.Let [(captured, intLit 42, false)]
      (.App (.Fix recursive (.Lam parameter (.Var captured))) (intLit 0))
    check "nonrecursive closure is removed"
      (Advanced.eliminateDeadFix identity == .Lam parameter (.Var parameter))
    check "lambda shadowing hides the recursive identifier"
      (Advanced.eliminateDeadFix shadowed == .Lam recursive (.Var recursive))
    for expression in [identity, shadowed, failing, .App failing (intLit 0), captures] do
      SoundnessAudit.compare "certified-dead-fix" expression

  test "builtin_state_totality_rejects_saturation_and_effectful_arguments" do
    let partialAdd := Expr.App (.Builtin .AddInteger) (intLit 2)
    let saturatedAdd := Expr.App partialAdd (intLit 3)
    let invalidProtocol := Expr.Force (.Builtin .AddInteger)
    let effectfulArgument := Expr.App (.Builtin .AddInteger) .Error
    check "an unsaturated builtin state is total" (isTotalPreLowerValue partialAdd)
    check "an unsaturated value-argument state is callable" (isCallableValue partialAdd)
    for rejected in [saturatedAdd, invalidProtocol, effectfulArgument] do
      check "unchecked builtin evaluation is not a total pre-lowering value" (!isTotalPreLowerValue rejected)

  test "certified_packing_handles_general_arity_and_deferred_values" do
    let captured := sourceVar 9904
    let parameter := sourceVar 9905
    let pureArguments := [intLit 7, boolLit true, Expr.Delay .Error,
      .Lam parameter (.Var captured), .Force (.Delay (intLit 9)), .Constr 0 [intLit 2]]
    let functions := [Expr.Error, intLit 0, Expr.Builtin .AddInteger,
      .Force (.Builtin .IfThenElse), .Lam parameter (.Var parameter)]
    for function in functions do
      for count in List.range 13 do
        let arguments := (List.range count).map fun index => pureArguments[index % pureArguments.length]!
        let expression := Expr.Let [(captured, intLit 42, false)] (arguments.foldl Expr.App function)
        for minimum in [0, 1, 2, 3, 8] do
          let packed := Advanced.packApplications minimum expression
          check "packing preserves the original full spine" (packed == referencePacking minimum expression)
          Soundness.preserves "general-arity-packing" expression packed
    let effectful := Expr.App (.App (.App (.Lam parameter (.Var parameter)) (intLit 0)) .Error) (intLit 2)
    check "packing does not move an erroring argument"
      (Advanced.packApplications 3 effectful == referencePacking 3 effectful)

  test "list_shape_facts_require_runtime_list_payloads" do
    let list := sourceVar 9910
    let head := sourceVar 9911
    let tail := sourceVar 9912
    let annotation := BuiltinType.TypeOperator (.TypeList (.AtomicType .TypeInteger))
    for payload in [Const.Integer 0, .Integer 1, .Bool false, .Bool true, .Unit,
        .Pair (.Integer 1, .Integer 2), .Data (.List [])] do
      let literal := Expr.Lit (payload, annotation)
      let projections := Expr.Let [(list, literal, false),
        (head, .App (.Force (.Builtin .HeadList)) (.Var list), false),
        (tail, .App (.Force (.Builtin .TailList)) (.Var list), false)] (intLit 42)
      let choice := Expr.Let [(list, literal, false)]
        (.Case (.App (.Force (.Builtin .NullList)) (.Var list)) [intLit 42, intLit 0])
      for expression in [projections, choice] do
        checkEq "malformed list source fails" (← Soundness.observation expression) "failure"
        for transform in [Advanced.fuseListDestructors, Advanced.fuseListChoices, Advanced.simplifyChoices,
            Advanced.shapeDCE, Advanced.simplify, Advanced.structural] do
          Soundness.preserves "list-payload-evidence" expression (transform expression)

  test "list_shape_facts_retain_native_list_representations" do
    let list := sourceVar 9920
    let head := sourceVar 9921
    let tail := sourceVar 9922
    let datum := BuiltinType.AtomicType .TypeData
    let literalLists : List (Const × BuiltinType) :=
      [(.ConstList [.Integer 7], .TypeOperator (.TypeList (.AtomicType .TypeInteger))),
       (.ConstDataList [.I 7], .TypeOperator (.TypeList datum)),
       (.ConstPairDataList [(.I 7, .I 8)], .TypeOperator (.TypeList (.TypeOperator (.TypePair datum datum))))]
    for literal in literalLists do
      check "runtime list representations remain eligible" (Advanced.knownList 1 [] (.Lit literal))
      let expression := Expr.Let [(list, .Lit literal, false),
        (head, .App (.Force (.Builtin .HeadList)) (.Var list), false),
        (tail, .App (.Force (.Builtin .TailList)) (.Var list), false)] (intLit 42)
      SoundnessAudit.compare "native-list-representations" expression

  test "data_folding_preserves_reference_list_representation" do
    let dataType := BuiltinType.AtomicType .TypeData
    let empty := Expr.Lit (.ConstList [],.TypeOperator (.TypeList dataType))
    let constructed := Expr.App (.App (.Force (.Builtin .MkCons))
      (.Lit (.Data (.I 3),dataType))) empty
    let consumed := Expr.App (.App (.Force (.Builtin .MkCons)) (intLit 7)) constructed
    let expression := Expr.Let [(sourceVar 9900,consumed,false)] (intLit 9)
    let before ← Soundness.tracedObservation expression
    let after ← Soundness.tracedObservation (Advanced.foldDataConstructors expression)
    check s!"Data folding changed reference semantics: {repr before} != {repr after}" (before == after)

  test "data_folding_preserves_representation_in_all_pipelines" do
    let dataType := BuiltinType.AtomicType .TypeData
    let annotation := BuiltinType.TypeOperator (.TypeList dataType)
    for fields in [[], [Moist.Plutus.Data.I 5]] do
      for representation in [Const.ConstList (fields.map Const.Data), .ConstDataList fields] do
        let constructed := Expr.App (.App (.Force (.Builtin .MkCons))
          (.Lit (.Data (.I 3),dataType))) (.Lit (representation,annotation))
        for head in [intLit 7, .Lit (.Data (.I 7),dataType)] do
          let consumed := Expr.App (.App (.Force (.Builtin .MkCons)) head) constructed
          let expression := Expr.Let [(sourceVar 9900,consumed,false)] (intLit 9)
          SoundnessAudit.compare "data-list-representation" expression

  test "data_folding_keeps_native_encoding_identical" do
    let dataType := BuiltinType.AtomicType .TypeData
    let annotation := BuiltinType.TypeOperator (.TypeList dataType)
    for fields in [[], [Moist.Plutus.Data.I 5], [.I 5, .B ByteArray.empty]] do
      let constructed := Expr.App (.App (.Force (.Builtin .MkCons))
        (.Lit (.Data (.I 3),dataType))) (.Lit (.ConstList (fields.map Const.Data),annotation))
      let folded := Advanced.foldDataConstructors constructed
      check "folding retains the generic list" (folded ==
        .Lit (.ConstList ((Moist.Plutus.Data.I 3 :: fields).map Const.Data),annotation))
      let encodedGeneric := Moist.Plutus.Encode.encode_program
        (.Program (.Version 1 1 0) (.Constant
          (.ConstList ((Moist.Plutus.Data.I 3 :: fields).map Const.Data),annotation)))
      let encodedSpecialized := Moist.Plutus.Encode.encode_program
        (.Program (.Version 1 1 0) (.Constant (.ConstDataList (.I 3 :: fields),annotation)))
      check "representation repair changes no Flat bytes"
        (encodedGeneric.toByteList == encodedSpecialized.toByteList)

end Test.MIR.Opt.FormalCoverage
