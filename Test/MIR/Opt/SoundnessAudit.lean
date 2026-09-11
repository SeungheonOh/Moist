import Test.MIR.Opt.Differential
import Moist.MIR.Compile

namespace Test.MIR.Opt.SoundnessAudit

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def parameter := sourceVar 9100
private def recursive := sourceVar 9101
private def counter := sourceVar 9102
private def callback := sourceVar 9103
private def saved := sourceVar 9104
private def duplicate := sourceVar 9105

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message,.AtomicType .TypeString))) body

private def booleanConsumer (condition : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) condition)
    (.Delay (trace "true" (intLit 11)))) (.Delay (trace "false" (intLit 22))))

private def transformations : List (String × (Expr → Expr)) :=
  [("static",Advanced.staticArguments),
   ("known-constructor-cases",fun expression => (caseMergePass expression).1),
   ("choices",Advanced.simplifyChoices),
   ("shape-DCE",Advanced.shapeDCE),
   ("list-destructors",Advanced.fuseListDestructors),
   ("list-choices",Advanced.fuseListChoices),
   ("products",Advanced.destructureProducts),
   ("checked-branches",Advanced.fuseCheckedListBranches),
   ("delayed-list-choices",Advanced.lowerDelayedListChoices),
   ("checked-combined",Advanced.optimizeCheckedBranches),
   ("delayed-sharing",Advanced.shareDelayedValues),
   ("dead-fix",Advanced.eliminateDeadFix),
   ("scalar-fold",Advanced.constantFold),
   ("data-fold",Advanced.foldDataConstructors),
   ("packing",Advanced.packApplications 2),
   ("builtin-sharing",Advanced.hoistBuiltinStates 2),
   ("constant-pooling",Advanced.poolConstants 1)]

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
      throw (IO.userError s!"Inconclusive native observation: {kind}: {message}")
    | _ => return "failure"

def compare (label : String) (expression : Expr) : IO Unit := do
  let original ← requireTerm (lowerExpr expression)
  let expected ← observe original
  let expectedTrace ← Soundness.tracedObservation expression
  let candidates ← transformations.mapM fun (name,transform) => do
    return (name,← requireTerm (lowerExpr (transform expression)))
  let production ← (List.range 8).mapM fun mask => do
    let term ← requireTerm (compileOptimized expression 0 0 {
      packApplications := mask % 2 == 1
      shareBuiltinStates := (mask / 2) % 2 == 1
      poolConstants := mask / 4 == 1 })
    return (s!"production-{mask}",term)
  for (name,candidate) in candidates ++ production do
    let actual ← observe candidate
    check s!"{label}/{name}/native: {expected} != {actual}\n{repr expression}" (actual == expected)
    let actualTrace ← Soundness.tracedObservation (liftUPLC candidate)
    check s!"{label}/{name}/trace: {repr expectedTrace} != {repr actualTrace}\n{repr expression}"
      (actualTrace == expectedTrace)

private def contexts (expression : Expr) : List Expr :=
  Differential.contexts expression ++
    [booleanConsumer expression,booleanConsumer (.App expression (boolLit true)),
      booleanConsumer (.Force expression)]

private def worker (base next : Expr) : Expr :=
  .Fix recursive (.Lam parameter (.Lam counter
    (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Var counter)) (intLit 0))
      [.App (.App (.Var recursive) next)
        (.App (.App (.Builtin .SubtractInteger) (.Var counter)) (intLit 1)),base])))

def tests : TestTree := suite "soundness-audit" do
  test "all_new_passes_and_option_combinations_generated_terms" do
    for seed in List.range 64 do
      let expression := (Differential.generate (3 + seed % 2) [] |>.run (seed + 1729)).1
      for (context,index) in (contexts expression).zipIdx do
        compare s!"generated/{seed}/{index}" context
    IO.println "14,400 new-pass/production comparisons, native results and Lean CEK traces."
  test "higher_order_recursive_result_summaries" do
    let bases := [Expr.Var parameter,boolLit true,intLit 0,.Error,
      trace "base" (boolLit false),.Delay (.Var parameter),
      .Lam callback (.Var parameter),
      .App (.Var parameter) (intLit 0)]
    for (base,baseIndex) in bases.zipIdx do
      for (next,nextIndex) in [Expr.Var parameter,intLit 0,boolLit false].zipIdx do
        for (argument,argumentIndex) in [boolLit true,intLit 0,
            Expr.Lam callback (boolLit true)].zipIdx do
          for count in [0,2] do
            let expression := Expr.App (.App (worker base next) argument) (intLit count)
            for (context,index) in [booleanConsumer expression,
                booleanConsumer (.Force expression),booleanConsumer (.App expression (intLit 7))].zipIdx do
              compare s!"recursive/{baseIndex}/{nextIndex}/{argumentIndex}/{count}/{index}" context
  test "closure_contexts_and_repeated_aliases" do
    let producers := [Expr.Lam parameter (.Var parameter),
      .Lam parameter (.Delay (.Var parameter)),
      .Lam parameter (.Lam callback (.Var parameter)),
      .Lam parameter (.Let [(saved,.Var parameter,false)]
        (.App (.Lam callback (.Var saved)) (intLit 0))),
      .Lam parameter (.Let [(saved,.Var parameter,false),(parameter,boolLit true,false)] (.Var saved))]
    for (producer,producerIndex) in producers.zipIdx do
      for (first,firstIndex) in [boolLit true,intLit 0].zipIdx do
        for (second,secondIndex) in [boolLit false,intLit 1].zipIdx do
          let expression := Expr.Let [(callback,producer,false),
              (saved,.App (.Var callback) first,false),
              (duplicate,.App (.Var callback) second,false)]
            (booleanConsumer (.Var duplicate))
          compare s!"closure/{producerIndex}/{firstIndex}/{secondIndex}" expression
  test "partial_builtin_states_preserve_validation_timing" do
    let builtins : List (BuiltinFun × Nat × Nat) := [(.AddInteger,0,2),(.IfThenElse,1,3),
      (.ChooseList,2,3),(.MkCons,1,2),(.ConstrData,0,2),(.Trace,1,2),(.ChooseData,1,6)]
    for (builtin,forces,arity) in builtins do
      let selector := (List.range forces).foldl (fun expression _ => Expr.Force expression) (.Builtin builtin)
      for supplied in List.range arity do
        for (argument,index) in [intLit 0,boolLit true,.Lam parameter (.Var parameter),
            .Delay .Error,.Constr 0 []].zipIdx do
          let partialState := (List.range supplied).foldl (fun function _ => Expr.App function argument) selector
          let duplicated := Expr.Let [(saved,partialState,false),(duplicate,partialState,false)]
            (.Let [(parameter,.Constr 0 [.Var saved,.Var duplicate],false)] (intLit 7))
          compare s!"partial/{repr builtin}/{supplied}/{index}" duplicated
          compare s!"forced-partial/{repr builtin}/{supplied}/{index}"
            (.Let [(saved,trace "before" (intLit 0),false)] (.Force partialState))
  test "constant_case_branch_counts" do
    let listType := BuiltinType.TypeOperator (.TypeList (.AtomicType .TypeInteger))
    let dataListType := BuiltinType.TypeOperator (.TypeList (.AtomicType .TypeData))
    let values := [Expr.Lit (.ConstList [],listType),.Lit (.ConstList [.Integer 3],listType),
      .Lit (.ConstDataList [],dataListType),.Lit (.ConstDataList [.I 3],dataListType)]
    for (value,index) in values.zipIdx do
      for count in List.range 5 do
        let alternatives := [Expr.Lam saved (.Lam duplicate (intLit 7)),intLit 8,
          trace "unreachable" (intLit 9),.Error]
        compare s!"list-case/{index}/{count}" (.Case value (alternatives.take count))
        compare s!"aliased-list-case/{index}/{count}" (.Let [(parameter,value,false),
          (callback,.Var parameter,false)] (.Case (.Var callback) (alternatives.take count)))
  test "folding_native_boundary_equivalence" do
    for builtin in [BuiltinFun.AddInteger,.SubtractInteger,.MultiplyInteger,.DivideInteger,
        .QuotientInteger,.RemainderInteger,.ModInteger,.EqualsInteger,
        .LessThanInteger,.LessThanEqualsInteger] do
      for (first,second) in [(Int.negSucc 0,0),(-7,3),(7,-3),(-7,-3),
          (2 ^ 255,3),(-(2 ^ 255),-3),(2 ^ 256,1)] do
        compare s!"scalar/{repr builtin}/{first}/{second}"
          (.App (.App (.Builtin builtin) (intLit first)) (intLit second))
    for (bytes,index) in [ByteArray.mk #[],⟨#[0x61,0]⟩,⟨#[0xC0,0xAF]⟩,
        ⟨#[0xED,0xA0,0x80]⟩,⟨#[0xF4,0x8F,0xBF,0xBF]⟩,⟨#[0xF4,0x90,0x80,0x80]⟩,
        ⟨Array.replicate 1025 0x61⟩].zipIdx do
      compare s!"utf8/{index}" (.App (.Builtin .DecodeUtf8)
        (.Lit (.ByteString bytes,.AtomicType .TypeByteString)))
    let fields := Expr.Lit (.ConstDataList [.I 3],.TypeOperator (.TypeList (.AtomicType .TypeData)))
    for tag in [Int.negSucc 0,0,6,7,127,128,2 ^ 64 - 1,2 ^ 64] do
      let constructed := Expr.App (.App (.Builtin .ConstrData) (intLit tag)) fields
      compare s!"data-tag/{tag}" (.Let [(saved,constructed,false)] (intLit 7))

end Test.MIR.Opt.SoundnessAudit
