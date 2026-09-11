import Test.MIR.Opt.Opportunities
import Test.MIR.Opt.Differential
import Test.MIR.Eval.Compile
import Test.MIR.Eval.Policy

namespace Test.MIR.OpportunityBench

open Moist.MIR
open Moist.Plutus.Term
open Test.MIR.Opt.Opportunities

structure Fixture where
  name : String
  script : Expr
  arguments : List (List Term)

private def integer (number : Int) : Term :=
  .Constant (.Integer number, .AtomicType .TypeInteger)

private def bytes (value : ByteArray) : Term :=
  .Constant (.ByteString value, .AtomicType .TypeByteString)

private def dataValue (value : Moist.Plutus.Data) : Term :=
  .Constant (.Data value, .AtomicType .TypeData)

private def scriptContext (minting : Bool) (redeemer : Moist.Plutus.Data) : Term :=
  let info : Moist.Plutus.Data := if minting then .Constr 0 [.B ⟨#[0xDE, 0xAD]⟩]
    else .Constr 1 [.Constr 0 [.B ⟨#[0xAA, 0xBB, 0xCC, 0xDD]⟩, .I 0], .Constr 1 []]
  dataValue (.Constr 0 [.Constr 0 [], redeemer, info])

private def native (name : String) (script : Term) (arguments : List (List Term)) : Fixture :=
  ⟨name, liftUPLC script, arguments⟩

private def synthetic : List Fixture :=
  let parameter := sourceVar 9001
  let comparison := Expr.App (.App (.Builtin .EqualsInteger) (.Var parameter)) (intLit 0)
  let conditional := Expr.Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) comparison)
    (.Delay (intLit 7))) (.Delay (intLit 9)))
  let repeated := Expr.Lit (.String (String.mk (List.replicate 128 'x')), .AtomicType .TypeString)
  let duplicateConstants := Expr.Lam parameter
    (.Case comparison [repeated, repeated])
  let recursive := sourceVar 9002
  let delayed := sourceVar 9003
  let listBinder := sourceVar 9004
  let headBinder := sourceVar 9005
  let tailBinder := sourceVar 9006
  let listConsumer := Expr.Lam parameter
    (.Let [(listBinder, .App (.Builtin .UnListData) (.Var parameter), false)]
      (.Let [(headBinder, .App (.Force (.Builtin .HeadList)) (.Var listBinder), false),
        (tailBinder, .App (.Force (.Builtin .TailList)) (.Var listBinder), false)]
        (.Constr 0 [.Var headBinder, .Var tailBinder])))
  let checked := sourceVar 9007
  let checkedInteger := fun body => Expr.Lam parameter
    (.Let [(checked, .App (.Builtin .UnIData) (.Var parameter), false)] body)
  let arithmeticIdentity := checkedInteger
    (.App (.App (.Builtin .AddInteger)
      (.App (.App (.Builtin .MultiplyInteger) (.Var checked)) (intLit 1))) (intLit 0))
  let dataRoundTrip := checkedInteger (.App (.Builtin .IData) (.Var checked))
  let repeatedCase := Expr.Lam parameter (.Let [(checked, comparison, false)]
    (.Case (.Var checked) [.Case (.Var checked) [intLit 7, .Error],
      .Case (.Var checked) [.Error, intLit 9]]))
  [⟨"synthetic/closed-arithmetic",
      .App (.App (.Builtin .MultiplyInteger)
        (.App (.App (.Builtin .AddInteger) (intLit 20)) (intLit 1))) (intLit 2), [[]]⟩,
   ⟨"synthetic/boolean-branch", .Lam parameter conditional,
      [[integer 0], [integer 1], [.Constant (.Bool true, .AtomicType .TypeBool)]]⟩,
   ⟨"synthetic/large-constant", duplicateConstants, [[integer 0], [integer 1]]⟩,
   ⟨"synthetic/dead-fix", .Fix recursive (.Lam parameter
      (.App (.App (.Builtin .AddInteger) (.Var parameter)) (intLit 1))), [[integer 7]]⟩,
   ⟨"synthetic/delay-sharing", .Let [(delayed, .Delay (.Lam parameter (.Var parameter)), false)]
      (.App (.App (.Builtin .AddInteger)
        (.App (.Force (.Var delayed)) (intLit 1)))
        (.App (.Force (.Var delayed)) (intLit 2))), [[]]⟩,
   ⟨"synthetic/list-fusion", listConsumer,
      [[dataValue (.List [.I 1, .I 2])], [dataValue (.List [])], [integer 0]]⟩,
   ⟨"synthetic/checked-arithmetic", arithmeticIdentity,
      [[dataValue (.I 7)], [dataValue (.I (-7))], [dataValue (.B ⟨#[]⟩)]]⟩,
   ⟨"synthetic/checked-data-round-trip", dataRoundTrip,
      [[dataValue (.I 7)], [dataValue (.I (-7))], [dataValue (.B ⟨#[]⟩)]]⟩,
   ⟨"synthetic/repeated-boolean-case", repeatedCase,
      [[integer 0], [integer 1], [.Constant (.Bool true, .AtomicType .TypeBool)]]⟩]

def fixtures : List Fixture :=
  let mint := scriptContext true (.I 42)
  let wrong := scriptContext true (.I 0)
  let spend := scriptContext false (.I 42)
  let txId : ByteArray := ⟨#[0xAA, 0xBB, 0xCC, 0xDD]⟩
  let nft := scriptContext true (.List [.B txId, .I 0])
  let corrupt := scriptContext true (.I 99)
  synthetic ++
  [native "native/factorial" Eval.Compile.factorialUPLC [[integer 1], [integer 5], [integer 10]],
   native "native/tree-sum" Eval.Compile.treeSumUPLC
     [[Eval.Compile.treeLeaf5UPLC], [Eval.Compile.treeSmallUPLC], [Eval.Compile.treeBigUPLC]],
   native "native/sop-access" Eval.Compile.testingUPLC [[Eval.Compile.mkA1UPLC, Eval.Compile.mkA2UPLC]],
   native "native/construct-payment" Eval.Compile.mkTestPaymentUPLC [[]],
   native "native/construct-nested" Eval.Compile.mkTestNestedUPLC [[]],
   native "native/extract-lovelace" Eval.Compile.extractLovelaceUPLC [[Eval.Compile.mkTestPaymentUPLC]],
   native "native/extract-time" Eval.Compile.extractPOSIXTimeUPLC [[Eval.Compile.mkTestTimeUPLC]],
   native "native/match-action" Eval.Compile.matchTestActionUPLC
     [[Eval.Compile.mkTestActionPayUPLC], [Eval.Compile.mkTestActionEmptyUPLC]],
   native "policy/always" Eval.Policy.cAlwaysMint [[mint], [spend]],
   native "policy/redeemer" Eval.Policy.cRedeemerGate [[mint], [wrong], [spend]],
   native "policy/currency" Eval.Policy.cCsCheck
     [[bytes ⟨#[0xDE, 0xAD]⟩, mint], [bytes ⟨#[0xCA, 0xFE]⟩, mint], [bytes ⟨#[0xDE, 0xAD]⟩, spend]],
   native "policy/nft" Eval.Policy.cNftMint
     [[bytes txId, integer 0, nft], [bytes txId, integer 1, nft],
      [bytes txId, integer 0, corrupt], [bytes txId, integer 0, spend]],
   native "policy/list-redeemer" Eval.Policy.cMatchingRedeemerFields
     [[scriptContext true (.List [.B txId, .B txId])],
      [scriptContext true (.List [.B txId, .B ⟨#[0]⟩])],
      [scriptContext true (.List [])], [scriptContext true (.List [.B txId])],
      [scriptContext true (.List [.I 0, .B txId])],
      [scriptContext true (.I 0)], [scriptContext false (.List [.B txId, .B txId])]]]

private def lowerOrFail (expression : Expr) : IO Term := do
  match lowerExpr expression with
  | .ok term => return term
  | .error message => throw (IO.userError message)

private def scriptBytes (script : Term) : Nat :=
  (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) script)).toByteList.length

private def measure (script : Term) (arguments : List Term) : IO (String × UInt64 × UInt64) := do
  match ← Moist.Plutus.Eval.evalTerm (arguments.foldl Term.Apply script)
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return (Moist.Plutus.Pretty.prettyTerm result.term, result.budget.cpu, result.budget.mem)
  | .error (kind, budget, message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError =>
      throw (IO.userError s!"Invalid benchmark result: {kind}: {message}")
    | _ => return ("failure", budget.cpu, budget.mem)

def runFixture (fixture : Fixture)
    (variants : List (String × (Expr → Except String Term)) :=
      ("baseline", fun expression => lowerExpr expression) :: productionCandidates) : IO Unit := do
  IO.eprintln s!"Measuring {fixture.name}"
  let baseline ← lowerOrFail fixture.script
  let expected ← fixture.arguments.mapM (measure baseline)
  for (variant, transform) in variants do
    IO.eprintln s!"  {variant}"
    let start ← IO.monoMsNow
    let script ← match transform fixture.script with
      | .ok term => pure term
      | .error message => throw (IO.userError s!"{variant}: {message}")
    let size := scriptBytes script
    let elapsed := (← IO.monoMsNow) - start
    for ((arguments, index), observation) in fixture.arguments.zipIdx |>.zip expected do
      let (outcome, cpu, memory) ← measure script arguments
      checkEq s!"{fixture.name}/{variant}/{index}" outcome observation.1
      IO.println s!"{fixture.name},{index},{variant},{cpu},{memory},{size},{elapsed}"
      (← IO.getStdout).flush

private def traceExpression (message : String) (result : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace))
    (.Lit (.String message, .AtomicType .TypeString))) result

def validateGuards : IO Unit := do
  let first := sourceVar 9100
  let second := sourceVar 9101
  let third := sourceVar 9102
  let function := Expr.Lam first (traceExpression "call"
    (.Lam second (.Lam third (intLit 0))))
  let packedOrder := Expr.App (.App (.App function (intLit 1))
    (traceExpression "argument" (intLit 2))) (intLit 3)
  let eagerChoice := Expr.App (.App (.App (.Force (.Builtin .IfThenElse)) (boolLit true))
    (traceExpression "then" (intLit 1))) (traceExpression "else" (intLit 2))
  let unknownChoice := Expr.App (.Lam first
    (.App (.App (.App (.Force (.Builtin .IfThenElse)) (.Var first))
      (intLit 1)) (intLit 2))) (.Constr 1 [])
  let untypedCase := Expr.Force (.Case (.Constr 1 [])
    [.Delay (intLit 1), .Delay (intLit 2)])
  let failedValidation := Expr.Let
    [(first, .App (.Builtin .UnIData) (boolLit true), false),
     (second, .App (.App (.Builtin .EqualsInteger) (.Var first)) (intLit 0), false)]
    (.Case (.Var second) [intLit 1, intLit 1])
  let checkedComparison := Expr.App (.Lam first
    (.Case (.App (.App (.Builtin .EqualsInteger) (.Var first)) (intLit 0))
      [intLit 7, intLit 7])) (boolLit true)
  let shadowed := Expr.Let [(first, intLit 0, false)]
    (.App (.Lam first (.Case (.Var first) [intLit 1, intLit 1]))
      (.Constr 0 [traceExpression "field" (intLit 2)]))
  let delayLogging := Expr.Let [(first, .Delay (traceExpression "forced" (intLit 1)), false)]
    (.App (.App (.Builtin .AddInteger) (.Force (.Var first))) (.Force (.Var first)))
  let delayEscaping := Expr.Let [(first, .Delay (intLit 1), false)]
    (.Force (.App (.Lam second (.Var second)) (.Var first)))
  let cases := [packedOrder, eagerChoice, unknownChoice, untypedCase,
    failedValidation, checkedComparison, shadowed, delayLogging, delayEscaping]
  for (expression, index) in cases.zipIdx do
    let expected ← Opt.Soundness.tracedObservation expression
    for (name, transform) in candidates do
      let actual ← Opt.Soundness.tracedObservation (transform expression)
      check s!"guard {index}/{name}: {repr expected} != {repr actual}" (actual == expected)
  let blindPacked := Expr.Case (.Constr 0
    [intLit 1, traceExpression "argument" (intLit 2), intLit 3]) [function]
  check "application packing counterexample distinguishes trace order"
    ((← Opt.Soundness.tracedObservation packedOrder) !=
      (← Opt.Soundness.tracedObservation blindPacked))
  IO.eprintln s!"Validated {cases.length * candidates.length} adversarial guard comparisons."

def validateNativeBuiltins : IO Unit := do
  let integers : List Int := [-257, -9, -1, 0, 1, 7, 256]
  let operations : List BuiltinFun := [.AddInteger, .SubtractInteger, .MultiplyInteger,
    .DivideInteger, .QuotientInteger, .RemainderInteger, .ModInteger,
    .EqualsInteger, .LessThanInteger, .LessThanEqualsInteger]
  for operation in operations do
    for left in integers do
      for right in integers do
        let expression := Expr.App (.App (.Builtin operation) (intLit left)) (intLit right)
        let expected ← measure (← lowerOrFail expression) []
        let actual ← measure (← lowerOrFail (constantFold expression)) []
        checkEq s!"native scalar {repr operation}/{left}/{right}" actual.1 expected.1
  let dataType : BuiltinType := .AtomicType .TypeData
  let listType : BuiltinType := .TypeOperator (.TypeList dataType)
  let first := sourceVar 9200
  let second := sourceVar 9201
  let nativeDataCases :=
    [Expr.App (.App (.Builtin .ConstrData) (intLit (-1))) (.Lit (.ConstList [], listType)),
     .App (.App (.Builtin .ConstrData) (intLit 0))
       (.Lit (.ConstList [.Data (.I 42)], listType)),
     .App (.App (.Force (.Builtin .MkCons)) (intLit 3)) (.Lit (.ConstList [], listType)),
     .App (.Builtin .BData) (boolLit true),
     .Let [(first, .App (.Builtin .UnConstrData) (boolLit true), false),
       (second, .App (.Force (.Force (.Builtin .FstPair))) (.Var first), false)]
       (.Case (.App (.App (.Builtin .EqualsInteger) (.Var second)) (intLit 0))
         [intLit 7, intLit 7]),
     .Let [(first, .App (.Builtin .UnConstrData)
       (.Lit (.Data (.Constr 0 []), dataType)), false),
       (second, .App (.Force (.Force (.Builtin .FstPair))) (.Var first), false)]
       (.Case (.App (.App (.Builtin .EqualsInteger) (.Var second)) (intLit 0))
         [intLit 7, intLit 7])]
  for (expression, index) in nativeDataCases.zipIdx do
    let expected ← measure (← lowerOrFail expression) []
    for (name, transform) in candidates do
      let actual ← measure (← lowerOrFail (transform expression)) []
      checkEq s!"native data guard {index}/{name}" actual.1 expected.1
  IO.eprintln s!"Validated {operations.length * integers.length ^ 2} native scalar cases and {nativeDataCases.length * candidates.length} native data guards."
  let byteSamples : List ByteArray := [⟨#[]⟩, ⟨#[0]⟩, ⟨#[0xFF]⟩,
    ⟨#[0xC0, 0x80]⟩, ⟨#[0xC2]⟩, "héllo".toUTF8]
  let byteLiteral := fun value => Expr.Lit (.ByteString value, .AtomicType .TypeByteString)
  let stringSamples := ["", "ascii", "héllo", "🙂"]
  let stringLiteral := fun value => Expr.Lit (.String value, .AtomicType .TypeString)
  let byteCases := byteSamples.flatMap fun left =>
    [.App (.Builtin .DecodeUtf8) (byteLiteral left),
     .App (.Builtin .LengthOfByteString) (byteLiteral left)] ++
    byteSamples.flatMap fun right => [.AppendByteString, .EqualsByteString].map fun operation =>
      Expr.App (.App (.Builtin operation) (byteLiteral left)) (byteLiteral right)
  let stringCases := stringSamples.flatMap fun left =>
    [Expr.App (.Builtin .EncodeUtf8) (stringLiteral left)] ++
    stringSamples.flatMap fun right => [.AppendString, .EqualsString].map fun operation =>
      Expr.App (.App (.Builtin operation) (stringLiteral left)) (stringLiteral right)
  for (expression, index) in (byteCases ++ stringCases).zipIdx do
    let expected ← measure (← lowerOrFail expression) []
    let actual ← measure (← lowerOrFail (constantFold expression)) []
    checkEq s!"native text guard {index}" actual.1 expected.1
  IO.eprintln s!"Validated {byteCases.length + stringCases.length} native byte/string cases."
  let projection := Expr.App (.Force (.Force (.Builtin .FstPair)))
    (.App (.Builtin .UnConstrData) (.Lit (.Data (.Constr 0 []), dataType)))
  let leanResult ← Opt.Soundness.observation projection
  let nativeResult ← measure (← lowerOrFail projection) []
  checkEq "UnConstrData model/native projection agreement" leanResult nativeResult.1

def validatePolicyShapes : IO Unit := do
  let txId : ByteArray := ⟨#[0xAA, 0xBB, 0xCC, 0xDD]⟩
  let redeemer : Moist.Plutus.Data := .List [.B txId, .I 0]
  let contextValues :=
    [Moist.Plutus.Data.I 0, .B ⟨#[]⟩, .List [], .Constr 0 []] ++
    (List.range 7).flatMap (fun tag =>
      (List.range 5).map fun count => Moist.Plutus.Data.Constr 0
        [.Constr 0 [], redeemer, .Constr (Int.ofNat tag) (List.replicate count (.I 0))])
  let script := liftUPLC Eval.Policy.cNftMint
  for (name, transform) in candidates do
    let before ← lowerOrFail script
    let after ← lowerOrFail (transform script)
    for (value, index) in contextValues.zipIdx do
      let arguments := [bytes txId, integer 0, dataValue value]
      let expected ← measure before arguments
      let actual ← measure after arguments
      checkEq s!"native policy shape {index}/{name}" actual.1 expected.1
  IO.eprintln s!"Validated {contextValues.length * candidates.length} native policy shape comparisons."

def validateCandidates (count : Nat := 1024) : IO Unit := do
  for seed in List.range count do
    let expression := (Opt.Differential.generate (3 + seed % 2) [] |>.run (seed + 1729)).1
    for (context, index) in (Opt.Differential.contexts expression).zipIdx do
      let expected ← Opt.Soundness.tracedObservation context
      for (name, transform) in productionCandidates do
        let compiled ← match transform context with
          | .ok term => pure term
          | .error message => throw (IO.userError s!"{name}: {message}")
        let actual ← Opt.Soundness.tracedObservation (liftUPLC compiled)
        check s!"candidate {name}, seed={seed}, context={index}: {repr expected} != {repr actual}"
          (actual == expected)
  IO.eprintln s!"Validated {count * 6 * productionCandidates.length} candidate comparisons, including traces."

private def byteBits (byte : UInt8) : List Bool :=
  let bits := byte.toBitVec
  (List.range 8).map (fun index => bits.getLsbD (7 - index))

def externalFixtures (directory : System.FilePath) (limit : Nat) : IO (List Fixture) := do
  let entries ← directory.readDir
  let files := entries.toList.filter (fun entry => entry.fileName.endsWith ".flat")
  let files := files.mergeSort (fun left right => left.fileName <= right.fileName)
  (files.take limit).mapM fun entry => do
    let content ← IO.FS.readBinFile entry.path
    match Moist.Plutus.Decode.Internal.decodeProgramFromBits (content.toList.flatMap byteBits) with
    | some (.Program _ term) => return native s!"external/{entry.fileName}" term [[]]
    | none => throw (IO.userError s!"Cannot decode {entry.path}")

def snapshotFixtures (path : System.FilePath := "docs/benchmarks/mir-structural-baseline.csv")
    : IO (List Fixture) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let decode := fun encoded => do
    match Moist.Plutus.Decode.Internal.decodeProgramFromHexString encoded with
    | some (.Program _ term) => pure term
    | none => throw (IO.userError "Invalid frozen UPLC encoding")
  (lines.drop 1 |>.filter (· != "")).mapM fun line => do
    match line.splitOn "," with
    | [name, index, script, arguments] =>
      let arguments ← if arguments.isEmpty then pure [] else (arguments.splitOn ";").mapM decode
      return native s!"{name}/{index}" (← decode script) [arguments]
    | _ => throw (IO.userError s!"Invalid frozen fixture row: {line}")

private def compileCore (structural : Expr → Expr) (expression : Expr) : Except String Term := do
  let prepared := Advanced.preLower (preLowerInlineExpr (optimizeExpr expression))
  let lowered ← lowerExpr (structural prepared)
  lowerExpr (Advanced.finish (liftUPLC lowered))

def structuralVariants : List (String × (Expr → Except String Term)) :=
  [("baseline", fun expression => lowerExpr expression),
   ("prelower-only", fun expression => lowerExpr (preLowerInlineExpr expression)),
   ("core-pipeline", compileCore id),
   ("core-pair-products", compileCore Advanced.destructureProducts),
   ("core-list-choices", compileCore Advanced.fuseListChoices),
   ("pair-products", fun expression => lowerExpr (Advanced.destructureProducts expression)),
   ("list-choices", fun expression => lowerExpr (Advanced.fuseListChoices expression)),
   ("structural", fun expression => lowerExpr (Advanced.structural expression)),
   ("production-default", production)]

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | "--structural-external" :: directory :: filenames =>
    IO.println "fixture,input,variant,cpu,memory,bytes,compile_ms"
    for filename in filenames do
      let content ← IO.FS.readBinFile (System.FilePath.mk directory / filename)
      let some (.Program _ term) := Moist.Plutus.Decode.Internal.decodeProgramFromBits (content.toList.flatMap byteBits)
        | throw (IO.userError s!"Cannot decode {filename}")
      runFixture (native s!"external/{filename}" term [[]]) structuralVariants
    return 0
  | _ => pure ()
  if arguments.contains "--structural" then
    IO.println "fixture,input,variant,cpu,memory,bytes,compile_ms"
    for fixture in ← snapshotFixtures do
      runFixture fixture structuralVariants
    return 0
  if arguments.contains "--snapshot-validators" then
    let encode := fun term => (Moist.Plutus.Encode.encode_program
      (.Program (.Version 1 1 0) term)).toHexString
    IO.println "fixture,input,script,arguments"
    for fixture in fixtures.filter (fun fixture => !fixture.name.startsWith "synthetic/") do
      let script ← lowerOrFail fixture.script
      for (arguments, index) in fixture.arguments.zipIdx do
        IO.println s!"{fixture.name},{index},{encode script},{String.intercalate ";" (arguments.map encode)}"
    return 0
  validateGuards
  validateNativeBuiltins
  validatePolicyShapes
  validateCandidates
  unless arguments.contains "--validate-only" do
    IO.println "fixture,input,variant,cpu,memory,bytes,compile_ms"
    let cases ← match arguments with
      | "--external" :: directory :: limit :: _ => externalFixtures directory (limit.toNat?.getD 16)
      | _ => pure fixtures
    for fixture in cases do
      runFixture fixture
  return 0

end Test.MIR.OpportunityBench
