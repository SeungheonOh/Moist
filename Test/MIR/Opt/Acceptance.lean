import Test.MIR.Opt.SoundnessAudit

namespace Test.MIR.Opt.Acceptance

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def input := sourceVar 12000
private def checked := sourceVar 12001
private def saved := sourceVar 12002
private def other := sourceVar 12003
private def recursive := sourceVar 12004
private def counter := sourceVar 12005

private def unit : Expr := .Lit (.Unit, .AtomicType .TypeUnit)
private def datum (value : Moist.Plutus.Data) : Expr := .Lit (.Data value, .AtomicType .TypeData)
private def unary (builtin : BuiltinFun) (argument : Expr) : Expr := .App (.Builtin builtin) argument
private def binary (builtin : BuiltinFun) (first second : Expr) : Expr :=
  .App (.App (.Builtin builtin) first) second
private def listCall (builtin : BuiltinFun) (argument : Expr) : Expr :=
  .App (.Force (.Builtin builtin)) argument
private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

def inputs : List Expr :=
  [intLit (-1), intLit 0, intLit 1, intLit (2 ^ 256), boolLit false, boolLit true, unit,
   .Lit (.ByteString ⟨#[0, 255]⟩, .AtomicType .TypeByteString),
   .Lit (.String "input", .AtomicType .TypeString),
   .Constr 0 [], .Constr 1 [], .Constr 0 [intLit 1, intLit 2],
   .Delay .Error, .Delay (boolLit true), .Lam saved (.Var saved), .Lam saved .Error,
   .Error, trace "argument" (datum (.I 3))] ++
  ([Moist.Plutus.Data.I 0, .I 3, .B ⟨#[]⟩, .List [], .List [.I 3],
    .List [.I 3, .B ⟨#[1]⟩], .Map [], .Map [(.I 0, .I 1)],
    .Constr 0 [], .Constr 1 [.I 3]].map datum) ++
  [Expr.Lit (.ConstList [], .TypeOperator (.TypeList (.AtomicType .TypeInteger))),
   .Lit (.ConstList [.Integer 3, .Integer 4], .TypeOperator (.TypeList (.AtomicType .TypeInteger))),
   .Lit (.ConstDataList [], Advanced.dataListType),
   .Lit (.ConstDataList [.I 3, .I 4], Advanced.dataListType),
   .Lit (.PairData (.I 3, .I 4), .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData))),
   .Lit (.ConstPairDataList [(.I 3, .I 4)], .TypeOperator (.TypeList
     (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)))))]

def transformations : List (String × (Expr → Expr)) :=
  Soundness.transformations ++ SoundnessAudit.transformations ++
  [("hygiene", uniqueOptimizationBinders),
   ("structural", Advanced.structural),
   ("advanced-pre-lower", Advanced.preLower),
   ("prepare-for-lowering", prepareForLowering)]

def candidates (script : Expr) : Except String (List (String × Term)) := do
  let individual ← transformations.mapM fun (name, transform) => do
    return (name, ← lowerExpr (transform script))
  let production ← (List.range 8).mapM fun mask => do
    return (s!"production-{mask}", ← compileOptimized script 0 0 {
      packApplications := mask % 2 == 1
      shareBuiltinStates := (mask / 2) % 2 == 1
      poolConstants := mask / 4 == 1 })
  return individual ++ production

private def listBody : Expr :=
  .Let [(saved, listCall .HeadList (.Var checked), false),
    (other, listCall .TailList (.Var checked), false)] (.Constr 0 [.Var saved, .Var other])

private def chooseList (value empty nonempty : Expr) : Expr :=
  .Force (.App (.App (.App (.Force (.Force (.Builtin .ChooseList))) value)
    (.Delay empty)) (.Delay nonempty))

private def loop (base next : Expr) : Expr :=
  .Fix recursive (.Lam input (.Lam counter
    (.Case (binary .LessThanEqualsInteger (.Var counter) (intLit 0))
      [.App (.App (.Var recursive) next) (binary .SubtractInteger (.Var counter) (intLit 1)), base])))

def scripts : List (String × Expr) :=
  let decode := unary .UnIData (.Var input)
  let comparison := binary .EqualsInteger decode (intLit 3)
  let pair := unary .UnConstrData (.Var input)
  let first := Expr.App (.Force (.Force (.Builtin .FstPair))) (.Var checked)
  let second := Expr.App (.Force (.Force (.Builtin .SndPair))) (.Var checked)
  let text := Expr.Lit (.String (String.mk (List.replicate 64 'x')), .AtomicType .TypeString)
  let guardedList := Expr.Case (listCall .NullList (.Var checked)) [listBody, unit]
  let bodies : List (String × Expr) :=
    [("identity", .Var input),
     ("beta", .App (.Lam checked (unary .UnIData (.Var checked))) (.Var input)),
     ("anf-order", binary .AddInteger (trace "left" decode) (trace "right" (intLit 1))),
     ("cse", .Let [(checked, decode, false), (saved, decode, false)]
       (binary .SubtractInteger (.Var checked) (.Var saved))),
     ("cse-trace-alias", .Let [(checked, .Force (.Builtin .Trace), false),
       (saved, .App (.App (.Var checked) (.Lit (.String "again", .AtomicType .TypeString))) decode, false),
       (other, .App (.App (.Var checked) (.Lit (.String "again", .AtomicType .TypeString))) decode, false)] unit),
     ("dce", .Let [(checked, .Delay .Error, false), (saved, decode, false)] unit),
     ("inline-frontier", .Let [(checked, decode, false)]
       (.Let [(saved, trace "after-decode" unit, false)] (.Var checked))),
     ("float", .App (.Lam checked (.Let [(saved, .Force (.Builtin .HeadList), false)]
       (.App (.Var saved) (.Var checked)))) (.Var input)),
     ("force-delay", .Let [(checked, .Delay (trace "force" decode), false)]
       (binary .AddInteger (.Force (.Var checked)) (.Force (.Var checked)))),
     ("delay-share", .Let [(checked, .Delay (.Var input), false)]
       (binary .AddInteger (.Force (.Var checked)) (.Force (.Var checked)))),
     ("case-fields", .Case (.Constr 0 [decode, trace "field" unit])
       [.Lam checked (.Lam saved (.Var checked))]),
     ("case-arity", .Case (.Constr 0 [decode]) [.Lam checked (.Lam saved .Error)]),
     ("checked-boolean", .Let [(checked, comparison, false)]
       (.Case (.Var checked) [.Case (.Var checked) [unit, .Error],
         .Case (.Var checked) [.Error, unit]])),
     ("boolean-choice", .Force (.App (.App (.App (.Force (.Builtin .IfThenElse)) comparison)
       (.Delay unit)) (.Delay .Error))),
     ("strict-choice", .App (.App (.App (.Force (.Builtin .IfThenElse)) comparison)
       unit) (trace "strict-unselected" .Error)),
     ("checked-integer", .Let [(checked, decode, false)]
       (binary .MultiplyInteger (.Var checked) (intLit 0))),
     ("checked-roundtrip", .Let [(checked, decode, false)] (unary .IData (.Var checked))),
     ("list-destructors", .Let [(checked, unary .UnListData (.Var input), false)] listBody),
     ("list-choice", .Let [(checked, unary .UnListData (.Var input), false)] guardedList),
     ("checked-list", .Let [(checked, .Var input, false)] guardedList),
     ("delayed-list", .Let [(checked, .Var input, false)] (chooseList (.Var checked) unit listBody)),
     ("pair", .Let [(checked, pair, false)] (.Constr 0 [first, second])),
     ("fold-scalar", binary .AddInteger decode (binary .DivideInteger (intLit (-7)) (intLit 3))),
     ("fold-data", .Let [(saved, unary .ListData
       (.App (.App (.Force (.Builtin .MkCons)) (unary .IData (intLit 3)))
         (unary .MkNilData unit)), false)] (binary .EqualsData (.Var input) (.Var saved))),
     ("packing", .App (.App (.App (.Lam checked (.Lam saved (.Lam other
       (unary .UnIData (.Var checked))))) (.Var input)) unit) unit),
     ("builtin-sharing", .Let [(checked, .Force (.Builtin .HeadList), false),
       (saved, .Force (.Builtin .HeadList), false)]
       (.Constr 0 [.App (.Var checked) (.Var input), .App (.Var saved) (.Var input)])),
     ("constant-pooling", .Case comparison [text, text]),
     ("shadowed-capture", .Let [(checked, .Var input, false), (saved, .Delay (.Var checked), false),
       (checked, boolLit false, false)] (unary .UnIData (.Force (.Var saved))))]
  (bodies.map fun (name, body) => (name, Expr.Lam input body)) ++
  [("eta", .Lam input (.App (.Builtin .UnIData) (.Var input))),
   ("dead-fix", .Fix recursive (.Lam input decode)),
   ("static-arguments", .Lam checked (.App (.App (loop (unary .UnIData (.Var input)) (.Var input))
       (.Var checked)) (intLit 3))),
   ("recursive-summary", .Lam checked (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
       (.App (.App (loop (.Var input) (intLit 0)) (.Var checked)) (intLit 1)))
       (.Delay unit)) (.Delay .Error))))]

private def protocolPrefixes (expression : Expr) (remaining : Moist.CEK.ExpectedArgs) : List Expr :=
  expression :: match remaining with
    | .one _ => []
    | .more kind rest =>
      let next := match kind with
        | .argQ => Expr.Force expression
        | .argV => .App expression (.Var input)
      protocolPrefixes next rest

def protocolScripts : List (String × Expr) :=
  Moist.Plutus.Decode.Internal.builtinTable.flatMap fun (_, builtin) =>
    (protocolPrefixes (.Builtin builtin) (Moist.CEK.expectedArgs builtin)).zipIdx.map fun (partialState, index) =>
      (s!"protocol/{repr builtin}/{index}", Expr.Lam input
        (.Let [(checked, partialState, false), (saved, partialState, false)]
          (.Var saved)))

def protocolInputs : List Expr :=
  [intLit 0, boolLit true, datum (.I 3), .Delay .Error, .Lam saved (.Var saved)]

def generatedScripts : List (String × Expr) :=
  (List.range 128).map fun seed =>
    let body := (Differential.generate (3 + seed % 3) [input] |>.run (seed + 29573)).1
    (s!"generated/{seed}", Expr.Lam input body)

def requireTerm (result : Except String Term) : IO Term := do
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

def nativeAccepts (term : Term) : IO Bool := do
  match ← Moist.Plutus.Eval.evalTerm term 10000000000 10000000 with
  | .ok _ => return true
  | .error (kind, _, message) =>
    match kind with
    | .typeMismatch | .nonFunctionalApplication | .nonConstrScrutinee | .missingCaseBranch
    | .builtinError | .builtinTermArgumentExpected | .nonPolymorphicInstantiation
    | .unexpectedBuiltinTermArgument => return false
    | _ => throw (IO.userError s!"Inconclusive acceptance observation: {kind}: {message}")

def observe (script argument : Term) (context : Nat) : Term :=
  let applied := Term.Apply script argument
  let consumed := match context with
    | 0 => applied
    | 1 => .Force applied
    | 2 => .Apply applied (.Constant (.Bool true, .AtomicType .TypeBool))
    | _ => .Case applied [.Constant (.Unit, .AtomicType .TypeUnit), .Error]
  .Apply (.Lam 0 (.Constant (.Unit, .AtomicType .TypeUnit))) consumed

def checkScript (name : String) (script : Expr) (arguments : List Expr := inputs) : IO Nat := do
  let baseline ← requireTerm (lowerExpr script)
  let compiled ← match candidates script with
    | .ok terms => pure terms
    | .error message => throw (IO.userError message)
  let mut count := 0
  for (argument, inputIndex) in arguments.zipIdx do
    let value ← requireTerm (lowerExpr argument)
    for context in List.range 4 do
      let original := observe baseline value context
      let expected ← nativeAccepts original
      let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
      for (pass, candidate) in compiled do
        let actual := observe candidate value context
        let label := s!"{name}/{inputIndex}/{context}/{pass}"
        check s!"{label}/native acceptance" ((← nativeAccepts actual) == expected)
        check s!"{label}/Lean outcome and trace"
          ((← Soundness.tracedObservation (liftUPLC actual)) == expectedTrace)
        count := count + 1
  return count

def tests : TestTree := suite "acceptance" do
  test "acceptance_oracle_rejects_inconclusive_results" do
    check "unit succeeds" (← nativeAccepts (.Constant (.Unit, .AtomicType .TypeUnit)))
    check "explicit error fails" (!(← nativeAccepts .Error))
    let rejectedOpenTerm ← try
      let _ ← nativeAccepts (.Var 1)
      pure false
    catch _ => pure true
    check "unbound variables are not ordinary rejection" rejectedOpenTerm
  test "every_pass_runs_on_shared_runtime_inputs" do
    for (name, transform) in transformations do
      check s!"{name}: no nonidentity witness"
        (scripts.any fun (_, script) => !(transform script == script))
    let mut count := 0
    for (name, script) in scripts do
      count := count + (← checkScript name script)
    IO.println s!"{count} shared-input pass/production comparisons; native acceptance and Lean traces."
  test "generated_closures_receive_inputs_after_optimization" do
    let mut count := 0
    for (name, script) in generatedScripts do
      count := count + (← checkScript name script (protocolInputs ++ [.Error]))
    IO.println s!"{count} generated closure comparisons with post-optimization arguments."
  test "all_builtin_partial_protocols_preserve_acceptance" do
    let mut count := 0
    for (name, script) in protocolScripts do
      count := count + (← checkScript name script protocolInputs)
    IO.println s!"{count} comparisons covering all builtin partial-application protocols."

end Test.MIR.Opt.Acceptance
