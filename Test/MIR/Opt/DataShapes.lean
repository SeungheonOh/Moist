import Test.MIR.Opt.Soundness
import Moist.MIR.Compile
import Moist.MIR.Optimize.Advanced.DataShapes

namespace Test.MIR.Opt.DataShapes

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def datum := sourceVar 880
private def policy := sourceVar 881
private def key := sourceVar 882
private def probe := sourceVar 883
private def partial' := sourceVar 884
private def result := sourceVar 885
private def list := sourceVar 886
private def loop := sourceVar 887
private def rest := sourceVar 888
private def pair := sourceVar 889

private def dataLit (value : Moist.Plutus.Data) : Expr := .Lit (.Data value, .AtomicType .TypeData)

private def bytes (values : List UInt8) : ByteArray := ⟨values.toArray⟩

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def samples : List Moist.Plutus.Data :=
  [.B (bytes []), .B (bytes [0]), .B (bytes [1, 2]), .B (bytes [0, 1, 2]), .I 0, .I 7,
    .Constr 0 [], .Constr 1 [.I 1], .List [], .List [.B (bytes [1, 2])], .Map [],
    .Map [(.B (bytes [1, 2]), .I 3)]]

private def requireTerm (result : Except String Term) : IO Term :=
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

private def observe (term : Term) : IO String := do
  match ← Moist.Plutus.Eval.evalTerm term
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result => return Moist.Plutus.Pretty.prettyTerm result.term
  | .error (kind, _, message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid observation: {kind}: {message}")
    | _ => return "failure"

/-- The passes, the simplifier and the whole compiler agree with the
    unoptimized script on every argument list, including traces. -/
private def compare (label : String) (script : Expr) (arguments : List (List Expr)) : IO Unit := do
  let raw ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.specializeDataChecks, Advanced.insertKeyBytes, Advanced.simplify,
      fun e => Advanced.simplify (Advanced.simplify e)].mapM fun transform =>
    requireTerm (lowerExpr (transform script))
  let compiled ← requireTerm (compileOptimized script)
  let sizeCompiled ← requireTerm (compileOptimized script 0 0
    { shareBuiltinStates := true, poolConstants := true })
  for (values, index) in arguments.zipIdx do
    let lowered ← values.mapM fun value => requireTerm (lowerExpr value)
    let original := lowered.foldl Term.Apply raw
    let expected ← observe original
    let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
    for (candidate, variant) in (candidates ++ [compiled, sizeCompiled]).zipIdx do
      let applied := lowered.foldl Term.Apply candidate
      checkEq s!"{label}/{index}/{variant}/native" (← observe applied) expected
      check s!"{label}/{index}/{variant}/trace"
        ((← Soundness.tracedObservation (liftUPLC applied)) == expectedTrace)

private partial def hasBuiltin (builtin : BuiltinFun) : Expr → Bool
  | .Builtin b => b == builtin
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => hasBuiltin builtin body
  | .App function argument => hasBuiltin builtin function || hasBuiltin builtin argument
  | .Constr _ fields => fields.any (hasBuiltin builtin)
  | .Case scrutinee alternatives =>
    hasBuiltin builtin scrutinee || alternatives.any (hasBuiltin builtin)
  | .Let bindings body => bindings.any (fun (_, rhs, _) => hasBuiltin builtin rhs) || hasBuiltin builtin body
  | _ => false

private partial def termHasBuiltin (builtin : BuiltinFun) : Term → Bool
  | .Builtin b => b == builtin
  | .Lam _ body | .Force body | .Delay body => termHasBuiltin builtin body
  | .Apply function argument => termHasBuiltin builtin function || termHasBuiltin builtin argument
  | .Constr _ fields => fields.any (termHasBuiltin builtin)
  | .Case scrutinee alternatives =>
    termHasBuiltin builtin scrutinee || alternatives.any (termHasBuiltin builtin)
  | _ => false

/-- Whether the default build of `script` contains `builtin`. -/
private def compiledHas (builtin : BuiltinFun) (script : Expr) : Bool :=
  match compileOptimized script with
  | .ok term => termHasBuiltin builtin term
  | .error _ => false

private def guard (scrutinee : Expr) (selected : Nat) : Expr :=
  let flag := fun index => boolLit (index == selected)
  .Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
    (Advanced.chooseDataApp scrutinee (flag 0) (flag 1) (flag 2) (flag 3) (flag 4)))
    (.Delay scrutinee)) (.Delay .Error))

private def comparison (first second : Expr) : Expr :=
  .App (.App (.Builtin .EqualsData) first) second

/-- `let key = unBData policy in body`, tracing so that order is observed. -/
private def keyed (body : Expr) : Expr :=
  .Lam policy (.Lam datum (.Let [(key, .App (.Builtin .UnBData) (.Var policy), false)]
    (trace "key" body)))

private def allPairs : List (List Expr) :=
  (samples.flatMap fun first => samples.map fun second => [dataLit first, dataLit second])

def tests : TestTree := suite "data-shapes" do
  test "kind_guards_become_unData_checks" do
    for selected in [0, 1, 2, 3, 4] do
      let script := Expr.Lam datum (guard (.Var datum) selected)
      check s!"guard {selected} rewritten"
        (!hasBuiltin .ChooseData (Advanced.specializeDataChecks script))
      compare s!"guard/{selected}" script (samples.map fun value => [dataLit value])
    let mixed := Expr.Lam datum (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
      (Advanced.chooseDataApp (.Var datum) (boolLit true) (boolLit false) (boolLit false)
        (boolLit false) (boolLit true))) (.Delay (.Var datum))) (.Delay .Error)))
    check "two kinds kept" (hasBuiltin .ChooseData (Advanced.specializeDataChecks mixed))
    compare "two kinds" mixed (samples.map fun value => [dataLit value])
    let other := Expr.Lam datum (.Lam probe (.Force (.App (.App (.App (.Force (.Builtin .IfThenElse))
      (Advanced.chooseDataApp (.Var datum) (boolLit false) (boolLit false) (boolLit false)
        (boolLit false) (boolLit true))) (.Delay (.Var probe))) (.Delay .Error))))
    check "other result kept" (hasBuiltin .ChooseData (Advanced.specializeDataChecks other))
    compare "other result" other (samples.map fun value => [dataLit value, intLit 4])
  test "key_comparisons_use_bytes" do
    for (script, index) in [
        keyed (comparison (.Var policy) (.Var datum)),
        keyed (comparison (.Var datum) (.Var policy)),
        keyed (.Let [(partial', .App (.Builtin .EqualsData) (.Var policy), false),
          (result, .App (.Var partial') (.Var datum), false)]
          (.Case (.Var result) [trace "different" (intLit 0), trace "equal" (intLit 1)])),
        keyed (.Let [(partial', .App (.Builtin .EqualsData) (.Var datum), false)]
          (.App (.Var partial') (.Var policy)))].zipIdx do
      check s!"comparison {index} rewritten" (!compiledHas .EqualsData script)
      check s!"comparison {index} compares bytes" (compiledHas .EqualsByteString script)
      compare s!"comparison/{index}" script allPairs
  test "key_comparisons_in_loops" do
    -- A lookup over a list of pairs keyed by `policy`.
    let lookup := Expr.Lam policy (.Lam list
      (.Let [(key, .App (.Builtin .UnBData) (.Var policy), false)]
        (.App (.Fix loop (.Lam rest
          (.Case (.Var rest)
            [.Lam pair (.Lam probe
              (.Case (comparison (.Var policy) (.App (.Force (.Force (.Builtin .FstPair))) (.Var pair)))
                [.App (.Var loop) (.Var probe),
                 .App (.Force (.Force (.Builtin .SndPair))) (.Var pair)])),
             dataLit (.I (-1))])))
          (.App (.Builtin .UnMapData) (.Var list)))))
    let maps : List Moist.Plutus.Data :=
      [.Map [], .Map [(.B (bytes [1, 2]), .I 1)], .Map [(.I 0, .I 9), (.B (bytes [0, 1, 2]), .I 4),
        (.B (bytes [1, 2]), .I 5)], .Map [(.B (bytes []), .I 6), (.List [], .I 7)], .I 3]
    check "loop comparison rewritten" (!compiledHas .EqualsData lookup)
    compare "loop" lookup ((samples.flatMap fun first => maps.map fun m => [dataLit first, dataLit m]))
  test "map_and_list_round_trips" do
    -- `source` is a data-list representation of the expected kind: decoded
    -- from the argument or a literal.
    let roundTrip (decode encode : BuiltinFun) (source : Expr) : Expr :=
      .Lam datum (.Let [(list, source, false),
        (probe, .App (.Builtin encode) (.Var list), false),
        (result, .App (.Builtin decode) (.Var probe), false)]
        (trace "decoded" (.App (.Builtin encode) (.Var result))))
    let countOf (builtin : BuiltinFun) : Expr → Nat := fun e =>
      let rec go : Nat → Expr → Nat
        | 0, _ => 0
        | fuel + 1, e => match e with
          | .Builtin b => if b == builtin then 1 else 0
          | .Lam _ body | .Fix _ body | .Force body | .Delay body => go fuel body
          | .App function argument => go fuel function + go fuel argument
          | .Let bindings body => (bindings.map fun (_, rhs, _) => go fuel rhs).sum + go fuel body
          | .Case scrutinee alternatives => go fuel scrutinee + (alternatives.map (go fuel)).sum
          | .Constr _ fields => (fields.map (go fuel)).sum
          | _ => 0
      go 1000 e
    let pairs : Expr := .Lit (.ConstPairDataList [(.I 1, .B (bytes [2])), (.I 3, .I 4)],
      .TypeOperator (.TypeList (.TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData)))))
    let mapTrip := roundTrip .UnMapData .MapData pairs
    check "map round trip removed" (countOf .UnMapData (Advanced.simplify mapTrip) == 0)
    compare "map round trip" mapTrip (samples.map fun value => [dataLit value])
    let decodedMap := roundTrip .UnMapData .MapData (.App (.Builtin .UnMapData) (.Var datum))
    compare "decoded map round trip" decodedMap (samples.map fun value => [dataLit value])
    let items : Expr := .Lit (.ConstDataList [.I 1, .B (bytes [2])],
      .TypeOperator (.TypeList (.AtomicType .TypeData)))
    let listTrip := roundTrip .UnListData .ListData items
    check "list round trip removed" (countOf .UnListData (Advanced.simplify listTrip) == 0)
    compare "list round trip" listTrip (samples.map fun value => [dataLit value])
    let decodedList := roundTrip .UnListData .ListData (.App (.Builtin .UnListData) (.Var datum))
    compare "decoded list round trip" decodedList (samples.map fun value => [dataLit value])
  test "unrelated_comparisons_are_kept" do
    let literal := Expr.Lam datum (comparison (.Var datum) (dataLit (.B (bytes []))))
    check "literal kept" (compiledHas .EqualsData literal)
    compare "literal" literal (samples.map fun value => [dataLit value])
    let unknown := Expr.Lam policy (.Lam datum (comparison (.Var policy) (.Var datum)))
    check "unknown kept" (compiledHas .EqualsData unknown)
    check "no key bytes without a key" (!compiledHas .AppendByteString unknown)
    let unused := keyed (intLit 0)
    check "no key bytes without a comparison" (!compiledHas .AppendByteString unused)
    compare "unused key" unused allPairs

end Test.MIR.Opt.DataShapes
