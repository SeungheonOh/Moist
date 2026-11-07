import Test.MIR.Opt.Soundness
import Moist.MIR.Compile
import Moist.MIR.Optimize.Advanced.TagChains

namespace Test.MIR.Opt.TagChains

open Moist.MIR Moist.Plutus.Term Test.MIR Test.Framework

private def datum := sourceVar 870
private def pair := sourceVar 871
private def tag := sourceVar 872
private def probe := sourceVar 873
private def argument := sourceVar 874
private def function := sourceVar 875
private def parameter := sourceVar 876
private def first := sourceVar 877
private def second := sourceVar 878

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def equals (left right : Expr) : Expr :=
  .App (.App (.Builtin .EqualsInteger) left) right

/-- `if condition then matched else otherwise`, as a Boolean case. -/
private def branch (condition matched otherwise : Expr) : Expr := .Case condition [otherwise, matched]

/-- The tag of a constructor datum, bound like a `@[plutus_data]` match does. -/
private def constructorTag (body : Expr) : Expr :=
  .Let [(pair, .App (.Builtin .UnConstrData) (.Var datum), false),
    (tag, .App (.Force (.Force (.Builtin .FstPair))) (.Var pair), false)] body

/-- An integer datum's value as the tag: negative and large tags occur. -/
private def integerTag (body : Expr) : Expr :=
  .Let [(tag, .App (.Builtin .UnIData) (.Var datum), false)] body

/-- A chain testing `values` in order, with `default` after the last test. -/
private def chain (values : List Int) (default : Expr) : Expr :=
  values.foldr (fun value rest =>
    branch (equals (.Var tag) (intLit value)) (trace s!"tag {value}" (intLit (value * 10))) rest)
    default

private def constructors : List Expr :=
  ((List.range 8).map fun index =>
    Expr.Lit (.Data (.Constr (Int.ofNat index) [.I 1]), .AtomicType .TypeData)) ++
  [.Lit (.Data (.Constr 100 []), .AtomicType .TypeData), .Lit (.Data (.I 3), .AtomicType .TypeData)]

private def integers : List Expr :=
  ((List.range 12).map fun index =>
    Expr.Lit (.Data (.I (Int.ofNat index - 4)), .AtomicType .TypeData)) ++
  [.Lit (.Data (.I 1000), .AtomicType .TypeData), .Lit (.Data (.Constr 0 []), .AtomicType .TypeData)]

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

/-- The pass alone, the simplifier containing it, and the whole compiler agree
    with the unoptimized script on every argument, including traces. -/
private def compare (label : String) (script : Expr) (arguments : List Expr) : IO Unit := do
  let raw ← requireTerm (lowerExpr script)
  let candidates ← [Advanced.caseTagChains, Advanced.simplify].mapM fun transform =>
    requireTerm (lowerExpr (transform script))
  let compiled ← requireTerm (compileOptimized script)
  let sizeCompiled ← requireTerm (compileOptimized script 0 0
    { shareBuiltinStates := true, poolConstants := true })
  for (value, index) in arguments.zipIdx do
    let lowered ← requireTerm (lowerExpr value)
    let original := Term.Apply raw lowered
    let expected ← observe original
    let expectedTrace ← Soundness.tracedObservation (liftUPLC original)
    for (candidate, variant) in (candidates ++ [compiled, sizeCompiled]).zipIdx do
      let applied := Term.Apply candidate lowered
      checkEq s!"{label}/{index}/{variant}/native" (← observe applied) expected
      check s!"{label}/{index}/{variant}/trace"
        ((← Soundness.tracedObservation (liftUPLC applied)) == expectedTrace)

/-- Whether the pass leaves an `equalsInteger` test in the script. -/
private partial def hasEquality : Expr → Bool
  | .Builtin .EqualsInteger => true
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => hasEquality body
  | .App function argument => hasEquality function || hasEquality argument
  | .Constr _ fields => fields.any hasEquality
  | .Case scrutinee alternatives => hasEquality scrutinee || alternatives.any hasEquality
  | .Let bindings body => bindings.any (fun (_, rhs, _) => hasEquality rhs) || hasEquality body
  | _ => false

private def converted (script : Expr) : Bool := !hasEquality (Advanced.caseTagChains script)

def tests : TestTree := suite "tag-chains" do
  test "error_defaults_become_integer_cases" do
    for (values, index) in [[0, 1, 2, 3], [0], [2, 0, 1], [3, 0], [1, 1, 0], [5, 2]].zipIdx do
      let constructor := Expr.Lam datum (constructorTag (chain values .Error))
      check s!"constructor chain {index} converted" (converted constructor)
      compare s!"constructor chain/{index}" constructor constructors
      let integer := Expr.Lam datum (integerTag (chain values .Error))
      check s!"integer chain {index} converted" (converted integer)
      compare s!"integer chain/{index}" integer integers
  test "direct_tag_expressions" do
    let constructorTagOf : Expr := .App (.Force (.Force (.Builtin .FstPair)))
      (.App (.Builtin .UnConstrData) (.Var datum))
    let integerTagOf : Expr := .App (.Builtin .UnIData) (.Var datum)
    let direct (subject : Expr) (values : List Int) (literalFirst : Bool) : Expr :=
      values.foldr (fun value rest =>
        branch (if literalFirst then equals (intLit value) subject else equals subject (intLit value))
          (trace s!"tag {value}" (intLit (value * 10))) rest) .Error
    for (values, index) in [[0], [2], [0, 1, 2], [1, 0], [3, 3, 1]].zipIdx do
      for literalFirst in [false, true] do
        let constructor := Expr.Lam datum (direct constructorTagOf values literalFirst)
        check s!"direct constructor {index} converted" (converted constructor)
        compare s!"direct constructor/{index}/{literalFirst}" constructor constructors
        let integer := Expr.Lam datum (direct integerTagOf values literalFirst)
        check s!"direct integer {index} converted" (converted integer)
        compare s!"direct integer/{index}/{literalFirst}" integer integers
    let failingDirect := Expr.Lam datum (branch (equals integerTagOf (intLit 0)) .Error
      (branch (equals integerTagOf (intLit 1)) .Error
        (branch (equals integerTagOf (intLit 2)) .Error (trace "default" (intLit 7)))))
    compare "direct failing tests" failingDirect integers
  test "unknown_and_negative_tests_are_kept" do
    let unknown := Expr.Lam datum (.Let [(tag, .App (.Builtin .UnBData) (.Var datum), false)]
      (chain [0, 1] .Error))
    check "unknown tag kept" (!converted unknown)
    compare "unknown tag" unknown [.Lit (.Data (.B ⟨#[1]⟩), .AtomicType .TypeData)]
    let negative := Expr.Lam datum (integerTag (chain [-1, 0] .Error))
    check "negative literal kept" (!converted negative)
    compare "negative literal" negative integers
    let far := Expr.Lam datum (integerTag (chain [40] .Error))
    check "distant tag kept" (!converted far)
    compare "distant tag" far integers
  test "shared_and_bound_tests" do
    let shared := Expr.Lam datum (constructorTag (.Let
      [(function, .App (.Builtin .EqualsInteger) (.Var tag), false)]
      (branch (.App (.Var function) (intLit 0)) (trace "zero" (intLit 0))
        (branch (.App (.Var function) (intLit 1)) (trace "one" (intLit 1)) .Error))))
    check "shared partial application converted" (converted shared)
    compare "shared partial application" shared constructors
    let bound := Expr.Lam datum (constructorTag (.Let
      [(function, .App (.Builtin .EqualsInteger) (.Var tag), false),
       (probe, .App (.Var function) (intLit 0), false)]
      (.Case (.Var probe) [.Let [(first, .App (.Var function) (intLit 1), false)]
        (.Case (.Var first) [.Error, trace "one" (intLit 1)]), trace "zero" (intLit 0)])))
    check "bound tests converted" (converted bound)
    compare "bound tests" bound constructors
    let reversed := Expr.Lam datum (constructorTag
      (branch (equals (intLit 1) (.Var tag)) (intLit 1)
        (branch (equals (intLit 0) (.Var tag)) (intLit 0) .Error)))
    check "literal first converted" (converted reversed)
    compare "literal first" reversed constructors
  test "failing_ranges" do
    let failing (values : List Int) (default : Expr) : Expr :=
      values.foldr (fun value rest => branch (equals (.Var tag) (intLit value)) .Error rest) default
    for (values, index) in [[0, 1, 2, 3, 4], [4, 3, 2, 1, 0], [2, 3, 4], [1, 0, 2],
        [0, 2, 3], [0, 1], [3, 1, 2, 0]].zipIdx do
      let default := trace "default" (intLit 7)
      compare s!"constructor range/{index}" (.Lam datum (constructorTag (failing values default)))
        constructors
      compare s!"integer range/{index}" (.Lam datum (integerTag (failing values default))) integers
    check "contiguous range converted"
      (converted (.Lam datum (integerTag (failing [0, 1, 2, 3, 4] (intLit 7)))))
    check "gapped range kept"
      (!converted (.Lam datum (integerTag (failing [0, 2, 3] (intLit 7)))))
  test "applied_chains" do
    let leaf (value : Int) : Expr :=
      .Lam parameter (trace s!"leaf {value}"
        (.App (.App (.Builtin .AddInteger) (.Var parameter)) (intLit value)))
    let applied := fun (default : Expr) => Expr.Lam datum (constructorTag (.Let
      [(argument, intLit 5, false)]
      (.App (branch (equals (.Var tag) (intLit 0)) (leaf 0)
        (branch (equals (.Var tag) (intLit 1)) (.Let [(second, trace "bound" (intLit 2), false)]
          (leaf 1)) default)) (.Var argument))))
    for (default, index) in [(Expr.Lam parameter .Error, 0), (.Error, 1), (leaf 9, 2)].zipIdx.map
        (fun ((default, index), _) => (default, index)) do
      compare s!"applied chain/{index}" (applied default) constructors
    check "applied chain converted" (converted (applied (.Lam parameter .Error)))
    let bound := Expr.Lam datum (constructorTag (.Let
      [(argument, intLit 5, false),
       (function, branch (equals (.Var tag) (intLit 0)) (leaf 0)
         (branch (equals (.Var tag) (intLit 1)) (leaf 1) (.Lam parameter .Error)), false)]
      (.App (.Var function) (.Var argument))))
    check "bound applied chain converted" (converted bound)
    compare "bound applied chain" bound constructors
    let effectful := Expr.Lam datum (constructorTag
      (.App (branch (equals (.Var tag) (intLit 0)) (leaf 0) (.Lam parameter .Error))
        (trace "argument" (intLit 5))))
    compare "effectful argument" effectful constructors

end Test.MIR.Opt.TagChains
