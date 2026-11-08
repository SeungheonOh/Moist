import Test.MIR.Helpers
import Moist.MIR.Compile
import Moist.CEK.Machine
import Moist.MIR.Optimize.Advanced

/-! # Guarded key comparisons

`case (equalsData d x) [miss, hit]` against a key `d` whose bytes
`k = unBData d` are bound compiles to a comparison of lengths followed by
`equalsByteString` for keys shorter than `keyGuardBound`. Every script is run
by the CEK model under both builtin semantics variants, unoptimized and
compiled (default and size builds), on keys and operands of every `Data` kind,
of equal and different lengths, and longer than the 65536 bytes variant E
accepts in `equalsByteString`.
-/

namespace Test.MIR.Opt.KeyGuards

open Moist.MIR Moist.Plutus.Term Moist.CEK Test.MIR Test.Framework

private def datum := sourceVar 1880
private def policy := sourceVar 1881
private def key := sourceVar 1882
private def probe := sourceVar 1883
private def list := sourceVar 1886
private def loop := sourceVar 1887
private def rest := sourceVar 1888
private def pair := sourceVar 1889

private def dataLit (value : Moist.Plutus.Data) : Expr := .Lit (.Data value, .AtomicType .TypeData)

private def bytes (values : List UInt8) : ByteArray := ⟨values.toArray⟩

private def filled (count : Nat) (value : UInt8) : ByteArray := ⟨(List.replicate count value).toArray⟩

/-- Bytes of every interesting length: empty, short, the guard bound and
    around it, and above the variant E bound. -/
private def keys : List ByteArray :=
  [bytes [], bytes [7], bytes [1, 2], filled 28 3, filled 63 4, filled 64 4, filled 65 4,
    filled 65537 5]

private def operands : List Moist.Plutus.Data :=
  (keys.map .B) ++
    [.B (bytes [0]), .B (bytes [2, 1]), .B (filled 28 9), .B (filled 64 9), .B (filled 65537 6),
      .B (filled 65538 5), .I 0, .I 7, .Constr 0 [], .Constr 1 [.B (bytes [1, 2])], .List [],
      .List [.B (bytes [1, 2])], .Map [], .Map [(.B (bytes [1, 2]), .I 3)]]

private def requireTerm (result : Except String Term) : IO Term :=
  match result with
  | .ok term => pure term
  | .error message => throw (IO.userError message)

private def observe (variant : SemVariant) (term : Term) : String :=
  match (eval (sv := variant) term (2 ^ 80) (2 ^ 80)).result with
  | .success (.VCon c) => s!"{repr c}"
  | .success _ => "non-constant"
  | .failure => "failure"
  | .outOfBudget => "out of budget"

private def variants : List SemVariant := [.C, .E]

private def variantName : SemVariant → String
  | .C => "C"
  | .E => "E"

/-- The compiled scripts agree with the unoptimized one under both variants. -/
private def compare (label : String) (script : Expr) (arguments : List (List Expr)) : IO Unit := do
  let raw ← requireTerm (lowerExpr script)
  let simplified ← requireTerm (lowerExpr (Advanced.simplify (Advanced.simplify script)))
  let compiled ← requireTerm (compileOptimized script)
  let sizeCompiled ← requireTerm (compileOptimized script 0 0
    { shareBuiltinStates := true, poolConstants := true })
  for (values, index) in arguments.zipIdx do
    let lowered ← values.mapM fun value => requireTerm (lowerExpr value)
    for variant in variants do
      let expected := observe variant (lowered.foldl Term.Apply raw)
      for (candidate, name) in [(simplified, "simplify"), (compiled, "default"), (sizeCompiled, "size")] do
        checkEq s!"{label}/{index}/{variantName variant}/{name}" (observe variant (lowered.foldl Term.Apply candidate))
          expected

private partial def termHasBuiltin (builtin : BuiltinFun) : Term → Bool
  | .Builtin b => b == builtin
  | .Lam _ body | .Force body | .Delay body => termHasBuiltin builtin body
  | .Apply function argument => termHasBuiltin builtin function || termHasBuiltin builtin argument
  | .Constr _ fields => fields.any (termHasBuiltin builtin)
  | .Case scrutinee alternatives =>
    termHasBuiltin builtin scrutinee || alternatives.any (termHasBuiltin builtin)
  | _ => false

private def compiledHas (builtin : BuiltinFun) (script : Expr) : Bool :=
  match compileOptimized script with
  | .ok term => termHasBuiltin builtin term
  | .error _ => false

private def comparison (first second : Expr) : Expr :=
  .App (.App (.Builtin .EqualsData) first) second

/-- `let key = unBData policy in case (comparison) [0, 1]`. -/
private def keyed (test : Expr) : Expr :=
  .Lam policy (.Lam datum (.Let [(key, .App (.Builtin .UnBData) (.Var policy), false)]
    (.Case test [intLit 0, intLit 1])))

private def pairs : List (List Expr) :=
  keys.flatMap fun k => operands.map fun o => [dataLit (.B k), dataLit o]

private def fstApp (x : Expr) : Expr := .App (.Force (.Force (.Builtin .FstPair))) x

private def sndApp (x : Expr) : Expr := .App (.Force (.Force (.Builtin .SndPair))) x

/-- A lookup over the entries of a map keyed by `policy`. -/
private def lookup : Expr :=
  .Lam policy (.Lam list
    (.Let [(key, .App (.Builtin .UnBData) (.Var policy), false)]
      (.App (.Fix loop (.Lam rest
        (.Case (.Var rest)
          [.Lam pair (.Lam probe
            (.Case (comparison (.Var policy) (fstApp (.Var pair)))
              [.App (.Var loop) (.Var probe), sndApp (.Var pair)])),
           dataLit (.I (-1))])))
        (.App (.Builtin .UnMapData) (.Var list)))))

private def maps : List Moist.Plutus.Data :=
  [.Map [], .Map [(.B (bytes [1, 2]), .I 1)],
    .Map [(.I 0, .I 9), (.B (filled 65537 5), .I 2), (.B (bytes [7]), .I 4), (.B (bytes [1, 2]), .I 5)],
    .Map [(.B (bytes []), .I 6), (.List [], .I 7), (.B (filled 28 3), .I 8)],
    .Map [(.B (filled 65538 5), .I 1), (.B (filled 64 4), .I 10), (.B (filled 63 4), .I 11)],
    .I 3]

def tests : TestTree := suite "key-guards" do
  test "comparisons_against_keys" do
    for (script, index) in [
        keyed (comparison (.Var policy) (.Var datum)),
        keyed (comparison (.Var datum) (.Var policy)),
        keyed (comparison (.Var policy) (.App (.Builtin .IData) (.App (.Builtin .UnIData) (.Var datum)))),
        keyed (comparison (.App (.Builtin .BData) (.App (.Builtin .UnBData) (.Var datum))) (.Var policy))
      ].zipIdx do
      check s!"comparison {index} compares bytes" (compiledHas .EqualsByteString script)
      check s!"comparison {index} tests lengths" (compiledHas .DropList script)
      compare s!"comparison/{index}" script pairs
  test "lookups_over_maps" do
    check "lookup compares bytes" (compiledHas .EqualsByteString lookup)
    compare "lookup" lookup (keys.flatMap fun k => maps.map fun m => [dataLit (.B k), dataLit m])
  test "unguarded_comparisons_are_kept" do
    let literal := Expr.Lam datum (.Case (comparison (.Var datum) (dataLit (.B (bytes [])))) [intLit 0, intLit 1])
    check "literal kept" (!compiledHas .DropList literal)
    compare "literal" literal (operands.map fun value => [dataLit value])
    let unknown := Expr.Lam policy (.Lam datum (.Case (comparison (.Var policy) (.Var datum)) [intLit 0, intLit 1]))
    check "unknown kept" (!compiledHas .DropList unknown)
    let unused := keyed (boolLit true)
    check "no guards without a comparison" (!compiledHas .DropList unused)

end Test.MIR.Opt.KeyGuards
