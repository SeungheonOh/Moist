import Moist.Symbolic.Compile
import Moist.CEK.Machine
import Test.Framework

namespace Test.Symbolic.Parity

open Moist.Plutus.Term (Term Const BuiltinType AtomicType BuiltinFun)
open Moist.Symbolic
open Moist.CEK
open Test.Framework

private abbrev intC (n : Int) : Term :=
  .Constant (.Integer n, .AtomicType .TypeInteger)

private abbrev bsC (xs : List UInt8) : Term :=
  .Constant (.ByteString ⟨xs.toArray⟩, .AtomicType .TypeByteString)

private abbrev nilC : Term :=
  .Constant (.ConstList [], .TypeOperator (.TypeList (.AtomicType .TypeInteger)))

private def expectBoolExpr (label : String) (expected : Bool) : SExpr → IO Unit
  | .bool actual =>
      unless actual == expected do
        throw <| IO.userError s!"{label}: expected {expected}, got {actual}"
  | actual => throw <| IO.userError s!"{label}: expected a folded Bool, got {actual}"

private def expectStableFailure (name : String) (fuel : Nat) (t : Term) : IO Unit := do
  let sr := symEval fuel [] t
  expectBoolExpr s!"{name}.inc" false sr.inc
  expectBoolExpr s!"{name}.err" true sr.err
  match (eval t).result with
  | .failure => pure ()
  | actual => throw <| IO.userError s!"{name}.cek: expected failure, got {actual}"

private def expectSide (name expected : String) (kind : InputKind) : IO Unit := do
  let actual := (compile 1 [(name, kind)] (intC 0)).sides.map SExpr.render
  unless actual.contains expected do
    throw <| IO.userError s!"missing side condition {expected}; got {actual}"

private def expectZ3Unsat (name smt : String) : IO Unit := do
  let path := s!"/tmp/moist_symbolic_{name}.smt2"
  IO.FS.writeFile path smt
  let out ← IO.Process.output { cmd := "z3", args := #[path] }
  unless (out.stdout.splitOn "\n").head?.getD "" == "unsat" do
    throw <| IO.userError s!"{name}: expected z3 unsat, got\n{out.stdout}\n{out.stderr}"

def tests : TreeBuilder Unit := do
  test "apply stops after function error" <| expectStableFailure "apply" 2
    (.Apply .Error (.Force (.Delay (intC 1))))

  test "constructor stops after first field error" <| expectStableFailure "constr" 2
    (.Constr 0 [.Error, .Force (.Delay (intC 1))])

  test "case stops after scrutinee error" <| expectStableFailure "case" 2
    (.Case .Error [.Force (.Delay (intC 1))])

  test "unsupported CEK builtin is an error, not incomplete" <| expectStableFailure "sha2" 4
    (.Apply (.Builtin .Sha2_256) (bsC [1, 2, 3]))

  test "mkCons rejects an SOP constructor as a ConstList element" <| expectStableFailure "mkCons" 6
    (.Apply (.Apply (.Force (.Builtin .MkCons)) (.Constr 0 [])) nilC)

  test "bare symbolic pair dispatch is determinate" do
    let r := symBuiltin .FstPair [.atom "x"]
    expectBoolExpr "fstPair.inc" false r.inc

  test "bare symbolic list dispatch is determinate" do
    let r := symBuiltin .HeadList [.atom "x"]
    expectBoolExpr "headList.inc" false r.inc

  test "raw symbolic inputs are constrained to lossless CEK constants" do
    expectSide "d" "(moist_wf_d d)" .data
    expectSide "xs" "(moist_const_vl xs)" .list
    expectSide "x" "(moist_const_v x)" .anyV

  test "bare symbolic constant Case dispatch is determinate" do
    let t : Term := .Case (.Var 1) [intC 10, intC 20]
    expectZ3Unsat "any_case"
      ((compile 4 [("x", .anyV)] t).toSMTLib goalIndeterminate)

def testTree : TestTree := suite "symbolic" tests

end Test.Symbolic.Parity
