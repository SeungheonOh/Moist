import Moist.SMT.DagRender
import Moist.SMT.Soundness.SolverBoundary

/-!
# Typed symbolic arithmetic identities

The smart arithmetic constructors are used only after `asInt` has supplied
the integer-denotation guard.  These regressions cover both expression
reduction and the production UPLC/query boundary, while checking that dynamic
type errors and the CEK-backed static path are unchanged.
-/

namespace Test.SMT.ArithmeticSmart

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

private abbrev tyInt : BuiltinType := .AtomicType .TypeInteger

private def intTerm (value : Int) : Term :=
  .Constant (.Integer value, tyInt)

private def app (function argument : Term) : Term :=
  .Apply function argument

private def app2 (builtin : BuiltinFun) (a b : Term) : Term :=
  app (app (.Builtin builtin) a) b

private def symbolicInteger : SymVal :=
  .const (.integer (.sym "smart_arithmetic_x"))

private def zero : SymVal :=
  .const (.integer (.int 0))

private def one : SymVal :=
  .const (.integer (.int 1))

private def exactSymbolicSuccess (expected : SExpr) : List Outcome → Bool
  | [.ok (.bool true) (.const (.integer actual)), .error (.bool false)] =>
      actual == expected
  | _ => false

-- Both operand orientations are covered where the identity is symmetric.
#guard exactSymbolicSuccess (.sym "smart_arithmetic_x")
  (evalBuiltinSym .AddInteger [zero, symbolicInteger])
#guard exactSymbolicSuccess (.sym "smart_arithmetic_x")
  (evalBuiltinSym .AddInteger [symbolicInteger, zero])
#guard exactSymbolicSuccess (.sym "smart_arithmetic_x")
  (evalBuiltinSym .SubtractInteger [zero, symbolicInteger])
#guard exactSymbolicSuccess (.int 0)
  (evalBuiltinSym .MultiplyInteger [zero, symbolicInteger])
#guard exactSymbolicSuccess (.int 0)
  (evalBuiltinSym .MultiplyInteger [symbolicInteger, zero])
#guard exactSymbolicSuccess (.sym "smart_arithmetic_x")
  (evalBuiltinSym .MultiplyInteger [one, symbolicInteger])
#guard exactSymbolicSuccess (.sym "smart_arithmetic_x")
  (evalBuiltinSym .MultiplyInteger [symbolicInteger, one])

private def guardedZeroWithTypeError (name : String) : List Outcome → Bool
  | [.ok successGuard (.const (.integer (.int 0))), .error errorGuard] =>
      let integerGuard := SExpr.isCtor "VInt" (.sym name)
      successGuard == integerGuard && errorGuard == SExpr.not integerGuard
  | _ => false

-- Multiplication by zero may simplify the value, but the dynamic `VInt`
-- projection guard and its complementary runtime-error outcome must remain.
#guard guardedZeroWithTypeError "smart_runtime_value"
  (evalBuiltinSym .MultiplyInteger
    [zero, .dyn (.sym "smart_runtime_value")])

private def exactGroundFive : List Outcome → Bool
  | [.ok (.bool true) (.const (.integer (.int 5)))] => true
  | _ => false

private def exactGroundTypeError : List Outcome → Bool
  | [.error (.bool true)] => true
  | _ => false

-- Saturated ground calls still use the executable CEK builtin path: a
-- successful call has no impossible error branch, and a bad type still errs.
#guard exactGroundFive (evalBuiltinSaturated .AddInteger
  [.const (.integer (.int 2)), .const (.integer (.int 3))])
#guard exactGroundTypeError (evalBuiltinSaturated .AddInteger
  [.const (.integer (.int 1)), .const (.bool (.bool true))])

/-- A normalization-heavy UPLC pipeline representative of arithmetic emitted
by frontends before their own cleanup passes. -/
def neutralPipeline (rounds : Nat) : Term :=
  (List.range rounds).foldl (fun current _ =>
    app2 .SubtractInteger
      (app2 .MultiplyInteger
        (app2 .AddInteger current (intTerm 0)) (intTerm 1))
      (intTerm 0)) (.Var 1)

def workload (rounds : Nat) : Term :=
  app2 .EqualsInteger (neutralPipeline rounds) (.Var 1)

def declaration : SymDecl := symInt "smart_arithmetic_x"

def productionScript (rounds : Nat) : Script :=
  scriptForBoolTrue (30 * rounds + 100) [declaration] (workload rounds)

-- The checked-query constructor accepts the same actual UPLC workload that
-- is benchmarked below, so the public `BoolTrueQuery.sound` endpoint applies.
#guard (BoolTrueQuery.compile? 700 [declaration] (workload 20)).isSome
#check BoolTrueQuery.sound

private def firstLine (output : String) : String :=
  (output.splitOn "\n").head?.getD ""

/-- Raw-Z3 smoke/size benchmark for the production compiler path. -/
unsafe def main : IO Unit := do
  let start ← IO.monoMsNow
  let rendered := (productionScript 500).renderDag
  let generated ← IO.monoMsNow
  let path : System.FilePath := "/tmp/moist-arithmetic-smart-production.smt2"
  IO.FS.writeFile path rendered
  let result ← IO.Process.output { cmd := "z3", args := #["-T:30", path.toString] }
  let solved ← IO.monoMsNow
  unless result.exitCode == 0 && result.stderr.isEmpty &&
      firstLine result.stdout == "sat" do
    throw <| IO.userError s!"arithmetic smart-constructor query failed:\n{result.stdout}{result.stderr}"
  IO.FS.removeFile path
  IO.println s!"arithmetic-smart-500: bytes={rendered.length} generation-ms={generated - start} z3-ms={solved - generated} status=sat"

end Test.SMT.ArithmeticSmart

unsafe def main : IO Unit := Test.SMT.ArithmeticSmart.main
