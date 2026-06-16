import Moist.Compile.Compile
import Moist.Smt.Semantics
import Moist.Verified.BigStep

/-! Scratch smoke test: `symEval` interpreted at a model vs `bigEval`. -/

open Moist.Plutus.Term
open Moist.CEK
open Moist.Compile
open Moist.Smt
open Moist.Verified.BigStep

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def biAdd : Term := .Builtin .AddInteger
private def biMul : Term := .Builtin .MultiplyInteger
private def biDiv : Term := .Builtin .DivideInteger
private def biLe  : Term := .Builtin .LessThanEqualsInteger
private def app2 (f a b : Term) : Term := .Apply (.Apply f a) b

/-- Interpret a `SymOut` at a model (the `concVal` of the plan, executable form). -/
private def interpOut (σ : Model) (o : SymOut) : Option SVal :=
  match evalSmt σ o.defined with
  | .B true => match o.value with | .sCon e => some (evalSmt σ e) | _ => none
  | _ => none

private def cekToSVal : CekValue → Option SVal
  | .VCon (.Integer n) => some (.I n)
  | .VCon (.Bool b)    => some (.B b)
  | _ => none

private def σx (xv : Int) : Model :=
  { ints := fun s => if s = "x" then xv else 0, bools := fun _ => false,
    datas := fun _ => .I 0, bytess := fun _ => ByteArray.empty }

-- 1. concrete: addInteger 3 5 = 8
#eval interpOut (σx 0) ((symEval 10 [] (app2 biAdd (intT 3) (intT 5))).getD ⟨.sCon (.litI 0), .trueE⟩)
-- expect some (I 8)
#eval (bigEval 10 .nil (app2 biAdd (intT 3) (intT 5))).bind cekToSVal
-- expect some (I 8)

-- 2. symbolic: (x*x) at x=5 ; env = [sCon (var x)] vs [VCon (Integer 5)]
private def sq : Term := app2 biMul (.Var 1) (.Var 1)
#eval (symEval 10 [.sCon (.var "x" .int)] sq).map (interpOut (σx 5))
-- expect some (some (I 25))
#eval (bigEval 10 (.cons (.VCon (.Integer 5)) .nil) sq).bind cekToSVal
-- expect some (I 25)

-- 3. comparison returns Bool: 0 ≤ x*x  at x = -4
private def nonneg : Term := app2 biLe (intT 0) sq
#eval (symEval 12 [.sCon (.var "x" .int)] nonneg).map (interpOut (σx (-4)))
-- expect some (some (B true))
#eval (bigEval 12 (.cons (.VCon (.Integer (-4))) .nil) nonneg).bind cekToSVal
-- expect some (B true)

-- 4. division guard: x / 0  → defined=false ⇒ interpOut none ; bigEval none
#eval (symEval 10 [.sCon (.var "x" .int)] (app2 biDiv (.Var 1) (intT 0))).map (interpOut (σx 5))
-- expect some none  (symEval commits, but defined=false at σ ⇒ interpOut none)
#eval (bigEval 10 (.cons (.VCon (.Integer 5)) .nil) (app2 biDiv (.Var 1) (intT 0))).bind cekToSVal
-- expect none

-- 5. division defined: x / 2 at x=7  → fdiv 7 2 = 3
#eval (symEval 10 [.sCon (.var "x" .int)] (app2 biDiv (.Var 1) (intT 2))).map (interpOut (σx 7))
-- expect some (some (I 3))
#eval (bigEval 10 (.cons (.VCon (.Integer 7)) .nil) (app2 biDiv (.Var 1) (intT 2))).bind cekToSVal
-- expect some (I 3)
