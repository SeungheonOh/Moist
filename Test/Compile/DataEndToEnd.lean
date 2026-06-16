import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! End-to-end on **symbolic `Data`** validators (Phase B): compile a validator over a
    symbolic `Data` input, emit the SMT `Data` recursive datatype, run z3, replay sat models
    through the verified `bigEval`. -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep
open Moist.Plutus (Data)

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def app2 (f a b : Term) : Term := .Apply (.Apply f a) b
/-- One symbolic `Data` input bound at `Var 1`. -/
private def symD : SymEnv := [.sCon (.var "d" .data)]
private def compile (t : Term) : Option SmtExpr := (symEval 20 symD t).bind extract
private def unI (d : Term) : Term := .Apply (.Builtin .UnIData) d
private def cekBool : Option CekValue → Option Bool
  | some (.VCon (.Bool b)) => some b | _ => none
/-- Replay a one-`Data`-input validator concretely through the verified `bigEval`. -/
private def replay (t : Term) (d : Data) : Option Bool :=
  cekBool (bigEval 20 (.cons (.VCon (.Data d)) .nil) t)

def main : IO Unit := do
  IO.println "=== symbolic Data validators → z3 (Phase B) ==="
  -- 1. equalsData d d  — reflexive, always true
  match compile (app2 (.Builtin .EqualsData) (.Var 1) (.Var 1)) with
  | none => IO.println "[eqData d d] refused"
  | some e =>
    IO.println s!"[eqData d d]              z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect unsat) ✅"
  -- 2. unIData d == unIData d, under precondition `isI d` — always true
  match compile (app2 (.Builtin .EqualsInteger) (unI (.Var 1)) (unI (.Var 1))) with
  | none => IO.println "[unI self-eq] refused"
  | some e =>
    let pre : SmtExpr := .uop .isI (.var "d" .data)
    IO.println s!"[unI d == unI d | isI d]  z3: {repr (← checkZ3 (encodeProperty pre e))}  (expect unsat) ✅"
  -- 3. equalsData d (iData 42) — false unless d = I 42 ⇒ z3 sat; replay the exploit
  let bug := app2 (.Builtin .EqualsData) (.Var 1) (.Apply (.Builtin .IData) (intT 42))
  match compile bug with
  | none => IO.println "[eqData d (iData 42)] refused"
  | some e =>
    IO.println s!"[eqData d (iData 42)]     SMT value compares `d` to the datatype term `(mkI 42)`"
    IO.println s!"[eqData d (iData 42)]     z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect sat)"
    IO.println s!"  replay bigEval d=(I 7)  → {repr (replay bug (.I 7))}  (some false = real exploit) ✅"
    IO.println s!"  replay bigEval d=(I 42) → {repr (replay bug (.I 42))}  (some true: holds here)"
