import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # Symbolic `Case` over a constructor choice (WI-1)

`Case (if b then Constr i.. else Constr j..) alts` — the scrutinee is a *symbolic choice* of
constructors, so `symEval` distributes the `Case` through the deferred `sIte`
(`Case (ite c x y) ≡ ite c (Case x) (Case y)`), dispatching each concrete leaf and merging
into an SMT `ite`.  Proven adequate (`symCase_adequate`); axiom-clean. -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def lite (c t e : Term) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) (.Delay t)) (.Delay e))
/-- `λx. 0 ≤ x` — a one-field alternative checking its field is non-negative. -/
private def nonNeg : Term := .Lam 0 (.Apply (.Apply (.Builtin .LessThanEqualsInteger) (intT 0)) (.Var 1))
/-- `validator b = Case (if b then Constr 0 [p] else Constr 1 [q]) [λx.0≤x, λx.0≤x]`. -/
private def validator (p q : Int) : Term :=
  .Case (lite (.Var 1) (.Constr 0 [intT p]) (.Constr 1 [intT q])) [nonNeg, nonNeg]

private def symB : SymEnv := [.sCon (.var "b" .bool)]
private def compileV (p q : Int) : Option SmtExpr := (symEval 30 symB (validator p q)).bind extract
private def cekBool : Option CekValue → Option Bool
  | some (.VCon (.Bool b)) => some b | _ => none
private def replay (p q : Int) (b : Bool) : Option Bool :=
  cekBool (bigEval 40 (.cons (.VCon (.Bool b)) .nil) (validator p q))

def main : IO Unit := do
  IO.println "=== symbolic Case over a constructor choice → z3 (WI-1) ==="
  -- differential: symEval (symbolic b), read at b=true/false, vs bigEval (concrete b)
  IO.println s!"  replay validator(5,3)  b=tt → {repr (replay 5 3 true)}, b=ff → {repr (replay 5 3 false)}  (both true)"
  IO.println s!"  replay validator(5,-3) b=tt → {repr (replay 5 (-3) true)}, b=ff → {repr (replay 5 (-3) false)}  (ff is the bug)"
  -- 1. both branches non-negative ⇒ always true ⇒ z3 unsat
  match compileV 5 3 with
  | none => IO.println "  [all-pos] refused"
  | some e =>
    IO.println s!"  [Case(if b then C0[5] else C1[3]) | 0≤·]  z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect unsat) ✅"
  -- 2. the `else` field is negative ⇒ false when b=false ⇒ z3 sat + bigEval replay
  match compileV 5 (-3) with
  | none => IO.println "  [bug] refused"
  | some e =>
    IO.println s!"  [Case(if b then C0[5] else C1[-3]) | 0≤·] z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect sat)"
    IO.println s!"     replay bigEval at b=false → {repr (replay 5 (-3) false)}  (some false = real counterexample) ✅"
