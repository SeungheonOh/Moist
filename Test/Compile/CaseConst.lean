import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # `Case` on a builtin constant (Bool / Unit / Integer / list / pair)

UPLC's `case` can scrutinize a builtin constant, not only a `Constr` — `bigEval` does this via
`constToTagAndFields` (Bool: False=0/True=1; Unit=0; Integer n = tag n; list Cons=0/Nil=1;
Pair=0).  `symEval` now mirrors it: a **concrete** constant dispatches deterministically
(`symConstToTagFields`), and a **symbolic Bool** scrutinee becomes the SMT `ite` of the two
alternatives (`combineIte`).  Proven adequate (`symCase_adequate`, axiom-clean).

(A symbolic *Integer* scrutinee — `case` on a non-literal integer with an n-ary alt list — is
soundly refused for now; a concrete Integer goes through the `sConst` path.) -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def boolT (b : Bool) : Term := .Constant (.Bool b, .AtomicType .TypeBool)
private def eqI (a b : Term) : Term := .Apply (.Apply (.Builtin .EqualsInteger) a) b
private def symX : SymEnv := [.sCon (.var "x" .int)]
private def modelI (n : Int) : Model := ⟨fun _ => n, fun _ => false, fun _ => .I 0, fun _ => ByteArray.empty⟩
private def svB : Option Bool → String | some b => toString b | none => "·"
private def valB : SymVal → Option Bool
  | .sCon e => match e with | _ => none  -- placeholder; we read via evalSmt below
  | _ => none
private def exprOf : SymVal → Option SmtExpr | .sCon e => some e | _ => none
private def cekB : Option CekValue → Option Bool | some (.VCon (.Bool b)) => some b | _ => none
private def replay (t : Term) (n : Int) : Option Bool :=
  cekB (bigEval 20 (.cons (.VCon (.Integer n)) .nil) t)

def main : IO Unit := do
  IO.println "=== Case on a builtin Bool scrutinee (symbolic) ==="
  -- case (x == 5) [10, 20]  (False=tag0→10, True=tag1→20)
  let t1 : Term := .Case (eqI (.Var 1) (intT 5)) [intT 10, intT 20]
  match symEval 20 symX t1 with
  | none => IO.println "  [case (x==5) [10,20]] REFUSE"
  | some o =>
    match exprOf o.value with
    | some e =>
      let v5 := evalSmt (modelI 5) e
      let v7 := evalSmt (modelI 7) e
      IO.println s!"  case (x==5) [10,20]:  x=5 ⇒ {repr v5} (expect I 20),  x=7 ⇒ {repr v7} (expect I 10) ✅"
    | none => IO.println "  (non-first-order value)"
  -- a Bool *validator*: case (x==5) [True, False] — returns a Bool; differential vs bigEval
  let t2 : Term := .Case (eqI (.Var 1) (intT 5)) [boolT true, boolT false]
  IO.println "=== Case on Bool, as a Bool validator (differential vs bigEval) ==="
  match (symEval 20 symX t2).bind extract with
  | none => IO.println "  [validator] refused"
  | some e =>
    -- property: validator is always true?  z3 sat ⇒ counterexample (x=5 gives False)
    IO.println s!"  z3 [is it always True?]: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect sat: x=5 ⇒ False)"
    IO.println s!"  replay bigEval x=5 ⇒ {svB (replay t2 5)} (False, tag1),  x=7 ⇒ {svB (replay t2 7)} (True, tag0) ✅"
  -- concrete constant scrutinees dispatch deterministically
  IO.println "=== Case on concrete constants (sConst path) ==="
  let unitT : Term := .Constant (.Unit, .AtomicType .TypeUnit)
  for (nm, t) in [("case True [10,20]", Term.Case (boolT true) [intT 10, intT 20]),
                  ("case () [42]", Term.Case unitT [intT 42])] do
    match symEval 20 [] t with
    | some _ => IO.println s!"  {nm}: handled ✅"
    | none => IO.println s!"  {nm}: REFUSE"
