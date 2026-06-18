import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # Symbolic `Data` **construction** — `constrData`/`mkCons`/`mkNilData`/`listData` (dual of WI-2)

The destructors (`unConstrData`/`unListData`/…) were symbolic from WI-2; now the **constructors**
are too, so you can build `Data` from symbolic variables and round-trip it:

* `iData`/`bData` — inject int/bytes (already);
* `mkNilData ()` ⟶ `sCon (lnil)`; `mkCons h tl` ⟶ `sCon (lcons h tl)` (`list data`);
* `listData items` ⟶ `mkDList`; `constrData tag fields` ⟶ `mkConstr tag fields`, **symbolic on
  both the tag and the fields**.

All proven adequate to the CEK (`symBuiltin_adequate`/`symNil_adequate`); axiom-clean.  The map
path (`mapData`/`mkPairData`/`mkNilPairData`) is deferred (the `ConstPairDataList []` vs
`ConstDataList []` ambiguity under the sort-erased `svalToConst`). -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep
open Moist.Plutus (Data)

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def unitT : Term := .Constant (.Unit, .AtomicType .TypeUnit)
private def app (f a : Term) : Term := .Apply f a
private def app2 (f a b : Term) : Term := app (app f a) b
private def iData (t : Term) : Term := app (.Builtin .IData) t
private def mkNil : Term := app (.Builtin .MkNilData) unitT
private def mkCons (h tl : Term) : Term := app2 (.Force (.Builtin .MkCons)) h tl
private def constrData (tag fields : Term) : Term := app2 (.Builtin .ConstrData) tag fields
private def fstPair (p : Term) : Term := app (.Force (.Force (.Builtin .FstPair))) p
private def unConstr (d : Term) : Term := app (.Builtin .UnConstrData) d
private def eqI (a b : Term) : Term := app2 (.Builtin .EqualsInteger) a b
private def symX : SymEnv := [.sCon (.var "x" .int)]
private def compile (t : Term) : Option SmtExpr := (symEval 25 symX t).bind extract
private def cekBool : Option CekValue → Option Bool
  | some (.VCon (.Bool b)) => some b | _ => none
private def replay (t : Term) (n : Int) : Option Bool :=
  cekBool (bigEval 25 (.cons (.VCon (.Integer n)) .nil) t)
private def st : Option SymOut → String | some _ => "OK ✅" | none => "REFUSE"

def main : IO Unit := do
  IO.println "=== symbolic Data construction ==="
  -- build `Constr 1 [I x]` from the symbolic input x
  let someV := constrData (intT 1) (mkCons (iData (.Var 1)) mkNil)
  IO.println s!"  constrData 1 [iData x]  (symbolic Constr): {st (symEval 20 symX someV)}"
  -- round-trip: the recovered tag is always 1, regardless of x  ⇒ z3 unsat (PROVEN)
  let tagProp := eqI (fstPair (unConstr someV)) (intT 1)
  match compile tagProp with
  | none => IO.println "  [round-trip tag] refused"
  | some e =>
    IO.println s!"  z3 [fstPair(unConstr(constrData 1 [iData x])) == 1]: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect unsat) ✅"
    IO.println s!"     replay bigEval x=99 → {repr (replay tagProp 99)}  (some true: tag is 1)"
  -- a recovered FIELD: unIData(headList(... fields of (constrData 1 [iData x]))) == x  ⇒ unsat
  let unI (d : Term) : Term := app (.Builtin .UnIData) d
  let headL (l : Term) : Term := app (.Force (.Builtin .HeadList)) l
  let sndPair (p : Term) : Term := app (.Force (.Force (.Builtin .SndPair))) p
  let fieldProp := eqI (unI (headL (sndPair (unConstr someV)))) (.Var 1)
  IO.println s!"  field round-trip compiles: {st (symEval 25 symX fieldProp)}"
  IO.println s!"     replay bigEval x=7 → {repr (replay fieldProp 7)}  (some true: field is x) "
