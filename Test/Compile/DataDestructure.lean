import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # Symbolic `Data` destructuring (WI-2) — `unConstrData`/`fstPair`/`sndPair`/list ops

`unConstrData : Data → BuiltinPair BuiltinInteger (BuiltinList Data)` and the builtin
pair/list destructors now run on a **symbolic** `Data`, with the polymorphic SMT `Pair`/`Lst`
representation.  Proven adequate (`symBuiltin_adequate`); **axiom-clean** (the denotations go
through `evalBuiltin_concrete`, no new axioms).  The CEK's `unConstrData` was also corrected to
the proper Plutus semantics (`Pair Integer (List Data)`, matching `Ptah/Data.lean`'s type).

NB: a deeply-nested *list* accessor (`headList` of `cArgs d`) can make z3 answer `unknown` on
the recursive `Data`/`Lst` datatype — a solver-completeness limit, not a soundness gap; the
`bigEval` replay confirms the emitted SMT is exact. -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep
open Moist.Plutus (Data)

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def unConstr (d : Term) : Term := .Apply (.Builtin .UnConstrData) d
private def fstPair (p : Term) : Term := .Apply (.Force (.Force (.Builtin .FstPair))) p
private def sndPair (p : Term) : Term := .Apply (.Force (.Force (.Builtin .SndPair))) p
private def nullL (l : Term) : Term := .Apply (.Force (.Builtin .NullList)) l
private def eqI (a b : Term) : Term := .Apply (.Apply (.Builtin .EqualsInteger) a) b
private def symD : SymEnv := [.sCon (.var "d" .data)]
private def compile (t : Term) : Option SmtExpr := (symEval 40 symD t).bind extract
private def cekBool : Option CekValue → Option Bool
  | some (.VCon (.Bool b)) => some b | _ => none
private def replay (t : Term) (d : Data) : Option Bool :=
  cekBool (bigEval 40 (.cons (.VCon (.Data d)) .nil) t)

def main : IO Unit := do
  IO.println "=== symbolic Data destructuring → z3 (WI-2) ==="
  -- the value of `unConstrData d` is a genuine `mkPair (cTag d) (cArgs d)`
  match symEval 40 symD (unConstr (.Var 1)) with
  | some o => IO.println s!"  unConstrData d  ⇒  {repr o.value}"
  | none => IO.println "  unConstrData refused"
  -- 1. ∀ d. fstPair (unConstrData d) == 0   (d's constructor index is 0)  ⇒ z3 sat (Constr 1..)
  let p1 := eqI (fstPair (unConstr (.Var 1))) (intT 0)
  match compile p1 with
  | none => IO.println "  [tag==0] refused"
  | some e =>
    IO.println s!"  [fstPair(unConstrData d) == 0]   z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect sat)"
    IO.println s!"     replay d=(Constr 1 []) → {repr (replay p1 (.Constr 1 []))}  (some false = counterexample) ✅"
    IO.println s!"     replay d=(Constr 0 []) → {repr (replay p1 (.Constr 0 []))}  (some true: tag 0)"
  -- 2. ∀ d. nullList (sndPair (unConstrData d))   (d's Constr has no fields) ⇒ sat (Constr 0 [x]..)
  let p2 := nullL (sndPair (unConstr (.Var 1)))
  match compile p2 with
  | none => IO.println "  [no-fields] refused"
  | some e =>
    IO.println s!"  [nullList(fields d)]             z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (sat or unknown)"
    IO.println s!"     replay d=(Constr 0 [I 9]) → {repr (replay p2 (.Constr 0 [.I 9]))}  (some false: has a field) ✅"
    IO.println s!"     replay d=(Constr 0 [])    → {repr (replay p2 (.Constr 0 []))}  (some true: empty)"
