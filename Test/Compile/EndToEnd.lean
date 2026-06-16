import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! End-to-end: compile real UPLC validators to SMT, run z3, replay counterexamples. -/

open Moist.Plutus.Term
open Moist.CEK
open Moist.Compile
open Moist.Smt
open Moist.Verified.BigStep

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def biLe  : Term := .Builtin .LessThanEqualsInteger
private def biLt  : Term := .Builtin .LessThanInteger
private def biMul : Term := .Builtin .MultiplyInteger
private def biAdd : Term := .Builtin .AddInteger
private def biSub : Term := .Builtin .SubtractInteger
private def app2 (f a b : Term) : Term := .Apply (.Apply f a) b

/-- One symbolic integer input `x` bound at `Var 1`. -/
private def symX : SymEnv := [.sCon (.var "x" .int)]

/-- GOOD validator body: `0 ≤ x*x` (a true property — z3 should say `unsat`). -/
private def goodBody : Term := app2 biLe (intT 0) (app2 biMul (.Var 1) (.Var 1))

/-- GOOD2: `x*x ≥ 2*x - 1`, i.e. `(x-1)² ≥ 0`. Rearranged: `0 ≤ x*x - (2*x - 1)`. -/
private def good2Body : Term :=
  app2 biLe (intT 0)
    (app2 biSub (app2 biMul (.Var 1) (.Var 1)) (app2 biSub (app2 biAdd (.Var 1) (.Var 1)) (intT 1)))

/-- BUGGY validator body: `x < 5` (false for `x ≥ 5` — z3 should say `sat`). -/
private def badBody : Term := app2 biLt (.Var 1) (intT 5)

/-- Two symbolic inputs `x` (Var 1), `y` (Var 2), for the division demo. -/
private def symXY : SymEnv := [.sCon (.var "x" .int), .sCon (.var "y" .int)]

/-- DIVISION validator body: `(x*y) / y = x` — true **under the precondition `y ≠ 0`**.
    Exercises the floored-division denotation, the `y ≠ 0` definedness guard, and a real
    SMT precondition `P = (y ≠ 0)`. -/
private def divBody : Term :=
  app2 (.Builtin .EqualsInteger)
    (app2 (.Builtin .DivideInteger) (app2 biMul (.Var 1) (.Var 2)) (.Var 2))
    (.Var 1)

/-- The precondition `y ≠ 0` as an `SmtExpr`. -/
private def yNeZero : SmtExpr := .neZeroE (.var "y" .int)

/-! ### A concrete `validator_sound` instantiation (the proof, not just the IO)

For `goodBody`, the compile facts (`symEval = some o`, `extract o = some e`,
`sortOf e = some .bool`) are all discharged by `rfl`/`decide`, so `validator_sound`
specializes to a closed theorem: *given* z3's `unsat`, the CEK evaluating `0 ≤ x*x` on any
concrete `x` halts at `true`.  This is the soundness guarantee made concrete. -/
-- The success formula compiles and is a well-sorted `Bool`.  `symEval` is well-founded
-- recursive (like `bigEval`) so it does not reduce under `decide`/`rfl`; the per-validator
-- "compiled with fuel to spare" check (§6.5) is therefore `native_decide` — a runtime check
-- that keeps `validator_sound` *itself* axiom-clean (the trust is only in this instantiation).
example : ((symEval 20 symX goodBody).bind extract).isSome = true := by native_decide
example : SmtExpr.sortOf (((symEval 20 symX goodBody).bind extract).getD .falseE)
    = some .bool := by native_decide

theorem goodBody_sound {o : SymOut} {e : SmtExpr}
    (hc : symEval 20 symX goodBody = some o) (hx : extract o = some e)
    (hsort : SmtExpr.sortOf e = some .bool)
    (hz3 : z3_says_unsat (toSMTLIB (encodeProperty .trueE e))) :
    ∀ σ : Model, evalSmt σ .trueE = .B true →
      Moist.Verified.Equivalence.Reaches
        (.compute [] (γE σ symX) goodBody) (.halt (.VCon (.Bool true))) :=
  validator_sound hc hx hsort hz3

/-- Compile a one-input validator body to its success formula `extract (symEval …)`. -/
private def compileBody (t : Term) : Option SmtExpr := (symEval 20 symX t).bind extract

/-- Read off a `Bool`/`Int` from a `bigEval` result (the concrete replay oracle). -/
private def cekBool : Option CekValue → Option Bool
  | some (.VCon (.Bool b)) => some b
  | _ => none

/-- Replay the validator concretely at `x := xv` via the verified `bigEval`. -/
private def replay (t : Term) (xv : Int) : Option Bool :=
  cekBool (bigEval 20 (.cons (.VCon (.Integer xv)) .nil) t)

def main : IO Unit := do
  IO.println "=== UPLC → SMT denotational compiler: end-to-end ==="
  -- 1. GOOD validator: 0 ≤ x*x
  match compileBody goodBody with
  | none => IO.println "[good] compile FAILED"
  | some e =>
    IO.println s!"[good] success formula sortOf = {repr (SmtExpr.sortOf e)}"
    let smt := toSMTLIB (encodeProperty .trueE e)
    IO.println "[good] SMT-LIB query (¬(true → success)):"
    IO.println smt
    let r ← checkZ3 (encodeProperty .trueE e)
    IO.println s!"[good] z3 verdict: {repr r}  (expect unsat ⇒ validator always true) ✅"
  -- 2. GOOD2 validator: (x-1)² ≥ 0
  match compileBody good2Body with
  | none => IO.println "[good2] compile FAILED"
  | some e =>
    let r ← checkZ3 (encodeProperty .trueE e)
    IO.println s!"[good2] (x-1)² ≥ 0 — z3 verdict: {repr r}  (expect unsat) ✅"
  -- 3. BUGGY validator: x < 5  → z3 sat ; replay the exploit through bigEval
  match compileBody badBody with
  | none => IO.println "[bad] compile FAILED"
  | some e =>
    let r ← checkZ3 (encodeProperty .trueE e)
    IO.println s!"[bad] x < 5 — z3 verdict: {repr r}  (expect sat ⇒ a counterexample exists)"
    -- self-checked replay (untrusted direction): bigEval at x = 6 must be `false`
    IO.println s!"[bad] replay bigEval at x=6 → {repr (replay badBody 6)}  (expect some false = real exploit) ✅"
    IO.println s!"[bad] replay bigEval at x=4 → {repr (replay badBody 4)}  (some true: validator holds here)"
  -- 4. DIVISION validator under precondition y ≠ 0:  (x*y)/y = x
  match (symEval 25 symXY divBody).bind extract with
  | none => IO.println "[div] compile FAILED"
  | some e =>
    IO.println s!"[div] success formula carries the y≠0 guard; sortOf = {repr (SmtExpr.sortOf e)}"
    -- WITHOUT the precondition, z3 finds y=0 (where the validator errors): sat
    let r0 ← checkZ3 (encodeProperty .trueE e)
    IO.println s!"[div] no precondition — z3: {repr r0}  (sat: y=0 makes it undefined)"
    -- WITH precondition y ≠ 0, the property holds: unsat
    let r1 ← checkZ3 (encodeProperty yNeZero e)
    IO.println s!"[div] precondition y≠0 — z3: {repr r1}  (expect unsat ⇒ (x*y)/y = x always) ✅"
