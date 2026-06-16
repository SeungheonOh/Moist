import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # Bounded model checking of **unbounded recursion** by `sIte` unrolling

A genuinely recursive UPLC program — `sum i = if i ≤ 0 then 0 else i + sum (i-1)`, built with
the call-by-value Z combinator — is symbolically executed over a *symbolic* input `i`.  The
recursion guard `i ≤ 0` is a symbolic boolean, so `IfThenElse` defers a `sIte` (lazy branches),
and `symForce` unrolls **both** branches up to the fuel budget, emitting nested SMT `ite`s.

* Where the unrolling reaches the base case the `defined` flag is `true` and the SMT `value`
  **provably** equals the CEK result (`symEval_adequate`).
* Beyond the unrolled depth `defined` is `false`: a fuel-exhausted branch is gated out
  (`combineIte … false`), so the tool makes **no claim** — sound bounded model checking.

Increasing the fuel unrolls the recursion arbitrarily deep (larger verified domain). -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep
open Moist.Smt.SmtExpr (andE)

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def lam (b : Term) : Term := .Lam 0 b
private def app2 (f a b : Term) : Term := .Apply (.Apply f a) b
private def addI (a b : Term) : Term := app2 (.Builtin .AddInteger) a b
private def subI (a b : Term) : Term := app2 (.Builtin .SubtractInteger) a b
private def leI  (a b : Term) : Term := app2 (.Builtin .LessThanEqualsInteger) a b
/-- Lazy if: `force [ (force ifThenElse) c (delay t) (delay e) ]` — lazy branches ⇒ `sIte`. -/
private def lite (c t e : Term) : Term :=
  .Force (.Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) (.Delay t)) (.Delay e))
/-- Call-by-value Z combinator: `λf. (λx. f (λv. (x x) v)) (λx. f (λv. (x x) v))`. -/
private def half : Term := lam (.Apply (.Var 2) (lam (app2 (.Var 2) (.Var 2) (.Var 1))))
private def zfix : Term := lam (.Apply half half)
/-- `bodyF self i = if i ≤ 0 then 0 else i + self (i-1)`  (`self`=Var 2, `i`=Var 1). -/
private def bodyF : Term :=
  lam (lam (lite (leI (.Var 1) (intT 0)) (intT 0)
                 (addI (.Var 1) (.Apply (.Var 2) (subI (.Var 1) (intT 1))))))
private def sumApp (i : Term) : Term := .Apply (.Apply zfix bodyF) i
/-- The validator `validator i : Bool = (0 ≤ sum i)`. -/
private def validator : Term := leI (intT 0) (sumApp (.Var 1))

/-- One symbolic integer input `i` bound at `Var 1`. -/
private def symI : SymEnv := [.sCon (.var "i" .int)]
private def iVar : SmtExpr := .var "i" .int
private def le (a b : SmtExpr) : SmtExpr := .bin .le a b
private def modelI (n : Int) : Model :=
  ⟨fun _ => n, fun _ => false, fun _ => .I 0, fun _ => ByteArray.empty⟩
private def svalI : SVal → Int | .I n => n | _ => -999
private def svalB : SVal → Bool | .B b => b | _ => false
private def valExpr : SymVal → SmtExpr | .sCon e => e | _ => .litI (-999)
private def mark (b : Bool) : String := if b then "T" else "·"
private def cekInt : Option CekValue → Option Int
  | some (.VCon (.Integer n)) => some n | _ => none

private def compileV (F : Nat) : Option SmtExpr := (symEval F symI validator).bind extract

def main : IO Unit := do
  IO.println "=== sum(i) = if i ≤ 0 then 0 else i + sum (i-1)  — recursion unrolled by sIte ==="
  -- 0. ground truth from the verified bigEval (≡ CEK)
  let truth := (List.range 9).map (fun n => toString ((cekInt (bigEval 300 .nil (sumApp (intT (Int.ofNat n))))).getD (-1)))
  IO.println s!"  bigEval sum(0..8)            = {truth}"
  -- 1. symbolic unroll: more fuel ⇒ deeper `defined` frontier, value exact where defined
  for F in [40, 60, 80] do
    match symEval F symI (sumApp (.Var 1)) with
    | none => IO.println s!"  F={F}: REFUSED"
    | some o =>
      let ds := (List.range 9).map (fun n => mark (svalB (evalSmt (modelI (Int.ofNat n)) o.defined)))
      let vs := (List.range 9).map (fun n => toString (svalI (evalSmt (modelI (Int.ofNat n)) (valExpr o.value))))
      IO.println s!"  F={F}: defined i=0..8 = {ds}"
      IO.println s!"         value   i=0..8 = {vs}"
  -- 2. real z3 bounded proof: 0 ≤ sum(i) holds for every i in the unrolled range [0,3] at F=40
  IO.println "--- z3 ---"
  match compileV 40 with
  | none => IO.println "  compile refused"
  | some e =>
    let pIn  := andE (le (.litI 0) iVar) (le iVar (.litI 3))   -- within F=40 unroll depth
    let pAll := le (.litI 0) iVar                               -- unbounded
    IO.println s!"  [0≤i≤3] z3: {repr (← checkZ3 (encodeProperty pIn e))}   (expect unsat — proven in range)"
    IO.println s!"  [0≤i  ] z3: {repr (← checkZ3 (encodeProperty pAll e))}  (expect sat — beyond depth, no claim)"
