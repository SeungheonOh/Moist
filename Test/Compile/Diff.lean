import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # Differential validation (§9)

Two continuous checks, run before/independent of any proof effort:

* **§9.1 — `symEval` vs `bigEval`.**  For many `(term, model)` pairs, the *executable* form
  of the adequacy theorem: `interpOut σ (symEval … ) = bigEval … (concretized env)`.  Catches
  compiler bugs **and** `evalSmt`/printer bugs.  Exercises arithmetic, comparisons, and the
  division-by-zero definedness guard.

* **§9.2 — `evalSmt` vs z3 on ground terms.**  For variable-free `SmtExpr`s — especially the
  four Plutus division/modulo operators across every sign combination — assert that z3 agrees
  with `evalSmt`'s value (`unsat` on `value ≠ evalSmt-value`).  Empirically defends the
  printer/standard-match TCB item, in particular the `moist_fdiv/fmod/tdiv/tmod` define-funs
  vs Lean's `Int.fdiv/fmod/tdiv/tmod`.
-/

open Moist.Plutus.Term
open Moist.CEK
open Moist.Compile
open Moist.Smt
open Moist.Verified.BigStep

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def app2 (f a b : Term) : Term := .Apply (.Apply f a) b
private def bi (b : BuiltinFun) : Term := .Builtin b
private def vx : Term := .Var 1   -- x
private def vy : Term := .Var 2   -- y

-- two symbolic int inputs: Var 1 = x, Var 2 = y
private def symXY : SymEnv := [.sCon (.var "x" .int), .sCon (.var "y" .int)]
private def concXY (xv yv : Int) : CekEnv :=
  .cons (.VCon (.Integer xv)) (.cons (.VCon (.Integer yv)) .nil)
private def modelXY (xv yv : Int) : Model :=
  { ints := fun s => if s = "x" then xv else if s = "y" then yv else 0, bools := fun _ => false,
    datas := fun _ => .I 0, bytess := fun _ => ByteArray.empty }

private def interpOut (σ : Model) (o : SymOut) : Option SVal :=
  match evalSmt σ o.defined with
  | .B true => match o.value with | .sCon e => some (evalSmt σ e) | _ => none
  | _ => none
private def cekSVal : CekValue → Option SVal
  | .VCon (.Integer n) => some (.I n)
  | .VCon (.Bool b)    => some (.B b)
  | _ => none

/-- The §9.1 oracle for a two-input term: `Option SVal` from each side. `none` = error/refuse. -/
private def lhsSym (t : Term) (xv yv : Int) : Option (Option SVal) :=
  (symEval 25 symXY t).map (interpOut (modelXY xv yv))
private def rhsBig (t : Term) (xv yv : Int) : Option SVal :=
  (bigEval 25 (concXY xv yv) t).bind cekSVal

private def testTerms : List (String × Term) :=
  [ ("x + y",           app2 (bi .AddInteger) vx vy)
  , ("x - y",           app2 (bi .SubtractInteger) vx vy)
  , ("x * y",           app2 (bi .MultiplyInteger) vx vy)
  , ("x * x + y",       app2 (bi .AddInteger) (app2 (bi .MultiplyInteger) vx vx) vy)
  , ("x ≤ y",           app2 (bi .LessThanEqualsInteger) vx vy)
  , ("x < y",           app2 (bi .LessThanInteger) vx vy)
  , ("x = y",           app2 (bi .EqualsInteger) vx vy)
  , ("0 ≤ x*x",         app2 (bi .LessThanEqualsInteger) (intT 0) (app2 (bi .MultiplyInteger) vx vx))
  , ("x / y  (floored)", app2 (bi .DivideInteger) vx vy)
  , ("x mod y (floored)",app2 (bi .ModInteger) vx vy)
  , ("x quot y (trunc)", app2 (bi .QuotientInteger) vx vy)
  , ("x rem y  (trunc)", app2 (bi .RemainderInteger) vx vy)
  , ("(λz. z+x) y",      .Apply (.Lam 0 (app2 (bi .AddInteger) (.Var 1) (.Var 2))) vy) ]

private def sampleVals : List Int := [-7, -3, -1, 0, 1, 2, 5, 8]

/-- §9.1 — run the executable adequacy check over `testTerms × sampleVals²`. -/
def runDiff : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for (name, t) in testTerms do
    for xv in sampleVals do
      for yv in sampleVals do
        let l := lhsSym t xv yv
        let r := rhsBig t xv yv
        -- symEval must commit (= some), and its interpretation must equal bigEval's value
        if l == some r then
          pass := pass + 1
        else
          fail := fail + 1
          IO.println s!"  MISMATCH {name} @ x={xv} y={yv}: symEval={repr l} bigEval={repr (some r)}"
  pure (pass, fail)

/-- §9.2 — for each ground division case, ask z3 whether `value ≠ evalSmt-value` is `unsat`
    (i.e. z3 agrees with `evalSmt`/the printer).  Returns (pass, fail). -/
def runGroundDiv : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  let ops : List (String × BinOp × (Int → Int → Int)) :=
    [ ("fdiv", .fdiv, Int.fdiv), ("fmod", .fmod, Int.fmod)
    , ("tdiv", .tdiv, Int.tdiv), ("tmod", .tmod, Int.tmod) ]
  let pairs : List (Int × Int) :=
    [ (7,2), (7,-2), (-7,2), (-7,-2), (8,3), (-8,3), (8,-3), (-8,-3), (5,5), (0,3) ]
  for (nm, op, f) in ops do
    for (x, y) in pairs do
      let lean := f x y
      -- query: is  (op x y) = lean  valid?   i.e.  ¬( (op x y) ≠ lean )  unsat
      let neq : SmtExpr := .not (.bin .eq (.bin op (.litI x) (.litI y)) (.litI lean))
      let res ← checkZ3 neq
      if res == .unsat then
        pass := pass + 1
      else
        fail := fail + 1
        IO.println s!"  Z3-DISAGREE {nm} {x} {y}: Lean={lean} z3 verdict={repr res}"
  pure (pass, fail)

def main : IO Unit := do
  IO.println "=== §9.1  symEval vs bigEval (executable adequacy) ==="
  let (p1, f1) ← runDiff
  IO.println s!"  {p1} passed, {f1} failed (of {p1 + f1} cases)"
  IO.println "=== §9.2  evalSmt vs z3 on ground division (printer fidelity) ==="
  let (p2, f2) ← runGroundDiv
  IO.println s!"  {p2} passed, {f2} failed (of {p2 + f2} cases)"
  if f1 == 0 && f2 == 0 then IO.println "ALL DIFFERENTIAL CHECKS PASSED ✅"
  else IO.println "SOME CHECKS FAILED ❌"
