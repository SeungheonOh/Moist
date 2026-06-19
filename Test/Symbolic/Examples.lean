import Moist.Symbolic.Compile

/-! # Worked examples: UPLC → SMT-LIB symbolic compilation, solved by z3

Each example builds a UPLC `Term` with one or more **symbolic** inputs, compiles
it to SMT-LIB with `Moist.Symbolic.compile`, prints the generated script, and
shells out to z3 to actually solve for the inputs.

Run / inspect with:  `lake build Test.Symbolic.Examples`  (the `#eval`s run z3)
or as an executable (see `Main`-style `#eval main` at the bottom).
-/

namespace Test.Symbolic.Examples

open Moist.Plutus.Term (Term Const BuiltinType AtomicType BuiltinFun)
open Moist.Symbolic

/-! ## Term builders (de Bruijn; `Var 1` = innermost / first symbolic input) -/

abbrev intC  (n : Int)  : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
abbrev boolC (b : Bool) : Term := .Constant (.Bool b, .AtomicType .TypeBool)
abbrev bsC   (bytes : List UInt8) : Term :=
  .Constant (.ByteString ⟨bytes.toArray⟩, .AtomicType .TypeByteString)
def b1 (b : BuiltinFun) (a : Term) : Term := .Apply (.Builtin b) a
def b2 (b : BuiltinFun) (x y : Term) : Term := .Apply (.Apply (.Builtin b) x) y
/-- `ifThenElse c t e` (polymorphic builtin: one force + three values). -/
def ite3 (c t e : Term) : Term :=
  .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t) e

/-! ## z3 driver -/

/-- Write `smt` to a temp file, run z3 on it, and return z3's stdout. -/
def runZ3 (smt : String) : IO String := do
  try
    let tmp := "/tmp/moist_sym_example.smt2"
    IO.FS.writeFile tmp smt
    let out ← IO.Process.output { cmd := "z3", args := #[tmp] }
    return out.stdout.trim ++ (if out.stderr.isEmpty then "" else "\n[stderr] " ++ out.stderr)
  catch e =>
    return s!"<could not run z3: {e}>"

/-- Does `s` contain `t` as a substring? -/
def contains? (s t : String) : Bool := (s.splitOn t).length ≥ 2

/-- Interpret z3's answer. On `unsat`, inspect the unsat core: if the
`determinate` (`¬inc`) guard is in it, the failure is an artefact of the fuel
bound (raise the fuel); otherwise the failure is genuine and bound-independent. -/
def verdict (z3out : String) : String :=
  let lines := (z3out.splitOn "\n").map String.trim
  if lines.contains "unsat" then
    let core := ((lines.dropWhile (· != "unsat")).drop 1).head?.getD ""
    if contains? core "determinate" then
      s!"⟹ UNSAT, but core = {core} contains `determinate`: INCONCLUSIVE — some inputs are\n   beyond the fuel horizon; the real answer may exist past it. Raise the fuel."
    else
      s!"⟹ UNSAT, core = {core} (no `determinate`): GENUINE — holds independent of the fuel bound."
  else if lines.contains "sat" then
    "⟹ SAT: a concrete witness exists (see model above)."
  else s!"⟹ {z3out}"

/-- Print the generated SMT-LIB and z3's answer + verdict for a compiled goal. -/
def demo (title : String) (c : Compiled) (goal : SymR → List (String × SExpr)) : IO Unit := do
  let smt := c.toSMTLib goal
  IO.println s!"════════════════════════════════════════════════════════════════"
  IO.println s!"  {title}"
  IO.println s!"════════════════════════════════════════════════════════════════"
  IO.println smt
  IO.println "──── z3 ────"
  let out ← runZ3 smt
  IO.println out
  IO.println (verdict out)
  IO.println ""

/-! ## Example 1 — symbolic `equalsInteger`/`addInteger`

`[(builtin equalsInteger) (con integer 10) [(builtin addInteger) (con integer 5) x]]`
with `x : Integer` symbolic — solve for `x` making the result `true` (expect `x = 5`). -/

def ex1 : Term := b2 .EqualsInteger (intC 10) (b2 .AddInteger (intC 5) (.Var 1))

#eval demo "Example 1: equalsInteger 10 (addInteger 5 x) = true   (expect x = 5)"
  (compile 10 [("x", .integer)] ex1) (goalReturnsBool · true)

/-! ## Example 2 — symbolic builtin `Case` on an Integer

`(case x [error, error, (con bool true)])` with `x : Integer` symbolic — the only
non-erroring choice is the branch index `2`, so solve for it (expect `x = 2`). -/

def ex2 : Term := .Case (.Var 1) [.Error, .Error, boolC true]

#eval demo "Example 2: case x [error, error, true] returns true   (expect x = 2)"
  (compile 10 [("x", .integer)] ex2) (goalReturnsBool · true)

/-! ## Example 3 — `ifThenElse` building a symbolic `Constr`, then `Case` on it

`(case (if x == 10 then Constr 0 [] else Constr 1 []) [error, (con bool true)])`.
Branch `0` errors, branch `1` returns `true`; so the term **errors** exactly when
`x = 10`. Solve for the error case (expect `x = 10`). -/

def ex3 : Term :=
  .Case (ite3 (b2 .EqualsInteger (.Var 1) (intC 10)) (.Constr 0 []) (.Constr 1 []))
        [.Error, boolC true]

#eval demo "Example 3: case (if x==10 then C0 else C1) [error, true] ERRORS   (expect x = 10)"
  (compile 12 [("x", .integer)] ex3) goalErrors

-- …and the *value* side of Example 3: it returns `true` when `x ≠ 10`.
#eval demo "Example 3b: same term returns true   (expect any x ≠ 10)"
  (compile 12 [("x", .integer)] ex3) (goalReturnsBool · true)

/-! ## Example 4 — `force`/`delay` interacting with symbolic data (lazy branch)

`force (if x < 0 then delay (con integer 100) else delay (addInteger x x))`.
Only the *selected* thunk is forced (laziness through `choice`). Solve for the
result being `100` (expect any `x < 0`) and for `addInteger x x = 6` (expect `x = 3`). -/

def ex4 : Term :=
  .Force (ite3 (b2 .LessThanInteger (.Var 1) (intC 0))
               (.Delay (intC 100))
               (.Delay (b2 .AddInteger (.Var 1) (.Var 1))))

#eval demo "Example 4: force (if x<0 then delay 100 else delay (x+x)) = 6   (expect x = 3)"
  (compile 14 [("x", .integer)] ex4) (goalReturnsInt · 6)

/-! ## Example 5 — opaque hashing congruence

`equalsByteString (sha2_256 a) (sha2_256 b)` with `a b : ByteString` symbolic.
Hashing is an *uninterpreted* function, so z3 only knows congruence. Asking for
`a = b` ∧ hashes-equal is trivially `sat`; asking for hashes-equal alone is also
`sat` (the UF can collide) — this demonstrates the opaque modelling. -/

def ex5 : Term := b2 .EqualsByteString (b1 .Sha2_256 (.Var 1)) (b1 .Sha2_256 (.Var 2))

#eval demo "Example 5: equalsByteString (sha2_256 a) (sha2_256 b) = true (opaque hash)"
  (compile 12 [("a", .bytestring), ("b", .bytestring)] ex5) (goalReturnsBool · true)

/-! ## Example 6 — bounded recursion (the fueled `sum`)

`sum n = if n < 1 then 0 else n + sum (n-1)`, encoded with the call-by-value
Z-combinator. With `n` symbolic, bounded unrolling makes the *incomplete*
condition a path predicate (`n` deeper than the fuel allows); for `n` within the
unrolling the value is exact. Solve `sum n = 10` (expect `n = 4`: 4+3+2+1). -/

/-- `Z = λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))` (CBV fixpoint), de Bruijn. -/
def zComb : Term :=
  let m : Term := .Lam 0 (.Apply (.Var 2) (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1))))
  .Lam 0 (.Apply m m)

/-- `F = λself. λn. force (if n<1 then delay 0 else delay (n + self (n-1)))`. -/
def sumF : Term :=
  .Lam 0 (.Lam 0
    (.Force (ite3 (b2 .LessThanInteger (.Var 1) (intC 1))
                  (.Delay (intC 0))
                  (.Delay (b2 .AddInteger (.Var 1)
                              (.Apply (.Var 2) (b2 .SubtractInteger (.Var 1) (intC 1))))))))

/-- `sum n` applied to the symbolic input (`n = Var 1`). -/
def ex6 : Term := .Apply (.Apply zComb sumF) (.Var 1)

#eval demo "Example 6: bounded recursion  sum n = 10   (expect n = 4)"
  (compile 200 [("n", .integer)] ex6) (goalReturnsInt · 10)

/-! ## Partiality / bidirectionality checks (the soundness property to come)

These probe that the *error* condition is tight — both "errors ⇒ must be this
input" and "succeeds ⇒ must NOT be that input" — by asking z3 to refute the
complement. `unsat` is the desired (good) answer in both. -/

-- For Example 2, `x = 2` must be the *unique* non-erroring input: assert it
-- succeeds *and* `x ≠ 2`.  Expect **unsat**.
#eval demo "Partiality 2: (succeeds ∧ x ≠ 2) for `case x [err,err,true]`   (expect UNSAT, genuine)"
  (compile 10 [("x", .integer)] ex2)
  (fun r => goalSucceeds r ++ [("assume_xne2", SExpr.sNot (SExpr.sEq (.atom "x") (.int 2)))])

-- For Example 3, `x = 10` must *always* error: assert it succeeds *and*
-- `x = 10`.  Expect **unsat** (the CEK must fail there).
#eval demo "Partiality 3: (succeeds ∧ x = 10) for Example 3   (expect UNSAT, genuine — must error)"
  (compile 12 [("x", .integer)] ex3)
  (fun r => goalSucceeds r ++ [("assume_xeq10", SExpr.sEq (.atom "x") (.int 10))])

/-! ## Builtin type-checking matches the CEK (the `MkCons` concern)

`mkCons` onto a `list(data)` requires the head to be `Data` — the CEK throws
otherwise, and so must the compiler, or adequacy would fail. -/

abbrev unitC : Term := .Constant (.Unit, .AtomicType .TypeUnit)
/-- `mkNilData ()` : an empty `list(data)` (`ConstDataList`). -/
def mkNilD : Term := .Apply (.Builtin .MkNilData) unitC
/-- `mkCons` needs one type-force then (head, tail). -/
def mkConsT (head tail : Term) : Term :=
  .Apply (.Apply (.Force (.Builtin .MkCons)) head) tail

/-- **Ill-typed**: cons the *integer* `x` onto a `list(data)` — the CEK errors for
every `x`, so the compiler must too: asking it to *succeed* is **unsat**. -/
def exConsBad : Term := mkConsT (.Var 1) mkNilD
#eval demo "MkCons type-check: cons Int onto list(data) can succeed?   (expect UNSAT)"
  (compile 12 [("x", .integer)] exConsBad) goalSucceeds

-- …and it *errors* for all `x`: asking it to error is **sat**.
#eval demo "MkCons type-check: cons Int onto list(data) errors          (expect SAT)"
  (compile 12 [("x", .integer)] exConsBad) goalErrors

/-- **Well-typed**: cons `iData x` (a `Data`) onto a `list(data)` — succeeds. -/
def exConsGood : Term := mkConsT (.Apply (.Builtin .IData) (.Var 1)) mkNilD
#eval demo "MkCons type-check: cons (iData x) onto list(data) succeeds   (expect SAT)"
  (compile 12 [("x", .integer)] exConsGood) goalSucceeds

/-! ## Diagnosing recursion failures: `inc` (fuel) vs a genuine result

`sum n = 55` needs `n = 10` (1+…+10), i.e. ~10 unrollings. With too little fuel
that witness is *beyond the horizon*: the query is `unsat`, but the unsat core
contains `determinate` — telling us the failure is a fuel artefact, not a real
"no such n". With enough fuel the witness `n = 10` is found. Contrast with the
genuine `unsat`s above (Partiality 2/3), whose cores do **not** mention
`determinate`. -/

-- Too little fuel: `sum n = 55` is `unsat` **because of the bound** (core has
-- `determinate`). The diagnostic says: raise the fuel.
#eval demo "Recursion diag: sum n = 55 at LOW fuel   (expect UNSAT, inc-limited)"
  (compile 70 [("n", .integer)] ex6) (goalReturnsInt · 55)

-- Enough fuel: the same query now finds `n = 10`.
#eval demo "Recursion diag: sum n = 55 at HIGH fuel   (expect SAT, n = 10)"
  (compile 130 [("n", .integer)] ex6) (goalReturnsInt · 55)

-- Fuel-coverage check: is any `n` indeterminate at this fuel? `sat` ⇒ the bound
-- does not cover all inputs (so negative results are inconclusive).
#eval demo "Recursion diag: is any n beyond the fuel horizon?   (expect SAT — fuel not total)"
  (compile 200 [("n", .integer)] ex6) goalIndeterminate

end Test.Symbolic.Examples
