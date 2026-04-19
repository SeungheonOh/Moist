import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.ANF
import Moist.MIR.Pretty
import Moist.Plutus.Eval
import Moist.Plutus.Pretty
import Test.Framework

namespace Test.MIR

open Moist.MIR
open Moist.Plutus.Term
open Moist.Plutus.Eval (evalTerm)
open Moist.Plutus.Pretty (prettyTerm)
open Test.Framework

/-! ## Variable Fixtures (uids 1-8) -/

def x : VarId := ⟨1, .source, "x"⟩
def y : VarId := ⟨2, .source, "y"⟩
def z : VarId := ⟨3, .source, "z"⟩
def f : VarId := ⟨4, .source, "f"⟩
def g : VarId := ⟨5, .source, "g"⟩
def n : VarId := ⟨6, .source, "n"⟩
def a : VarId := ⟨7, .source, "a"⟩
def b : VarId := ⟨8, .source, "b"⟩

/-! ## Additional Variable Fixtures (uids 9-11) -/

def c : VarId := ⟨9, .source, "c"⟩
def d : VarId := ⟨10, .source, "d"⟩
def w : VarId := ⟨11, .source, "w"⟩

/-! ## Optimization Test Fixtures (uids 50+) -/

def v : VarId := ⟨50, .source, "v"⟩

/-! Dummy bound vars for expected expressions (uids 900+).
    alphaEq matches by binding position, so exact uids don't matter. -/

def t1 : VarId := ⟨901, .source, "t"⟩
def t2 : VarId := ⟨902, .source, "t"⟩
def t3 : VarId := ⟨903, .source, "t"⟩

/-! ## Literal Helpers -/

def intLit (val : Int) : Expr :=
  .Lit (.Integer val, .AtomicType .TypeInteger)

def boolLit (val : Bool) : Expr :=
  .Lit (.Bool val, .AtomicType .TypeBool)

/-! ## Assertion Helpers (IO Unit, for use inside .test bodies) -/

def check (name : String) (cond : Bool) : IO Unit :=
  unless cond do throw (.userError s!"FAIL: {name}")

def checkEq [BEq α] [ToString α] (name : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (.userError s!"FAIL: {name}\n  expected: {expected}\n  actual:   {actual}")

def checkAlphaEq (name : String) (actual expected : Expr) : IO Unit :=
  unless alphaEq actual expected do
    throw (.userError s!"FAIL: {name}\n  expected: {pretty expected}\n  actual:   {pretty actual}")

def checkANF (name : String) (e : Expr) : IO Unit :=
  unless e.isANF do
    throw (.userError s!"FAIL: {name} -- not ANF\n  {pretty e}")

def checkChanged (name : String) (actual expected : Bool) : IO Unit :=
  unless actual == expected do
    throw (.userError s!"FAIL: {name} -- expected changed={expected}, got changed={actual}")

def checkPassResult (name : String) (result : Expr × Bool) (expected : Expr)
    (expectedChanged : Bool) : IO Unit := do
  checkAlphaEq name result.1 expected
  checkChanged s!"{name}_changed" result.2 expectedChanged

/-! ## TestTree Combinators (TreeBuilder) -/

def checkTest (name : String) (cond : Bool) : TreeBuilder Unit :=
  test name (unless cond do throw (.userError s!"FAIL: {name}"))

def eqTest [BEq α] [ToString α] (name : String) (actual expected : α) : TreeBuilder Unit :=
  test name (unless actual == expected do
    throw (.userError s!"FAIL: {name}\n  expected: {expected}\n  actual:   {actual}"))

def alphaEqTest (name : String) (actual expected : Expr) : TreeBuilder Unit :=
  test name (unless alphaEq actual expected do
    throw (.userError s!"FAIL: {name}\n  expected: {pretty expected}\n  actual:   {pretty actual}"))

def passResultTest (name : String) (result : Expr × Bool) (expected : Expr) (expectedChanged : Bool) : TreeBuilder Unit :=
  test name (do
    unless alphaEq result.1 expected do
      throw (.userError s!"FAIL: {name}\n  expected: {pretty expected}\n  actual:   {pretty result.1}")
    unless result.2 == expectedChanged do
      throw (.userError s!"FAIL: {name}_changed -- expected changed={expectedChanged}, got changed={result.2}"))

/-! ## Normalization Helper -/

def normalize (e : Expr) (start : Nat := 100) : Expr :=
  runFresh (anfNormalize e) start

/-! ## Shared Test Fixtures -/

/-- Large lambda exceeding inlineThreshold (size = 8 > 5). -/
def largeLam : Expr :=
  .Lam y (.App (.Var y) (.App (.Var y) (.App (.Var y) (.Var y))))

/-! ## Factorial Expression (from MIR-Plan.md) -/

def factorialMIR : Expr :=
  let fac  : VarId := ⟨10, .source, "fac"⟩
  let n    : VarId := ⟨11, .source, "n"⟩
  let t0   : VarId := ⟨12, .source, "isZero"⟩
  let t1   : VarId := ⟨13, .source, "n1"⟩
  let t2   : VarId := ⟨14, .source, "facN1"⟩
  .Let
    [(fac,
      .Fix fac
        (.Lam n
          (.Let
            [(t0, .App (.App (.Builtin .EqualsInteger) (.Var n))
                       (intLit 0), false)]
            (.Force
              (.App
                (.App
                  (.App (.Builtin .IfThenElse) (.Var t0))
                  (.Delay (intLit 1)))
                (.Delay
                  (.Let
                    [(t1, .App (.App (.Builtin .SubtractInteger) (.Var n))
                                (intLit 1), false),
                     (t2, .App (.Var fac) (.Var t1), false)]
                    (.App (.App (.Builtin .MultiplyInteger) (.Var n))
                          (.Var t2)))))))), false)]
    (.App (.Var fac) (intLit 10))

/-! ## Data Deconstruction Expression -/

def dataDeconstructMIR : Expr :=
  let foo  : VarId := ⟨20, .source, "foo"⟩
  let flds : VarId := ⟨21, .source, "flds"⟩
  let fA   : VarId := ⟨22, .source, "fA"⟩
  let fC   : VarId := ⟨23, .source, "fC"⟩
  let fD   : VarId := ⟨24, .source, "fD"⟩
  let sndP := Expr.Force (.Force (.Builtin .SndPair))
  let hd   := Expr.Force (.Builtin .HeadList)
  let tl   := Expr.Force (.Builtin .TailList)
  .Lam foo
    (.Let [(flds, .App sndP (.App (.Builtin .UnConstrData) (.Var foo)), false)]
      (.Let [(fA, .App (.Builtin .UnIData) (.App hd (.Var flds)), false)]
        (.Let [(fC, .App (.Builtin .UnIData)
                (.App hd (.App tl (.App tl (.Var flds)))), false)]
          (.Let [(fD, .App (.Builtin .UnIData)
                  (.App hd (.App tl (.App tl (.App tl (.Var flds))))), false)]
            (.App (.App (.Builtin .AddInteger) (.Var fA))
              (.App (.App (.Builtin .AddInteger) (.Var fC)) (.Var fD)))))))

/-! ## Golden Test Formatters -/

def mkGoldenCase (name : String) (input : Expr) (freshStart : Nat := 100) : TreeBuilder Unit :=
  golden name <| pure <|
    let normalized := runFresh (anfNormalize input) freshStart
    let isAnf := normalized.isANF
    goldenSections [("output", pretty normalized), ("isANF", s!"{isAnf}")]

def mkIdempotencyCase (name : String) (input : Expr) : TreeBuilder Unit :=
  golden name <| pure <|
    let n1 := runFresh (anfNormalize input) 100
    let n2 := runFresh (anfNormalize n1) 200
    let equiv := alphaEq n1 n2
    goldenSections [("firstPass", pretty n1), ("secondPass", pretty n2), ("alphaEquivalent", s!"{equiv}")]

/-! ## UPLC Eval Golden Helpers -/

/-- Golden test that evaluates a compiled UPLC `Term` and records the result + budget. -/
def mkTermEvalGolden (name : String) (term : Term) : TreeBuilder Unit :=
  golden name do
    match ← evalTerm term with
    | .ok r =>
      pure <| goldenSections [("result", prettyTerm r.term), ("cpu", s!"{r.budget.cpu}"), ("mem", s!"{r.budget.mem}")]
    | .error (err, budget, msg) =>
      pure <| goldenSections [("error", s!"{err}: {msg}"), ("cpu", s!"{budget.cpu}"), ("mem", s!"{budget.mem}")]

/-- Golden test that applies arguments to a UPLC function term, evaluates, and records result + budget. -/
def mkTermApplyEvalGolden (name : String) (fn : Term) (args : List Term) : TreeBuilder Unit :=
  mkTermEvalGolden name (args.foldl Term.Apply fn)

end Test.MIR
