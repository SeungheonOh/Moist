import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.ANF
import Moist.MIR.Pretty
import Test.Framework

namespace Test.MIR

open Moist.MIR
open Moist.Plutus.Term

/-! ## Variable Fixtures (uids 1-8) -/

def x : VarId := ⟨1, "x"⟩
def y : VarId := ⟨2, "y"⟩
def z : VarId := ⟨3, "z"⟩
def f : VarId := ⟨4, "f"⟩
def g : VarId := ⟨5, "g"⟩
def n : VarId := ⟨6, "n"⟩
def a : VarId := ⟨7, "a"⟩
def b : VarId := ⟨8, "b"⟩

/-! ## Additional Variable Fixtures (uids 9-11) -/

def c : VarId := ⟨9, "c"⟩
def d : VarId := ⟨10, "d"⟩
def w : VarId := ⟨11, "w"⟩

/-! Dummy bound vars for expected expressions (uids 900+).
    alphaEq matches by binding position, so exact uids don't matter. -/

def t1 : VarId := ⟨901, "t"⟩
def t2 : VarId := ⟨902, "t"⟩
def t3 : VarId := ⟨903, "t"⟩

/-! ## Literal Helpers -/

def intLit (val : Int) : Expr :=
  .Lit (.Integer val, .AtomicType .TypeInteger)

def boolLit (val : Bool) : Expr :=
  .Lit (.Bool val, .AtomicType .TypeBool)

/-! ## Assertion Helpers -/

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

/-! ## Normalization Helper -/

def normalize (e : Expr) (start : Nat := 100) : Expr :=
  runFresh (anfNormalize e) start

/-! ## Factorial Expression (from MIR-Plan.md) -/

def factorialMIR : Expr :=
  let fac  : VarId := ⟨10, "fac"⟩
  let n    : VarId := ⟨11, "n"⟩
  let t0   : VarId := ⟨12, "isZero"⟩
  let t1   : VarId := ⟨13, "n1"⟩
  let t2   : VarId := ⟨14, "facN1"⟩
  .Let
    [(fac,
      .Fix fac
        (.Lam n
          (.Let
            [(t0, .App (.App (.Builtin .EqualsInteger) (.Var n))
                       (intLit 0))]
            (.Force
              (.App
                (.App
                  (.App (.Builtin .IfThenElse) (.Var t0))
                  (.Delay (intLit 1)))
                (.Delay
                  (.Let
                    [(t1, .App (.App (.Builtin .SubtractInteger) (.Var n))
                                (intLit 1)),
                     (t2, .App (.Var fac) (.Var t1))]
                    (.App (.App (.Builtin .MultiplyInteger) (.Var n))
                          (.Var t2)))))))))]
    (.App (.Var fac) (intLit 10))

/-! ## Data Deconstruction Expression

Represents extracting fields 0, 2, 3 from a Data-encoded constructor
and summing them:

```
λfoo.
  let flds = sndPair (unConstrData foo)
  let a    = unIData (headList flds)           -- field 0
  let c    = unIData (headList (tailList (tailList flds)))  -- field 2
  let d    = unIData (headList (tailList (tailList (tailList flds))))  -- field 3
  in addInteger a (addInteger c d)
```

CSE opportunities: `force tailList`, `force headList`, `tailList flds`,
and `tailList (tailList flds)` are all shared sub-expressions.
-/

def dataDeconstructMIR : Expr :=
  let foo  : VarId := ⟨20, "foo"⟩
  let flds : VarId := ⟨21, "flds"⟩
  let fA   : VarId := ⟨22, "fA"⟩
  let fC   : VarId := ⟨23, "fC"⟩
  let fD   : VarId := ⟨24, "fD"⟩
  let sndP := Expr.Force (.Force (.Builtin .SndPair))
  let hd   := Expr.Force (.Builtin .HeadList)
  let tl   := Expr.Force (.Builtin .TailList)
  .Lam foo
    (.Let [(flds, .App sndP (.App (.Builtin .UnConstrData) (.Var foo)))]
      (.Let [(fA, .App (.Builtin .UnIData) (.App hd (.Var flds)))]
        (.Let [(fC, .App (.Builtin .UnIData)
                (.App hd (.App tl (.App tl (.Var flds)))))]
          (.Let [(fD, .App (.Builtin .UnIData)
                  (.App hd (.App tl (.App tl (.App tl (.Var flds))))))]
            (.App (.App (.Builtin .AddInteger) (.Var fA))
              (.App (.App (.Builtin .AddInteger) (.Var fC)) (.Var fD)))))))

/-! ## Golden Test Formatters -/

def mkGoldenCase (name : String) (input : Expr) (freshStart : Nat := 100) : Test.Framework.GoldenSpec :=
  let normalized := runFresh (anfNormalize input) freshStart
  let isAnf := normalized.isANF
  let output := s!"--- Input ---\n{pretty input}\n--- Output ---\n{pretty normalized}\n--- isANF ---\n{isAnf}"
  { name, render := pure output }

def mkIdempotencyCase (name : String) (input : Expr) : Test.Framework.GoldenSpec :=
  let n1 := runFresh (anfNormalize input) 100
  let n2 := runFresh (anfNormalize n1) 200
  let equiv := alphaEq n1 n2
  let output := s!"--- Input ---\n{pretty input}\n--- First Pass ---\n{pretty n1}\n--- Second Pass ---\n{pretty n2}\n--- Alpha Equivalent ---\n{equiv}"
  { name, render := pure output }

end Test.MIR
