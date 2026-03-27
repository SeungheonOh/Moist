import Moist.CEK.Machine
import Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term

/-! # CEK Machine Smoke Tests -/

private def intT (i : Int) : Term := .Constant (.Integer i, .AtomicType .TypeInteger)
private def boolT (b : Bool) : Term := .Constant (.Bool b, .AtomicType .TypeBool)

-- 1. Literal: 42
#eval (eval (intT 42)).result

-- 2. Identity: (λ. Var 1) 42
#eval (eval (.Apply (.Lam 0 (.Var 1)) (intT 42))).result

-- 3. addInteger 3 5 = 8, budget should be cpu=181308, mem=602
#eval
  let r := eval (.Apply (.Apply (.Builtin .AddInteger) (intT 3)) (intT 5))
  (r.result, r.consumed)

-- 4. Force (Delay 42)
#eval (eval (.Force (.Delay (intT 42)))).result

-- 5. let x=10, y=20 in add x y = 30
#eval (eval
  (.Apply (.Lam 0 (.Apply (.Lam 0
    (.Apply (.Apply (.Builtin .AddInteger) (.Var 2)) (.Var 1)))
    (intT 20))) (intT 10))).result

-- 6. Error → failure
#eval (eval .Error).result

-- 7. IfThenElse true 1 2 = 1
#eval (eval
  (.Force (.Apply (.Apply (.Apply
    (.Force (.Builtin .IfThenElse)) (boolT true))
    (.Delay (intT 1))) (.Delay (intT 2))))).result

-- 8. Unbound var → failure
#eval (eval (.Var 99)).result

-- 9. Case Constr
#eval (eval
  (.Case (.Constr 0 [intT 10, intT 20])
    [.Lam 0 (.Lam 0 (.Apply (.Apply (.Builtin .AddInteger) (.Var 2)) (.Var 1)))])).result

-- 10. Dead let example: both should produce 10
private def f_term : Term :=
  .Lam 0 (.Apply (.Lam 0 (intT 10)) (.Apply (.Apply (.Builtin .AddInteger) (intT 3)) (intT 4)))
private def g_term : Term := .Lam 0 (intT 10)

#eval (eval (.Apply f_term (intT 99))).result
#eval (eval (.Apply g_term (intT 99))).result

-- Same observation
open Moist.Verified.Semantics in
#eval (obsOf (eval (.Apply f_term (intT 99))).result,
       obsOf (eval (.Apply g_term (intT 99))).result)

def main : IO Unit := pure ()
