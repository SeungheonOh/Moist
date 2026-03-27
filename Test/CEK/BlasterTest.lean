import Blaster
import Moist.CEK.ClosedAt
import Moist.CEK.Machine
import Moist.CEK.Bisim
import Moist.CEK.DeadLet
import Moist.MIR.Semantics
import Moist.MIR.LowerTotal

open Moist.CEK
open Moist.CEK.DeadLet
open Moist.Plutus.Term
open Moist.MIR
open Moist.MIR.Semantics

/-! # Lean-blaster on CEK dead-let properties

NOTE: blaster uses `admit` (Z3-trusted, not kernel-verified).
-/

-- === Already proved individually, testing blaster can handle them ===

-- step_preserves for compute + Constant
#blaster (timeout: 10) [∀ (s1 s2 : Stack) (env1 env2 : CekEnv) (c : Const) (ty : BuiltinType),
  step (.compute s1 env1 (.Constant (c, ty))) = .ret s1 (.VCon c) ∧
  step (.compute s2 env2 (.Constant (c, ty))) = .ret s2 (.VCon c)]

-- step on Apply
#blaster (timeout: 10) [∀ (s : Stack) (env : CekEnv) (f x : Term),
  step (.compute s env (.Apply f x)) = .compute (.arg x env :: s) env f]

-- 5-step decomposition for Apply (Lam 0 body) (Constant (c, ty))
-- This is the key lemma we proved by chaining 5 rfl steps
#blaster (timeout: 30) (unfold-depth: 20)
  [∀ (body : Term) (env : CekEnv) (c : Const) (ty : BuiltinType),
    steps 5 (.compute [] env (.Apply (.Lam 0 body) (.Constant (c, ty)))) =
    .compute [] (env.extend (.VCon c)) body]

-- closedAt monotonicity (simple case)
#blaster (timeout: 10) [∀ (n d d' : Nat), n ≤ d → d ≤ d' → n ≤ d']

-- The concrete dead-let example: lowering equality
private def x_ : VarId := ⟨1, "x"⟩
private def foo_ : VarId := ⟨2, "foo"⟩
private def intLit_ (i : Int) : Expr := .Lit (.Integer i, .AtomicType .TypeInteger)

def testLhs : Expr :=
  .Lam x_ (.Let [(foo_, .App (.App (.Builtin .AddInteger) (intLit_ 1)) (intLit_ 2), false)]
           (intLit_ 10))
def testRhs : Expr := .Lam x_ (intLit_ 10)

-- Can blaster verify the lowering? (requires unfolding lowerTotal)
#blaster (timeout: 60) (unfold-depth: 200)
  [lowerTotal [foo_] (intLit_ 10) = lowerTotal [] (intLit_ 10)]

-- The FULL dead_let_sound_closed for the concrete example
-- This is very ambitious
theorem concrete_dead_let_blaster :
    BehEqClosed (.Let [(foo_, .App (.App (.Builtin .AddInteger) (intLit_ 1)) (intLit_ 2), false)]
      (intLit_ 10)) (intLit_ 10) := by
  blaster (timeout: 120) (unfold-depth: 300)
