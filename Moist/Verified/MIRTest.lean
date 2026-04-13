import Moist.Verified.MIR
import Moist.CEK.DecidableEq

/-! # MIR-Level Refinement Tests

Manual proofs that concrete MIR-to-MIR transformations are correct
refinements under the biorthogonal logical relation.
-/

namespace Moist.Verified.MIRTest

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal expandFix fixCount)
open Moist.Plutus.Term (Term Const BuiltinFun BuiltinType AtomicType)
open Moist.Verified.MIR
open Moist.Verified.Equivalence

-- ── Abbreviations ──

private def a : VarId := { uid := 0 }
private def x : VarId := { uid := 1 }
private def y : VarId := { uid := 2 }

private abbrev intLit (n : Int) : Expr := .Lit (.Integer n, .AtomicType .TypeInteger)
private abbrev intTerm (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private abbrev mirLam (v : VarId) (body : Expr) : Expr := .Lam v body
private abbrev mirApp (f arg : Expr) : Expr := .App f arg
private abbrev mirLet (v : VarId) (rhs : Expr) (body : Expr) : Expr :=
  .Let [(v, rhs, false)] body
private abbrev addInt : Expr := .Builtin .AddInteger

--------------------------------------------------------------------------------
-- 1. Dead let elimination: let x = a in 10 ⊑ᴹ 10
--    where `a` is a free variable at depth 1
--
--    LHS lowers to: Apply (Lam 0 (Constant 10)) (Var 1)
--    RHS lowers to: Constant 10
--    The let-bound variable x is unused, so the let is dead.
--------------------------------------------------------------------------------

/-- Dead let elimination at depth 1.
    `let x = a in 10` refines `10` because the let-bound variable is unused. -/
theorem dead_let_refines_lit :
    MIRRefines (mirLet x (.Var a) (intLit 10)) (intLit 10) := by
  sorry

--------------------------------------------------------------------------------
-- 2. λy. let x = a in 10 ⊑ᴹ λy. 10
--    Dead let elimination under a lambda.
--------------------------------------------------------------------------------

theorem dead_let_under_lam :
    MIRRefines (mirLam y (mirLet x (.Var a) (intLit 10)))
               (mirLam y (intLit 10)) := by
  sorry

--------------------------------------------------------------------------------
-- 3. Delay (1 + 3) ⊑ᴹ Delay 4   (constant folding under delay)
--
--    LHS lowers to: Delay (Apply (Apply (Builtin AddInteger) (Constant 1)) (Constant 3))
--    RHS lowers to: Delay (Constant 4)
--    When forced, both produce VCon (Integer 4).
--------------------------------------------------------------------------------

theorem delay_const_fold :
    MIRRefines (.Delay (mirApp (mirApp addInt (intLit 1)) (intLit 3)))
               (.Delay (intLit 4)) := by
  sorry

--------------------------------------------------------------------------------
-- 4. λx y. Delay (1 + 3) ⊑ᴹ λx y. Delay 4
--    Constant folding under lambdas.
--------------------------------------------------------------------------------

theorem delay_const_fold_under_lam :
    MIRRefines (mirLam x (mirLam y (.Delay (mirApp (mirApp addInt (intLit 1)) (intLit 3)))))
               (mirLam x (mirLam y (.Delay (intLit 4)))) := by
  sorry

end Moist.Verified.MIRTest
