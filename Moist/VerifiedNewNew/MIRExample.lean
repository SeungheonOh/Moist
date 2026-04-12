import Moist.VerifiedNewNew.DeadLet

/-! # MIR Dead Let Elimination Examples

Concrete examples of dead-let elimination proved via `dead_let_sound`.
-/

namespace Moist.VerifiedNewNew.MIRExample

open Moist.MIR (Expr VarId freeVars isPure fixCount)
open Moist.VerifiedNewNew.MIR
open Moist.VerifiedNewNew.DeadLet

private def a : VarId := { uid := 0, hint := "a" }
private def x : VarId := { uid := 1, hint := "x" }

private abbrev intLit (n : Int) : Expr :=
  .Lit (.Integer n, .AtomicType .TypeInteger)

/-- `let x = 10 in a` refines `a` (where `a` is a free variable).
    The let-bound `x` is unused in the body `a`, and the RHS `10` is pure. -/
theorem let_x_10_in_a_refines_a :
    .Let [({ uid := 1 }, intLit 10, false)] (.Var { uid := 0 }) ⊑ᴹ .Var { uid := 0 } := by
  apply dead_let_sound
  exact {
    unused := by native_decide
    safe := by native_decide
    fixFree := by native_decide
  }

end Moist.VerifiedNewNew.MIRExample
