import Moist.Verified.DeadLet

/-! # MIR Dead Let Elimination Examples

Concrete examples of dead-let elimination proved via `dead_let_mirRefines`.
-/

namespace Moist.Verified.MIRExample

open Moist.MIR (Expr VarId freeVars)
open Moist.Verified.MIR
open Moist.Verified.DeadLet

private def a : VarId := { uid := 0, hint := "a" }
private def x : VarId := { uid := 1, hint := "x" }

private abbrev intLit (n : Int) : Expr :=
  .Lit (.Integer n, .AtomicType .TypeInteger)

/-- `let x = 10 in a` refines `a` (where `a` is a free variable).
    The let-bound `x` is unused in the body `a`. -/
theorem let_x_10_in_a_refines_a :
    (.Let [({ uid := 1 }, intLit 10, false)] (.Var { uid := 0 }) : Expr) ⊑ᴹ
      .Var { uid := 0 } :=
  dead_let_mirRefines (by native_decide) (by native_decide)

end Moist.Verified.MIRExample
