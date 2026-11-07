import Moist.Verified.MIR.Hoist

/-! # Atomization: `e ⊑ let x = e in x` -/

namespace Moist.Verified.MIR

open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal expandFix envLookupT_cons_self)
open Moist.Verified (closedAt)
open Moist.Verified.FundamentalRefines (ftlr)

theorem mirCtxRefines_atomize (e : Expr) (x : VarId) :
    MIRCtxRefines e (.Let [(x, e, false)] (.Var x)) := by
  refine mirCtxRefines_of_shape (fun env => lowerTotalExpr env e) (fun _ t => t)
    (fun _ t => .Apply (.Lam 0 (.Var 1)) t) (fun env => ?_) (fun env => ?_)
    (fun _ _ k h => by simpa [closedAt] using h) ?_
  · dsimp only; cases lowerTotalExpr env e <;> rfl
  · have hx : lowerTotalExpr (x :: env) (.Var x) = some (.Var 1) := by
      simp [lowerTotalExpr, expandFix, lowerTotal, envLookupT_cons_self]
    rw [lowerTotalExpr_let_single, hx]; dsimp only
    cases lowerTotalExpr env e <;> rfl
  · intro env t ht k j _ ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    exact obsRefinesK_of_steps_right (n := 3) rfl <|
      ftlr _ t (lowerTotalExpr_closedAt ht) j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi _ _
        (stackRefK_funV_id_augment_right hπ)

end Moist.Verified.MIR
