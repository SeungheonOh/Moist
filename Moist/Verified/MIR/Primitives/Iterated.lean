import Moist.Verified.MIR.Primitives.Atomize
import Moist.Verified.MIR.Primitives.LetFlattenRhsHead

/-! # Binding-list and argument-list helpers -/

namespace Moist.Verified.MIR

open Moist.MIR (Expr VarId lowerTotalExpr flattenLetBody)
open Moist.Verified.Equivalence (ListRel)

/-- `Constr` congruence on a whole argument list. -/
theorem mirCtxRefines_constr_of_listRel (tag : Nat) {args₁ args₂ : List Expr}
    (h : ListRel MIRCtxRefines args₁ args₂) :
    MIRCtxRefines (.Constr tag args₁) (.Constr tag args₂) := by
  cases args₁ <;> cases args₂ <;> first
    | exact mirCtxRefines_refl _
    | exact h.elim
    | exact mirCtxRefines_constr h.1 h.2

theorem mirCtxRefines_flattenLetBody (binds : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let binds body) (flattenLetBody binds body) :=
  mirCtxRefines_of_lowerEq fun env => by
    cases body <;> first
      | rfl
      | exact lowerTotalExpr_let_flatten_body _ _ _ env

end Moist.Verified.MIR
