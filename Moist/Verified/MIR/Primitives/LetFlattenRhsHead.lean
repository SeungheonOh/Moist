import Moist.Verified.MIR.Hoist

/-! # Flattening `let`-valued bindings

`flattenLetBinds` turns `let x = (let ibs in e) in …` into
`let ibs; x = e in …`. Each step is a hoist out of the binding's RHS
(`MFrame.letRhs`), valid when the inner binders are fresh for the later
bindings and the body, which is what `flattenReadyCheck` checks. -/

namespace Moist.Verified.MIR

open Moist.MIR (Expr VarId lowerTotalExpr wrapLet freeVars flattenLetBinds flattenReadyCheck)

theorem mirCtxRefines_let_flatten_rhs_head (x : VarId) (ibs : List (VarId × Expr × Bool))
    (ib : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (hfresh : ∀ b ∈ ibs,
      (∀ r ∈ rest, (freeVars r.2.1).contains b.1 = false) ∧ (freeVars body).contains b.1 = false) :
    MIRCtxRefines (.Let ((x, .Let ibs ib, er) :: rest) body)
      (.Let (ibs ++ (x, ib, er) :: rest) body) :=
  have F := (MFrame.letRhs x er rest body).lowerTotalExpr_fill
  mirCtxRefines_trans (mirCtxRefines_of_lowerEq
      (m₂ := (MFrame.letRhs x er rest body).fill (wrapLet ibs ib)) fun env => by
      show lowerTotalExpr env ((MFrame.letRhs x er rest body).fill (.Let ibs ib)) = _
      rw [F, F, lowerTotalExpr_wrapLet]) <|
  mirCtxRefines_trans (mirCtxRefines_hoist_wrapLet (.letRhs x er rest body) trivial ibs ib hfresh) <|
  mirCtxRefines_of_lowerEq fun env => by
    rw [lowerTotalExpr_wrapLet]
    exact lowerTotalExpr_let_flatten_body ibs ((x, ib, er) :: rest) body env

/-- `flattenLetBinds` refines whenever `flattenReadyCheck` accepts. -/
theorem mirCtxRefines_flattenLetBinds (body : Expr) :
    ∀ (binds : List (VarId × Expr × Bool)), flattenReadyCheck body binds = true →
      MIRCtxRefines (.Let binds body) (.Let (flattenLetBinds binds) body)
  | [], _ => mirCtxRefines_refl _
  | (v, e, er) :: rest, h => by
    have tail : ∀ pre, flattenReadyCheck body rest = true →
        MIRCtxRefines (.Let (pre ++ rest) body) (.Let (pre ++ flattenLetBinds rest) body) :=
      fun pre hr =>
        mirCtxRefines_trans
          (mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_let_flatten_body pre rest body env).symm) <|
        mirCtxRefines_trans (mirCtxRefines_let_body (mirCtxRefines_flattenLetBinds body rest hr)) <|
        mirCtxRefines_of_lowerEq (lowerTotalExpr_let_flatten_body pre _ body)
    cases e with
    | Let ibs ib =>
      simp only [flattenReadyCheck, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hbody, hrest⟩, hr⟩ := h
      have := tail (ibs ++ [(v, ib, er)]) hr
      simp only [List.append_assoc, List.singleton_append] at this
      exact mirCtxRefines_trans
        (mirCtxRefines_let_flatten_rhs_head v ibs ib er rest body fun b hb =>
          ⟨fun r hr' => hrest b hb r hr', hbody b hb⟩) this
    | _ => exact tail [_] h

end Moist.Verified.MIR
