import Moist.Verified.TagChainsSoundness.Push
import Moist.Verified.MIR.Hoist

/-! # Bindings consumed by the next case or application

`let b = r in case b alts` and `case r alts` evaluate `r` at the same point
and select the same alternative when `b` does not occur in `alts`; the
alternatives then run in an environment that differs only by the unused
binding (`unanfCase_rewrites`, a shift bisimulation). Likewise
`let g = T in g y` applies the value of `T` to the value of `y` exactly as
`T y` does (`unanfApp_rewrites`). A binding that the body ignores and whose
right-hand side returns is dropped (`deadTag_rewrites`).
-/

namespace Moist.Verified.TagChains

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts
open Moist.Verified.BetaValueRefines Moist.Verified.Contextual

theorem shiftBisimEnv_extend {d : Nat} {ρ : CekEnv} (w : CekValue) :
    EnvWellFormed d ρ → ShiftBisimEnv (shiftRename 1) d ρ (ρ.extend w)
  | .zero => .zero
  | .succ (k := k) (v := v) hrest _ hl hv => by
    refine .succ (v₁ := v) (v₂ := v) (shiftBisimEnv_extend w hrest) hl ?_
      (shiftBisimValue_refl_id v hv)
    rw [shiftRename_ge (by omega)]
    exact hl

theorem freeVarsList_not_contains {x : VarId} :
    ∀ {es : List Expr}, (freeVarsList es).contains x = false →
      ∀ e ∈ es, (freeVars e).contains x = false
  | [], _, e, he => by cases he
  | e :: es, h, e', he => by
    rw [freeVarsList] at h
    have hu : ((freeVars e).union (freeVarsList es)).contains x = false := h
    rcases List.mem_cons.mp he with rfl | he
    · cases h₁ : (freeVars e').contains x
      · rfl
      · have := VarSet.contains_union_left _ (freeVarsList es) _ h₁
        rw [hu] at this; cases this
    · apply freeVarsList_not_contains (es := es) _ e' he
      cases h₂ : (freeVarsList es).contains x
      · rfl
      · have := VarSet.contains_union_right (freeVars e) _ _ h₂
        rw [hu] at this; cases this

/-- `let b = r in case b alts` selects like `case r alts`. -/
theorem unanfCase_rewrites (Γ : List (VarId × Expr)) {b s : VarId} {r : Expr} {er : Bool}
    {alts : List Expr} (hs : (s == b) = true) (hfree : (freeVarsList alts).contains b = false) :
    TagRewrites Γ (.Let [(b, r, er)] (.Case (.Var s) alts)) (.Case r alts) := by
  intro env t hd _ hlow
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨tsv, talts₁, htsv, htalts₁, rfl⟩ := lowerTotalExpr_case_some htb
  rw [lowerTotalExpr_var, envLookupT_cons, if_pos (varId_beq_symm hs)] at htsv
  cases htsv
  rw [MIR.lowerTotalExprList_prepend_unused env b alts (freeVarsList_not_contains hfree)] at htalts₁
  cases htalts : MIR.lowerTotalExprList env alts with
  | none => rw [htalts] at htalts₁; cases htalts₁
  | some talts =>
    rw [htalts] at htalts₁; cases htalts₁
    refine ⟨.Case tr talts, by rw [MIR.lowerTotalExpr_case_of_list, htr, htalts]; rfl, ?_⟩
    intro ρ π henv hlen hπ _
    apply obsRefines_of_steps 3 1
    show ObsRefines (.compute (.funV (.VLam (.Case (.Var 1) (renameTermList (shiftRename 1) talts)) ρ) :: π) ρ tr)
      (.compute (.caseScrutinee talts ρ :: π) ρ tr)
    apply obsRefines_of_continuation
    intro v hv
    have hvwf := halts_wellFormed henv hlen (MIR.lowerTotalExpr_closedAt htr) hv
    refine obsRefines_of_reaches
      (s₁' := .ret (.caseScrutinee (renameTermList (shiftRename 1) talts) (ρ.extend v) :: π) v)
      (s₂' := .ret (.caseScrutinee talts ρ :: π) v) ⟨3, rfl⟩ (reaches_refl _) ?_
    exact (obsRefines_of_shiftBisim (.ret (shiftBisimValue_refl_id v hvwf)
      (.cons (.caseScrutinee (FundamentalRefines.is0preserving_shiftRename (by omega))
        (shiftBisimEnv_extend v henv) (lowerTotalExprList_closedAtList htalts))
        (shiftBisimStack_refl hπ)))).2

/-- `let g = f in g y` applies like `f y`. -/
theorem unanfApp_rewrites (Γ : List (VarId × Expr)) {g h y : VarId} {f : Expr} {er : Bool}
    (hg : (h == g) = true) (hy : (y == g) = false) :
    TagRewrites Γ (.Let [(g, f, er)] (.App (.Var h) (.Var y))) (.App f (.Var y)) := by
  intro env t hd _ hlow
  obtain ⟨tf, tb, htf, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  obtain ⟨th, ty, hth, hty, rfl⟩ := lowerTotalExpr_app_some htb
  rw [lowerTotalExpr_var, envLookupT_cons, if_pos (varId_beq_symm hg)] at hth
  cases hth
  rw [lowerTotalExpr_var, envLookupT_cons, if_neg (by
    intro hgy; rw [varId_beq_symm hgy] at hy; cases hy)] at hty
  cases hj : envLookupT env y with
  | none => rw [hj] at hty; cases hty
  | some j =>
    rw [hj] at hty; cases hty
    refine ⟨.Apply tf (.Var (j + 1)), by
      rw [MIR.lowerTotalExpr_app, htf, lowerTotalExpr_var, hj]; rfl, ?_⟩
    intro ρ π _ _ _ _
    apply obsRefines_of_steps 3 1
    show ObsRefines
      (.compute (.funV (.VLam (.Apply (.Var (0 + 1)) (.Var (j + 1 + 1))) ρ) :: π) ρ tf)
      (.compute (.arg (.Var (j + 1)) ρ :: π) ρ tf)
    apply obsRefines_of_continuation
    intro v _
    apply obsRefines_of_steps 4 1
    show ObsRefines (.compute (.funV v :: π) (ρ.extend v) (.Var (j + 1 + 1)))
      (.compute (.funV v :: π) ρ (.Var (j + 1)))
    exact obsRefines_of_steps 1 1 (by
      simp only [steps, step, CekEnv.extend, CekEnv.lookup]; exact obsRefines_refl _)

/-- A binding that the body ignores and whose right-hand side returns. -/
theorem deadTag_rewrites {Γ : List (VarId × Expr)} {b : VarId} {r body : Expr} {er : Bool}
    (hfree : (freeVars body).contains b = false) (hret : tagReturns Γ r = true) :
    TagRewrites Γ (.Let [(b, r, er)] body) body := by
  intro env t hd _ hlow
  obtain ⟨tr, tb, htr, htb, rfl⟩ := lowerTotalExpr_let_single_some hlow
  rw [MIR.lowerTotalExpr_prepend_unused env b body hfree] at htb
  cases hB : lowerTotalExpr env body with
  | none => rw [hB] at htb; cases htb
  | some tB =>
    rw [hB] at htb; cases htb
    exact ⟨tB, rfl, factRefines_dead_let 0 (MIR.lowerTotalExpr_closedAt hB)
      (fun ρ hF henv _ => tagReturns_halts hret hF hd henv htr)⟩

theorem tagApplication_rewrites (Γ : List (VarId × Expr)) (f a : Expr) :
    TagRewrites Γ (.App f a) (tagApplication Γ f a) := by
  unfold tagApplication
  split
  · rename_i s alts y
    dsimp only
    split
    · exact pushArgument_rewrites Γ y _
    · exact TagRewrites.refl _ _
  · exact TagRewrites.refl _ _

theorem dropTagBinding_rewrites (Γ : List (VarId × Expr)) (b : VarId) (r : Expr) (er : Bool)
    (body : Expr) : TagRewrites Γ (.Let [(b, r, er)] body) (dropTagBinding Γ b r er body) := by
  unfold dropTagBinding
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact deadTag_rewrites h.1 h.2
  · exact TagRewrites.refl _ _

theorem tagBinding_rewrites (Γ : List (VarId × Expr)) (b : VarId) (r : Expr) (er : Bool)
    (body : Expr) : TagRewrites Γ (.Let [(b, r, er)] body) (tagBinding Γ b r er body) := by
  unfold tagBinding
  split
  · split
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      exact (unanfCase_rewrites Γ hcond.1.1 hcond.1.2).trans (tagCaseRule_getD_rewrites _ _ _)
    · exact dropTagBinding_rewrites Γ b _ er _
  · rename_i g y
    split
    · rename_i hcond
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      split
      · split
        · exact (unanfApp_rewrites Γ hcond.1 hcond.2).trans (pushArgument_rewrites Γ y _)
        · exact dropTagBinding_rewrites Γ b _ er _
      · exact dropTagBinding_rewrites Γ b _ er _
    · exact dropTagBinding_rewrites Γ b _ er _
  · exact dropTagBinding_rewrites Γ b _ er _

end Moist.Verified.TagChains
