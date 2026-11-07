import Moist.Verified.TagChainsSoundness.Rules

/-! # Applying a tree of field-less cases

`(case s alts) y` evaluates `s`, selects an alternative, evaluates it and
applies the result to `y`. When the value of `s` carries no fields, which is
the case for Booleans and integers, `case s [a y | a ∈ alts]` performs the
same selection and continues with the same evaluation (`push_rewrites`).
Applying `error` or `λx. error` fails. Pushing recursively, the tag rules apply
at every pushed case (`pushArgument_rewrites`).
-/

namespace Moist.Verified.TagChains

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts
open Moist.Verified.BetaValueRefines Moist.Verified.Contextual

theorem lowerTotalExprList_map_app {env : List VarId} {y : Expr} {ty : Term}
    (hy : lowerTotalExpr env y = some ty) :
    ∀ {alts : List Expr} {talts : List Term}, MIR.lowerTotalExprList env alts = some talts →
      MIR.lowerTotalExprList env (alts.map fun a => .App a y) =
        some (talts.map fun a => .Apply a ty)
  | [], talts, h => by rw [MIR.lowerTotalExprList_nil] at h; cases h; exact MIR.lowerTotalExprList_nil env
  | a :: alts, talts, h => by
    rw [MIR.lowerTotalExprList_cons] at h
    cases ha : lowerTotalExpr env a with
    | none => rw [ha] at h; cases h
    | some ta =>
      cases has : MIR.lowerTotalExprList env alts with
      | none => rw [ha, has] at h; cases h
      | some tas =>
        rw [ha, has] at h; cases h
        simp only [List.map_cons]
        rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExpr_app, ha, hy,
          lowerTotalExprList_map_app hy has]
        rfl

/-- Selecting an alternative of a field-less constant before or after
    pushing an argument frame into the alternatives. -/
theorem case_push_ret {ρ : CekEnv} {π : Stack} {talts : List Term} {ty : Term} (c : Const)
    (hc : ∀ tag n fields, constToTagAndFields c = some (tag, n, fields) → fields = []) :
    ObsRefines (.ret (.caseScrutinee talts ρ :: .arg ty ρ :: π) (.VCon c))
      (.ret (.caseScrutinee (talts.map fun a => .Apply a ty) ρ :: π) (.VCon c)) := by
  apply obsRefines_of_step
  cases hct : constToTagAndFields c with
  | none => simp only [step, hct]; exact obsRefines_refl _
  | some r =>
    obtain ⟨tag, n, fields⟩ := r
    have := hc tag n fields hct
    subst this
    simp only [step, hct, List.length_map, List.map_nil, List.nil_append, List.getElem?_map]
    split
    · exact obsRefines_refl _
    · cases ha : talts[tag]? with
      | none => simp only [Option.map_none]; exact obsRefines_refl _
      | some alt =>
        simp only [Option.map_some]
        exact obsRefines_of_reaches (reaches_refl _) ⟨1, rfl⟩ (obsRefines_refl _)

theorem bool_fieldless (b : Bool) :
    ∀ tag n fields, constToTagAndFields (.Bool b) = some (tag, n, fields) → fields = [] := by
  intro tag n fields h
  cases b <;> simp [constToTagAndFields] at h <;> exact h.2.2

theorem integer_fieldless (k : Int) :
    ∀ tag n fields, constToTagAndFields (.Integer k) = some (tag, n, fields) → fields = [] := by
  intro tag n fields h
  simp only [constToTagAndFields] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.symm
  · cases h

theorem push_rewrites {Γ : List (VarId × Expr)} {s : Expr} {alts : List Expr} {y : VarId}
    (hfield : fieldlessScrutinee Γ s = true) :
    TagRewrites Γ (.App (.Case s alts) (.Var y)) (.Case s (alts.map fun a => .App a (.Var y))) := by
  intro env t hd _ hlow
  obtain ⟨tc, ty, htc, hty, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨ts, talts, hts, htalts, rfl⟩ := lowerTotalExpr_case_some htc
  refine ⟨.Case ts (talts.map fun a => .Apply a ty), by
    rw [MIR.lowerTotalExpr_case_of_list, hts, lowerTotalExprList_map_app hty htalts]; rfl, ?_⟩
  intro ρ π _ _ _ hF
  apply obsRefines_of_steps 2 1
  show ObsRefines (.compute (.caseScrutinee talts ρ :: .arg ty ρ :: π) ρ ts)
    (.compute (.caseScrutinee (talts.map fun a => .Apply a ty) ρ :: π) ρ ts)
  apply obsRefines_of_continuation
  intro v hv
  unfold fieldlessScrutinee at hfield
  rw [Bool.or_eq_true] at hfield
  rcases hfield with hb | hi
  · obtain ⟨b, rfl⟩ := knownBooleanLocal_sound (fun _ _ _ _ h => h) 64 Γ s hb hF hd hts hv
    exact case_push_ret _ (bool_fieldless b)
  · obtain ⟨k, rfl⟩ := knownInteger_sound (fun _ _ _ _ h => h) 64 Γ s hi hF hd hts hv
    exact case_push_ret _ (integer_fieldless k)

theorem error_app_rewrites (Γ : List (VarId × Expr)) (y : VarId) :
    TagRewrites Γ (.App .Error (.Var y)) .Error := by
  intro env t _ _ hlow
  obtain ⟨te, ty, hte, hty, rfl⟩ := lowerTotalExpr_app_some hlow
  rw [lowerTotalExpr_error] at hte; cases hte
  refine ⟨.Error, lowerTotalExpr_error env, fun ρ π _ _ _ _ => ?_⟩
  exact obsRefines_of_errors ⟨2, rfl⟩ ⟨1, rfl⟩

theorem lam_error_app_rewrites (Γ : List (VarId × Expr)) (x y : VarId) :
    TagRewrites Γ (.App (.Lam x .Error) (.Var y)) .Error := by
  intro env t _ _ hlow
  obtain ⟨tl, ty, htl, hty, rfl⟩ := lowerTotalExpr_app_some hlow
  obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_some htl
  rw [lowerTotalExpr_error] at htb; cases htb
  obtain ⟨j, _, rfl⟩ := lowerTotalExpr_var_some hty
  refine ⟨.Error, lowerTotalExpr_error env, fun ρ π _ _ _ _ => ?_⟩
  refine obsRefines_of_errors ?_ ⟨1, rfl⟩
  cases hl : ρ.lookup (j + 1) with
  | none => exact ⟨4, by simp [steps, step, hl]⟩
  | some v => exact ⟨6, by simp [steps, step, hl]⟩

theorem listRel_push (Γ : List (VarId × Expr)) (y : VarId) (alts : List Expr)
    (h : ∀ a ∈ alts, TagRewrites Γ (.App a (.Var y)) (pushArgument Γ y a)) :
    ListRel (TagRewrites Γ) (alts.map fun a => .App a (.Var y))
      (alts.attach.map fun ⟨a, _⟩ => pushArgument Γ y a) := by
  rw [attach_map_eq_map]
  induction alts with
  | nil => trivial
  | cons a as ih =>
    exact ⟨h a (.head _), ih fun a' ha' => h a' (.tail _ ha')⟩

theorem pushArgument_rewrites (Γ : List (VarId × Expr)) (y : VarId) (f : Expr) :
    TagRewrites Γ (.App f (.Var y)) (pushArgument Γ y f) := by
  by_cases hcase : ∃ s alts, f = .Case s alts
  · obtain ⟨s, alts, rfl⟩ := hcase
    rw [pushArgument.eq_1]
    split
    · rename_i hfield
      exact (push_rewrites hfield).trans ((TagRewrites.case_alternatives
        (listRel_push Γ y alts fun a _ => pushArgument_rewrites Γ y a)).trans
          (tagCaseRule_getD_rewrites _ _ _))
    · exact TagRewrites.refl _ _
  · by_cases herr : f = .Error
    · subst herr; rw [pushArgument.eq_2]; exact error_app_rewrites Γ y
    · by_cases hlam : ∃ x, f = .Lam x .Error
      · obtain ⟨x, rfl⟩ := hlam
        rw [pushArgument.eq_3]; exact lam_error_app_rewrites Γ x y
      · rw [pushArgument.eq_4 _ _ _ (fun s a h => hcase ⟨s, a, h⟩) herr (fun x h => hlam ⟨x, h⟩)]
        exact TagRewrites.refl _ _
termination_by exprSize f
decreasing_by subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega

end Moist.Verified.TagChains
