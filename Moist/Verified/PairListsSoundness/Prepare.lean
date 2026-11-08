import Moist.MIR.Optimize.Advanced.PairLists
import Moist.Verified.ProductsSoundness
import Moist.Verified.KeyGuardsSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # Preparing the component binders of list heads

`prepareHeads` binds two fresh names to the head of a list `case`
alternative, unused, right inside the alternative. A binding of a variable
returns on every path and the body ignores it, so the alternative is refined
(`prepareWalk_factRel`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines Moist.Verified.MIR

/-- Two unused bindings of the head inside the cons alternative. -/
theorem alt_insert_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)} {h t a b : VarId} {B B' : Expr}
    (hB : FactRel G Produces Γ B B') (hah : (a == h) = false)
    (hfa : (freeVars B').contains a = false) (hfb : (freeVars B').contains b = false)
    (hGh : G h) (hGt : G t) :
    FactRel G Produces Γ (.Lam h (.Lam t B))
      (.Lam h (.Lam t (.Let [(a, .Var h, false)] (.Let [(b, .Var h, false)] B')))) := by
  intro env t₀ hG hd hfresh hk hs hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨hh, ht, hfB⟩ := hfresh
  obtain ⟨hd₁, hk₁, hs₁, hn₁⟩ := enter_binder hd hk hs hh
  obtain ⟨hd₂, hk₂, hs₂, hn₂⟩ := enter_binder hd₁ hk₁ hs₁ ht
  obtain ⟨tX, htX, rfl⟩ := lowerTotalExpr_lam_some hlow
  obtain ⟨tB, htB, rfl⟩ := lowerTotalExpr_lam_some htX
  obtain ⟨tB', htB', hrB⟩ := hB (t :: h :: env) tB (allG_cons hGt (allG_cons hGh hG)) hd₂ hfB hk₂ hs₂ htB
  have hth : (t == h) = false := by
    cases hc : (t == h)
    · rfl
    · rw [envLookupT_cons, varId_beq_symm hc] at ht; simp at ht
  -- the body below the two new binders
  have hB'a : lowerTotalExpr (a :: t :: h :: env) B' = some (renameTerm (shiftRename 1) tB') := by
    rw [MIR.lowerTotalExpr_prepend_unused _ a B' hfa, htB']; rfl
  have hB'b : lowerTotalExpr (b :: a :: t :: h :: env) B' =
      some (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tB')) := by
    rw [MIR.lowerTotalExpr_prepend_unused _ b B' hfb, hB'a]; rfl
  have hh₂ : envLookupT (t :: h :: env) h = some 1 := by
    rw [envLookupT_cons_neq t h _ hth, envLookupT_cons]; simp [varId_beq_self]
  have hh₃ : envLookupT (a :: t :: h :: env) h = some 2 := by
    rw [envLookupT_cons_neq a h _ hah, hh₂]; rfl
  refine ⟨.Lam 0 (.Lam 0 (.Apply (.Lam 0 (.Apply (.Lam 0
    (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tB'))) (.Var 3))) (.Var 2))), ?_, ?_⟩
  · rw [MIR.lowerTotalExpr_lam, MIR.lowerTotalExpr_lam, lowerTotalExpr_let_single, lowerTotalExpr_var, hh₂]
    simp only [Option.map_some]
    rw [lowerTotalExpr_let_single, lowerTotalExpr_var, hh₃]
    simp only [Option.map_some, hB'b]
    rfl
  · have cB := MIR.lowerTotalExpr_closedAt htB
    have cB' := MIR.lowerTotalExpr_closedAt htB'
    simp only [List.length_cons] at cB cB' hrB
    have c1 := closedAt_shift cB'
    have c2 := closedAt_shift c1
    -- the two unused bindings
    have hins : FactRefines (env.length + 1 + 1) (fun _ => True) tB'
        (.Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tB')))
          (.Var 3))) (.Var 2)) := by
      refine (factRefines_add_let (r := .Var 2) 0 cB' ?_).trans ?_
      · intro ρ _ henv _
        obtain ⟨v, hv, _⟩ := envWellFormed_lookup _ henv (n := 2) (by omega) (by omega)
        exact ⟨v, halts_var_of_lookup hv⟩
      · refine factRefines_let (G := fun _ => True) 0 0 (by simp [closedAt]) (fun _ _ _ _ => trivial) ?_
        refine factRefines_add_let (r := .Var 3) 0 c1 ?_
        intro ρ _ henv _
        obtain ⟨v, hv, _⟩ := envWellFormed_lookup _ henv (n := 3) (by omega) (by omega)
        exact ⟨v, halts_var_of_lookup hv⟩
    have hbody : FactRefines (env.length + 1 + 1) (FactsHold Produces Γ (t :: h :: env)) tB
        (.Apply (.Lam 0 (.Apply (.Lam 0 (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) tB')))
          (.Var 3))) (.Var 2)) :=
      hrB.trans (hins.mono fun _ _ => trivial)
    refine factRefines_lam 0 0 (by simpa using MIR.lowerTotalExpr_closedAt htX) ?_
      (fun ρ v hF => hF.extend v hn₁) ?_
    · simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by simpa [Nat.add_assoc] using c2, by omega⟩, by omega⟩
    · refine factRefines_lam 0 0 cB ?_ (fun ρ v hF => hF.extend v hn₂) hbody
      simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by simpa [Nat.add_assoc] using c2, by omega⟩, by omega⟩

omit sv in
theorem maxUidExprList_cons' (e : Expr) (es : List Expr) :
    maxUidExprList (e :: es) = max (maxUidExpr e) (maxUidExprList es) := by
  simp only [maxUidExprList]

omit sv in
theorem fresh_uid {base : Nat} {x : VarId} (h : base ≤ x.uid) (hg : x.origin = .gen) :
    ∀ y, (y == x) = true → ¬ GenSafe base y := not_genSafe h hg

mutual
  theorem prepareWalk_factRel (env : List (VarId × Expr)) (Γ : List (VarId × Expr)) (e : Expr) (next : Nat)
      (hmax : maxUidExpr e < next) :
      FactRel (GenSafe next) Produces Γ e (prepareWalk env e next).1 ∧ next ≤ (prepareWalk env e next).2 ∧
        maxUidExpr (prepareWalk env e next).1 < (prepareWalk env e next).2 := by
    match e with
    | .Case s alts =>
      by_cases hA : ∃ l h t body rest, s = .Var l ∧ alts = .Lam h (.Lam t body) :: rest
      · obtain ⟨l, h, t, body, rest, rfl, rfl⟩ := hA
        rw [prepareWalk.eq_1]
        simp only [maxUidExpr, maxUidExprList] at hmax
        have ihb := prepareWalk_factRel env Γ body next (by omega)
        have ihr := prepareList_factRel env Γ rest (prepareWalk env body next).2 (by omega)
        have hrest := listRel_weaken (genSafe_mono ihb.2.1) ihr.1
        split
        · dsimp only
          refine ⟨?_, by omega, ?_⟩
          · refine FactRel.case (FactRel.refl _ _ _ _) ⟨?_, hrest⟩
            refine alt_insert_factRel ihb.1 ((VarId.beq_false_iff _ _).mpr (.inr (by simp; omega)))
              (maxUidExpr_fresh _ _ (by simp; omega)) (maxUidExpr_fresh _ _ (by simp; omega))
              (.inl (by omega)) (.inl (by omega))
          · simp only [maxUidExpr, maxUidExprList, maxUidExprBinds]; omega
        · dsimp only
          refine ⟨FactRel.case (FactRel.refl _ _ _ _)
            ⟨FactRel.lam (.inl (by omega)) (FactRel.lam (.inl (by omega)) ihb.1), hrest⟩, by omega, ?_⟩
          simp only [maxUidExpr, maxUidExprList]; omega
      · rw [prepareWalk.eq_2 _ _ _ _ (fun l h t body rest h₁ h₂ => hA ⟨l, h, t, body, rest, h₁, h₂⟩)]
        simp only [maxUidExpr] at hmax
        have ihs := prepareWalk_factRel env Γ s next (by omega)
        have iha := prepareList_factRel env Γ alts (prepareWalk env s next).2 (by omega)
        exact ⟨FactRel.case ihs.1 (listRel_weaken (genSafe_mono ihs.2.1) iha.1), by omega,
          by simp only [maxUidExpr]; omega⟩
    | .Let [] body =>
      rw [prepareWalk]
      simp only [maxUidExpr, maxUidExprBinds] at hmax
      have ih := prepareWalk_factRel env Γ body next (by omega)
      exact ⟨ih.1.congr_left (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body), ih.2⟩
    | .Let ((x, r, er) :: rest) body =>
      rw [prepareWalk]
      simp only [maxUidExpr, maxUidExprBinds] at hmax
      have ihr := prepareWalk_factRel env Γ r next (by omega)
      have ihrest := prepareWalk_factRel ((x, (prepareWalk env r next).1) :: env)
        ((x, (prepareWalk env r next).1) :: Γ) (.Let rest body) (prepareWalk env r next).2
        (by simp only [maxUidExpr]; omega)
      refine ⟨(FactRel.let_single (er := er) (prepareWalk env r next).1 (.inl (by omega)) (.inr rfl)
        ihr.1 (ihrest.1.weaken (genSafe_mono ihr.2.1)) (fun _ _ _ _ _ _ hp => hp)).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _),
        by omega, ?_⟩
      simp only [maxUidExpr, maxUidExprBinds]; omega
    | .Lam x b =>
      rw [prepareWalk]
      simp only [maxUidExpr] at hmax
      have ih := prepareWalk_factRel env Γ b next (by omega)
      exact ⟨ih.1.lam (.inl (by omega)), ih.2.1, by simp only [maxUidExpr]; omega⟩
    | .Fix f b =>
      rw [prepareWalk]
      simp only [maxUidExpr] at hmax
      have ih := prepareWalk_factRel env Γ b next (by omega)
      refine ⟨?_, ih.2.1, by simp only [maxUidExpr]; omega⟩
      cases hb : b with
      | Lam x inner =>
        subst hb
        rw [prepareWalk]
        simp only [maxUidExpr] at hmax
        have ihi := prepareWalk_factRel env Γ inner next (by omega)
        exact ihi.1.fix_lam (.inl (by omega)) (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
      | _ =>
        intro env t _ _ _ _ _ hlow
        rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
        cases hlow
    | .App fn a =>
      rw [prepareWalk]
      simp only [maxUidExpr] at hmax
      have ihf := prepareWalk_factRel env Γ fn next (by omega)
      have iha := prepareWalk_factRel env Γ a (prepareWalk env fn next).2 (by omega)
      exact ⟨ihf.1.app (iha.1.weaken (genSafe_mono ihf.2.1)), by omega,
        by simp only [maxUidExpr]; omega⟩
    | .Force b =>
      rw [prepareWalk]
      simp only [maxUidExpr] at hmax
      have ih := prepareWalk_factRel env Γ b next (by omega)
      exact ⟨ih.1.force, ih.2.1, by simp only [maxUidExpr]; omega⟩
    | .Delay b =>
      rw [prepareWalk]
      simp only [maxUidExpr] at hmax
      have ih := prepareWalk_factRel env Γ b next (by omega)
      exact ⟨ih.1.delay, ih.2.1, by simp only [maxUidExpr]; omega⟩
    | .Constr tag fields =>
      rw [prepareWalk]
      simp only [maxUidExpr] at hmax
      have ih := prepareList_factRel env Γ fields next (by omega)
      exact ⟨FactRel.constr ih.1, ih.2.1, by simp only [maxUidExpr]; omega⟩
    | .Var _ | .Lit _ | .Builtin _ | .Error =>
      rw [prepareWalk]; exact ⟨FactRel.refl _ _ _ _, Nat.le_refl _, by simpa using hmax⟩
  termination_by 2 * exprSize e
  decreasing_by
    all_goals first
      | (simp only [exprSize, exprSizeList, exprSizeBinds]; omega)
      | (subst_vars; simp only [exprSize, exprSizeList]; omega)
      | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)

  theorem prepareList_factRel (env : List (VarId × Expr)) (Γ : List (VarId × Expr)) (es : List Expr)
      (next : Nat) (hmax : maxUidExprList es < next) :
      ListRel (FactRel (GenSafe next) Produces Γ) es (prepareList env es next).1 ∧
        next ≤ (prepareList env es next).2 ∧
        maxUidExprList (prepareList env es next).1 < (prepareList env es next).2 := by
    match es with
    | [] => rw [prepareList]; exact ⟨trivial, Nat.le_refl _, by simp [maxUidExprList]; omega⟩
    | e :: rest =>
      rw [prepareList]
      simp only [maxUidExprList] at hmax
      have ihe := prepareWalk_factRel env Γ e next (by omega)
      have ihr := prepareList_factRel env Γ rest (prepareWalk env e next).2 (by omega)
      refine ⟨⟨ihe.1, listRel_weaken (genSafe_mono ihe.2.1) ihr.1⟩, by omega, ?_⟩
      simp only [maxUidExprList]; omega
  termination_by 2 * exprSizeList es + 1
  decreasing_by
    all_goals (simp only [exprSizeList]; have := exprSize_pos e; omega)
end

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Preparing the component binders of list heads refines its input. -/
theorem prepareHeads_refines (e : Expr) : MIRCtxRefines e (Advanced.prepareHeads e) := by
  unfold Advanced.prepareHeads
  simp only
  split
  · rename_i hws
    refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (prepareWalk_factRel [] [] _ _ (by omega)).1
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
