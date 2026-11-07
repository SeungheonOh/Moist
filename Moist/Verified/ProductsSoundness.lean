import Moist.Verified.ProductsSoundness.Unbox
import Moist.Verified.PreLowerSoundness

/-! # Product destructuring

`destructureProducts` unboxes projection-only bindings of known builtin pairs
and lowers projections of known pairs to native `case`. The walk numbers its
component binders from a counter above every identifier of the program; every
binder it has not generated yet is fresh for the environment it runs in
(`GenSafe`), and its facts record dominating bindings only.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

theorem FactRel.weaken {G G' : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e e' : Expr} (h : FactRel G P Γ e e') (hGG : ∀ y, G' y → G y) :
    FactRel G' P Γ e e' :=
  fun env t hG hd hf hk hs hlow => h env t (fun y hy => hGG y (hG y hy)) hd hf hk hs hlow

theorem listRel_weaken {G G' : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} (hGG : ∀ y, G' y → G y) :
    ∀ {es es' : List Expr}, ListRel (FactRel G P Γ) es es' → ListRel (FactRel G' P Γ) es es'
  | [], [], _ => trivial
  | [], _ :: _, h => absurd h id
  | _ :: _, [], h => absurd h id
  | _ :: _, _ :: _, h => ⟨h.1.weaken hGG, listRel_weaken hGG h.2⟩

theorem genSafe_mono {n m : Nat} (h : n ≤ m) : ∀ y, GenSafe n y → GenSafe m y :=
  fun _ hy => hy.elim (fun h' => .inl (by omega)) .inr

mutual
  theorem productWalk_factRel (Γ : List (VarId × Expr)) (e : Expr) (next : Nat)
      (hmax : maxUidExpr e < next) :
      FactRel (GenSafe next) Produces Γ e (productWalk Γ e next).1 ∧ next ≤ (productWalk Γ e next).2 := by
    match e with
    | .Let [] body =>
      rw [productWalk]
      simp only [maxUidExpr, maxUidExprBinds] at hmax
      have ih := productWalk_factRel Γ body next (by omega)
      exact ⟨ih.1.congr_left (fun env => lowerTotalExpr_let_nil env body)
        (fun avoid => freshIn_let_nil avoid body), ih.2⟩
    | .Let ((x, r, er) :: rest) body =>
      rw [productWalk]
      simp only [maxUidExpr, maxUidExprBinds] at hmax
      have ihr := productWalk_factRel Γ r next (by omega)
      have generic : FactRel (GenSafe next) Produces Γ (.Let ((x, r, er) :: rest) body)
            (.Let [(x, (productWalk Γ r next).1, er)]
              (productWalk ((x, (productWalk Γ r next).1) :: Γ) (.Let rest body)
                (productWalk Γ r next).2).1) ∧
          next ≤ (productWalk ((x, (productWalk Γ r next).1) :: Γ) (.Let rest body)
            (productWalk Γ r next).2).2 := by
        have ihrest := productWalk_factRel ((x, (productWalk Γ r next).1) :: Γ) (.Let rest body)
          (productWalk Γ r next).2 (by simp only [maxUidExpr]; omega)
        exact ⟨(FactRel.let_single (er := er) (productWalk Γ r next).1 (.inl (by omega)) (.inr rfl)
          ihr.1 (ihrest.1.weaken (genSafe_mono ihr.2)) (fun _ _ _ _ _ _ hp => hp)).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _),
          by omega⟩
      split
      · rename_i hcond
        simp only [Bool.and_eq_true] at hcond
        obtain ⟨⟨hknown, _⟩, hproj⟩ := hcond
        have hS := maxUidExpr_replaceProjections
          (({ uid := (productWalk Γ r next).2 + 1, origin := .gen, hint := "second" }, sndApp x) ::
            ({ uid := (productWalk Γ r next).2, origin := .gen, hint := "first" }, fstApp x) ::
            (x, (productWalk Γ r next).1) :: Γ) x
          { uid := (productWalk Γ r next).2, origin := .gen, hint := "first" }
          { uid := (productWalk Γ r next).2 + 1, origin := .gen, hint := "second" } (.Let rest body)
        simp only [maxUidExpr] at hS
        have ihS := productWalk_factRel Γ
          (replaceProjections
            (({ uid := (productWalk Γ r next).2 + 1, origin := .gen, hint := "second" }, sndApp x) ::
              ({ uid := (productWalk Γ r next).2, origin := .gen, hint := "first" }, fstApp x) ::
              (x, (productWalk Γ r next).1) :: Γ) x
            { uid := (productWalk Γ r next).2, origin := .gen, hint := "first" }
            { uid := (productWalk Γ r next).2 + 1, origin := .gen, hint := "second" } (.Let rest body))
          ((productWalk Γ r next).2 + 2) (by omega)
        refine ⟨(unbox_factRel (er := er) (genSafe_mono (by omega)) (.inl (by simp)) (.inl (by simp))
          (not_genSafe (by simp; omega) rfl) (not_genSafe (by simp; omega) rfl)
          (beq_false_of_uid_lt (by simp)) (beq_false_of_uid_lt (by simp; omega))
          (beq_false_of_uid_lt (by simp; omega)) ⟨by simp only [maxUidExpr]; omega,
            by simp only [maxUidExpr]; omega⟩ ihr.1 hknown hproj ihS.1).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _),
          by dsimp only; omega⟩
      · split
        · rename_i argument isFirst hprojected
          obtain ⟨fn, hr, hkind⟩ := projectedArgument_some hprojected
          have hsz : exprSize argument + 2 ≤ exprSize r := by
            subst hr; have := exprSize_pos fn; simp only [exprSize]; omega
          have hmaxa : maxUidExpr argument ≤ maxUidExpr r := by
            subst hr; simp only [maxUidExpr]; omega
          have iha := productWalk_factRel Γ argument next (by omega)
          by_cases hknown : knownProduct Γ (productWalk Γ argument next).1 = true
          · rw [if_pos hknown]
            have ihS := productWalk_factRel Γ
              (.Let ((x, .Var (if isFirst then
                  ({ uid := (productWalk Γ argument next).2, origin := .gen, hint := "first" } : VarId)
                else { uid := (productWalk Γ argument next).2 + 1, origin := .gen, hint := "second" }),
                er) :: rest) body)
              ((productWalk Γ argument next).2 + 2)
              (by simp only [maxUidExpr, maxUidExprBinds]; split <;> simp <;> omega)
            subst hr
            refine ⟨(unboxProjection_factRel (er := er) (k := isFirst) (genSafe_mono (by omega))
              (.inl (by simp)) (.inl (by simp))
              (not_genSafe (by simp; omega) rfl) (not_genSafe (by simp; omega) rfl)
              (beq_false_of_uid_lt (by simp)) (beq_false_of_uid_lt (by simp; omega))
              (beq_false_of_uid_lt (by simp; omega)) ⟨by simp only [maxUidExpr]; omega,
                by simp only [maxUidExpr]; omega⟩ rfl hkind iha.1 hknown
              (ihS.1.congr_left (fun env => (lowerTotalExpr_let_cons env _ _ _).symm)
                (fun avoid => (freshIn_let_cons avoid _ _ _).symm))).congr_left
              (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _),
              by dsimp only; omega⟩
          · rw [if_neg hknown]; exact generic
        · exact generic
    | .Lam x b =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ih := productWalk_factRel Γ b next (by omega)
      exact ⟨ih.1.lam (.inl (by omega)), ih.2⟩
    | .Fix f b =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ih := productWalk_factRel Γ b next (by omega)
      refine ⟨?_, ih.2⟩
      cases hb : b with
      | Lam x inner =>
        rw [productWalk]
        subst hb
        simp only [maxUidExpr] at hmax
        have ihi := productWalk_factRel Γ inner next (by omega)
        exact ihi.1.fix_lam (.inl (by omega)) (.inl (by omega)) (fun y hy => .inr (by rw [hy]; simp))
      | _ =>
        intro env t _ _ _ _ _ hlow
        rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
        cases hlow
    | .App fn a =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ihf := productWalk_factRel Γ fn next (by omega)
      have iha := productWalk_factRel Γ a (productWalk Γ fn next).2 (by omega)
      have congruence := ihf.1.app (iha.1.weaken (genSafe_mono ihf.2))
      split
      · rename_i heq
        split
        · rename_i hknown
          rw [heq] at ihf
          exact ⟨project_factRel (.inl ⟨rfl, rfl⟩) (beq_false_symm (beq_false_of_uid_lt (by simp)))
            ihf.1 (iha.1.weaken (genSafe_mono ihf.2)) hknown, by omega⟩
        · exact ⟨congruence, by omega⟩
      · rename_i heq
        split
        · rename_i hknown
          rw [heq] at ihf
          exact ⟨project_factRel (.inr ⟨rfl, rfl⟩) (beq_false_symm (beq_false_of_uid_lt (by simp)))
            ihf.1 (iha.1.weaken (genSafe_mono ihf.2)) hknown, by omega⟩
        · exact ⟨congruence, by omega⟩
      · exact ⟨congruence, by omega⟩
    | .Force b =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ih := productWalk_factRel Γ b next (by omega)
      exact ⟨ih.1.force, ih.2⟩
    | .Delay b =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ih := productWalk_factRel Γ b next (by omega)
      exact ⟨ih.1.delay, ih.2⟩
    | .Constr tag fields =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ih := productWalkList_factRel Γ fields next (by omega)
      exact ⟨FactRel.constr ih.1, ih.2⟩
    | .Case scrutinee alternatives =>
      rw [productWalk]
      simp only [maxUidExpr] at hmax
      have ihs := productWalk_factRel Γ scrutinee next (by omega)
      have iha := productWalkList_factRel Γ alternatives (productWalk Γ scrutinee next).2 (by omega)
      exact ⟨FactRel.case ihs.1 (listRel_weaken (genSafe_mono ihs.2) iha.1), by omega⟩
    | .Var _ | .Lit _ | .Builtin _ | .Error =>
      rw [productWalk]; exact ⟨FactRel.refl _ _ _ _, Nat.le_refl _⟩
  termination_by 2 * exprSize e
  decreasing_by
    all_goals first
      | (simp only [exprSize, exprSizeBinds]; omega)
      | (subst_vars; simp only [exprSize]; omega)
      | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
      | (apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (exprSize_replaceProjections _ _ _ _ _))
         simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)

  theorem productWalkList_factRel (Γ : List (VarId × Expr)) (es : List Expr) (next : Nat)
      (hmax : maxUidExprList es < next) :
      ListRel (FactRel (GenSafe next) Produces Γ) es (productWalkList Γ es next).1 ∧
        next ≤ (productWalkList Γ es next).2 := by
    match es with
    | [] => rw [productWalkList]; exact ⟨trivial, Nat.le_refl _⟩
    | e :: rest =>
      rw [productWalkList]
      simp only [maxUidExprList] at hmax
      have ihe := productWalk_factRel Γ e next (by omega)
      have ihr := productWalkList_factRel Γ rest (productWalk Γ e next).2 (by omega)
      exact ⟨⟨ihe.1, listRel_weaken (genSafe_mono ihe.2) ihr.1⟩, by omega⟩
  termination_by 2 * exprSizeList es + 1
  decreasing_by
    all_goals (simp only [exprSizeList]; have := exprSize_pos e; omega)
end

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Product destructuring refines its input. -/
theorem destructureProducts_refines (e : Expr) : MIRCtxRefines e (Advanced.destructureProducts e) := by
  unfold Advanced.destructureProducts
  simp only
  refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
    (mirCtxRefines_trans ?_ (PreLower.preLowerInlineExpr_refines _ _))
  split
  · rename_i hws
    exact mirCtxRefines_of_factRel hws
      (fun y hy => .inl (by have := freeVars_uid_lt hy; omega))
      (fun y hy => .inr (by rw [hy]; simp))
      (productWalk_factRel [] _ _ (by omega)).1
  · exact mirCtxRefines_refl _

end Moist.Verified.MIR
