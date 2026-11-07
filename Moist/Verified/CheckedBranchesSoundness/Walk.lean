import Moist.Verified.CheckedBranchesSoundness.Branches
import Moist.Verified.CheckedBranchesSoundness.Lowering

/-! # The checked branch walk

Every node either keeps its shape (congruence), fuses a head/tail pair of a
list recorded as non-empty, or records a list fact for one branch of a list
discriminator. Bindings record the right-hand side they evaluate, and an
alias of a non-empty list is itself non-empty.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified

theorem beq_force_nullList' {x : Expr} (h : (x == Expr.Force (.Builtin .NullList)) = true) :
    x = .Force (.Builtin .NullList) := by
  cases x with
  | Force e =>
    cases e with
    | Builtin b' =>
      have : (b' == BuiltinFun.NullList) = true := h
      cases b' <;> first | rfl | cases this
    | _ => cases h
  | _ => cases h

theorem headTailList_some {Γ : List (VarId × Expr)} {N : List VarId} {hr tr : Expr} {l : VarId}
    (h : headTailList Γ N hr tr = some l) :
    ∃ l', resolveHead 64 Γ hr = .App (.Force (.Builtin .HeadList)) (.Var l) ∧
      resolveHead 64 Γ tr = .App (.Force (.Builtin .TailList)) (.Var l') ∧
      (l == l') = true ∧ N.contains l = true := by
  unfold headTailList at h
  split at h
  · rename_i l₀ l₁ hh ht
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨l₁, hh, ht, hc.1, hc.2⟩
    · cases h
  · cases h

theorem CheckedRel.of_flatten {Γ : List (VarId × Expr)} {N : List VarId}
    {bs flat : List (VarId × Expr × Bool)} {body inner e' : Expr}
    (hflat : flattenBindings bs body = (flat, inner)) (h : CheckedRel Γ N (.Let flat inner) e') :
    CheckedRel Γ N (.Let bs body) e' := by
  apply h.congr_left
  · intro env; rw [← flattenBindings_lower bs body env, hflat]
  · intro avoid; rw [← flattenBindings_fresh bs body avoid, hflat]

theorem flatten_one_nil_lt {bs : List (VarId × Expr × Bool)} {body inner r : Expr} {x : VarId}
    {er : Bool} (hf : flattenBindings bs body = ([(x, r, er)], inner)) :
    exprSize (.Let [] inner) < exprSize (.Let bs body) := by
  have bound := exprSize_flattenBindings bs body
  rw [hf] at bound
  have := exprSize_pos r
  simp only [exprSize, exprSizeBinds] at bound ⊢
  omega

theorem checkedBranchWalk_rel (e : Expr) (Γ : List (VarId × Expr)) (N : List VarId) :
    CheckedRel Γ N e (checkedBranchWalk Γ N e) := by
  match e with
  | .App function argument =>
    by_cases hshape : ∃ sel l em ne, function = .App (.App sel (.Var l)) em ∧ argument = .Delay ne
    · obtain ⟨sel, l, em, ne, rfl, rfl⟩ := hshape
      rw [checkedBranchWalk.eq_1]
      split
      · rename_i hcond
        exact CheckedRel.choose (beq_chooseList hcond) (checkedBranchWalk_rel em Γ N)
          (checkedBranchWalk_rel ne Γ (l :: N))
      · exact (checkedBranchWalk_rel _ Γ N).app (checkedBranchWalk_rel _ Γ N)
    · rw [checkedBranchWalk.eq_2 _ _ _ _ (fun s l em ne h₁ h₂ => hshape ⟨s, l, em, ne, h₁, h₂⟩)]
      exact (checkedBranchWalk_rel function Γ N).app (checkedBranchWalk_rel argument Γ N)
  | .Case scrutinee alternatives =>
    by_cases hshape : ∃ sel l ne em, scrutinee = .App sel (.Var l) ∧ alternatives = [ne, em]
    · obtain ⟨sel, l, ne, em, rfl, rfl⟩ := hshape
      rw [checkedBranchWalk.eq_3]
      split
      · rename_i hcond
        exact CheckedRel.nullCase (beq_force_nullList' hcond) (checkedBranchWalk_rel ne Γ (l :: N))
          (checkedBranchWalk_rel em Γ N)
      · exact CheckedRel.case (checkedBranchWalk_rel _ Γ N)
          (listRel_checked_attach_map _ _ fun c _ => checkedBranchWalk_rel c Γ N)
    · rw [checkedBranchWalk.eq_4 _ _ _ _ (fun s l ne em h₁ h₂ => hshape ⟨s, l, ne, em, h₁, h₂⟩)]
      exact CheckedRel.case (checkedBranchWalk_rel scrutinee Γ N)
        (listRel_checked_attach_map _ _ fun c _ => checkedBranchWalk_rel c Γ N)
  | .Let bs body =>
    rw [checkedBranchWalk.eq_5]
    split
    · rename_i inner hflat
      apply CheckedRel.of_flatten hflat
      exact (checkedBranchWalk_rel inner Γ N).congr_left (fun env => lowerTotalExpr_let_nil env inner)
        (fun avoid => freshIn_let_nil avoid inner)
    · rename_i x r er rest inner hflat
      split
      · rename_i t tr te remaining
        apply CheckedRel.of_flatten hflat
        have fallback : CheckedRel Γ N (.Let ((x, r, er) :: (t, tr, te) :: remaining) inner)
            (.Let [(x, checkedBranchWalk Γ N r, er)]
              (checkedBranchWalk ((x, checkedBranchWalk Γ N r) :: Γ)
                (aliasFacts N x (checkedBranchWalk Γ N r)) (.Let ((t, tr, te) :: remaining) inner))) :=
          (CheckedRel.let_single (checkedBranchWalk Γ N r) (.inr rfl) (checkedBranchWalk_rel r Γ N)
            (checkedBranchWalk_rel _ _ _) (aliasFacts_step _ _ _)).congr_left
            (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
        split
        · rename_i l hsome
          obtain ⟨l', hhead, htail, hll, hnon⟩ := headTailList_some hsome
          have ihsuffix := checkedBranchWalk_rel (.Let remaining inner) ((t, tr) :: (x, r) :: Γ) N
          refine (CheckedRel.fusion (he := er) (te := te) hhead htail hll hnon ihsuffix).congr_left ?_ ?_
          · intro env
            rw [lowerTotalExpr_let_cons env (x, r, er), lowerTotalExpr_let_single,
              lowerTotalExpr_let_single, lowerTotalExpr_let_cons (x :: env) (t, tr, te)]
          · intro avoid
            rw [freshIn_let_cons avoid (x, r, er), freshIn_let_single, freshIn_let_single,
              freshIn_let_cons (x :: avoid) (t, tr, te)]
        · exact fallback
      · apply CheckedRel.of_flatten hflat
        exact (CheckedRel.let_single (checkedBranchWalk Γ N r) (.inr rfl) (checkedBranchWalk_rel r Γ N)
          (checkedBranchWalk_rel _ _ _) (aliasFacts_step _ _ _)).congr_left
          (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
  | .Lam x b => rw [checkedBranchWalk.eq_6]; exact (checkedBranchWalk_rel b Γ N).lam
  | .Fix f b =>
    rw [checkedBranchWalk.eq_7]
    cases b with
    | Lam x inner =>
      rw [checkedBranchWalk.eq_6]
      exact (checkedBranchWalk_rel inner Γ N).fix_lam
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .Force b => rw [checkedBranchWalk.eq_8]; exact (checkedBranchWalk_rel b Γ N).force
  | .Delay b => rw [checkedBranchWalk.eq_9]; exact (checkedBranchWalk_rel b Γ N).delay
  | .Constr tag fields =>
    rw [checkedBranchWalk.eq_10]
    exact CheckedRel.constr (listRel_checked_attach_map fields _ fun c _ => checkedBranchWalk_rel c Γ N)
  | .Var _ | .Lit _ | .Builtin _ | .Error => rw [checkedBranchWalk]; exact CheckedRel.refl _ _ _
termination_by exprSize e
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (subst_vars; simp only [exprSize]; omega)
    | (subst_vars; simp only [exprSize, exprSizeList]; omega)
    | (subst_vars; have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | exact (flatten_two_lt (by assumption)).1
    | exact (flatten_two_lt (by assumption)).2.1
    | exact (flatten_two_lt (by assumption)).2.2
    | exact flatten_nil_lt (by assumption)
    | exact (flatten_one_lt (by assumption)).1
    | exact (flatten_one_lt (by assumption)).2
    | exact flatten_one_nil_lt (by assumption)

end Moist.Verified.ShapeFacts
