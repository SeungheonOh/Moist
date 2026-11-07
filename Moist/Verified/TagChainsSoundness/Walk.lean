import Moist.Verified.TagChainsSoundness.Binding
import Moist.Verified.CheckedBranchesSoundness.Lowering

/-! # The tag chain walk

Every node is first related to the walk of its children by a congruence,
recording the source right-hand side of each binding as a fact. The local
rewrite of the node (a tag rule at a case, a pushed argument at an
application, a consumed or dropped binding at a let) then refines the
congruence result in the same environment (`FactRel.post`).
-/

namespace Moist.Verified.TagChains

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.ShapeFacts

theorem tagChainWalk_factRel (e : Expr) (Γ : List (VarId × Expr)) :
    FactRel (fun _ => True) Produces Γ e (tagChainWalk Γ e) := by
  match e with
  | .Case scrutinee alternatives =>
    rw [tagChainWalk.eq_1]
    exact FactRel.post (FactRel.case (tagChainWalk_factRel scrutinee Γ)
      (listRel_attach_map alternatives _ fun c _ => tagChainWalk_factRel c Γ))
        (tagCaseRule_getD_rewrites _ _ _)
  | .App f a =>
    rw [tagChainWalk.eq_2]
    exact FactRel.post ((tagChainWalk_factRel f Γ).app (tagChainWalk_factRel a Γ))
      (tagApplication_rewrites _ _ _)
  | .Let [] body =>
    rw [tagChainWalk.eq_3]
    exact (tagChainWalk_factRel body Γ).congr_left
      (fun env => lowerTotalExpr_let_nil env body) (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    rw [tagChainWalk.eq_4]
    refine (FactRel.post ?_ (tagBinding_rewrites _ _ _ _ _))
    exact (FactRel.let_single r trivial (.inl rfl) (tagChainWalk_factRel r Γ)
      (tagChainWalk_factRel (.Let rest body) ((x, r) :: Γ))
      (fun _ _ _ _ _ _ hp => hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
      (fun avoid => freshIn_let_cons avoid _ _ _)
  | .Lam x b => rw [tagChainWalk.eq_5]; exact (tagChainWalk_factRel b Γ).lam trivial
  | .Fix f b =>
    rw [tagChainWalk]
    cases b with
    | Lam x inner =>
      rw [tagChainWalk.eq_5]
      exact (tagChainWalk_factRel inner Γ).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .Force b => rw [tagChainWalk]; exact (tagChainWalk_factRel b Γ).force
  | .Delay b => rw [tagChainWalk]; exact (tagChainWalk_factRel b Γ).delay
  | .Constr tag fields =>
    rw [tagChainWalk]
    exact FactRel.constr (listRel_attach_map fields _ fun c _ => tagChainWalk_factRel c Γ)
  | .Var _ | .Lit _ | .Builtin _ | .Error => rw [tagChainWalk]; exact FactRel.refl _ _ _ _
termination_by exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

end Moist.Verified.TagChains

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Compiling constructor-tag test chains to integer cases refines its input. -/
theorem caseTagChains_refines (e : Expr) : MIRCtxRefines e (caseTagChains e) := by
  unfold caseTagChains
  simp only
  split
  · exact mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_of_factRel (by assumption) (fun _ _ => trivial) (fun _ _ => trivial)
        (Moist.Verified.TagChains.tagChainWalk_factRel _ []))
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
