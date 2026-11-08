import Moist.Verified.TagGuardSoundness.PairGuard
import Moist.Verified.FailFastSoundness
import Moist.Verified.HygieneSoundness

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of constructor-tag prechecks

`tagGuards_refines`: for every MIR expression `e`, `e ⊑Ctxᴹ tagGuards e`.

The walk is certified with the `FactRel` congruences; its facts are the
rewritten right-hand sides of the enclosing bindings, exactly the facts the
pass passes to `pairGuard`. At every guarded pair case the rewrite of the
alternative (`pairGuard_sound`) is post-composed under the facts.
-/

namespace Moist.Verified.TagGuard

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

theorem FactRel.postFacts {G : VarId → Prop} {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {e e₁ e₂ : Expr} (h : FactRel G P Γ e e₁)
    (h₂ : ∀ env t₁, EnvDistinct env → lowerTotalExpr env e₁ = some t₁ →
      ∃ t₂, lowerTotalExpr env e₂ = some t₂ ∧ FactRefines env.length (FactsHold P Γ env) t₁ t₂) :
    FactRel G P Γ e e₂ := by
  intro env t hG hd hf hk hs ht
  obtain ⟨t₁, ht₁, hr⟩ := h env t hG hd hf hk hs ht
  obtain ⟨t₂, ht₂, hr₂⟩ := h₂ env t₁ hd ht₁
  exact ⟨t₂, ht₂, hr.trans hr₂⟩

theorem listRel_tag_of {Γ : List (VarId × Expr)} :
    ∀ {es : List Expr}, (∀ e ∈ es, FactRel AnyName Produces Γ e (tagGuardWalk Γ e)) →
      ListRel (FactRel AnyName Produces Γ) es (es.map (tagGuardWalk Γ))
  | [], _ => trivial
  | e :: _, h => ⟨h e (.head _), listRel_tag_of fun e' he' => h e' (.tail _ he')⟩

/-- The guard at a pair case, post-composed under the facts. -/
theorem pairGuard_post {Γ : List (VarId × Expr)} {e₁ body guarded : Expr} {t₁ f₁ : VarId}
    (h : pairGuard Γ t₁ f₁ body = some guarded) :
    ∀ env t, EnvDistinct env →
      lowerTotalExpr env (.Case (.App (.Builtin .UnConstrData) e₁) [.Lam t₁ (.Lam f₁ body)]) = some t →
      ∃ t', lowerTotalExpr env (.Case (.App (.Builtin .UnConstrData) e₁) [.Lam t₁ (.Lam f₁ guarded)]) =
        some t' ∧ FactRefines env.length (FactsHold Produces Γ env) t t' := by
  intro env t hd hlow
  obtain ⟨tsc, talts, htsc, htalts, rfl⟩ := lowerTotalExpr_case_some hlow
  obtain ⟨tf, tE, htf, htE, rfl⟩ := lowerTotalExpr_app_some htsc
  rw [lowerTotalExpr_builtin] at htf; cases htf
  rw [MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil] at htalts
  cases hl : lowerTotalExpr env (.Lam t₁ (.Lam f₁ body)) with
  | none => rw [hl] at htalts; cases htalts
  | some tl =>
    rw [hl] at htalts; cases htalts
    obtain ⟨tl1, htl1, rfl⟩ := lowerTotalExpr_lam_some hl
    obtain ⟨tbody, htbody, rfl⟩ := lowerTotalExpr_lam_some htl1
    obtain ⟨tg, htg, hr⟩ := pairGuard_sound h env tbody hd htbody
    refine ⟨.Case (.Apply (.Builtin .UnConstrData) tE) [.Lam 0 (.Lam 0 tg)], ?_,
      factRefines_pairCase (MIR.lowerTotalExpr_closedAt htE) hr⟩
    rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_app, lowerTotalExpr_builtin, htE,
      MIR.lowerTotalExprList_cons, MIR.lowerTotalExprList_nil, MIR.lowerTotalExpr_lam,
      MIR.lowerTotalExpr_lam, htg]
    rfl

omit sv in
theorem pairCaseView_some' {e e₁ body : Expr} {t f : VarId}
    (h : pairCaseView e = some (e₁, t, f, body)) :
    e = .Case (.App (.Builtin .UnConstrData) e₁) [.Lam t (.Lam f body)] :=
  pairCaseView_some h

theorem tagGuardWalk_factRel : ∀ (N : Nat) (e : Expr), exprSize e < N →
    ∀ Γ, FactRel AnyName Produces Γ e (tagGuardWalk Γ e) := by
  intro N
  induction N with
  | zero => intro _ h; omega
  | succ N ih =>
  intro e hsize Γ
  match e with
  | .Let [] body =>
    rw [tagGuardWalk]
    simp only [exprSize, exprSizeBinds] at hsize
    exact (ih body (by omega) Γ).congr_left (fun env => lowerTotalExpr_let_nil env body)
      (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    rw [tagGuardWalk]
    simp only [exprSize, exprSizeBinds] at hsize
    have ihr := ih r (by omega) Γ
    have ihb := ih (.Let rest body) (by have := exprSize_pos r; simp only [exprSize]; omega)
      ((x, tagGuardWalk Γ r) :: Γ)
    have hlet : FactRel AnyName Produces Γ (.Let ((x, r, er) :: rest) body)
        (.Let [(x, tagGuardWalk Γ r, er)] (tagGuardWalk ((x, tagGuardWalk Γ r) :: Γ) (.Let rest body))) :=
      (FactRel.let_single (er := er) (tagGuardWalk Γ r) trivial (.inr rfl) ihr ihb
        (fun _ _ _ _ _ _ hp => hp)).congr_left
        (fun env => lowerTotalExpr_let_cons env _ _ _) (fun avoid => freshIn_let_cons avoid _ _ _)
    exact hlet.congr_right fun env => lowerTotalExpr_consLet' env _ _
  | .Lam x b =>
    rw [tagGuardWalk]
    simp only [exprSize] at hsize
    exact (ih b (by omega) Γ).lam trivial
  | .Fix f b =>
    rw [tagGuardWalk]
    simp only [exprSize] at hsize
    cases hb : b with
    | Lam x inner =>
      subst hb
      rw [tagGuardWalk]
      simp only [exprSize] at hsize
      exact (ih inner (by omega) Γ).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a =>
    rw [tagGuardWalk]
    simp only [exprSize] at hsize
    exact (ih f (by omega) Γ).app (ih a (by omega) Γ)
  | .Force b =>
    rw [tagGuardWalk]
    simp only [exprSize] at hsize
    exact (ih b (by omega) Γ).force
  | .Delay b =>
    rw [tagGuardWalk]
    simp only [exprSize] at hsize
    exact (ih b (by omega) Γ).delay
  | .Constr tag fields =>
    rw [tagGuardWalk, productList_attach_map]
    simp only [exprSize] at hsize
    exact FactRel.constr (listRel_tag_of fun e he =>
      ih e (by have := exprSize_lt_of_mem he; omega) Γ)
  | .Case s alts =>
    rw [tagGuardWalk]
    simp only [exprSize] at hsize
    have hcase : FactRel AnyName Produces Γ (.Case s alts)
        (.Case (tagGuardWalk Γ s) (alts.attach.map fun ⟨a, _⟩ => tagGuardWalk Γ a)) := by
      rw [productList_attach_map]
      exact FactRel.case (ih s (by omega) Γ) (listRel_tag_of fun e he =>
        ih e (by have := exprSize_lt_of_mem he; omega) Γ)
    dsimp only
    split
    · rename_i e₁ t₁ f₁ body hview
      split
      · rename_i guarded hguard
        have heq := pairCaseView_some' hview
        rw [heq] at hcase
        exact FactRel.postFacts hcase (pairGuard_post hguard)
      · exact hcase
    · exact hcase
  | .Var _ | .Lit _ | .Builtin _ | .Error =>
    rw [tagGuardWalk]; exact FactRel.refl _ _ _ _

end Moist.Verified.TagGuard

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts Moist.Verified.TagGuard

/-- Constructor-tag prechecks refine their input. -/
theorem tagGuards_refines (e : Expr) : MIRCtxRefines e (Advanced.tagGuards e) := by
  unfold Advanced.tagGuards
  simp only
  refine mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e) ?_
  split
  · rename_i hws
    exact mirCtxRefines_of_factRel hws (fun _ _ => trivial) (fun _ _ => trivial)
      (tagGuardWalk_factRel _ _ (Nat.lt_succ_self _) [])
  · exact mirCtxRefines_refl _

end Moist.Verified.MIR
