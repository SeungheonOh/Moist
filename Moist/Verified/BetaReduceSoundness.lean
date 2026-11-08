import Moist.Verified.InlineSoundness
import Moist.Verified.HygieneSoundness
import Moist.MIR.Optimize.BetaReduce

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of general beta reduction

`betaReducePass_refines : MIRCtxRefines e (betaReducePass e s).1.1` for every
MIR expression `e` and fresh-name state `s`.

The root freshening is exact on lowering (`Hygiene.uniqueOptimizationBinders_lower`)
and the reserved counter sits above every uid of the prepared term. The walk
keeps every uid of its output below the counter, so each contraction meets the
freshness precondition of the substitution/lowering commutation: an atomic
argument is the Inline pass's atom beta rule (`betaReduce_soundness`), and a
non-atomic one only changes `App (Lam p b) x` into `Let [(p, x, false)] b`,
which lowers identically (`mirCtxRefines_app_lam_to_let`). -/

namespace Moist.Verified.MIR.BetaReduce

open Moist.MIR
  (Expr VarId FreshState subst betaReduce betaContract betaReduceCore betaReduceCoreList
   betaReduceCoreBinds betaReducePass maxUidExpr maxUidExprList maxUidExprBinds
   uniqueOptimizationBinders)
open Moist.Verified.MIR
  (MIRCtxRefines mirCtxRefines_refl mirCtxRefines_trans mirCtxRefines_app mirCtxRefines_lam
   mirCtxRefines_fix_lam mirCtxRefines_fix_nonlam_lhs mirCtxRefines_force mirCtxRefines_delay
   mirCtxRefines_constr mirCtxRefines_case mirCtxRefines_let_binds_congr mirCtxRefines_let_body
   mirCtxRefines_app_lam_to_let betaReduce_soundness)
open Moist.Verified.InlineSoundness.Rename (maxUid_list_cons)
open Moist.Verified.InlineSoundness.SubstCommute (subst_fresh)
open Moist.Verified.InlineSoundness.Preservation (betaReduce_lam)
open Moist.Verified.Equivalence (ListRel)

/-! ## Equations of the walk -/

section Equations
variable (s : FreshState)

omit sv in
theorem core_app (f x : Expr) :
    betaReduceCore (.App f x) s =
      betaContract (betaReduceCore f s).1.1 (betaReduceCore x (betaReduceCore f s).2).1.1
        ((betaReduceCore f s).1.2 || (betaReduceCore x (betaReduceCore f s).2).1.2)
        (betaReduceCore x (betaReduceCore f s).2).2 := by
  rw [Moist.MIR.betaReduceCore.eq_1]; rfl

omit sv in
theorem core_lam (x : VarId) (b : Expr) :
    (betaReduceCore (.Lam x b) s).1.1 = .Lam x (betaReduceCore b s).1.1 ∧
      (betaReduceCore (.Lam x b) s).2 = (betaReduceCore b s).2 := by
  rw [Moist.MIR.betaReduceCore.eq_2]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_fix (f : VarId) (b : Expr) :
    (betaReduceCore (.Fix f b) s).1.1 = .Fix f (betaReduceCore b s).1.1 ∧
      (betaReduceCore (.Fix f b) s).2 = (betaReduceCore b s).2 := by
  rw [Moist.MIR.betaReduceCore.eq_3]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_force (e : Expr) :
    (betaReduceCore (.Force e) s).1.1 = .Force (betaReduceCore e s).1.1 ∧
      (betaReduceCore (.Force e) s).2 = (betaReduceCore e s).2 := by
  rw [Moist.MIR.betaReduceCore.eq_4]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_delay (e : Expr) :
    (betaReduceCore (.Delay e) s).1.1 = .Delay (betaReduceCore e s).1.1 ∧
      (betaReduceCore (.Delay e) s).2 = (betaReduceCore e s).2 := by
  rw [Moist.MIR.betaReduceCore.eq_5]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_constr (tag : Nat) (args : List Expr) :
    (betaReduceCore (.Constr tag args) s).1.1 = .Constr tag (betaReduceCoreList args s).1.1 ∧
      (betaReduceCore (.Constr tag args) s).2 = (betaReduceCoreList args s).2 := by
  rw [Moist.MIR.betaReduceCore.eq_6]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_case (scrut : Expr) (alts : List Expr) :
    (betaReduceCore (.Case scrut alts) s).1.1 =
        .Case (betaReduceCore scrut s).1.1 (betaReduceCoreList alts (betaReduceCore scrut s).2).1.1 ∧
      (betaReduceCore (.Case scrut alts) s).2 = (betaReduceCoreList alts (betaReduceCore scrut s).2).2 := by
  rw [Moist.MIR.betaReduceCore.eq_7]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_let (binds : List (VarId × Expr × Bool)) (body : Expr) :
    (betaReduceCore (.Let binds body) s).1.1 =
        .Let (betaReduceCoreBinds binds s).1.1 (betaReduceCore body (betaReduceCoreBinds binds s).2).1.1 ∧
      (betaReduceCore (.Let binds body) s).2 = (betaReduceCore body (betaReduceCoreBinds binds s).2).2 := by
  rw [Moist.MIR.betaReduceCore.eq_8]; exact ⟨rfl, rfl⟩

omit sv in
theorem core_leaf (e : Expr)
    (leaf : match e with | .Var _ | .Lit _ | .Builtin _ | .Error => True | _ => False) :
    betaReduceCore e s = ((e, false), s) := by
  cases e <;> first | exact leaf.elim | (rw [Moist.MIR.betaReduceCore.eq_9] <;> first | rfl | (intros; simp_all))

omit sv in
theorem coreList_nil : betaReduceCoreList [] s = (([], false), s) := by
  rw [Moist.MIR.betaReduceCoreList.eq_1]; rfl

omit sv in
theorem coreList_cons (e : Expr) (rest : List Expr) :
    (betaReduceCoreList (e :: rest) s).1.1 =
        (betaReduceCore e s).1.1 :: (betaReduceCoreList rest (betaReduceCore e s).2).1.1 ∧
      (betaReduceCoreList (e :: rest) s).2 = (betaReduceCoreList rest (betaReduceCore e s).2).2 := by
  rw [Moist.MIR.betaReduceCoreList.eq_2]; exact ⟨rfl, rfl⟩

omit sv in
theorem coreBinds_nil : betaReduceCoreBinds [] s = (([], false), s) := by
  rw [Moist.MIR.betaReduceCoreBinds.eq_1]; rfl

omit sv in
theorem coreBinds_cons (v : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool)) :
    (betaReduceCoreBinds ((v, rhs, er) :: rest) s).1.1 =
        (v, (betaReduceCore rhs s).1.1, er) :: (betaReduceCoreBinds rest (betaReduceCore rhs s).2).1.1 ∧
      (betaReduceCoreBinds ((v, rhs, er) :: rest) s).2 =
        (betaReduceCoreBinds rest (betaReduceCore rhs s).2).2 := by
  rw [Moist.MIR.betaReduceCoreBinds.eq_2]; exact ⟨rfl, rfl⟩

end Equations

/-! ## The contraction step -/

omit sv in
theorem contract_lam (p : VarId) (b x : Expr) (c : Bool) (s : FreshState) :
    betaContract (.Lam p b) x c s =
      if x.isAtom then (((subst p x b s).1, true), (subst p x b s).2)
      else ((.Let [(p, x, false)] b, true), s) := by
  simp only [betaContract]; split <;> rfl

omit sv in
theorem contract_other (f x : Expr) (c : Bool) (s : FreshState) (h : ∀ p b, f ≠ .Lam p b) :
    betaContract f x c s = ((.App f x, c), s) := by
  cases f <;> first | rfl | exact absurd rfl (h _ _)

omit sv in
theorem contract_fresh (f x : Expr) (c : Bool) (s : FreshState)
    (hf : maxUidExpr f < s.next) (hx : maxUidExpr x < s.next) :
    maxUidExpr (betaContract f x c s).1.1 < (betaContract f x c s).2.next ∧
      s.next ≤ (betaContract f x c s).2.next := by
  cases f with
  | Lam p b =>
    rw [contract_lam]
    simp only [maxUidExpr] at hf
    split
    · exact subst_fresh p x b s (by omega) hx
    · simp only [maxUidExpr, maxUidExprBinds]; omega
  | _ => rw [contract_other _ _ _ _ (by intros; simp)]; simp only [maxUidExpr] at hf ⊢; omega

theorem contract_refines (f x : Expr) (c : Bool) (s : FreshState)
    (hf : maxUidExpr f < s.next) (hx : maxUidExpr x < s.next) :
    MIRCtxRefines (.App f x) (betaContract f x c s).1.1 := by
  cases f with
  | Lam p b =>
    rw [contract_lam]
    split
    · rename_i hatom
      have h := betaReduce_soundness (.Lam p b) x s hf hx
      rwa [betaReduce_lam, if_pos hatom] at h
    · exact mirCtxRefines_app_lam_to_let p b x
  | _ => rw [contract_other _ _ _ _ (by intros; simp)]; exact mirCtxRefines_refl _

/-! ## Every uid of the output stays below the counter -/

mutual
  theorem core_fresh : ∀ (e : Expr) (s : FreshState), maxUidExpr e < s.next →
      maxUidExpr (betaReduceCore e s).1.1 < (betaReduceCore e s).2.next ∧
        s.next ≤ (betaReduceCore e s).2.next
    | .Var _, s, fe | .Lit _, s, fe | .Builtin _, s, fe | .Error, s, fe => by
      rw [core_leaf s _ trivial]; exact ⟨fe, Nat.le_refl _⟩
    | .Lam x b, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_lam s x b
      simp only [maxUidExpr] at fe
      have := core_fresh b s (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Fix f b, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_fix s f b
      simp only [maxUidExpr] at fe
      have := core_fresh b s (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .App f x, s, fe => by
      simp only [maxUidExpr] at fe
      have hf := core_fresh f s (by omega)
      have hx := core_fresh x (betaReduceCore f s).2 (by omega)
      have := contract_fresh (betaReduceCore f s).1.1 (betaReduceCore x (betaReduceCore f s).2).1.1
        ((betaReduceCore f s).1.2 || (betaReduceCore x (betaReduceCore f s).2).1.2)
        (betaReduceCore x (betaReduceCore f s).2).2 (by omega) hx.1
      rw [core_app]; omega
    | .Force e, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_force s e
      simp only [maxUidExpr] at fe
      have := core_fresh e s fe
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Delay e, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_delay s e
      simp only [maxUidExpr] at fe
      have := core_fresh e s fe
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Constr tag args, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_constr s tag args
      simp only [maxUidExpr] at fe
      have := coreList_fresh args s fe
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Case scrut alts, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_case s scrut alts
      simp only [maxUidExpr] at fe
      have hs := core_fresh scrut s (by omega)
      have := coreList_fresh alts (betaReduceCore scrut s).2 (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
    | .Let binds body, s, fe => by
      obtain ⟨h₁, h₂⟩ := core_let s binds body
      simp only [maxUidExpr] at fe
      have hb := coreBinds_fresh binds s (by omega)
      have := core_fresh body (betaReduceCoreBinds binds s).2 (by omega)
      rw [h₁, h₂]; simp only [maxUidExpr]; omega
  termination_by e => sizeOf e

  theorem coreList_fresh : ∀ (es : List Expr) (s : FreshState), maxUidExprList es < s.next →
      maxUidExprList (betaReduceCoreList es s).1.1 < (betaReduceCoreList es s).2.next ∧
        s.next ≤ (betaReduceCoreList es s).2.next
    | [], s, fe => by rw [coreList_nil]; exact ⟨fe, Nat.le_refl _⟩
    | e :: rest, s, fe => by
      obtain ⟨h₁, h₂⟩ := coreList_cons s e rest
      rw [maxUid_list_cons] at fe
      have he := core_fresh e s (by omega)
      have := coreList_fresh rest (betaReduceCore e s).2 (by omega)
      rw [h₁, h₂, maxUid_list_cons]; omega
  termination_by es => sizeOf es

  theorem coreBinds_fresh : ∀ (binds : List (VarId × Expr × Bool)) (s : FreshState),
      maxUidExprBinds binds < s.next →
      maxUidExprBinds (betaReduceCoreBinds binds s).1.1 < (betaReduceCoreBinds binds s).2.next ∧
        s.next ≤ (betaReduceCoreBinds binds s).2.next
    | [], s, fe => by rw [coreBinds_nil]; exact ⟨fe, Nat.le_refl _⟩
    | (v, rhs, er) :: rest, s, fe => by
      obtain ⟨h₁, h₂⟩ := coreBinds_cons s v rhs er rest
      simp only [maxUidExprBinds] at fe
      have hr := core_fresh rhs s (by omega)
      have := coreBinds_fresh rest (betaReduceCore rhs s).2 (by omega)
      rw [h₁, h₂]; simp only [maxUidExprBinds]; omega
  termination_by binds => sizeOf binds
end

/-! ## Refinement of the walk -/

mutual
  theorem core_refines : ∀ (e : Expr) (s : FreshState), maxUidExpr e < s.next →
      MIRCtxRefines e (betaReduceCore e s).1.1
    | .Var _, s, _ | .Lit _, s, _ | .Builtin _, s, _ | .Error, s, _ => by
      rw [core_leaf s _ trivial]; exact mirCtxRefines_refl _
    | .Lam x b, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_lam s x b).1]
      exact mirCtxRefines_lam (core_refines b s (by omega))
    | .Fix f b, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_fix s f b).1]
      cases b with
      | Lam x inner =>
        simp only [maxUidExpr] at fe
        rw [(core_lam s x inner).1]
        exact mirCtxRefines_fix_lam (core_refines inner s (by omega))
      | _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; simp)
    | .App f x, s, fe => by
      simp only [maxUidExpr] at fe
      have hf := core_fresh f s (by omega)
      have hx := core_fresh x (betaReduceCore f s).2 (by omega)
      rw [core_app]
      exact mirCtxRefines_trans
        (mirCtxRefines_app (core_refines f s (by omega))
          (core_refines x (betaReduceCore f s).2 (by omega)))
        (contract_refines _ _ _ _ (by omega) hx.1)
    | .Force e, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_force s e).1]
      exact mirCtxRefines_force (core_refines e s fe)
    | .Delay e, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_delay s e).1]
      exact mirCtxRefines_delay (core_refines e s fe)
    | .Constr tag args, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_constr s tag args).1]
      cases args with
      | nil => rw [coreList_nil]; exact mirCtxRefines_refl _
      | cons e rest =>
        rw [maxUid_list_cons] at fe
        rw [(coreList_cons s e rest).1]
        have := core_fresh e s (by omega)
        exact mirCtxRefines_constr (core_refines e s (by omega))
          (coreList_listRel rest _ (by omega))
    | .Case scrut alts, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_case s scrut alts).1]
      have := core_fresh scrut s (by omega)
      exact mirCtxRefines_case (core_refines scrut s (by omega))
        (coreList_listRel alts _ (by omega))
    | .Let binds body, s, fe => by
      simp only [maxUidExpr] at fe
      rw [(core_let s binds body).1]
      have fb := coreBinds_fresh binds s (by omega)
      exact mirCtxRefines_trans
        (mirCtxRefines_let_binds_congr binds (betaReduceCoreBinds binds s).1.1 body
          (coreBinds_listRel binds s (by omega)))
        (mirCtxRefines_let_body (core_refines body _ (by omega)))
  termination_by e => sizeOf e

  theorem coreList_listRel : ∀ (es : List Expr) (s : FreshState), maxUidExprList es < s.next →
      ListRel MIRCtxRefines es (betaReduceCoreList es s).1.1
    | [], s, _ => by rw [coreList_nil]; exact True.intro
    | e :: rest, s, fe => by
      rw [maxUid_list_cons] at fe
      rw [(coreList_cons s e rest).1]
      have := core_fresh e s (by omega)
      exact ⟨core_refines e s (by omega), coreList_listRel rest _ (by omega)⟩
  termination_by es => sizeOf es

  theorem coreBinds_listRel : ∀ (binds : List (VarId × Expr × Bool)) (s : FreshState),
      maxUidExprBinds binds < s.next →
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
        binds (betaReduceCoreBinds binds s).1.1
    | [], s, _ => by rw [coreBinds_nil]; exact True.intro
    | (v, rhs, er) :: rest, s, fe => by
      simp only [maxUidExprBinds] at fe
      rw [(coreBinds_cons s v rhs er rest).1]
      have := core_fresh rhs s (by omega)
      exact ⟨⟨rfl, rfl, core_refines rhs s (by omega)⟩, coreBinds_listRel rest _ (by omega)⟩
  termination_by binds => sizeOf binds
end

/-! ## The pass -/

omit sv in
theorem betaReducePass_eq (e : Expr) (s : FreshState) :
    betaReducePass e s =
      betaReduceCore (uniqueOptimizationBinders e)
        { next := max s.next (maxUidExpr (uniqueOptimizationBinders e) + 1) } := rfl

theorem betaReducePass_refines (e : Expr) (s : FreshState) :
    MIRCtxRefines e (betaReducePass e s).1.1 := by
  rw [betaReducePass_eq]
  exact mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
    (core_refines _ _ (by show _ < max _ _; omega))

/-- The output's uids stay below the returned counter, which never decreases. -/
theorem betaReducePass_fresh (e : Expr) (s : FreshState) :
    maxUidExpr (betaReducePass e s).1.1 < (betaReducePass e s).2.next ∧
      s.next ≤ (betaReducePass e s).2.next := by
  rw [betaReducePass_eq]
  have := core_fresh (uniqueOptimizationBinders e)
    { next := max s.next (maxUidExpr (uniqueOptimizationBinders e) + 1) }
    (by show _ < max _ _; omega)
  refine ⟨this.1, ?_⟩
  have h2 := this.2
  simp only at h2
  omega

end Moist.Verified.MIR.BetaReduce
