import Moist.Verified.FloatOut.Lowering

variable [sv : Moist.CEK.SemVariant]

/-! # Single float-out steps on MIR

* `mirCtxRefines_floatLam`: `λx. let v = p; rest in b ⊑ let v = p in λx. let rest in b`
* `mirCtxRefines_floatFix`: the same out of `fix f (λx. …)`
* `mirCtxRefines_letSwap`: a pure binding moves before an earlier one
* `mirCtxRefines_floatCaseAlt`: a pure binding at an alternative's head moves
  before the case

Each needs `p` pure and the usual non-capture conditions. -/

namespace Moist.Verified.FloatOut

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (renameTerm renameTermList shiftRename liftRename)
open Moist.Verified.Contextual (CtxRefines)
open Moist.Verified.MIR (MIRCtxRefines mirCtxRefines_refl mirCtxRefines_trans
  mirCtxRefines_of_lowerEq mirCtxRefines_app mirCtxRefines_hoist MFrame
  lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons lowerTotalExprList_append
  lowerTotalExprList_prepend_unused lowerTotalExpr_prepend_unused lowerTotalExpr_closedAt
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_case_of_list lowerTotalExpr_let_single
  lowerTotalExpr_let_flatten_body lowerTotalList_closedAtList)
open Moist.Verified.InlineSoundness.Rename (lowerTotalExpr_let_cons lowerTotalExpr_fix_lam)
open Moist.Verified.InlineSoundness.Totality (TotalTerm lowerTotal_total)

/-- `MIRCtxRefines` from lowerings that factor through a common `P env`, with
    the factored terms contextually refining each other. -/
theorem mirCtxRefines_of_shapeCtx {α : Type} {m₁ m₂ : Expr}
    (P : List VarId → Option α) (T₁ T₂ : List VarId → α → Term)
    (h₁ : ∀ env, lowerTotalExpr env m₁ = (P env).map (T₁ env))
    (h₂ : ∀ env, lowerTotalExpr env m₂ = (P env).map (T₂ env))
    (hsem : ∀ env a, P env = some a → CtxRefines (T₁ env a) (T₂ env a)) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  rw [h₁, h₂]
  cases hP : P env with
  | none => exact ⟨id, trivial⟩
  | some a => exact ⟨fun _ => rfl, hsem env a hP⟩

omit sv in
theorem total_of_pure {env : List VarId} {p : Expr} {tp : Term} (hp : isPure p = true)
    (h : lowerTotalExpr env p = some tp) : TotalTerm tp :=
  lowerTotal_total (expandFix p) env tp (Moist.Verified.Purity.isPure_expandFix p hp) h

/-! ## Lambda -/

theorem mirCtxRefines_floatLam {x v : VarId} {p : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {B : Expr}
    (hp : isPure p = true) (hx : (freeVars p).contains x = false) (hvx : (v == x) = false) :
    MIRCtxRefines (.Lam x (.Let ((v, p, er) :: rest) B))
      (.Let [(v, p, er)] (.Lam x (.Let rest B))) := by
  refine mirCtxRefines_of_shapeCtx
    (fun env => (lowerTotalExpr env p).bind fun tp =>
      (lowerTotalExpr (v :: x :: env) (.Let rest B)).map fun tb => (tp, tb))
    (fun _ a => .Lam 0 (.Apply (.Lam 0 a.2) (renameTerm (shiftRename 1) a.1)))
    (fun _ a => .Apply (.Lam 0 (.Lam 0 (renameTerm swapRename a.2))) a.1)
    (fun env => ?_) (fun env => ?_) (fun env a h => ?_)
  · rw [lowerTotalExpr_lam, lowerTotalExpr_let_cons, lowerTotalExpr_prepend_unused env x p hx]
    dsimp only
    cases lowerTotalExpr env p <;> cases lowerTotalExpr (v :: x :: env) (.Let rest B) <;> rfl
  · rw [lowerTotalExpr_let_single, lowerTotalExpr_lam, lowerTotalExpr_swap hvx env]
    dsimp only
    cases lowerTotalExpr env p <;> cases lowerTotalExpr (v :: x :: env) (.Let rest B) <;> rfl
  · obtain ⟨tp, tb⟩ := a
    cases hp' : lowerTotalExpr env p <;> cases hb : lowerTotalExpr (v :: x :: env) (.Let rest B) <;>
      simp [hp', hb] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ctxRefines_floatLam (total_of_pure hp hp') (lowerTotalExpr_closedAt hp')
      (by simpa using lowerTotalExpr_closedAt hb)

/-! ## Recursive lambda -/

theorem mirCtxRefines_floatFix {f x v : VarId} {p : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {B : Expr}
    (hp : isPure p = true) (hf : (freeVars p).contains f = false)
    (hx : (freeVars p).contains x = false) (hvf : (v == f) = false) (hvx : (v == x) = false) :
    MIRCtxRefines (.Fix f (.Lam x (.Let ((v, p, er) :: rest) B)))
      (.Let [(v, p, er)] (.Fix f (.Lam x (.Let rest B)))) := by
  have hmax : maxUidExpr (expandFix (.Let ((v, p, er) :: rest) B)) =
      max v.uid (max (maxUidExpr (expandFix p)) (maxUidExpr (expandFix (.Let rest B)))) := by
    simp only [expandFix, expandFixBinds, maxUidExpr, maxUidExprBinds]
    omega
  let s : VarId :=
    ⟨max (maxUidExpr p) (maxUidExpr (expandFix (.Let ((v, p, er) :: rest) B))) + 1, .gen, "s"⟩
  have hs₁ : maxUidExpr (expandFix (.Let ((v, p, er) :: rest) B)) < s.uid := by
    simp only [s]; omega
  have hs₂ : maxUidExpr (expandFix (.Let rest B)) < s.uid := by simp only [s]; omega
  have hps : (freeVars p).contains s = false := maxUidExpr_fresh p s (by simp only [s]; omega)
  have hvs : (v == s) = false :=
    Moist.Verified.InlineSoundness.Rename.beq_false_of_uid (by simp only [s]; omega)
  refine mirCtxRefines_of_shapeCtx
    (fun env => (lowerTotalExpr env p).bind fun tp =>
      (lowerTotalExpr (v :: x :: f :: s :: env) (.Let rest B)).map fun tb => (tp, tb))
    (fun _ a => fixLamWrapUplc (.Apply (.Lam 0 a.2) (renameTerm (shiftRename 1)
      (renameTerm (shiftRename 1) (renameTerm (shiftRename 1) a.1)))))
    (fun _ a => .Apply (.Lam 0 (fixLamWrapUplc (rotRename a.2))) a.1)
    (fun env => ?_) (fun env => ?_) (fun env a h => ?_)
  · rw [lowerTotalExpr_fix_lam env f x _ s hs₁, lowerTotalExpr_let_cons,
      lowerTotalExpr_prepend_unused _ x p hx, lowerTotalExpr_prepend_unused _ f p hf,
      lowerTotalExpr_prepend_unused _ s p hps]
    dsimp only
    cases lowerTotalExpr env p <;> cases lowerTotalExpr (v :: x :: f :: s :: env) (.Let rest B) <;>
      rfl
  · have h₁ := lowerTotalExpr_swap hvx (f :: s :: env) (.Let rest B)
    have h₂ := lowerTotalExpr_lookupShift (.Let rest B)
      (lookupShift_cons x (lookupShift_swap hvf (s :: env)))
    have h₃ := lowerTotalExpr_lookupShift (.Let rest B)
      (lookupShift_cons x (lookupShift_cons f (lookupShift_swap hvs env)))
    rw [lowerTotalExpr_let_single, lowerTotalExpr_fix_lam (v :: env) f x _ s hs₂, h₃, h₂, h₁]
    dsimp only
    cases lowerTotalExpr env p <;> cases lowerTotalExpr (v :: x :: f :: s :: env) (.Let rest B) <;>
      rfl
  · obtain ⟨tp, tb⟩ := a
    cases hp' : lowerTotalExpr env p <;>
      cases hb : lowerTotalExpr (v :: x :: f :: s :: env) (.Let rest B) <;> simp [hp', hb] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ctxRefines_floatFix (total_of_pure hp hp') (lowerTotalExpr_closedAt hp')
      (by simpa using lowerTotalExpr_closedAt hb)

/-! ## Reordering a pure binding before an earlier one -/

omit sv in
theorem lowerTotalExpr_app_lam (env : List VarId) (x : VarId) (M e : Expr) (er : Bool) :
    lowerTotalExpr env (.App (.Lam x M) e) = lowerTotalExpr env (.Let [(x, e, er)] M) := by
  rw [lowerTotalExpr_app, lowerTotalExpr_lam, lowerTotalExpr_let_single]
  cases lowerTotalExpr env e <;> cases lowerTotalExpr (x :: env) M <;> rfl

theorem mirCtxRefines_letSwap {s f : VarId} {e p : Expr} {er₁ er₂ : Bool}
    {rest : List (VarId × Expr × Bool)} {B : Expr}
    (hp : isPure p = true) (hps : (freeVars p).contains s = false)
    (hef : (freeVars e).contains f = false) (hfs : (f == s) = false) :
    MIRCtxRefines (.Let ((s, e, er₁) :: (f, p, er₂) :: rest) B)
      (.Let ((f, p, er₂) :: (s, e, er₁) :: rest) B) := by
  have h₀ : MIRCtxRefines (.Let ((s, e, er₁) :: (f, p, er₂) :: rest) B)
      (.App (.Lam s (.Let ((f, p, er₂) :: rest) B)) e) := mirCtxRefines_of_lowerEq fun env => by
    rw [lowerTotalExpr_app_lam env s _ e er₁, lowerTotalExpr_let_flatten_body]; rfl
  have h₁ : MIRCtxRefines (.App (.Lam s (.Let ((f, p, er₂) :: rest) B)) e)
      (.App (.Let [(f, p, er₂)] (.Lam s (.Let rest B))) e) :=
    mirCtxRefines_app (mirCtxRefines_floatLam hp hps hfs) (mirCtxRefines_refl e)
  have h₂ := mirCtxRefines_hoist (.appFun e) trivial (v := f) hef p (.Lam s (.Let rest B)) er₂
  have h₃ : MIRCtxRefines (.Let [(f, p, er₂)] (.App (.Lam s (.Let rest B)) e))
      (.Let ((f, p, er₂) :: (s, e, er₁) :: rest) B) := mirCtxRefines_of_lowerEq fun env => by
    rw [lowerTotalExpr_let_single, lowerTotalExpr_app_lam _ s _ e er₁,
      lowerTotalExpr_let_flatten_body, lowerTotalExpr_let_cons]
    simp only [List.cons_append, List.nil_append]
    cases lowerTotalExpr env p <;> cases lowerTotalExpr (f :: env) (.Let ((s, e, er₁) :: rest) B) <;>
      rfl
  exact mirCtxRefines_trans h₀ (mirCtxRefines_trans h₁ (mirCtxRefines_trans h₂ h₃))

/-! ## Case alternative -/

theorem mirCtxRefines_floatCaseAlt {scrut : Expr} {pre post : List Expr} {v : VarId}
    {p A : Expr} {er : Bool} (hp : isPure p = true)
    (hs : (freeVars scrut).contains v = false)
    (hpre : ∀ a ∈ pre, (freeVars a).contains v = false)
    (hpost : ∀ a ∈ post, (freeVars a).contains v = false) :
    MIRCtxRefines (.Case scrut (pre ++ .Let [(v, p, er)] A :: post))
      (.Let [(v, p, er)] (.Case scrut (pre ++ A :: post))) := by
  refine mirCtxRefines_of_shapeCtx
    (fun env => (lowerTotalExpr env scrut).bind fun tS =>
      (lowerTotalExprList env pre).bind fun tpre =>
      (lowerTotalExpr env p).bind fun tP =>
      (lowerTotalExpr (v :: env) A).bind fun tA =>
      (lowerTotalExprList env post).map fun tpost => (tS, tpre, tP, tA, tpost))
    (fun _ a => .Case a.1 (a.2.1 ++ .Apply (.Lam 0 a.2.2.2.1) a.2.2.1 :: a.2.2.2.2))
    (fun _ a => .Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) a.1)
        (renameTermList (shiftRename 1) a.2.1 ++ a.2.2.2.1 ::
          renameTermList (shiftRename 1) a.2.2.2.2))) a.2.2.1)
    (fun env => ?_) (fun env => ?_) (fun env a h => ?_)
  · rw [lowerTotalExpr_case_of_list, lowerTotalExprList_append, lowerTotalExprList_cons,
      lowerTotalExpr_let_single]
    dsimp only
    cases lowerTotalExpr env scrut <;> cases lowerTotalExprList env pre <;>
      cases lowerTotalExpr env p <;> cases lowerTotalExpr (v :: env) A <;>
      cases lowerTotalExprList env post <;> rfl
  · rw [lowerTotalExpr_let_single, lowerTotalExpr_case_of_list, lowerTotalExprList_append,
      lowerTotalExprList_cons, lowerTotalExpr_prepend_unused env v scrut hs,
      lowerTotalExprList_prepend_unused env v pre hpre,
      lowerTotalExprList_prepend_unused env v post hpost]
    dsimp only
    cases lowerTotalExpr env scrut <;> cases lowerTotalExprList env pre <;>
      cases lowerTotalExpr env p <;> cases lowerTotalExpr (v :: env) A <;>
      cases lowerTotalExprList env post <;> rfl
  · obtain ⟨tS, tpre, tP, tA, tpost⟩ := a
    cases h₁ : lowerTotalExpr env scrut <;> cases h₂ : lowerTotalExprList env pre <;>
      cases h₃ : lowerTotalExpr env p <;> cases h₄ : lowerTotalExpr (v :: env) A <;>
      cases h₅ : lowerTotalExprList env post <;> simp [h₁, h₂, h₃, h₄, h₅] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ctxRefines_floatCase (total_of_pure hp h₃) (lowerTotalExpr_closedAt h₃)
      (lowerTotalExpr_closedAt h₁) (lowerTotalList_closedAtList env _ _ h₂)
      (lowerTotalList_closedAtList env _ _ h₅) (by simpa using lowerTotalExpr_closedAt h₄)

end Moist.Verified.FloatOut
