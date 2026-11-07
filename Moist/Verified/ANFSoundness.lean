import Moist.Verified.MIR.Primitives
import Moist.Verified.MIR.AlphaRenameSoundness

/-! # ANF normalization soundness

`anfNormalize_refines`: the pipeline alpha-rename → `anfNormalizeCore` →
`flattenAll` refines its input.

`anfNormalizeCore` names each non-atomic operand with `anfAtom`
(`mirCtxRefines_atomize`) and hoists the resulting `let` out of the operand's
evaluation frame (`mirCtxRefines_hoist_wrapLet`). A hoist needs the fresh name
to avoid the frame's other operands; this follows from the uid bound
`maxUidExpr e < s.next`, which `anfNormalizeCore_fresh` propagates. -/

namespace Moist.Verified.MIR

open Moist.MIR
open Moist.Verified.Equivalence (ListRel)

/-! ## `anfAtom` -/

theorem anfAtom_eq (e : Expr) (s : FreshState) :
    anfAtom e s = if e.isAtom then ((e, []), s)
      else ((.Var ⟨s.next, .gen, "anf"⟩, [(⟨s.next, .gen, "anf"⟩, e, false)]), ⟨s.next + 1⟩) := by
  unfold anfAtom; split <;> rfl

theorem anfAtom_isAtom (e : Expr) (s : FreshState) : (anfAtom e s).1.1.isAtom = true := by
  rw [anfAtom_eq]; split <;> simp_all [Expr.isAtom]

theorem anfAtom_refines (e : Expr) (s : FreshState) :
    MIRCtxRefines e (wrapLet (anfAtom e s).1.2 (anfAtom e s).1.1) := by
  rw [anfAtom_eq]; split
  · exact mirCtxRefines_refl _
  · exact mirCtxRefines_atomize e _

theorem anfAtom_fresh (e : Expr) (s : FreshState) (h : maxUidExpr e < s.next) :
    s.next ≤ (anfAtom e s).2.next ∧ maxUidExpr (anfAtom e s).1.1 < (anfAtom e s).2.next ∧
      maxUidExprBinds (anfAtom e s).1.2 < (anfAtom e s).2.next := by
  rw [anfAtom_eq]; split <;> simp [maxUidExpr, maxUidExprBinds] <;> omega

/-- The names `anfAtom` binds are fresh for anything below `s.next`. -/
theorem anfAtom_binds_fresh {e : Expr} {s : FreshState} {y : Expr}
    (hy : maxUidExpr y < s.next) : ∀ b ∈ (anfAtom e s).1.2, (freeVars y).contains b.1 = false := by
  rw [anfAtom_eq]; split
  · simp
  · simp only [List.mem_singleton]
    rintro _ rfl
    exact maxUidExpr_fresh y _ hy

theorem maxUidExpr_wrapLet_lt {bs : List (VarId × Expr × Bool)} {body : Expr} {n : Nat}
    (hbs : maxUidExprBinds bs < n) (hbody : maxUidExpr body < n) :
    maxUidExpr (wrapLet bs body) < n := by
  cases bs with
  | nil => exact hbody
  | cons _ _ => simp only [wrapLet, maxUidExpr]; omega

theorem maxUidExprList_lt_of_mem {es : List Expr} {n : Nat} (h : maxUidExprList es < n) :
    ∀ e ∈ es, maxUidExpr e < n := fun _ he =>
  Nat.lt_of_le_of_lt (maxUidExpr_le_maxUidExprList_of_mem he) h

/-- `Constr tag (pre ++ args)` with atomic `pre` refines its `anfAtomList` form. -/
theorem anfAtomList_spec (tag : Nat) :
    ∀ (args pre : List Expr) (s : FreshState), maxUidExprList args < s.next →
      maxUidExprList pre < s.next → (∀ a ∈ pre, a.isAtom = true) →
      s.next ≤ (anfAtomList args s).2.next ∧
      maxUidExprList (anfAtomList args s).1.1 < (anfAtomList args s).2.next ∧
      maxUidExprBinds (anfAtomList args s).1.2 < (anfAtomList args s).2.next ∧
      MIRCtxRefines (.Constr tag (pre ++ args))
        (wrapLet (anfAtomList args s).1.2 (.Constr tag (pre ++ (anfAtomList args s).1.1)))
  | [], pre, s, _, _, _ => by
    show s.next ≤ s.next ∧ maxUidExprList [] < s.next ∧ maxUidExprBinds [] < s.next ∧
      MIRCtxRefines (.Constr tag (pre ++ [])) (wrapLet [] (.Constr tag (pre ++ [])))
    exact ⟨Nat.le_refl _, by simp only [maxUidExprList]; omega, by simp only [maxUidExprBinds]; omega,
      mirCtxRefines_refl _⟩
  | a :: rest, pre, s, hargs, hpre, hpreA => by
    simp only [maxUidExprList] at hargs
    show s.next ≤ (anfAtomList rest (anfAtom a s).2).2.next ∧
      maxUidExprList ((anfAtom a s).1.1 :: (anfAtomList rest (anfAtom a s).2).1.1) <
        (anfAtomList rest (anfAtom a s).2).2.next ∧
      maxUidExprBinds ((anfAtom a s).1.2 ++ (anfAtomList rest (anfAtom a s).2).1.2) <
        (anfAtomList rest (anfAtom a s).2).2.next ∧
      MIRCtxRefines _ (wrapLet ((anfAtom a s).1.2 ++ (anfAtomList rest (anfAtom a s).2).1.2)
        (.Constr tag (pre ++ (anfAtom a s).1.1 :: (anfAtomList rest (anfAtom a s).2).1.1)))
    have href := anfAtom_refines a s
    have hfresh : ∀ b ∈ (anfAtom a s).1.2, ∀ y ∈ pre ++ rest, (freeVars y).contains b.1 = false :=
      fun b hb y hy => anfAtom_binds_fresh (by
        rcases List.mem_append.mp hy with hy | hy
        · exact maxUidExprList_lt_of_mem hpre y hy
        · exact maxUidExprList_lt_of_mem (by omega) y hy) b hb
    have hatom := anfAtom_isAtom a s
    obtain ⟨m₁, F₁, B₁⟩ := anfAtom_fresh a s (by omega)
    generalize anfAtom a s = r at href hfresh hatom m₁ F₁ B₁ ⊢
    have hpre' : maxUidExprList (pre ++ [r.1.1]) < r.2.next := by
      have := maxUidExprList_append pre [r.1.1]
      simp only [maxUidExprList] at this; omega
    obtain ⟨m₂, F₂, B₂, ih⟩ := anfAtomList_spec tag rest (pre ++ [r.1.1]) r.2 (by omega) hpre'
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hpreA x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hatom)
    simp only [List.append_assoc, List.singleton_append] at ih
    refine ⟨by omega, by simp only [maxUidExprList]; omega,
      by have := maxUidExprBinds_append r.1.2 (anfAtomList rest r.2).1.2; omega, ?_⟩
    exact mirCtxRefines_trans (mirCtxRefines_fill (.constr tag pre rest) href) <|
      mirCtxRefines_trans (mirCtxRefines_hoist_wrapLet (.constr tag pre rest) hpreA _ _ hfresh) <|
      mirCtxRefines_trans (mirCtxRefines_wrapLet_body ih) <|
      mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_wrapLet_append _ _ _ env).symm

/-! ## `anfNormalizeCore` unfolding -/

section
variable (s : FreshState)

private theorem anfNormalizeCore_force_eq (e : Expr) : anfNormalizeCore (.Force e) s =
    let r := anfNormalizeCore e s
    let a := anfAtom r.1 r.2
    (wrapLet a.1.2 (.Force a.1.1), a.2) := rfl

private theorem anfNormalizeCore_app_eq (f x : Expr) : anfNormalizeCore (.App f x) s =
    let r₁ := anfNormalizeCore f s
    let r₂ := anfNormalizeCore x r₁.2
    let a₁ := anfAtom r₁.1 r₂.2
    let a₂ := anfAtom r₂.1 a₁.2
    (wrapLet (a₁.1.2 ++ a₂.1.2) (.App a₁.1.1 a₂.1.1), a₂.2) := rfl

private theorem anfNormalizeCore_case_eq (scrut : Expr) (alts : List Expr) :
    anfNormalizeCore (.Case scrut alts) s =
    let r := anfNormalizeCore scrut s
    let a := anfAtom r.1 r.2
    let l := anfNormalizeListCore alts a.2
    (wrapLet a.1.2 (.Case a.1.1 l.1), l.2) := rfl

private theorem anfNormalizeCore_constr_eq (tag : Nat) (args : List Expr) :
    anfNormalizeCore (.Constr tag args) s =
    let l := anfNormalizeListCore args s
    let a := anfAtomList l.1 l.2
    (wrapLet a.1.2 (.Constr tag a.1.1), a.2) := rfl

private theorem anfNormalizeCore_let_eq (binds : List (VarId × Expr × Bool)) (body : Expr) :
    anfNormalizeCore (.Let binds body) s =
    let r := anfNormalizeBindsCore binds s
    let b := anfNormalizeCore body r.2
    (flattenLetBody r.1 b.1, b.2) := rfl

end

/-! ## Freshness -/

mutual

theorem anfNormalizeCore_fresh (e : Expr) (s : FreshState) (h : maxUidExpr e < s.next) :
    s.next ≤ (anfNormalizeCore e s).2.next ∧
      maxUidExpr (anfNormalizeCore e s).1 < (anfNormalizeCore e s).2.next := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => exact ⟨Nat.le_refl _, h⟩
  | .Lam x body =>
    simp only [maxUidExpr] at h
    obtain ⟨m, F⟩ := anfNormalizeCore_fresh body s (by omega)
    refine ⟨m, ?_⟩
    show maxUidExpr (.Lam x (anfNormalizeCore body s).1) < (anfNormalizeCore body s).2.next
    simp only [maxUidExpr]; omega
  | .Fix f body =>
    simp only [maxUidExpr] at h
    obtain ⟨m, F⟩ := anfNormalizeCore_fresh body s (by omega)
    refine ⟨m, ?_⟩
    show maxUidExpr (.Fix f (anfNormalizeCore body s).1) < (anfNormalizeCore body s).2.next
    simp only [maxUidExpr]; omega
  | .Delay e =>
    simp only [maxUidExpr] at h
    obtain ⟨m, F⟩ := anfNormalizeCore_fresh e s h
    refine ⟨m, ?_⟩
    show maxUidExpr (.Delay (anfNormalizeCore e s).1) < (anfNormalizeCore e s).2.next
    simp only [maxUidExpr]; omega
  | .Force e =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_force_eq]; dsimp only
    obtain ⟨m, F⟩ := anfNormalizeCore_fresh e s h
    generalize anfNormalizeCore e s = r at m F ⊢
    obtain ⟨m', F', B'⟩ := anfAtom_fresh r.1 r.2 F
    exact ⟨by omega, maxUidExpr_wrapLet_lt B' (by simp only [maxUidExpr]; omega)⟩
  | .App f x =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_app_eq]; dsimp only
    obtain ⟨m₁, F₁⟩ := anfNormalizeCore_fresh f s (by omega)
    generalize anfNormalizeCore f s = r₁ at m₁ F₁ ⊢
    obtain ⟨m₂, F₂⟩ := anfNormalizeCore_fresh x r₁.2 (by omega)
    generalize anfNormalizeCore x r₁.2 = r₂ at m₂ F₂ ⊢
    obtain ⟨m₃, F₃, B₃⟩ := anfAtom_fresh r₁.1 r₂.2 (by omega)
    generalize anfAtom r₁.1 r₂.2 = a₁ at m₃ F₃ B₃ ⊢
    obtain ⟨m₄, F₄, B₄⟩ := anfAtom_fresh r₂.1 a₁.2 (by omega)
    generalize anfAtom r₂.1 a₁.2 = a₂ at m₄ F₄ B₄ ⊢
    have := maxUidExprBinds_append a₁.1.2 a₂.1.2
    exact ⟨by omega, maxUidExpr_wrapLet_lt (by omega) (by simp only [maxUidExpr]; omega)⟩
  | .Case scrut alts =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_case_eq]; dsimp only
    obtain ⟨m₁, F₁⟩ := anfNormalizeCore_fresh scrut s (by omega)
    generalize anfNormalizeCore scrut s = r at m₁ F₁ ⊢
    obtain ⟨m₂, F₂, B₂⟩ := anfAtom_fresh r.1 r.2 F₁
    generalize anfAtom r.1 r.2 = a at m₂ F₂ B₂ ⊢
    obtain ⟨m₃, F₃⟩ := anfNormalizeList_fresh alts a.2 (by omega)
    exact ⟨by omega, maxUidExpr_wrapLet_lt (by omega) (by simp only [maxUidExpr]; omega)⟩
  | .Constr tag args =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_constr_eq]; dsimp only
    obtain ⟨m₁, F₁⟩ := anfNormalizeList_fresh args s h
    generalize anfNormalizeListCore args s = l at m₁ F₁ ⊢
    obtain ⟨m₂, F₂, B₂, -⟩ := anfAtomList_spec tag l.1 [] l.2 F₁ (by simp only [maxUidExprList]; omega)
      (fun _ h => absurd h List.not_mem_nil)
    exact ⟨by omega, maxUidExpr_wrapLet_lt B₂ (by simp only [maxUidExpr]; omega)⟩
  | .Let binds body =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_let_eq]; dsimp only
    obtain ⟨m₁, F₁⟩ := anfNormalizeBinds_fresh binds s (by omega)
    generalize anfNormalizeBindsCore binds s = r at m₁ F₁ ⊢
    obtain ⟨m₂, F₂⟩ := anfNormalizeCore_fresh body r.2 (by omega)
    generalize anfNormalizeCore body r.2 = b at m₂ F₂ ⊢
    refine ⟨by omega, ?_⟩
    cases hb : b.1 <;> simp only [flattenLetBody, maxUidExpr] <;> rw [hb] at F₂ <;>
      simp only [maxUidExpr] at F₂ <;>
      first
      | omega
      | (have := maxUidExprBinds_append r.1 ‹List (VarId × Expr × Bool)›; omega)
termination_by sizeOf e

theorem anfNormalizeList_fresh (es : List Expr) (s : FreshState) (h : maxUidExprList es < s.next) :
    s.next ≤ (anfNormalizeListCore es s).2.next ∧
      maxUidExprList (anfNormalizeListCore es s).1 < (anfNormalizeListCore es s).2.next := by
  match es with
  | [] => exact ⟨Nat.le_refl _, h⟩
  | e :: rest =>
    simp only [maxUidExprList] at h
    obtain ⟨m₁, F₁⟩ := anfNormalizeCore_fresh e s (by omega)
    obtain ⟨m₂, F₂⟩ := anfNormalizeList_fresh rest (anfNormalizeCore e s).2 (by omega)
    show _ ≤ (anfNormalizeListCore rest (anfNormalizeCore e s).2).2.next ∧
      maxUidExprList ((anfNormalizeCore e s).1 :: (anfNormalizeListCore rest _).1) <
        (anfNormalizeListCore rest (anfNormalizeCore e s).2).2.next
    simp only [maxUidExprList]; exact ⟨by omega, by omega⟩
termination_by sizeOf es

theorem anfNormalizeBinds_fresh (binds : List (VarId × Expr × Bool)) (s : FreshState)
    (h : maxUidExprBinds binds < s.next) :
    s.next ≤ (anfNormalizeBindsCore binds s).2.next ∧
      maxUidExprBinds (anfNormalizeBindsCore binds s).1 < (anfNormalizeBindsCore binds s).2.next := by
  match binds with
  | [] => exact ⟨Nat.le_refl _, h⟩
  | (v, e, er) :: rest =>
    simp only [maxUidExprBinds] at h
    obtain ⟨m₁, F₁⟩ := anfNormalizeCore_fresh e s (by omega)
    obtain ⟨m₂, F₂⟩ := anfNormalizeBinds_fresh rest (anfNormalizeCore e s).2 (by omega)
    show _ ≤ (anfNormalizeBindsCore rest (anfNormalizeCore e s).2).2.next ∧
      maxUidExprBinds ((v, (anfNormalizeCore e s).1, er) :: (anfNormalizeBindsCore rest _).1) <
        (anfNormalizeBindsCore rest (anfNormalizeCore e s).2).2.next
    simp only [maxUidExprBinds]; exact ⟨by omega, by omega⟩
termination_by sizeOf binds

end

/-! ## Refinement -/

mutual

theorem anfNormalizeCore_refines (e : Expr) (s : FreshState) (h : maxUidExpr e < s.next) :
    MIRCtxRefines e (anfNormalizeCore e s).1 := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => exact mirCtxRefines_refl _
  | .Lam x body =>
    simp only [maxUidExpr] at h
    exact mirCtxRefines_lam (anfNormalizeCore_refines body s (by omega))
  | .Delay e =>
    simp only [maxUidExpr] at h
    exact mirCtxRefines_delay (anfNormalizeCore_refines e s h)
  | .Fix f body =>
    simp only [maxUidExpr] at h
    by_cases hb : ∃ x inner, body = .Lam x inner
    · obtain ⟨x, inner, rfl⟩ := hb
      simp only [maxUidExpr] at h
      exact mirCtxRefines_fix_lam (anfNormalizeCore_refines inner s (by omega))
    · exact mirCtxRefines_fix_nonlam_lhs fun x inner heq => hb ⟨x, inner, heq⟩
  | .Force e =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_force_eq]; dsimp only
    have hr := anfNormalizeCore_refines e s h
    generalize anfNormalizeCore e s = r at hr ⊢
    exact mirCtxRefines_trans (mirCtxRefines_force hr) <|
      mirCtxRefines_trans (mirCtxRefines_fill .force (anfAtom_refines r.1 r.2)) <|
      mirCtxRefines_hoist_wrapLet .force trivial _ _ fun _ _ => trivial
  | .App f x =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_app_eq]; dsimp only
    have hf := anfNormalizeCore_refines f s (by omega)
    obtain ⟨m₁, F₁⟩ := anfNormalizeCore_fresh f s (by omega)
    generalize anfNormalizeCore f s = r₁ at hf m₁ F₁ ⊢
    have hx := anfNormalizeCore_refines x r₁.2 (by omega)
    obtain ⟨m₂, F₂⟩ := anfNormalizeCore_fresh x r₁.2 (by omega)
    generalize anfNormalizeCore x r₁.2 = r₂ at hx m₂ F₂ ⊢
    have ha₁ := anfAtom_refines r₁.1 r₂.2
    have hb₁ := anfAtom_binds_fresh (e := r₁.1) F₂
    have hatom := anfAtom_isAtom r₁.1 r₂.2
    obtain ⟨-, F₃, -⟩ := anfAtom_fresh r₁.1 r₂.2 (by omega)
    generalize anfAtom r₁.1 r₂.2 = a₁ at ha₁ hb₁ hatom F₃ ⊢
    have ha₂ := anfAtom_refines r₂.1 a₁.2
    have hb₂ := anfAtom_binds_fresh (e := r₂.1) F₃
    generalize anfAtom r₂.1 a₁.2 = a₂ at ha₂ hb₂ ⊢
    exact mirCtxRefines_trans (mirCtxRefines_app hf hx) <|
      mirCtxRefines_trans (mirCtxRefines_fill (.appFun r₂.1) ha₁) <|
      mirCtxRefines_trans (mirCtxRefines_hoist_wrapLet (.appFun r₂.1) trivial _ _ hb₁) <|
      mirCtxRefines_trans (mirCtxRefines_wrapLet_body <|
        mirCtxRefines_trans (mirCtxRefines_fill (.appArg a₁.1.1) ha₂) <|
          mirCtxRefines_hoist_wrapLet (.appArg a₁.1.1) hatom _ _ hb₂) <|
      mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_wrapLet_append _ _ _ env).symm
  | .Case scrut alts =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_case_eq]; dsimp only
    have hs := anfNormalizeCore_refines scrut s (by omega)
    obtain ⟨m₁, F₁⟩ := anfNormalizeCore_fresh scrut s (by omega)
    generalize anfNormalizeCore scrut s = r at hs m₁ F₁ ⊢
    have ha := anfAtom_refines r.1 r.2
    have hb : ∀ b ∈ (anfAtom r.1 r.2).1.2, ∀ alt ∈ alts, (freeVars alt).contains b.1 = false :=
      fun b hb alt halt =>
        anfAtom_binds_fresh (maxUidExprList_lt_of_mem (by omega : maxUidExprList alts < _) alt halt)
          b hb
    obtain ⟨m₂, -, -⟩ := anfAtom_fresh r.1 r.2 F₁
    generalize anfAtom r.1 r.2 = a at ha hb m₂ ⊢
    exact mirCtxRefines_trans (mirCtxRefines_fill (.case alts) hs) <|
      mirCtxRefines_trans (mirCtxRefines_fill (.case alts) ha) <|
      mirCtxRefines_trans (mirCtxRefines_hoist_wrapLet (.case alts) trivial _ _ hb) <|
      mirCtxRefines_wrapLet_body <|
        mirCtxRefines_case (mirCtxRefines_refl _) (anfNormalizeList_refines alts a.2 (by omega))
  | .Constr tag args =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_constr_eq]; dsimp only
    have hl := anfNormalizeList_refines args s h
    obtain ⟨-, F⟩ := anfNormalizeList_fresh args s h
    generalize anfNormalizeListCore args s = l at hl F ⊢
    exact mirCtxRefines_trans (mirCtxRefines_constr_of_listRel tag hl)
      (anfAtomList_spec tag l.1 [] l.2 F (by simp only [maxUidExprList]; omega)
        (fun _ h => absurd h List.not_mem_nil)).2.2.2
  | .Let binds body =>
    simp only [maxUidExpr] at h
    rw [anfNormalizeCore_let_eq]; dsimp only
    have hb := anfNormalizeBinds_refines binds s (by omega)
    obtain ⟨m, -⟩ := anfNormalizeBinds_fresh binds s (by omega)
    generalize anfNormalizeBindsCore binds s = r at hb m ⊢
    exact mirCtxRefines_trans (mirCtxRefines_let_binds_congr _ _ body hb) <|
      mirCtxRefines_trans (mirCtxRefines_let_body (anfNormalizeCore_refines body r.2 (by omega))) <|
      mirCtxRefines_flattenLetBody _ _
termination_by sizeOf e

theorem anfNormalizeList_refines (es : List Expr) (s : FreshState)
    (h : maxUidExprList es < s.next) :
    ListRel MIRCtxRefines es (anfNormalizeListCore es s).1 := by
  match es with
  | [] => exact trivial
  | e :: rest =>
    simp only [maxUidExprList] at h
    obtain ⟨m, -⟩ := anfNormalizeCore_fresh e s (by omega)
    exact ⟨anfNormalizeCore_refines e s (by omega),
      anfNormalizeList_refines rest (anfNormalizeCore e s).2 (by omega)⟩
termination_by sizeOf es

theorem anfNormalizeBinds_refines (binds : List (VarId × Expr × Bool)) (s : FreshState)
    (h : maxUidExprBinds binds < s.next) :
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
      binds (anfNormalizeBindsCore binds s).1 := by
  match binds with
  | [] => exact trivial
  | (v, e, er) :: rest =>
    simp only [maxUidExprBinds] at h
    obtain ⟨m, -⟩ := anfNormalizeCore_fresh e s (by omega)
    exact ⟨⟨rfl, rfl, anfNormalizeCore_refines e s (by omega)⟩,
      anfNormalizeBinds_refines rest (anfNormalizeCore e s).2 (by omega)⟩
termination_by sizeOf binds

end

/-! ## `flattenAll` -/

mutual

theorem flattenAll_refines (e : Expr) : MIRCtxRefines e (flattenAll e) := by
  match e with
  | .Var _ | .Lit _ | .Builtin _ | .Error => simp only [flattenAll]; exact mirCtxRefines_refl _
  | .Lam x body => simp only [flattenAll]; exact mirCtxRefines_lam (flattenAll_refines body)
  | .Fix f body =>
    simp only [flattenAll]
    by_cases hb : ∃ x inner, body = .Lam x inner
    · obtain ⟨x, inner, rfl⟩ := hb
      simp only [flattenAll]
      exact mirCtxRefines_fix_lam (flattenAll_refines inner)
    · exact mirCtxRefines_fix_nonlam_lhs fun x inner heq => hb ⟨x, inner, heq⟩
  | .App f x =>
    simp only [flattenAll]; exact mirCtxRefines_app (flattenAll_refines f) (flattenAll_refines x)
  | .Force e => simp only [flattenAll]; exact mirCtxRefines_force (flattenAll_refines e)
  | .Delay e => simp only [flattenAll]; exact mirCtxRefines_delay (flattenAll_refines e)
  | .Constr tag args =>
    simp only [flattenAll]; exact mirCtxRefines_constr_of_listRel tag (flattenAllList_refines args)
  | .Case scrut alts =>
    simp only [flattenAll]
    exact mirCtxRefines_case (flattenAll_refines scrut) (flattenAllList_refines alts)
  | .Let binds body =>
    simp only [flattenAll]
    have h := mirCtxRefines_trans (mirCtxRefines_let_binds_congr _ _ body (flattenAllBinds_refines binds))
      (mirCtxRefines_let_body (flattenAll_refines body))
    split
    · exact mirCtxRefines_trans h (mirCtxRefines_flattenLetBinds _ _ ‹_›)
    · exact h
termination_by sizeOf e

theorem flattenAllList_refines (es : List Expr) : ListRel MIRCtxRefines es (flattenAllList es) := by
  match es with
  | [] => simp only [flattenAllList]; exact trivial
  | e :: rest =>
    simp only [flattenAllList]; exact ⟨flattenAll_refines e, flattenAllList_refines rest⟩
termination_by sizeOf es

theorem flattenAllBinds_refines (binds : List (VarId × Expr × Bool)) :
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
      binds (flattenAllBinds binds) := by
  match binds with
  | [] => simp only [flattenAllBinds]; exact trivial
  | (v, e, er) :: rest =>
    simp only [flattenAllBinds]
    exact ⟨⟨rfl, rfl, flattenAll_refines e⟩, flattenAllBinds_refines rest⟩
termination_by sizeOf binds

end

/-! ## Pipeline -/

theorem anfNormalize_refines (e : Expr) (s : Moist.MIR.FreshState) :
    MIRCtxRefines e (Moist.MIR.anfNormalize e s).1 := by
  have core : ∀ e : Expr, MIRCtxRefines e
      (flattenAll (runFresh (anfNormalizeCore e) (maxUidExpr e + 1))) := fun e =>
    mirCtxRefines_trans (anfNormalizeCore_refines e _ (Nat.lt_succ_self _)) (flattenAll_refines _)
  show MIRCtxRefines e (anfNormalizeFlat e)
  unfold anfNormalizeFlat
  split
  · exact mirCtxRefines_trans
      (mirCtxRefines_of_lowerEq (alphaRenameTop_lowerTotalExpr_eq e _ (Nat.lt_succ_self _) ‹_›))
      (core _)
  · exact core e

end Moist.Verified.MIR
