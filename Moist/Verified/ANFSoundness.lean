import Moist.Verified.MIR.Primitives
import Moist.Verified.MIR.AlphaRenameSoundness

/-! # ANF normalization soundness top-level theorem -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet)
open Moist.Verified (closedAt closedAtList renameTerm shiftRename)
open Moist.Verified.Contextual (Context fill ObsRefines CtxEq CtxRefines ctxEq_refl ctxRefines_refl ctxRefines_trans ctxEq_lam ctxEq_app ctxRefines_lam ctxRefines_app)
open Moist.Verified.Equivalence (ListRel ObsEq ObsRefinesK steps Reaches obsRefinesK_mono obsRefinesK_zero_ret listRel_mono)
open Moist.Verified.Contextual.SoundnessRefines (EnvRefinesK BehRefinesK ValueRefinesK StackRefK valueRefinesK_mono evalBuiltin_compat_refines obsRefinesK_error stackRefK_mono listRel_valueRefinesK_mono applyArgFrames_stackRefK listRel_refl_vcon_refines)
open Moist.Verified.FundamentalRefines (ftlr renameRefines renameRefinesR renameRefinesR_shift1 is0preserving_id is0preserving_shiftRename RenameEnvRefR envRefinesK_to_renameEnvRefR_shift renameEnvRefR_mono)

/-! ## Section 11. anfAtom specification and the main mutual induction -/


/-- Direct compute lemmas for `anfAtom` — one for each branch. These bypass
    the monadic abstraction by just computing the function directly. -/
private theorem anfAtom_var (v : VarId) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfAtom (.Var v)) s = ((.Var v, []), s) := rfl

private theorem anfAtom_lit (lit : _) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfAtom (.Lit lit)) s = ((.Lit lit, []), s) := rfl

private theorem anfAtom_builtin (b : _) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfAtom (.Builtin b)) s = ((.Builtin b, []), s) := rfl

/-- Under the always-wrap `anfAtom`, the Let case is uniform with other
    non-atomic expressions: we always produce `(.Var v, [(v, .Let bs body, false)])`. -/
private theorem anfAtom_let (bs : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfAtom (Expr.Let bs body)) s =
      ((Expr.Var ⟨s.next, "anf"⟩,
        [(⟨s.next, "anf"⟩, Expr.Let bs body, false)]),
       { next := s.next + 1 }) := by
  show (if (Expr.Let bs body).isAtom then pure (Expr.Let bs body, [])
    else do
      let v ← Moist.MIR.freshVar "anf"
      pure (Expr.Var v, [(v, Expr.Let bs body, false)])) s = _
  have h1 : (Expr.Let bs body).isAtom = false := rfl
  simp only [h1]
  rfl

private theorem anfAtom_nonletnon (e : Expr)
    (he : e.isAtom = false)
    (hnotlet : ∀ bs body, e ≠ Expr.Let bs body)
    (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfAtom e) s = ((Expr.Var ⟨s.next, "anf"⟩,
        [(⟨s.next, "anf"⟩, e, false)]),
      { next := s.next + 1 }) := by
  cases e with
  | Var _ => simp [Expr.isAtom] at he
  | Lit _ => simp [Expr.isAtom] at he
  | Builtin _ => simp [Expr.isAtom] at he
  | Let bs body => exact absurd rfl (hnotlet bs body)
  | App f x =>
    show (do if (Expr.App f x).isAtom then pure (Expr.App f x, []) else
      (match (Expr.App f x) with
        | Expr.Let bs body =>
          if body.isAtom then pure (body, bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body, false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.App f x, false)]))) s = _
    have h1 : (Expr.App f x).isAtom = false := rfl
    simp only [h1]
    rfl
  | Force inner =>
    show (do if (Expr.Force inner).isAtom then pure (Expr.Force inner, []) else
      (match (Expr.Force inner) with
        | Expr.Let bs body =>
          if body.isAtom then pure (body, bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body, false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Force inner, false)]))) s = _
    have h1 : (Expr.Force inner).isAtom = false := rfl
    simp only [h1]
    rfl
  | Delay inner =>
    show (do if (Expr.Delay inner).isAtom then pure (Expr.Delay inner, []) else
      (match (Expr.Delay inner) with
        | Expr.Let bs body =>
          if body.isAtom then pure (body, bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body, false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Delay inner, false)]))) s = _
    have h1 : (Expr.Delay inner).isAtom = false := rfl
    simp only [h1]
    rfl
  | Lam x body =>
    show (do if (Expr.Lam x body).isAtom then pure (Expr.Lam x body, []) else
      (match (Expr.Lam x body) with
        | Expr.Let bs body' =>
          if body'.isAtom then pure (body', bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body', false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Lam x body, false)]))) s = _
    have h1 : (Expr.Lam x body).isAtom = false := rfl
    simp only [h1]
    rfl
  | Case scrut alts =>
    show (do if (Expr.Case scrut alts).isAtom then pure (Expr.Case scrut alts, []) else
      (match (Expr.Case scrut alts) with
        | Expr.Let bs body =>
          if body.isAtom then pure (body, bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body, false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Case scrut alts, false)]))) s = _
    have h1 : (Expr.Case scrut alts).isAtom = false := rfl
    simp only [h1]
    rfl
  | Constr tag args =>
    show (do if (Expr.Constr tag args).isAtom then pure (Expr.Constr tag args, []) else
      (match (Expr.Constr tag args) with
        | Expr.Let bs body =>
          if body.isAtom then pure (body, bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body, false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Constr tag args, false)]))) s = _
    have h1 : (Expr.Constr tag args).isAtom = false := rfl
    simp only [h1]
    rfl
  | Fix f body =>
    show (do if (Expr.Fix f body).isAtom then pure (Expr.Fix f body, []) else
      (match (Expr.Fix f body) with
        | Expr.Let bs body' =>
          if body'.isAtom then pure (body', bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body', false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Fix f body, false)]))) s = _
    have h1 : (Expr.Fix f body).isAtom = false := rfl
    simp only [h1]
    rfl
  | Error =>
    show (do if (Expr.Error).isAtom then pure (Expr.Error, []) else
      (match (Expr.Error) with
        | Expr.Let bs body =>
          if body.isAtom then pure (body, bs)
          else do
            let v ← Moist.MIR.freshVar "anf"
            pure (Expr.Var v, bs ++ [(v, body, false)])
        | _ => do
          let v ← Moist.MIR.freshVar "anf"
          pure (Expr.Var v, [(v, Expr.Error, false)]))) s = _
    have h1 : (Expr.Error).isAtom = false := rfl
    simp only [h1]
    rfl

/-- `anfAtom_spec`: for any initial state `s₁`, running `anfAtom e` yields a
    pair `(atom, binds)` such that `atom.isAtom = true` and
    `e ≈Ctxᴹ wrapLet binds atom` bidirectionally. -/
theorem anfAtom_spec (e : Expr) (s₁ : Moist.MIR.FreshState) :
    ((Moist.MIR.anfAtom e) s₁).1.1.isAtom = true ∧
    MIRCtxRefines e
      (Moist.MIR.wrapLet ((Moist.MIR.anfAtom e) s₁).1.2
        ((Moist.MIR.anfAtom e) s₁).1.1) ∧
    MIRCtxRefines
      (Moist.MIR.wrapLet ((Moist.MIR.anfAtom e) s₁).1.2
        ((Moist.MIR.anfAtom e) s₁).1.1) e := by
  match e with
  | .Var v =>
    rw [anfAtom_var v s₁]
    exact ⟨rfl, mirCtxRefines_refl _, mirCtxRefines_refl _⟩
  | .Lit lit =>
    rw [anfAtom_lit lit s₁]
    exact ⟨rfl, mirCtxRefines_refl _, mirCtxRefines_refl _⟩
  | .Builtin b =>
    rw [anfAtom_builtin b s₁]
    exact ⟨rfl, mirCtxRefines_refl _, mirCtxRefines_refl _⟩
  | .Let bs body =>
    rw [anfAtom_let bs body s₁]
    refine ⟨rfl, ?_, ?_⟩
    · show MIRCtxRefines (.Let bs body) (Moist.MIR.wrapLet _ _)
      rw [wrapLet_cons]; exact mirCtxRefines_atomize_fwd (.Let bs body) ⟨s₁.next, "anf"⟩
    · show MIRCtxRefines (Moist.MIR.wrapLet _ _) (.Let bs body)
      rw [wrapLet_cons]; exact mirCtxRefines_atomize_bwd (.Let bs body) ⟨s₁.next, "anf"⟩
  | .App _ _ | .Force _ | .Delay _ | .Lam _ _ | .Case _ _ | .Constr _ _
  | .Fix _ _ | .Error =>
    rw [anfAtom_nonletnon _ rfl (by intros; intro heq; cases heq) s₁]
    refine ⟨rfl, ?_, ?_⟩
    · rw [wrapLet_cons]; exact mirCtxRefines_atomize_fwd _ ⟨s₁.next, "anf"⟩
    · rw [wrapLet_cons]; exact mirCtxRefines_atomize_bwd _ ⟨s₁.next, "anf"⟩

/-! ## Section 12. Main ANF soundness theorem -/

/-! ### Section 12a. Compute lemmas for `anfNormalizeCore` on each constructor

Each lemma equates `(anfNormalizeCore e) s` to a concrete pair built from
sub-calls, useful for unfolding in the main induction. -/

private theorem anfNormalizeCore_lam_eq (x : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Lam x body)) s =
      ((.Lam x (Moist.MIR.anfNormalizeCore body s).1),
       (Moist.MIR.anfNormalizeCore body s).2) := by
  show (do let body' ← Moist.MIR.anfNormalizeCore body; pure (Expr.Lam x body')) s = _
  rfl

private theorem anfNormalizeCore_delay_eq (inner : Expr) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Delay inner)) s =
      ((.Delay (Moist.MIR.anfNormalizeCore inner s).1),
       (Moist.MIR.anfNormalizeCore inner s).2) := by
  show (do let e' ← Moist.MIR.anfNormalizeCore inner; pure (Expr.Delay e')) s = _
  rfl

private theorem anfNormalizeCore_fix_eq (f : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Fix f body)) s =
      ((.Fix f (Moist.MIR.anfNormalizeCore body s).1),
       (Moist.MIR.anfNormalizeCore body s).2) := by
  show (do let body' ← Moist.MIR.anfNormalizeCore body; pure (Expr.Fix f body')) s = _
  rfl

private theorem anfNormalizeCore_force_eq (inner : Expr) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Force inner)) s =
      (let (inner', s₁) := Moist.MIR.anfNormalizeCore inner s
       let ((atom, binds), s₂) := Moist.MIR.anfAtom inner' s₁
       (Moist.MIR.wrapLet binds (.Force atom), s₂)) := by
  show (do
      let e' ← Moist.MIR.anfNormalizeCore inner
      let (atom, binds) ← Moist.MIR.anfAtom e'
      pure (Moist.MIR.wrapLet binds (Expr.Force atom))) s = _
  rfl

private theorem anfNormalizeCore_app_eq (f x : Expr) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.App f x)) s =
      (let (f', s₁) := Moist.MIR.anfNormalizeCore f s
       let (x', s₂) := Moist.MIR.anfNormalizeCore x s₁
       let ((fAtom, fBinds), s₃) := Moist.MIR.anfAtom f' s₂
       let ((xAtom, xBinds), s₄) := Moist.MIR.anfAtom x' s₃
       (Moist.MIR.wrapLet (fBinds ++ xBinds) (.App fAtom xAtom), s₄)) := by
  show (do
      let f' ← Moist.MIR.anfNormalizeCore f
      let x' ← Moist.MIR.anfNormalizeCore x
      let (fAtom, fBinds) ← Moist.MIR.anfAtom f'
      let (xAtom, xBinds) ← Moist.MIR.anfAtom x'
      pure (Moist.MIR.wrapLet (fBinds ++ xBinds) (Expr.App fAtom xAtom))) s = _
  rfl

private theorem anfNormalizeCore_case_eq (scrut : Expr) (alts : List Expr)
    (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Case scrut alts)) s =
      (let (scrut', s₁) := Moist.MIR.anfNormalizeCore scrut s
       let ((atom, binds), s₂) := Moist.MIR.anfAtom scrut' s₁
       let (alts', s₃) := Moist.MIR.anfNormalizeListCore alts s₂
       (Moist.MIR.wrapLet binds (.Case atom alts'), s₃)) := by
  show (do
      let scrut' ← Moist.MIR.anfNormalizeCore scrut
      let (atom, binds) ← Moist.MIR.anfAtom scrut'
      let alts' ← Moist.MIR.anfNormalizeListCore alts
      pure (Moist.MIR.wrapLet binds (Expr.Case atom alts'))) s = _
  rfl

private theorem anfNormalizeCore_constr_eq (tag : Nat) (args : List Expr)
    (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Constr tag args)) s =
      (let (args', s₁) := Moist.MIR.anfNormalizeListCore args s
       let ((atoms, allBinds), s₂) := Moist.MIR.anfAtomList args' s₁
       (Moist.MIR.wrapLet allBinds (.Constr tag atoms), s₂)) := by
  show (do
      let args' ← Moist.MIR.anfNormalizeListCore args
      let (atoms, allBinds) ← Moist.MIR.anfAtomList args'
      pure (Moist.MIR.wrapLet allBinds (Expr.Constr tag atoms))) s = _
  rfl

private theorem anfNormalizeCore_let_eq (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeCore (.Let binds body)) s =
      (let (normalized, s₁) := Moist.MIR.anfNormalizeBindsCore binds s
       let (body', s₂) := Moist.MIR.anfNormalizeCore body s₁
       (Moist.MIR.flattenLetBody normalized body', s₂)) := by
  show (do
      let normalized ← Moist.MIR.anfNormalizeBindsCore binds
      let body' ← Moist.MIR.anfNormalizeCore body
      pure (Moist.MIR.flattenLetBody normalized body')) s = _
  rfl

private theorem anfNormalizeList_nil_eq (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeListCore []) s = (([] : List Expr), s) := rfl

private theorem anfNormalizeList_cons_eq (e : Expr) (rest : List Expr)
    (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeListCore (e :: rest)) s =
      (let (e', s₁) := Moist.MIR.anfNormalizeCore e s
       let (rest', s₂) := Moist.MIR.anfNormalizeListCore rest s₁
       (e' :: rest', s₂)) := by
  show (do
      let e' ← Moist.MIR.anfNormalizeCore e
      let rest' ← Moist.MIR.anfNormalizeListCore rest
      pure (e' :: rest')) s = _
  rfl

private theorem anfNormalizeBinds_nil_eq (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeBindsCore []) s = (([] : List (VarId × Expr × Bool)), s) := rfl

private theorem anfNormalizeBinds_cons_eq (v : VarId) (e : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState) :
    (Moist.MIR.anfNormalizeBindsCore ((v, e, er) :: rest)) s =
      (let (e', s₁) := Moist.MIR.anfNormalizeCore e s
       let (rest', s₂) := Moist.MIR.anfNormalizeBindsCore rest s₁
       ((v, e', er) :: rest', s₂)) := by
  show (do
      let e' ← Moist.MIR.anfNormalizeCore e
      let rest' ← Moist.MIR.anfNormalizeBindsCore rest
      pure ((v, e', er) :: rest')) s = _
  rfl

/-- Every variable introduced by `anfAtom e s` has uid exactly `s.next`. -/
private theorem anfAtom_binds_uid (e : Expr) (s : Moist.MIR.FreshState) :
    ∀ b ∈ ((Moist.MIR.anfAtom e) s).1.2, b.1.uid = s.next := by
  intro b hb
  by_cases h : e.isAtom = true
  · -- atomic case: binds = [], so membership is impossible
    have hres : (Moist.MIR.anfAtom e) s = ((e, []), s) := by
      show (if e.isAtom = true then (pure (e, []) : Moist.MIR.FreshM _)
        else do let v ← Moist.MIR.freshVar "anf"; pure (Expr.Var v, [(v, e, false)])) s = _
      rw [if_pos h]; rfl
    rw [hres] at hb
    exact absurd hb (by simp)
  · have hf : e.isAtom = false := by
      cases h' : e.isAtom with
      | true => exact absurd h' h
      | false => rfl
    have hres : (Moist.MIR.anfAtom e) s =
        ((Expr.Var ⟨s.next, "anf"⟩, [(⟨s.next, "anf"⟩, e, false)]),
         { next := s.next + 1 }) := by
      show (if e.isAtom = true then (pure (e, []) : Moist.MIR.FreshM _)
        else do let v ← Moist.MIR.freshVar "anf"; pure (Expr.Var v, [(v, e, false)])) s = _
      rw [if_neg (by simp [hf])]
      rfl
    rw [hres] at hb
    simp at hb
    rw [hb]

/-- If `anfAtom` produced a non-empty binding list, then the state advanced by 1. -/
private theorem anfAtom_state_succ_of_binds_nonempty (e : Expr) (s : Moist.MIR.FreshState)
    (h : ((Moist.MIR.anfAtom e) s).1.2 ≠ []) :
    ((Moist.MIR.anfAtom e) s).2.next = s.next + 1 := by
  by_cases hat : e.isAtom = true
  · exfalso
    have : (Moist.MIR.anfAtom e) s = ((e, []), s) := by
      show (if e.isAtom = true then (pure (e, []) : Moist.MIR.FreshM _)
        else do let v ← Moist.MIR.freshVar "anf"; pure (Expr.Var v, [(v, e, false)])) s = _
      rw [if_pos hat]; rfl
    apply h; show ((Moist.MIR.anfAtom e) s).1.2 = []; rw [this]
  · have hf : e.isAtom = false := by
      cases h' : e.isAtom with | true => exact absurd h' hat | false => rfl
    have : (Moist.MIR.anfAtom e) s =
        ((Expr.Var ⟨s.next, "anf"⟩, [(⟨s.next, "anf"⟩, e, false)]),
         { next := s.next + 1 }) := by
      show (if e.isAtom = true then (pure (e, []) : Moist.MIR.FreshM _)
        else do let v ← Moist.MIR.freshVar "anf"; pure (Expr.Var v, [(v, e, false)])) s = _
      rw [if_neg (by simp [hf])]; rfl
    show ((Moist.MIR.anfAtom e) s).2.next = _; rw [this]

/-- If `v` is not free in `e` and `v.uid ≠ s.next`, then `v` is not free in the
    output `wrapLet binds atom` of `anfAtom e s`. This is the key lemma for
    threading freshness through sibling subterms in the main induction. -/
private theorem anfAtom_wrapLet_freshIn (e : Expr) (s : Moist.MIR.FreshState) (v : VarId)
    (hv_e : (Moist.MIR.freeVars e).contains v = false)
    (hv_uid : v.uid ≠ s.next) :
    (Moist.MIR.freeVars (Moist.MIR.wrapLet ((Moist.MIR.anfAtom e) s).1.2
      ((Moist.MIR.anfAtom e) s).1.1)).contains v = false := by
  by_cases h : e.isAtom = true
  · have hres : (Moist.MIR.anfAtom e) s = ((e, []), s) := by
      show (if e.isAtom = true then (pure (e, []) : Moist.MIR.FreshM _)
        else do let v ← Moist.MIR.freshVar "anf"; pure (Expr.Var v, [(v, e, false)])) s = _
      rw [if_pos h]; rfl
    rw [hres]
    show (Moist.MIR.freeVars (Moist.MIR.wrapLet [] e)).contains v = false
    exact hv_e
  · have hf : e.isAtom = false := by
      cases h' : e.isAtom with
      | true => exact absurd h' h
      | false => rfl
    have hres : (Moist.MIR.anfAtom e) s =
        ((Expr.Var ⟨s.next, "anf"⟩, [(⟨s.next, "anf"⟩, e, false)]),
         { next := s.next + 1 }) := by
      show (if e.isAtom = true then (pure (e, []) : Moist.MIR.FreshM _)
        else do let v ← Moist.MIR.freshVar "anf"; pure (Expr.Var v, [(v, e, false)])) s = _
      rw [if_neg (by simp [hf])]; rfl
    rw [hres]
    rw [wrapLet_cons]
    -- Goal: (freeVars (.Let [(⟨s.next, "anf"⟩, e, false)] (.Var ⟨s.next, "anf"⟩))).contains v = false
    show (Moist.MIR.freeVars (Expr.Let [(⟨s.next, "anf"⟩, e, false)]
      (Expr.Var ⟨s.next, "anf"⟩))).contains v = false
    -- freeVars (.Let bs body) = freeVarsLet bs body
    -- freeVarsLet [(y,rhs,er) :: rest] body = (freeVars rhs).union ((freeVarsLet rest body).erase y)
    -- freeVarsLet [] body = freeVars body
    simp only [Moist.MIR.freeVars, Moist.MIR.freeVarsLet]
    apply Moist.MIR.VarSet.union_not_contains_fwd
    · exact hv_e
    · apply Moist.MIR.VarSet.erase_not_contains_fwd
      rw [Moist.MIR.VarSet.singleton_contains']
      show ((⟨s.next, "anf"⟩ : VarId) == v) = false
      have : ((⟨s.next, "anf"⟩ : VarId) == v) = decide ((⟨s.next, "anf"⟩ : VarId).uid = v.uid) := rfl
      rw [this]
      exact decide_eq_false (fun heq => hv_uid heq.symm)

/-- `anfAtom` binds' uids exceed any sibling expression with `maxUidExpr y < s.next`. -/
private theorem anfAtom_binds_fresh_in (e : Expr) (s : Moist.MIR.FreshState)
    (y : Expr) (hy : Moist.MIR.maxUidExpr y < s.next) :
    ∀ b ∈ ((Moist.MIR.anfAtom e) s).1.2, (Moist.MIR.freeVars y).contains b.1 = false := by
  intro b hb
  have huid : b.1.uid = s.next := anfAtom_binds_uid e s b hb
  have h_gt : b.1.uid > Moist.MIR.maxUidExpr y := by omega
  exact Moist.MIR.maxUidExpr_fresh y b.1 h_gt

/-! ### Section 12b. Strong `anfAtom` spec with state tracking

Extends `anfAtom_spec` with (i) monotonicity `s.next ≤ s'.next ≤ s.next + 1`,
(ii) `FreshGt` preservation: if all vars in `e` have uid `< s.next`, then all
vars in the output atom and binds have uid `< s'.next`. -/

/-- Monotonicity: `anfAtom` either keeps state unchanged or advances by 1. -/
private theorem anfAtom_mono (e : Expr) (s : Moist.MIR.FreshState) :
    s.next ≤ ((Moist.MIR.anfAtom e) s).2.next ∧
    ((Moist.MIR.anfAtom e) s).2.next ≤ s.next + 1 := by
  match e with
  | .Var v => rw [anfAtom_var v s]; exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | .Lit lit => rw [anfAtom_lit lit s]; exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | .Builtin b => rw [anfAtom_builtin b s]; exact ⟨Nat.le_refl _, Nat.le_succ _⟩
  | .Let bs body => rw [anfAtom_let bs body s]; exact ⟨by simp, by simp⟩
  | .App _ _ | .Force _ | .Delay _ | .Lam _ _ | .Case _ _ | .Constr _ _
  | .Fix _ _ | .Error =>
    rw [anfAtom_nonletnon _ rfl (by intros; intro heq; cases heq) s]
    exact ⟨by simp, by simp⟩

/-- Stronger `anfAtom` freshness: the output has maxUid strictly less than
    `s'.next` (where `s'` is the output state), assuming input has maxUid
    less than `s.next`. This is the invariant we use in the main induction. -/
private theorem anfAtom_fresh (e : Expr) (s : Moist.MIR.FreshState)
    (h : Moist.MIR.maxUidExpr e < s.next) :
    Moist.MIR.maxUidExpr (Moist.MIR.wrapLet ((Moist.MIR.anfAtom e) s).1.2
      ((Moist.MIR.anfAtom e) s).1.1) < ((Moist.MIR.anfAtom e) s).2.next := by
  match e with
  | .Var v =>
    rw [anfAtom_var v s]
    show Moist.MIR.maxUidExpr (.Var v) < s.next; exact h
  | .Lit lit => rw [anfAtom_lit lit s]; show Moist.MIR.maxUidExpr (.Lit _) < s.next; exact h
  | .Builtin b => rw [anfAtom_builtin b s]; show Moist.MIR.maxUidExpr (.Builtin _) < s.next; exact h
  | .Let bs body =>
    rw [anfAtom_let bs body s, wrapLet_cons]
    show Moist.MIR.maxUidExpr
      (.Let [(⟨s.next, "anf"⟩, .Let bs body, false)] (.Var ⟨s.next, "anf"⟩)) < s.next + 1
    have hlet : Moist.MIR.maxUidExpr (.Let bs body) < s.next := h
    simp only [Moist.MIR.maxUidExpr, Moist.MIR.maxUidExprBinds] at hlet ⊢
    omega
  | .App _ _ | .Force _ | .Delay _ | .Lam _ _ | .Case _ _ | .Constr _ _
  | .Fix _ _ | .Error =>
    rw [anfAtom_nonletnon _ rfl (by intros; intro heq; cases heq) s, wrapLet_cons]
    simp only [Moist.MIR.maxUidExpr, Moist.MIR.maxUidExprBinds] at h ⊢
    omega

/-- `anfAtom` maxUid bound: the output expression (wrapLet binds atom) has
    maxUid no greater than `max (maxUidExpr e) s.next`. -/
private theorem anfAtom_maxUid' (e : Expr) (s : Moist.MIR.FreshState) :
    Moist.MIR.maxUidExpr (Moist.MIR.wrapLet ((Moist.MIR.anfAtom e) s).1.2
      ((Moist.MIR.anfAtom e) s).1.1) ≤ max (Moist.MIR.maxUidExpr e) s.next := by
  match e with
  | .Var v => rw [anfAtom_var v s]; show Moist.MIR.maxUidExpr (.Var v) ≤ _
              simp only [Moist.MIR.maxUidExpr]; omega
  | .Lit lit => rw [anfAtom_lit lit s]; show Moist.MIR.maxUidExpr (.Lit _) ≤ _
                simp only [Moist.MIR.maxUidExpr]; omega
  | .Builtin b => rw [anfAtom_builtin b s]; show Moist.MIR.maxUidExpr (.Builtin _) ≤ _
                  simp only [Moist.MIR.maxUidExpr]; omega
  | .Let bs body =>
    rw [anfAtom_let bs body s, wrapLet_cons]
    show Moist.MIR.maxUidExpr
      (.Let [(⟨s.next, "anf"⟩, .Let bs body, false)] (.Var ⟨s.next, "anf"⟩)) ≤ _
    simp only [Moist.MIR.maxUidExpr, Moist.MIR.maxUidExprBinds]; omega
  | .App _ _ | .Force _ | .Delay _ | .Lam _ _ | .Case _ _ | .Constr _ _
  | .Fix _ _ | .Error =>
    rw [anfAtom_nonletnon _ rfl (by intros; intro heq; cases heq) s, wrapLet_cons]
    simp only [Moist.MIR.maxUidExpr, Moist.MIR.maxUidExprBinds]; omega


/-! ### Section 12e-bis-pre. `anfNormalizeCore` output shape preservation

Shows that `anfNormalizeCore` produces a non-`.Lam` output when given a non-`.Lam`
input. Needed for the `.Fix` case of the main induction where both sides'
lowerings should fail to be `some`. -/

private theorem anfNormalizeCore_nonlam_preserves (body : Expr)
    (h : ∀ x inner, body ≠ .Lam x inner) (s : Moist.MIR.FreshState) :
    ∀ x inner, (Moist.MIR.anfNormalizeCore body s).1 ≠ .Lam x inner := by
  intros x' inner'
  -- Helper: any wrapLet of a non-Lam non-Let body is not a Lam
  have wrap_ne : ∀ (binds : List (VarId × Expr × Bool)) (b : Expr),
      (∀ x i, b ≠ .Lam x i) → Moist.MIR.wrapLet binds b ≠ .Lam x' inner' := by
    intro binds b hb
    cases binds with
    | nil => exact hb x' inner'
    | cons _ _ => rw [wrapLet_cons]; intro h'; cases h'
  match body with
  | .Var v =>
    rw [show (Moist.MIR.anfNormalizeCore (.Var v)) s = (.Var v, s) from rfl]; intro heq; cases heq
  | .Lit lit =>
    rw [show (Moist.MIR.anfNormalizeCore (.Lit lit)) s = (.Lit lit, s) from rfl]; intro heq; cases heq
  | .Builtin b =>
    rw [show (Moist.MIR.anfNormalizeCore (.Builtin b)) s = (.Builtin b, s) from rfl]; intro heq; cases heq
  | .Error =>
    rw [show (Moist.MIR.anfNormalizeCore .Error) s = (.Error, s) from rfl]; intro heq; cases heq
  | .Lam x inner => exact absurd rfl (h x inner)
  | .Fix f body' => rw [anfNormalizeCore_fix_eq f body' s]; intro heq; cases heq
  | .Delay inner => rw [anfNormalizeCore_delay_eq inner s]; intro heq; cases heq
  | .Force inner =>
    rw [anfNormalizeCore_force_eq inner s]
    exact wrap_ne _ _ (by intros; intro h'; cases h')
  | .App fn arg =>
    rw [anfNormalizeCore_app_eq fn arg s]
    exact wrap_ne _ _ (by intros; intro h'; cases h')
  | .Case scrut alts =>
    rw [anfNormalizeCore_case_eq scrut alts s]
    exact wrap_ne _ _ (by intros; intro h'; cases h')
  | .Constr tag args =>
    rw [anfNormalizeCore_constr_eq tag args s]
    exact wrap_ne _ _ (by intros; intro h'; cases h')
  | .Let binds body' =>
    rw [anfNormalizeCore_let_eq binds body' s]
    intro heq
    have key : ∀ (normBinds : List (VarId × Expr × Bool)) (b : Expr),
        Moist.MIR.flattenLetBody normBinds b ≠ Expr.Lam x' inner' := by
      intros normBinds b
      cases b <;> (simp only [Moist.MIR.flattenLetBody]; intro h'; cases h')
    exact key _ _ heq

/-! ### Section 12f. Main mutual induction

The theorem carries four invariants:
1. Forward refinement: `e ≈ (anfNormalizeCore e s).1`
2. Backward refinement: `(anfNormalizeCore e s).1 ≈ e`
3. State monotonicity: `s.next ≤ (anfNormalizeCore e s).2.next`
4. Output freshness: `FreshGt (anfNormalizeCore e s).2 (anfNormalizeCore e s).1`
   (i.e., `maxUidExpr (output) < (output state).next`)

Termination is by `sizeOf e`. -/


private theorem maxUidExpr_le_wrapLet (binds : List (VarId × Expr × Bool)) (atom : Expr) :
    Moist.MIR.maxUidExpr atom ≤ Moist.MIR.maxUidExpr (Moist.MIR.wrapLet binds atom) := by
  cases binds with
  | nil => exact Nat.le_refl _
  | cons b rest => rw [wrapLet_cons]; simp only [Moist.MIR.maxUidExpr]; omega

private theorem maxUidExprBinds_le_wrapLet
    (binds : List (VarId × Expr × Bool)) (atom : Expr) :
    Moist.MIR.maxUidExprBinds binds ≤ Moist.MIR.maxUidExpr (Moist.MIR.wrapLet binds atom) := by
  cases binds with
  | nil => simp [Moist.MIR.maxUidExprBinds]
  | cons b rest => rw [wrapLet_cons]; simp [Moist.MIR.maxUidExpr]; omega

/-- `flattenLetBody` is forward-refined by `.Let binds body`. -/
private theorem mirCtxRefines_flattenLetBody_fwd
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let binds body) (Moist.MIR.flattenLetBody binds body) := by
  match body with
  | .Let ib ibody => exact mirCtxRefines_let_flatten_body_fwd binds ib ibody
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _
  | .Force _ | .Delay _ | .Constr _ _ | .Case _ _ => exact mirCtxRefines_refl _

private theorem mirCtxRefines_flattenLetBody_bwd
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (Moist.MIR.flattenLetBody binds body) (.Let binds body) := by
  match body with
  | .Let ib ibody => exact mirCtxRefines_let_flatten_body_bwd binds ib ibody
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _
  | .Force _ | .Delay _ | .Constr _ _ | .Case _ _ => exact mirCtxRefines_refl _

/-- `maxUidExpr` of `flattenLetBody binds body` is bounded by the `.Let binds body` form. -/
private theorem maxUidExpr_flattenLetBody_le
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    Moist.MIR.maxUidExpr (Moist.MIR.flattenLetBody binds body) ≤
      max (Moist.MIR.maxUidExprBinds binds) (Moist.MIR.maxUidExpr body) := by
  match body with
  | .Let ib ibody =>
    simp only [Moist.MIR.flattenLetBody, Moist.MIR.maxUidExpr]
    have := Moist.MIR.maxUidExprBinds_append binds ib; omega
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _
  | .Force _ | .Delay _ | .Constr _ _ | .Case _ _ =>
    simp only [Moist.MIR.flattenLetBody, Moist.MIR.maxUidExpr]
    omega

/-- `flattenLetBody` preserves the freshness bound. -/
private theorem freshGt_flattenLetBody
    (binds : List (VarId × Expr × Bool)) (body : Expr) (s : Moist.MIR.FreshState)
    (hbinds : Moist.MIR.maxUidExprBinds binds < s.next)
    (hbody : Moist.MIR.maxUidExpr body < s.next) :
    Moist.MIR.maxUidExpr (Moist.MIR.flattenLetBody binds body) < s.next := by
  have := maxUidExpr_flattenLetBody_le binds body
  omega

/-- Freshness for `wrapLet binds body`: bounded by the max of binds-uids and body-uid. -/
private theorem freshGt_wrapLet
    (binds : List (VarId × Expr × Bool)) (body : Expr) (s : Moist.MIR.FreshState)
    (hbinds : Moist.MIR.maxUidExprBinds binds < s.next)
    (hbody : Moist.MIR.maxUidExpr body < s.next) :
    Moist.MIR.maxUidExpr (Moist.MIR.wrapLet binds body) < s.next := by
  cases binds with
  | nil => exact hbody
  | cons b rest =>
    rw [wrapLet_cons]
    simp only [Moist.MIR.maxUidExpr]
    omega

/-- Freshness for `wrapLet binds (.Case atom alts)`. -/
private theorem freshGt_wrapLet_case
    (binds : List (VarId × Expr × Bool)) (atom : Expr) (alts : List Expr)
    (s : Moist.MIR.FreshState)
    (hatom : Moist.MIR.maxUidExpr atom < s.next)
    (halts : Moist.MIR.maxUidExprList alts < s.next)
    (hbinds : Moist.MIR.maxUidExprBinds binds < s.next) :
    Moist.MIR.maxUidExpr (Moist.MIR.wrapLet binds (.Case atom alts)) < s.next := by
  cases binds with
  | nil => show Moist.MIR.maxUidExpr (.Case atom alts) < _
           simp only [Moist.MIR.maxUidExpr]; omega
  | cons b rest => rw [wrapLet_cons]; simp only [Moist.MIR.maxUidExpr]; omega

/-- Freshness for `wrapLet binds (.Constr tag atoms)`. -/
private theorem freshGt_wrapLet_constr
    (binds : List (VarId × Expr × Bool)) (tag : Nat) (atoms : List Expr)
    (s : Moist.MIR.FreshState)
    (hatoms : Moist.MIR.maxUidExprList atoms < s.next)
    (hbinds : Moist.MIR.maxUidExprBinds binds < s.next) :
    Moist.MIR.maxUidExpr (Moist.MIR.wrapLet binds (.Constr tag atoms)) < s.next := by
  cases binds with
  | nil => show Moist.MIR.maxUidExpr (.Constr tag atoms) < _
           simp only [Moist.MIR.maxUidExpr]; exact hatoms
  | cons b rest => rw [wrapLet_cons]; simp only [Moist.MIR.maxUidExpr]; omega

/-- Combined specification for `anfAtomList`: produces atoms (all `isAtom`) and bindings
    such that `.Constr tag (pre ++ args)` is bidirectionally refined by
    `wrapLet binds (.Constr tag (pre ++ atoms))` for any atomic prefix `pre`,
    plus state monotonicity and output freshness. -/
private theorem anfAtomList_spec
    (args : List Expr) (s : Moist.MIR.FreshState) (tag : Nat) (pre : List Expr)
    (hargs : Moist.MIR.maxUidExprList args < s.next)
    (hpre_uid : Moist.MIR.maxUidExprList pre < s.next)
    (hpre_atom : ∀ a ∈ pre, a.isAtom = true) :
    s.next ≤ (Moist.MIR.anfAtomList args s).2.next ∧
    Moist.MIR.maxUidExprList (Moist.MIR.anfAtomList args s).1.1 <
      (Moist.MIR.anfAtomList args s).2.next ∧
    Moist.MIR.maxUidExprBinds (Moist.MIR.anfAtomList args s).1.2 <
      (Moist.MIR.anfAtomList args s).2.next ∧
    (∀ a ∈ (Moist.MIR.anfAtomList args s).1.1, a.isAtom = true) ∧
    MIRCtxRefines (.Constr tag (pre ++ args))
      (Moist.MIR.wrapLet (Moist.MIR.anfAtomList args s).1.2
        (.Constr tag (pre ++ (Moist.MIR.anfAtomList args s).1.1))) ∧
    MIRCtxRefines
      (Moist.MIR.wrapLet (Moist.MIR.anfAtomList args s).1.2
        (.Constr tag (pre ++ (Moist.MIR.anfAtomList args s).1.1)))
      (.Constr tag (pre ++ args)) := by
  induction args generalizing s pre with
  | nil =>
    show s.next ≤ s.next ∧ _
    refine ⟨Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
    · show Moist.MIR.maxUidExprList ([] : List Expr) < s.next
      simp [Moist.MIR.maxUidExprList]; omega
    · show Moist.MIR.maxUidExprBinds ([] : List (VarId × Expr × Bool)) < s.next
      simp [Moist.MIR.maxUidExprBinds]; omega
    · intro a ha
      have ha' : a ∈ ([] : List Expr) := ha
      exact absurd ha' (by simp)
    · exact mirCtxRefines_refl _
    · exact mirCtxRefines_refl _
  | cons a rest ih =>
    -- Extract per-element facts
    have ha_uid : Moist.MIR.maxUidExpr a < s.next := by
      simp only [Moist.MIR.maxUidExprList] at hargs; omega
    have hrest_uid : Moist.MIR.maxUidExprList rest < s.next := by
      simp only [Moist.MIR.maxUidExprList] at hargs; omega
    obtain ⟨hatom_flag, hatom_fwd, hatom_bwd⟩ := anfAtom_spec a s
    have hmono := (anfAtom_mono a s).1
    have hatom_fresh := anfAtom_fresh a s ha_uid
    have hα_uid : Moist.MIR.maxUidExpr (Moist.MIR.anfAtom a s).1.1 <
        (Moist.MIR.anfAtom a s).2.next := by
      have := maxUidExpr_le_wrapLet (Moist.MIR.anfAtom a s).1.2 (Moist.MIR.anfAtom a s).1.1
      omega
    have hβ_uid : Moist.MIR.maxUidExprBinds (Moist.MIR.anfAtom a s).1.2 <
        (Moist.MIR.anfAtom a s).2.next := by
      have := maxUidExprBinds_le_wrapLet (Moist.MIR.anfAtom a s).1.2 (Moist.MIR.anfAtom a s).1.1
      omega
    -- IH at s₁ with pre' = pre ++ [α]
    have hrest_uid_s₁ : Moist.MIR.maxUidExprList rest <
        (Moist.MIR.anfAtom a s).2.next := by omega
    have hpre'_uid : Moist.MIR.maxUidExprList (pre ++ [(Moist.MIR.anfAtom a s).1.1]) <
        (Moist.MIR.anfAtom a s).2.next := by
      have := Moist.MIR.maxUidExprList_append pre [(Moist.MIR.anfAtom a s).1.1]
      have hsing : Moist.MIR.maxUidExprList [(Moist.MIR.anfAtom a s).1.1] =
          Moist.MIR.maxUidExpr (Moist.MIR.anfAtom a s).1.1 := by
        simp [Moist.MIR.maxUidExprList]
      omega
    have hpre'_atom : ∀ x ∈ pre ++ [(Moist.MIR.anfAtom a s).1.1], x.isAtom = true := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpre_atom x hx
      · rcases List.mem_singleton.mp hx with rfl
        exact hatom_flag
    obtain ⟨ih_mono, ih_atoms_uid, ih_binds_uid, ih_atoms_flag, ih_fwd, ih_bwd⟩ :=
      ih (Moist.MIR.anfAtom a s).2 (pre ++ [(Moist.MIR.anfAtom a s).1.1])
        hrest_uid_s₁ hpre'_uid hpre'_atom
    -- Freshness of pre/rest w.r.t. β
    have hpre_β_fresh : ∀ x ∈ pre, ∀ b ∈ (Moist.MIR.anfAtom a s).1.2,
        (Moist.MIR.freeVars x).contains b.1 = false := fun x hx b hb =>
      anfAtom_binds_fresh_in a s x
        (by have := Moist.MIR.maxUidExpr_le_maxUidExprList_of_mem hx; omega) b hb
    have hrest_β_fresh : ∀ x ∈ rest, ∀ b ∈ (Moist.MIR.anfAtom a s).1.2,
        (Moist.MIR.freeVars x).contains b.1 = false := fun x hx b hb =>
      anfAtom_binds_fresh_in a s x
        (by have := Moist.MIR.maxUidExpr_le_maxUidExprList_of_mem hx; omega) b hb
    show s.next ≤ (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).2.next ∧
      Moist.MIR.maxUidExprList ((Moist.MIR.anfAtom a s).1.1 ::
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1) <
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).2.next ∧
      Moist.MIR.maxUidExprBinds ((Moist.MIR.anfAtom a s).1.2 ++
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.2) <
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).2.next ∧
      (∀ x ∈ (Moist.MIR.anfAtom a s).1.1 ::
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1, x.isAtom = true) ∧
      MIRCtxRefines (.Constr tag (pre ++ a :: rest))
        (Moist.MIR.wrapLet ((Moist.MIR.anfAtom a s).1.2 ++
          (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.2)
          (.Constr tag (pre ++ ((Moist.MIR.anfAtom a s).1.1 ::
            (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1)))) ∧
      MIRCtxRefines
        (Moist.MIR.wrapLet ((Moist.MIR.anfAtom a s).1.2 ++
          (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.2)
          (.Constr tag (pre ++ ((Moist.MIR.anfAtom a s).1.1 ::
            (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1))))
        (.Constr tag (pre ++ a :: rest))
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · show Moist.MIR.maxUidExprList ((Moist.MIR.anfAtom a s).1.1 ::
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1) < _
      simp only [Moist.MIR.maxUidExprList]; omega
    · have := Moist.MIR.maxUidExprBinds_append (Moist.MIR.anfAtom a s).1.2
        (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.2
      omega
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hatom_flag
      · exact ih_atoms_flag x hx
    · -- Forward refinement chain
      have hassoc1 : pre ++ a :: rest = pre ++ [a] ++ rest := by simp
      have hassoc2 : pre ++ ((Moist.MIR.anfAtom a s).1.1 ::
          (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1) =
          pre ++ [(Moist.MIR.anfAtom a s).1.1] ++
            (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1 := by simp
      rw [hassoc1, hassoc2]
      refine mirCtxRefines_trans
        (mirCtxRefines_constr_of_listRel tag
          (listRel_app_of_refl_mid_mirCtxRefines hatom_fwd))
        (mirCtxRefines_trans
          (mirCtxRefines_constr_of_listRel tag
            (listRel_app_of_refl_mid_mirCtxRefines (mirCtxRefines_wrapLet_eq_fwd _ _)))
          (mirCtxRefines_trans
            (mirCtxRefines_let_hoist_constr_arg_iter_fwd _ tag pre _ rest
              hpre_atom hpre_β_fresh hrest_β_fresh)
            (mirCtxRefines_trans
              (mirCtxRefines_let_body ih_fwd)
              (mirCtxRefines_trans
                (mirCtxRefines_let_body (mirCtxRefines_wrapLet_eq_fwd _ _))
                (mirCtxRefines_trans
                  (mirCtxRefines_let_flatten_body_fwd _ _ _)
                  (mirCtxRefines_wrapLet_eq_bwd _ _))))))
    · -- Backward refinement chain (symmetric)
      have hassoc1 : pre ++ a :: rest = pre ++ [a] ++ rest := by simp
      have hassoc2 : pre ++ ((Moist.MIR.anfAtom a s).1.1 ::
          (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1) =
          pre ++ [(Moist.MIR.anfAtom a s).1.1] ++
            (Moist.MIR.anfAtomList rest (Moist.MIR.anfAtom a s).2).1.1 := by simp
      rw [hassoc1, hassoc2]
      refine mirCtxRefines_trans
        (mirCtxRefines_wrapLet_eq_fwd _ _)
        (mirCtxRefines_trans
          (mirCtxRefines_let_flatten_body_bwd _ _ _)
          (mirCtxRefines_trans
            (mirCtxRefines_let_body (mirCtxRefines_wrapLet_eq_bwd _ _))
            (mirCtxRefines_trans
              (mirCtxRefines_let_body ih_bwd)
              (mirCtxRefines_trans
                (mirCtxRefines_let_hoist_constr_arg_iter_bwd _ tag pre _ rest
                  hpre_atom hpre_β_fresh hrest_β_fresh)
                (mirCtxRefines_trans
                  (mirCtxRefines_constr_of_listRel tag
                    (listRel_app_of_refl_mid_mirCtxRefines (mirCtxRefines_wrapLet_eq_bwd _ _)))
                  (mirCtxRefines_constr_of_listRel tag
                    (listRel_app_of_refl_mid_mirCtxRefines hatom_bwd)))))))

mutual

theorem anfNormalizeCore_mirCtxRefines (e : Expr) (s : Moist.MIR.FreshState)
    (hfresh : FreshGt s e) :
    MIRCtxRefines e (Moist.MIR.anfNormalizeCore e s).1 ∧
    MIRCtxRefines (Moist.MIR.anfNormalizeCore e s).1 e ∧
    s.next ≤ (Moist.MIR.anfNormalizeCore e s).2.next ∧
    FreshGt (Moist.MIR.anfNormalizeCore e s).2 (Moist.MIR.anfNormalizeCore e s).1 := by
  match e with
  | .Var v =>
    rw [show (Moist.MIR.anfNormalizeCore (.Var v)) s = (.Var v, s) from rfl]
    refine ⟨mirCtxRefines_refl _, mirCtxRefines_refl _, Nat.le_refl _, ?_⟩
    exact hfresh
  | .Lit lit =>
    rw [show (Moist.MIR.anfNormalizeCore (.Lit lit)) s = (.Lit lit, s) from rfl]
    refine ⟨mirCtxRefines_refl _, mirCtxRefines_refl _, Nat.le_refl _, ?_⟩
    exact hfresh
  | .Builtin b =>
    rw [show (Moist.MIR.anfNormalizeCore (.Builtin b)) s = (.Builtin b, s) from rfl]
    refine ⟨mirCtxRefines_refl _, mirCtxRefines_refl _, Nat.le_refl _, ?_⟩
    exact hfresh
  | .Error =>
    rw [show (Moist.MIR.anfNormalizeCore .Error) s = (.Error, s) from rfl]
    refine ⟨mirCtxRefines_refl _, mirCtxRefines_refl _, Nat.le_refl _, ?_⟩
    exact hfresh
  | .Lam x body =>
    rw [anfNormalizeCore_lam_eq x body s]
    have hlam_uid : Moist.MIR.maxUidExpr (.Lam x body) < s.next := hfresh
    simp only [Moist.MIR.maxUidExpr] at hlam_uid
    have hbody_fresh : FreshGt s body := by show Moist.MIR.maxUidExpr body < _; omega
    obtain ⟨hfwd, hbwd, hmono, hfresh'⟩ :=
      anfNormalizeCore_mirCtxRefines body s hbody_fresh
    have hb : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore body s).1 <
      (Moist.MIR.anfNormalizeCore body s).2.next := hfresh'
    refine ⟨mirCtxRefines_lam hfwd, mirCtxRefines_lam hbwd, hmono, ?_⟩
    show Moist.MIR.maxUidExpr (.Lam x _) < _
    simp only [Moist.MIR.maxUidExpr]
    omega
  | .Delay inner =>
    rw [anfNormalizeCore_delay_eq inner s]
    have hinner_fresh : FreshGt s inner := by
      have : Moist.MIR.maxUidExpr (.Delay inner) < s.next := hfresh
      simp only [Moist.MIR.maxUidExpr] at this; exact this
    obtain ⟨hfwd, hbwd, hmono, hfresh'⟩ :=
      anfNormalizeCore_mirCtxRefines inner s hinner_fresh
    refine ⟨mirCtxRefines_delay hfwd, mirCtxRefines_delay hbwd, hmono, ?_⟩
    show Moist.MIR.maxUidExpr (.Delay _) < _
    simp only [Moist.MIR.maxUidExpr]
    exact hfresh'
  | .Fix f body =>
    rw [anfNormalizeCore_fix_eq f body s]
    have hfix_uid : Moist.MIR.maxUidExpr (.Fix f body) < s.next := hfresh
    simp only [Moist.MIR.maxUidExpr] at hfix_uid
    have hbody_fresh : FreshGt s body := by
      show Moist.MIR.maxUidExpr body < s.next; omega
    obtain ⟨hfwd, hbwd, hmono, hfresh'⟩ :=
      anfNormalizeCore_mirCtxRefines body s hbody_fresh
    refine ⟨?_, ?_, hmono, ?_⟩
    · -- Forward
      match body, hbody_fresh with
      | .Lam x inner, hbody_fresh =>
        have hinner_fresh : FreshGt s inner := by
          show Moist.MIR.maxUidExpr inner < s.next
          have : Moist.MIR.maxUidExpr (.Lam x inner) < s.next := hbody_fresh
          simp only [Moist.MIR.maxUidExpr] at this; omega
        have ⟨hfwd_inner, _, _, _⟩ := anfNormalizeCore_mirCtxRefines inner s hinner_fresh
        rw [show (Moist.MIR.anfNormalizeCore (.Lam x inner) s).1 =
            .Lam x (Moist.MIR.anfNormalizeCore inner s).1 from by rw [anfNormalizeCore_lam_eq]]
        exact mirCtxRefines_fix_lam hfwd_inner
      | .Var _, _ | .Lit _, _ | .Builtin _, _ | .Error, _ | .Fix _ _, _
      | .App _ _, _ | .Force _, _ | .Delay _, _ | .Constr _ _, _ | .Case _ _, _ | .Let _ _, _ =>
        exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    · -- Backward
      match body, hbody_fresh with
      | .Lam x inner, hbody_fresh =>
        have hinner_fresh : FreshGt s inner := by
          show Moist.MIR.maxUidExpr inner < s.next
          have : Moist.MIR.maxUidExpr (.Lam x inner) < s.next := hbody_fresh
          simp only [Moist.MIR.maxUidExpr] at this; omega
        have ⟨_, hbwd_inner, _, _⟩ := anfNormalizeCore_mirCtxRefines inner s hinner_fresh
        rw [show (Moist.MIR.anfNormalizeCore (.Lam x inner) s).1 =
            .Lam x (Moist.MIR.anfNormalizeCore inner s).1 from by rw [anfNormalizeCore_lam_eq]]
        exact mirCtxRefines_fix_lam hbwd_inner
      | .Var _, _ | .Lit _, _ | .Builtin _, _ | .Error, _ | .Fix _ _, _ | .App _ _, _
      | .Force _, _ | .Delay _, _ | .Constr _ _, _ | .Case _ _, _ | .Let _ _, _ =>
        exact mirCtxRefines_fix_nonlam_both
          (anfNormalizeCore_nonlam_preserves _ (by intros; intro h; cases h) s)
          (by intros; intro h; cases h)
    · -- Output freshness
      show Moist.MIR.maxUidExpr (.Fix f _) < _
      simp only [Moist.MIR.maxUidExpr]
      have hf' : f.uid < s.next := by omega
      have hb : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore body s).1 <
        (Moist.MIR.anfNormalizeCore body s).2.next := hfresh'
      omega
  | .Force inner =>
    rw [anfNormalizeCore_force_eq inner s]
    have hinner_fresh : FreshGt s inner := by
      have : Moist.MIR.maxUidExpr (.Force inner) < s.next := hfresh
      simp only [Moist.MIR.maxUidExpr] at this; exact this
    obtain ⟨hfwd_in, hbwd_in, hmono_in, hfresh_in⟩ :=
      anfNormalizeCore_mirCtxRefines inner s hinner_fresh
    obtain ⟨hatom_flag, hatom_fwd, hatom_bwd⟩ :=
      anfAtom_spec (Moist.MIR.anfNormalizeCore inner s).1 (Moist.MIR.anfNormalizeCore inner s).2
    have hatom_mn := (anfAtom_mono (Moist.MIR.anfNormalizeCore inner s).1
      (Moist.MIR.anfNormalizeCore inner s).2).1
    have hinner_F : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore inner s).1 <
      (Moist.MIR.anfNormalizeCore inner s).2.next := hfresh_in
    have hatom_out := anfAtom_fresh (Moist.MIR.anfNormalizeCore inner s).1
      (Moist.MIR.anfNormalizeCore inner s).2 hinner_F
    refine ⟨?_, ?_, Nat.le_trans hmono_in hatom_mn, ?_⟩
    · -- Forward: .Force inner ≈ .Force inner' ≈ .Force (wrapLet binds atom) ≈ .Let binds (.Force atom) ≈ wrapLet ...
      refine mirCtxRefines_trans (mirCtxRefines_force hfwd_in) ?_
      refine mirCtxRefines_trans (mirCtxRefines_force hatom_fwd) ?_
      refine mirCtxRefines_trans (mirCtxRefines_force (mirCtxRefines_wrapLet_eq_fwd _ _)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_hoist_force_iter_fwd _ _) ?_
      exact mirCtxRefines_wrapLet_eq_bwd _ _
    · -- Backward (symmetric)
      refine mirCtxRefines_trans (mirCtxRefines_wrapLet_eq_fwd _ _) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_hoist_force_iter_bwd _ _) ?_
      refine mirCtxRefines_trans (mirCtxRefines_force (mirCtxRefines_wrapLet_eq_bwd _ _)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_force hatom_bwd) ?_
      exact mirCtxRefines_force hbwd_in
    · -- Output freshness
      have hb_le := maxUidExprBinds_le_wrapLet
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore inner s).1)
          (Moist.MIR.anfNormalizeCore inner s).2).1.2
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore inner s).1)
          (Moist.MIR.anfNormalizeCore inner s).2).1.1
      have ha_le := maxUidExpr_le_wrapLet
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore inner s).1)
          (Moist.MIR.anfNormalizeCore inner s).2).1.2
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore inner s).1)
          (Moist.MIR.anfNormalizeCore inner s).2).1.1
      apply freshGt_wrapLet _ _ _ (Nat.lt_of_le_of_lt hb_le hatom_out)
      show Moist.MIR.maxUidExpr (.Force _) < _
      simp only [Moist.MIR.maxUidExpr]
      exact Nat.lt_of_le_of_lt ha_le hatom_out
  | .App fn arg =>
    rw [anfNormalizeCore_app_eq fn arg s]
    have hap_uid : Moist.MIR.maxUidExpr (.App fn arg) < s.next := hfresh
    simp only [Moist.MIR.maxUidExpr] at hap_uid
    have hfn_fresh : FreshGt s fn := by show Moist.MIR.maxUidExpr fn < _; omega
    obtain ⟨hfn_f, hfn_b, hfn_m, hfn_F⟩ := anfNormalizeCore_mirCtxRefines fn s hfn_fresh
    have harg_fresh : FreshGt (Moist.MIR.anfNormalizeCore fn s).2 arg := by
      show Moist.MIR.maxUidExpr arg < _; omega
    obtain ⟨harg_f, harg_b, harg_m, harg_F⟩ :=
      anfNormalizeCore_mirCtxRefines arg (Moist.MIR.anfNormalizeCore fn s).2 harg_fresh
    let fn' := (Moist.MIR.anfNormalizeCore fn s).1
    let s₁ := (Moist.MIR.anfNormalizeCore fn s).2
    let arg' := (Moist.MIR.anfNormalizeCore arg s₁).1
    let s₂ := (Moist.MIR.anfNormalizeCore arg s₁).2
    have hfn_m : s.next ≤ s₁.next := hfn_m
    have harg_m : s₁.next ≤ s₂.next := harg_m
    have hfn'_F : Moist.MIR.maxUidExpr fn' < s₁.next := hfn_F
    have harg'_F : Moist.MIR.maxUidExpr arg' < s₂.next := harg_F
    obtain ⟨hfn_atom_flag, hfn_atom_fwd, hfn_atom_bwd⟩ := anfAtom_spec fn' s₂
    let fAtom := ((Moist.MIR.anfAtom fn') s₂).1.1
    let fBinds := ((Moist.MIR.anfAtom fn') s₂).1.2
    let s₃ := ((Moist.MIR.anfAtom fn') s₂).2
    have hfn_atom_mn : s₂.next ≤ s₃.next := (anfAtom_mono fn' s₂).1
    obtain ⟨hx_atom_flag, hx_atom_fwd, hx_atom_bwd⟩ := anfAtom_spec arg' s₃
    let xAtom := ((Moist.MIR.anfAtom arg') s₃).1.1
    let xBinds := ((Moist.MIR.anfAtom arg') s₃).1.2
    let s₄ := ((Moist.MIR.anfAtom arg') s₃).2
    have hx_atom_mn : s₃.next ≤ s₄.next := (anfAtom_mono arg' s₃).1
    have hfn'_F_s₂ : Moist.MIR.maxUidExpr fn' < s₂.next := by
      have := harg_m; omega
    have harg'_F_s₃ : Moist.MIR.maxUidExpr arg' < s₃.next := by
      have := hfn_atom_mn; omega
    -- anfAtom output bounds (wrapLet binds atom < s'.next)
    have hf_wbnd : Moist.MIR.maxUidExpr (Moist.MIR.wrapLet fBinds fAtom) < s₃.next :=
      anfAtom_fresh fn' s₂ hfn'_F_s₂
    have hx_wbnd : Moist.MIR.maxUidExpr (Moist.MIR.wrapLet xBinds xAtom) < s₄.next :=
      anfAtom_fresh arg' s₃ harg'_F_s₃
    -- Atom & binds bounds via wrapLet
    have hfAtom_le := maxUidExpr_le_wrapLet fBinds fAtom
    have hfBinds_le := maxUidExprBinds_le_wrapLet fBinds fAtom
    have hxAtom_le := maxUidExpr_le_wrapLet xBinds xAtom
    have hxBinds_le := maxUidExprBinds_le_wrapLet xBinds xAtom
    -- Freshness side conditions for the hoist primitives
    have hfB_fresh_xArg : ∀ b ∈ fBinds,
        (Moist.MIR.freeVars (Moist.MIR.wrapLet xBinds xAtom)).contains b.1 = false := by
      intro b hb
      have huid : b.1.uid = s₂.next := anfAtom_binds_uid fn' s₂ b hb
      have hne : ((Moist.MIR.anfAtom fn') s₂).1.2 ≠ [] := by
        intro h
        have : b ∈ ([] : List (VarId × Expr × Bool)) := h ▸ hb
        exact absurd this (by simp)
      have hsucc : s₃.next = s₂.next + 1 := anfAtom_state_succ_of_binds_nonempty fn' s₂ hne
      apply anfAtom_wrapLet_freshIn arg' s₃ b.1
      · exact Moist.MIR.maxUidExpr_fresh arg' b.1 (by omega)
      · omega
    have hxB_fresh_fAtom : ∀ b ∈ xBinds,
        (Moist.MIR.freeVars fAtom).contains b.1 = false := by
      intro b hb
      have huid : b.1.uid = s₃.next := anfAtom_binds_uid arg' s₃ b hb
      apply Moist.MIR.maxUidExpr_fresh fAtom b.1
      -- Need: maxUidExpr fAtom < b.1.uid = s₃.next.
      -- maxUidExpr fAtom ≤ maxUidExpr (wrapLet fBinds fAtom) < s₃.next.
      omega
    refine ⟨?_, ?_,
      Nat.le_trans hfn_m (Nat.le_trans harg_m (Nat.le_trans hfn_atom_mn hx_atom_mn)), ?_⟩
    · -- Forward
      refine mirCtxRefines_trans (mirCtxRefines_app hfn_f harg_f) ?_
      refine mirCtxRefines_trans (mirCtxRefines_app hfn_atom_fwd hx_atom_fwd) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_app (mirCtxRefines_wrapLet_eq_fwd _ _) (mirCtxRefines_refl _)) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_hoist_app_left_iter_fwd fBinds fAtom _ hfB_fresh_xArg) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_body (mirCtxRefines_app (mirCtxRefines_refl _)
          (mirCtxRefines_wrapLet_eq_fwd _ _))) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_body
          (mirCtxRefines_let_hoist_app_right_atom_iter_fwd xBinds fAtom xAtom
            hfn_atom_flag hxB_fresh_fAtom)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_flatten_body_fwd _ _ _) ?_
      exact mirCtxRefines_wrapLet_eq_bwd _ _
    · -- Backward (symmetric)
      refine mirCtxRefines_trans (mirCtxRefines_wrapLet_eq_fwd _ _) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_flatten_body_bwd _ _ _) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_body
          (mirCtxRefines_let_hoist_app_right_atom_iter_bwd xBinds fAtom xAtom
            hfn_atom_flag hxB_fresh_fAtom)) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_body (mirCtxRefines_app (mirCtxRefines_refl _)
          (mirCtxRefines_wrapLet_eq_bwd _ _))) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_hoist_app_left_iter_bwd fBinds fAtom _ hfB_fresh_xArg) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_app (mirCtxRefines_wrapLet_eq_bwd _ _) (mirCtxRefines_refl _)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_app hfn_atom_bwd hx_atom_bwd) ?_
      exact mirCtxRefines_app hfn_b harg_b
    · -- Output freshness
      -- Show maxUidExpr (wrapLet (fBinds ++ xBinds) (.App fAtom xAtom)) < s₄.next
      have hbinds_app := Moist.MIR.maxUidExprBinds_append fBinds xBinds
      have hfBinds_b : Moist.MIR.maxUidExprBinds fBinds < s₄.next := by
        have := hx_atom_mn; omega
      have hxBinds_b : Moist.MIR.maxUidExprBinds xBinds < s₄.next := by omega
      have hmxbinds_app : Moist.MIR.maxUidExprBinds (fBinds ++ xBinds) < s₄.next := by omega
      have hfAtom_b : Moist.MIR.maxUidExpr fAtom < s₄.next := by
        have := hx_atom_mn; omega
      have hxAtom_b : Moist.MIR.maxUidExpr xAtom < s₄.next := by omega
      apply freshGt_wrapLet _ _ _ hmxbinds_app
      show Moist.MIR.maxUidExpr (.App fAtom xAtom) < _
      simp only [Moist.MIR.maxUidExpr]; omega
  | .Case scrut alts =>
    rw [anfNormalizeCore_case_eq scrut alts s]
    have hcase_uid : Moist.MIR.maxUidExpr (.Case scrut alts) < s.next := hfresh
    simp only [Moist.MIR.maxUidExpr] at hcase_uid
    have hscrut_fresh : FreshGt s scrut := by
      show Moist.MIR.maxUidExpr scrut < s.next; omega
    have halts_fresh : Moist.MIR.maxUidExprList alts < s.next := by omega
    obtain ⟨hscrut_f, hscrut_b, hscrut_m, hscrut_F⟩ :=
      anfNormalizeCore_mirCtxRefines scrut s hscrut_fresh
    have hscrut_F' : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore scrut s).1 <
      (Moist.MIR.anfNormalizeCore scrut s).2.next := hscrut_F
    obtain ⟨hatom_flag, hatom_fwd, hatom_bwd⟩ :=
      anfAtom_spec (Moist.MIR.anfNormalizeCore scrut s).1 (Moist.MIR.anfNormalizeCore scrut s).2
    have hatom_mn := (anfAtom_mono (Moist.MIR.anfNormalizeCore scrut s).1
      (Moist.MIR.anfNormalizeCore scrut s).2).1
    have hatom_out := anfAtom_fresh (Moist.MIR.anfNormalizeCore scrut s).1
      (Moist.MIR.anfNormalizeCore scrut s).2 hscrut_F
    have halts_fresh_s₂ : Moist.MIR.maxUidExprList alts <
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).2.next := by
      have := hscrut_m; omega
    obtain ⟨halts_fwd, halts_bwd, halts_m, halts_F⟩ :=
      anfNormalizeList_mirCtxRefines alts _ halts_fresh_s₂
    -- Names are too long to inline; alias the components
    have hbinds_fresh_alts : ∀ b ∈
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.2,
        (Moist.MIR.freeVarsList alts).contains b.1 = false := by
      intro b hb
      have huid : b.1.uid = (Moist.MIR.anfNormalizeCore scrut s).2.next :=
        anfAtom_binds_uid _ _ b hb
      have h1 : Moist.MIR.maxUidExprList alts < s.next := halts_fresh
      exact Moist.MIR.maxUidExprList_fresh alts b.1 (by omega)
    have hα_uid : Moist.MIR.maxUidExpr
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.1 <
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).2.next := by
      have := maxUidExpr_le_wrapLet
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.2
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.1
      omega
    have hβ_uid : Moist.MIR.maxUidExprBinds
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.2 <
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).2.next := by
      have := maxUidExprBinds_le_wrapLet
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.2
        ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
          (Moist.MIR.anfNormalizeCore scrut s).2).1.1
      omega
    refine ⟨?_, ?_, Nat.le_trans hscrut_m (Nat.le_trans hatom_mn halts_m), ?_⟩
    · -- Forward chain: case → wrap → let → hoist → body-norm → unwrap
      refine mirCtxRefines_trans (mirCtxRefines_case hscrut_f
        (listRel_mirCtxRefines_refl alts)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_case hatom_fwd
        (listRel_mirCtxRefines_refl alts)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_case
        (mirCtxRefines_wrapLet_eq_fwd _ _) (listRel_mirCtxRefines_refl alts)) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_hoist_case_scrut_iter_fwd _ _ alts hbinds_fresh_alts) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_body (mirCtxRefines_case (mirCtxRefines_refl _) halts_fwd)) ?_
      exact mirCtxRefines_wrapLet_eq_bwd _ _
    · -- Backward chain (symmetric)
      refine mirCtxRefines_trans (mirCtxRefines_wrapLet_eq_fwd _ _) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_body (mirCtxRefines_case (mirCtxRefines_refl _) halts_bwd)) ?_
      refine mirCtxRefines_trans
        (mirCtxRefines_let_hoist_case_scrut_iter_bwd _ _ alts hbinds_fresh_alts) ?_
      refine mirCtxRefines_trans (mirCtxRefines_case
        (mirCtxRefines_wrapLet_eq_bwd _ _) (listRel_mirCtxRefines_refl alts)) ?_
      refine mirCtxRefines_trans (mirCtxRefines_case hatom_bwd
        (listRel_mirCtxRefines_refl alts)) ?_
      exact mirCtxRefines_case hscrut_b (listRel_mirCtxRefines_refl alts)
    · -- Output freshness
      have halts_F' : Moist.MIR.maxUidExprList
          (Moist.MIR.anfNormalizeListCore alts
            ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
              (Moist.MIR.anfNormalizeCore scrut s).2).2).1 <
          (Moist.MIR.anfNormalizeListCore alts
            ((Moist.MIR.anfAtom (Moist.MIR.anfNormalizeCore scrut s).1)
              (Moist.MIR.anfNormalizeCore scrut s).2).2).2.next := halts_F
      exact freshGt_wrapLet_case _ _ _ _
        (Nat.lt_of_lt_of_le hα_uid halts_m) halts_F'
        (Nat.lt_of_lt_of_le hβ_uid halts_m)
  | .Constr tag args =>
    rw [anfNormalizeCore_constr_eq tag args s]
    have hargs_fresh : FreshGtList s args := by
      have : Moist.MIR.maxUidExpr (.Constr tag args) < s.next := hfresh
      simp only [Moist.MIR.maxUidExpr] at this; exact this
    have ⟨hargs_fwd, hargs_bwd, hargs_m, hargs_F⟩ :=
      anfNormalizeList_mirCtxRefines args s hargs_fresh
    -- Use anfAtomList_spec on args' = anfNormalizeListCore args at state s₁ with empty prefix
    have hargs_F' : Moist.MIR.maxUidExprList (Moist.MIR.anfNormalizeListCore args s).1 <
        (Moist.MIR.anfNormalizeListCore args s).2.next := hargs_F
    have hpre_uid : Moist.MIR.maxUidExprList ([] : List Expr) <
        (Moist.MIR.anfNormalizeListCore args s).2.next := by
      simp [Moist.MIR.maxUidExprList]; omega
    obtain ⟨hAL_mono, hAL_atoms_uid, hAL_binds_uid, _, hAL_fwd, hAL_bwd⟩ :=
      anfAtomList_spec (Moist.MIR.anfNormalizeListCore args s).1
        (Moist.MIR.anfNormalizeListCore args s).2 tag [] hargs_F hpre_uid
        (by intro a ha; simp at ha)
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- forward: .Constr tag args ≈ wrapLet binds (.Constr tag atoms)
      refine mirCtxRefines_trans (mirCtxRefines_constr_of_listRel tag hargs_fwd) ?_
      simpa using hAL_fwd
    · -- backward
      refine mirCtxRefines_trans ?_ (mirCtxRefines_constr_of_listRel tag hargs_bwd)
      simpa using hAL_bwd
    · -- monotonicity
      exact Nat.le_trans hargs_m hAL_mono
    · -- freshness
      exact freshGt_wrapLet_constr _ tag _ _ hAL_atoms_uid hAL_binds_uid
  | .Let binds body =>
    rw [anfNormalizeCore_let_eq binds body s]
    have hlet_uid : Moist.MIR.maxUidExpr (.Let binds body) < s.next := hfresh
    simp only [Moist.MIR.maxUidExpr] at hlet_uid
    have hbinds_fresh : FreshGtBinds s binds := by
      show Moist.MIR.maxUidExprBinds binds < s.next; omega
    obtain ⟨hbinds_fwd, hbinds_bwd, hbinds_m, hbinds_F⟩ :=
      anfNormalizeBinds_mirCtxRefines binds s hbinds_fresh
    have hbinds_F' : Moist.MIR.maxUidExprBinds (Moist.MIR.anfNormalizeBindsCore binds s).1 <
      (Moist.MIR.anfNormalizeBindsCore binds s).2.next := hbinds_F
    have hbody_fresh_s₁ : FreshGt (Moist.MIR.anfNormalizeBindsCore binds s).2 body := by
      show Moist.MIR.maxUidExpr body < _; have := hbinds_m; omega
    obtain ⟨hbody_f, hbody_b, hbody_m, hbody_F⟩ :=
      anfNormalizeCore_mirCtxRefines body (Moist.MIR.anfNormalizeBindsCore binds s).2 hbody_fresh_s₁
    have hbody_F' : Moist.MIR.maxUidExpr
      (Moist.MIR.anfNormalizeCore body (Moist.MIR.anfNormalizeBindsCore binds s).2).1 <
      (Moist.MIR.anfNormalizeCore body (Moist.MIR.anfNormalizeBindsCore binds s).2).2.next := hbody_F
    refine ⟨?_, ?_, Nat.le_trans hbinds_m hbody_m, ?_⟩
    · -- forward: .Let binds body ≈ ... ≈ flattenLetBody norm body'
      refine mirCtxRefines_trans (mirCtxRefines_let_binds_congr _ _ body hbinds_fwd) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_body hbody_f) ?_
      exact mirCtxRefines_flattenLetBody_fwd _ _
    · -- backward
      refine mirCtxRefines_trans (mirCtxRefines_flattenLetBody_bwd _ _) ?_
      refine mirCtxRefines_trans (mirCtxRefines_let_body hbody_b) ?_
      exact mirCtxRefines_let_binds_congr _ _ body hbinds_bwd
    · -- output freshness
      exact freshGt_flattenLetBody _ _ _
        (Nat.lt_of_lt_of_le hbinds_F' hbody_m) hbody_F'
termination_by sizeOf e

theorem anfNormalizeList_mirCtxRefines (es : List Expr) (s : Moist.MIR.FreshState)
    (hfresh : FreshGtList s es) :
    ListRel MIRCtxRefines es (Moist.MIR.anfNormalizeListCore es s).1 ∧
    ListRel MIRCtxRefines (Moist.MIR.anfNormalizeListCore es s).1 es ∧
    s.next ≤ (Moist.MIR.anfNormalizeListCore es s).2.next ∧
    FreshGtList (Moist.MIR.anfNormalizeListCore es s).2 (Moist.MIR.anfNormalizeListCore es s).1 := by
  match es with
  | [] =>
    rw [anfNormalizeList_nil_eq]
    exact ⟨True.intro, True.intro, Nat.le_refl _, hfresh⟩
  | e :: rest =>
    rw [anfNormalizeList_cons_eq]
    have hfresh_e : FreshGt s e := by
      show Moist.MIR.maxUidExpr e < s.next
      have : Moist.MIR.maxUidExprList (e :: rest) < s.next := hfresh
      simp only [Moist.MIR.maxUidExprList] at this; omega
    have hfresh_rest : FreshGtList s rest := by
      show Moist.MIR.maxUidExprList rest < s.next
      have : Moist.MIR.maxUidExprList (e :: rest) < s.next := hfresh
      simp only [Moist.MIR.maxUidExprList] at this; omega
    have ⟨hfwd_e, hbwd_e, hmono_e, hfresh_e'⟩ := anfNormalizeCore_mirCtxRefines e s hfresh_e
    have hfresh_rest_s₁ : FreshGtList (Moist.MIR.anfNormalizeCore e s).2 rest := by
      show Moist.MIR.maxUidExprList rest < (Moist.MIR.anfNormalizeCore e s).2.next
      exact Nat.lt_of_lt_of_le hfresh_rest hmono_e
    have ⟨hfwd_rest, hbwd_rest, hmono_rest, hfresh_rest'⟩ :=
      anfNormalizeList_mirCtxRefines rest (Moist.MIR.anfNormalizeCore e s).2 hfresh_rest_s₁
    refine ⟨⟨hfwd_e, hfwd_rest⟩, ⟨hbwd_e, hbwd_rest⟩, ?_, ?_⟩
    · exact Nat.le_trans hmono_e hmono_rest
    · show Moist.MIR.maxUidExprList ((Moist.MIR.anfNormalizeCore e s).1 ::
        (Moist.MIR.anfNormalizeListCore rest (Moist.MIR.anfNormalizeCore e s).2).1) <
        (Moist.MIR.anfNormalizeListCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next
      simp only [Moist.MIR.maxUidExprList]
      have he'_uid : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore e s).1 <
        (Moist.MIR.anfNormalizeCore e s).2.next := hfresh_e'
      have hrest'_uid : Moist.MIR.maxUidExprList
        (Moist.MIR.anfNormalizeListCore rest (Moist.MIR.anfNormalizeCore e s).2).1 <
        (Moist.MIR.anfNormalizeListCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := hfresh_rest'
      have hmono_12 : (Moist.MIR.anfNormalizeCore e s).2.next ≤
        (Moist.MIR.anfNormalizeListCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := hmono_rest
      omega
termination_by sizeOf es

theorem anfNormalizeBinds_mirCtxRefines (binds : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (hfresh : FreshGtBinds s binds) :
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
            binds (Moist.MIR.anfNormalizeBindsCore binds s).1 ∧
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
            (Moist.MIR.anfNormalizeBindsCore binds s).1 binds ∧
    s.next ≤ (Moist.MIR.anfNormalizeBindsCore binds s).2.next ∧
    FreshGtBinds (Moist.MIR.anfNormalizeBindsCore binds s).2
                 (Moist.MIR.anfNormalizeBindsCore binds s).1 := by
  match binds with
  | [] =>
    rw [anfNormalizeBinds_nil_eq]
    exact ⟨True.intro, True.intro, Nat.le_refl _, hfresh⟩
  | (v, e, er) :: rest =>
    rw [anfNormalizeBinds_cons_eq v e er rest s]
    have hv_uid : v.uid < s.next := by
      have : Moist.MIR.maxUidExprBinds ((v, e, er) :: rest) < s.next := hfresh
      simp only [Moist.MIR.maxUidExprBinds] at this; omega
    have he_fresh : FreshGt s e := by
      show Moist.MIR.maxUidExpr e < s.next
      have : Moist.MIR.maxUidExprBinds ((v, e, er) :: rest) < s.next := hfresh
      simp only [Moist.MIR.maxUidExprBinds] at this; omega
    have hrest_fresh : FreshGtBinds s rest := by
      show Moist.MIR.maxUidExprBinds rest < s.next
      have : Moist.MIR.maxUidExprBinds ((v, e, er) :: rest) < s.next := hfresh
      simp only [Moist.MIR.maxUidExprBinds] at this; omega
    have ⟨he_f, he_b, he_m, he_F⟩ := anfNormalizeCore_mirCtxRefines e s he_fresh
    have hrest_fresh_s₁ : FreshGtBinds (Moist.MIR.anfNormalizeCore e s).2 rest := by
      show Moist.MIR.maxUidExprBinds rest < (Moist.MIR.anfNormalizeCore e s).2.next
      exact Nat.lt_of_lt_of_le hrest_fresh he_m
    have ⟨hrest_fwd, hrest_bwd, hrest_m, hrest_F⟩ :=
      anfNormalizeBinds_mirCtxRefines rest (Moist.MIR.anfNormalizeCore e s).2 hrest_fresh_s₁
    refine ⟨⟨⟨rfl, rfl, he_f⟩, hrest_fwd⟩, ⟨⟨rfl, rfl, he_b⟩, hrest_bwd⟩, ?_, ?_⟩
    · exact Nat.le_trans he_m hrest_m
    · show Moist.MIR.maxUidExprBinds ((v, (Moist.MIR.anfNormalizeCore e s).1, er) ::
        (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).1) <
        (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next
      simp only [Moist.MIR.maxUidExprBinds]
      have hv_bnd : v.uid <
          (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := by
        have : v.uid < s.next := hv_uid
        have : s.next ≤ (Moist.MIR.anfNormalizeCore e s).2.next := he_m
        have : (Moist.MIR.anfNormalizeCore e s).2.next ≤
          (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := hrest_m
        omega
      have he'_bnd : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore e s).1 <
          (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := by
        have : Moist.MIR.maxUidExpr (Moist.MIR.anfNormalizeCore e s).1 <
          (Moist.MIR.anfNormalizeCore e s).2.next := he_F
        have : (Moist.MIR.anfNormalizeCore e s).2.next ≤
          (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := hrest_m
        omega
      have hrest'_bnd : Moist.MIR.maxUidExprBinds
          (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).1 <
          (Moist.MIR.anfNormalizeBindsCore rest (Moist.MIR.anfNormalizeCore e s).2).2.next := hrest_F
      omega
termination_by sizeOf binds

end

/-- **Main soundness theorem** for ANF normalization (unrestricted).
    Uses the mutual induction `anfNormalizeCore_mirCtxRefines` to derive
    bidirectional refinement, then collapses to `MIRCtxEq`. -/
theorem anfNormalizeCore_sound (e : Expr) :
    MIRCtxEq e (Moist.MIR.runFresh (Moist.MIR.anfNormalizeCore e)
      (Moist.MIR.maxUidExpr e + 1)) := by
  have hfresh : FreshGt ⟨Moist.MIR.maxUidExpr e + 1⟩ e := by
    show Moist.MIR.maxUidExpr e < Moist.MIR.maxUidExpr e + 1
    omega
  have ⟨hfwd, hbwd, _, _⟩ :=
    anfNormalizeCore_mirCtxRefines e ⟨Moist.MIR.maxUidExpr e + 1⟩ hfresh
  exact mirCtxEq_of_mirCtxRefines_bidir hfwd hbwd

/-! ## Pipeline soundness: alpha-rename + ANF normalization

For Fix-free input, the pipeline is contextually equivalent to the
original. We run alpha-rename and ANF in *independent* fresh supplies
(each starting above its input's `maxUidExpr`), which sidesteps any
need to track state between the two phases. -/

/-- Alpha-rename is transparent at the `lowerTotalExpr` level: for
    Fix-free input, `MIRCtxEq e m ↔ MIRCtxEq (alphaRenameTop e K).1 m`. -/
private theorem alphaRenameTop_mirCtxEq_transport (e : Expr) (m : Expr)
    (K : Moist.MIR.FreshState)
    (hK : Moist.MIR.maxUidExpr e < K.next)
    (hFixFree : Moist.MIR.fixCount e = 0) :
    MIRCtxEq (Moist.MIR.alphaRenameTop e K).1 m → MIRCtxEq e m := by
  intro h env
  have hlow_eq :
      Moist.MIR.lowerTotalExpr env e =
      Moist.MIR.lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 :=
    alphaRenameTop_lowerTotalExpr_eq e K hK hFixFree env
  have ⟨hiff, hctx⟩ := h env
  rw [hlow_eq]
  exact ⟨hiff, hctx⟩

/-- **Alpha-rename + ANF pipeline soundness** (without `topFlatten`):
    the two phases composed with independent fresh supplies are
    contextually equivalent to the input (for Fix-free input). -/
theorem anfNormalizeCore_alphaRename_sound (e : Expr)
    (hFixFree : Moist.MIR.fixCount e = 0) :
    let renamed := Moist.MIR.runFresh (Moist.MIR.alphaRenameTop e)
                     (Moist.MIR.maxUidExpr e + 1)
    MIRCtxEq e
      (Moist.MIR.runFresh (Moist.MIR.anfNormalizeCore renamed)
        (Moist.MIR.maxUidExpr renamed + 1)) := by
  -- Apply `anfNormalizeCore_sound` to the alpha-renamed expression, then
  -- transport the equivalence back to the original via alpha-rename's
  -- lowering-preservation.
  let K : Moist.MIR.FreshState := ⟨Moist.MIR.maxUidExpr e + 1⟩
  have hK : Moist.MIR.maxUidExpr e < K.next := Nat.lt_succ_self _
  have h_anf := anfNormalizeCore_sound (Moist.MIR.alphaRenameTop e K).1
  exact alphaRenameTop_mirCtxEq_transport e _ K hK hFixFree h_anf

/-! ## Composition via `MIRCtxRefines`

To compose alpha-rename soundness, ANF soundness, and `topFlatten`
soundness into an end-to-end `MIRCtxEq`, we work at the `MIRCtxRefines`
level (which has a closedness-free transitivity) and collapse at the
end. Alpha-rename is lifted to bidirectional `MIRCtxRefines` directly
from the `lowerTotalExpr`-preservation property. -/

/-- Alpha-rename as a forward `MIRCtxRefines` (Fix-free input). -/
theorem alphaRenameTop_mirCtxRefines_fwd (e : Expr) (K : Moist.MIR.FreshState)
    (hK : Moist.MIR.maxUidExpr e < K.next)
    (hFixFree : Moist.MIR.fixCount e = 0) :
    MIRCtxRefines e (Moist.MIR.alphaRenameTop e K).1 := by
  intro env
  have hlow_eq :
      Moist.MIR.lowerTotalExpr env e =
      Moist.MIR.lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 :=
    alphaRenameTop_lowerTotalExpr_eq e K hK hFixFree env
  refine ⟨fun h => hlow_eq ▸ h, ?_⟩
  rw [hlow_eq]
  cases Moist.MIR.lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 with
  | none => trivial
  | some t => exact Moist.Verified.Contextual.ctxRefines_refl t

/-- Alpha-rename as a backward `MIRCtxRefines` (Fix-free input). -/
theorem alphaRenameTop_mirCtxRefines_bwd (e : Expr) (K : Moist.MIR.FreshState)
    (hK : Moist.MIR.maxUidExpr e < K.next)
    (hFixFree : Moist.MIR.fixCount e = 0) :
    MIRCtxRefines (Moist.MIR.alphaRenameTop e K).1 e := by
  intro env
  have hlow_eq :
      Moist.MIR.lowerTotalExpr env e =
      Moist.MIR.lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 :=
    alphaRenameTop_lowerTotalExpr_eq e K hK hFixFree env
  refine ⟨fun h => hlow_eq.symm ▸ h, ?_⟩
  rw [hlow_eq]
  cases Moist.MIR.lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 with
  | none => trivial
  | some t => exact Moist.Verified.Contextual.ctxRefines_refl t

/-! ## `flattenReadyCheck` soundness

`flattenReadyCheck` is the bool-valued runtime check that decides
`FlattenReady`. Proving the implication lets `anfNormalizeFlat` be
self-validating — if the check passes we flatten safely, otherwise we
skip flattening (still sound). -/

theorem flattenReadyCheck_implies_FlattenReady (body : Expr) :
    ∀ (binds : List (VarId × Expr × Bool)),
      Moist.MIR.flattenReadyCheck body binds = true → FlattenReady body binds
  | [] => fun _ => .nil
  | (v, e, er) :: rest => fun h => by
    show FlattenReady body ((v, e, er) :: rest)
    -- Unfold the bool check
    simp only [Moist.MIR.flattenReadyCheck] at h
    cases e_cases : e with
    | Let ibs ibody =>
      rw [e_cases] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h_body, h_rest⟩, h_rec⟩ := h
      have hfresh_body : ∀ ib ∈ ibs,
          (Moist.MIR.freeVars body).contains ib.1 = false := by
        intro ib hib
        have h' := List.all_eq_true.mp h_body ib hib
        show (Moist.MIR.freeVars body).contains ib.1 = false
        cases h'' : (Moist.MIR.freeVars body).contains ib.1
        · rfl
        · rw [h''] at h'; exact absurd h' (by simp)
      have hfresh_rest : ∀ ib ∈ ibs, ∀ r ∈ rest,
          (Moist.MIR.freeVars r.2.1).contains ib.1 = false := by
        intro ib hib r hr
        have h' := List.all_eq_true.mp h_rest ib hib
        have h'' := List.all_eq_true.mp h' r hr
        show (Moist.MIR.freeVars r.2.1).contains ib.1 = false
        cases h''' : (Moist.MIR.freeVars r.2.1).contains ib.1
        · rfl
        · rw [h'''] at h''; exact absurd h'' (by simp)
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h_rec
      exact FlattenReady.letCons hfresh_body hfresh_rest hrec
    | Var _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Lit _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Builtin _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Error =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Lam _ _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Fix _ _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | App _ _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Force _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Delay _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Constr _ _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq
    | Case _ _ =>
      rw [e_cases] at h
      have hrec := flattenReadyCheck_implies_FlattenReady body rest h
      refine FlattenReady.nonLetCons (fun ibs ibody => ?_) hrec
      intro heq; cases heq

/-! ## `flattenAll` soundness (bidirectional MIRCtxRefines) -/

/-- `flattenAll` preserves "not a Lam": if the input isn't a `.Lam`,
    neither is the output. -/
private theorem flattenAll_nonLam (e : Expr)
    (h : ∀ x inner, e ≠ .Lam x inner) :
    ∀ x inner, Moist.MIR.flattenAll e ≠ .Lam x inner := by
  intro x inner heq
  cases e with
  | Lam x' inner' => exact absurd rfl (h x' inner')
  | Var v =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Lit lit =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Builtin b =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Error =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Fix f body =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | App f x =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Force inner =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Delay inner =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Constr tag args =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Case scrut alts =>
    simp only [Moist.MIR.flattenAll] at heq; cases heq
  | Let binds body =>
    simp only [Moist.MIR.flattenAll] at heq
    split at heq <;> cases heq

mutual

theorem flattenAll_mirCtxRefines_fwd (e : Expr) :
    MIRCtxRefines e (Moist.MIR.flattenAll e) := by
  match e with
  | .Var v =>
    show MIRCtxRefines (.Var v) (Moist.MIR.flattenAll (.Var v))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_refl _
  | .Lit lit =>
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_refl _
  | .Builtin b =>
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_refl _
  | .Error =>
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_refl _
  | .Lam x body =>
    show MIRCtxRefines (.Lam x body) (Moist.MIR.flattenAll (.Lam x body))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_lam (flattenAll_mirCtxRefines_fwd body)
  | .Fix f body =>
    show MIRCtxRefines (.Fix f body) (Moist.MIR.flattenAll (.Fix f body))
    unfold Moist.MIR.flattenAll
    match body with
    | .Lam x inner =>
      have h_inner := flattenAll_mirCtxRefines_fwd inner
      show MIRCtxRefines (.Fix f (.Lam x inner))
        (.Fix f (Moist.MIR.flattenAll (.Lam x inner)))
      unfold Moist.MIR.flattenAll
      exact mirCtxRefines_fix_lam h_inner
    | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _
    | .Force _ | .Delay _ | .Constr _ _ | .Case _ _ | .Let _ _ =>
      refine mirCtxRefines_fix_nonlam_both ?_ ?_
      · intros x inner heq; cases heq
      · exact flattenAll_nonLam _ (by intros; intro h; cases h)
  | .App f x =>
    show MIRCtxRefines (.App f x) (Moist.MIR.flattenAll (.App f x))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_app (flattenAll_mirCtxRefines_fwd f)
      (flattenAll_mirCtxRefines_fwd x)
  | .Force inner =>
    show MIRCtxRefines (.Force inner) (Moist.MIR.flattenAll (.Force inner))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_force (flattenAll_mirCtxRefines_fwd inner)
  | .Delay inner =>
    show MIRCtxRefines (.Delay inner) (Moist.MIR.flattenAll (.Delay inner))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_delay (flattenAll_mirCtxRefines_fwd inner)
  | .Constr tag args =>
    show MIRCtxRefines (.Constr tag args) (Moist.MIR.flattenAll (.Constr tag args))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_constr_of_listRel tag
      (flattenAllList_mirCtxRefines_fwd args)
  | .Case scrut alts =>
    show MIRCtxRefines (.Case scrut alts) (Moist.MIR.flattenAll (.Case scrut alts))
    unfold Moist.MIR.flattenAll
    exact mirCtxRefines_case (flattenAll_mirCtxRefines_fwd scrut)
      (flattenAllList_mirCtxRefines_fwd alts)
  | .Let binds body =>
    let binds' := Moist.MIR.flattenAllBinds binds
    let body' := Moist.MIR.flattenAll body
    show MIRCtxRefines (.Let binds body) (Moist.MIR.flattenAll (.Let binds body))
    show MIRCtxRefines (.Let binds body)
      (Moist.MIR.flattenAll (.Let binds body))
    unfold Moist.MIR.flattenAll
    -- After unfold, the goal has an if-then-else with the destructured form.
    have h_binds_congr : MIRCtxRefines (.Let binds body)
        (.Let (Moist.MIR.flattenAllBinds binds) body) :=
      mirCtxRefines_let_binds_congr binds (Moist.MIR.flattenAllBinds binds) body
        (flattenAllBinds_mirCtxRefines_fwd binds)
    have h_body_congr : MIRCtxRefines
        (.Let (Moist.MIR.flattenAllBinds binds) body)
        (.Let (Moist.MIR.flattenAllBinds binds) (Moist.MIR.flattenAll body)) :=
      mirCtxRefines_let_body (flattenAll_mirCtxRefines_fwd body)
    have h_step : MIRCtxRefines (.Let binds body)
        (.Let (Moist.MIR.flattenAllBinds binds) (Moist.MIR.flattenAll body)) :=
      mirCtxRefines_trans h_binds_congr h_body_congr
    by_cases hcheck : Moist.MIR.flattenReadyCheck
                        (Moist.MIR.flattenAll body)
                        (Moist.MIR.flattenAllBinds binds) = true
    · rw [if_pos hcheck]
      have hfr : FlattenReady (Moist.MIR.flattenAll body)
          (Moist.MIR.flattenAllBinds binds) :=
        flattenReadyCheck_implies_FlattenReady _ _ hcheck
      have h_flat : MIRCtxRefines
          (.Let (Moist.MIR.flattenAllBinds binds) (Moist.MIR.flattenAll body))
          (.Let (Moist.MIR.flattenLetBinds (Moist.MIR.flattenAllBinds binds))
            (Moist.MIR.flattenAll body)) :=
        mirCtxRefines_flattenLetBinds_fwd _ _ hfr
      exact mirCtxRefines_trans h_step h_flat
    · have hfalse : Moist.MIR.flattenReadyCheck (Moist.MIR.flattenAll body)
          (Moist.MIR.flattenAllBinds binds) = false := by
        cases h' : Moist.MIR.flattenReadyCheck (Moist.MIR.flattenAll body)
                     (Moist.MIR.flattenAllBinds binds)
        · rfl
        · exact absurd h' hcheck
      rw [if_neg (by rw [hfalse]; exact Bool.false_ne_true)]
      exact h_step
termination_by sizeOf e

theorem flattenAll_mirCtxRefines_bwd (e : Expr) :
    MIRCtxRefines (Moist.MIR.flattenAll e) e := by
  match e with
  | .Var v =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Var v)) (.Var v)
    simp only [Moist.MIR.flattenAll]; exact mirCtxRefines_refl _
  | .Lit lit =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Lit lit)) (.Lit lit)
    simp only [Moist.MIR.flattenAll]; exact mirCtxRefines_refl _
  | .Builtin b =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Builtin b)) (.Builtin b)
    simp only [Moist.MIR.flattenAll]; exact mirCtxRefines_refl _
  | .Error =>
    show MIRCtxRefines (Moist.MIR.flattenAll .Error) .Error
    simp only [Moist.MIR.flattenAll]; exact mirCtxRefines_refl _
  | .Lam x body =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Lam x body)) (.Lam x body)
    simp only [Moist.MIR.flattenAll]
    exact mirCtxRefines_lam (flattenAll_mirCtxRefines_bwd body)
  | .Fix f body =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Fix f body)) (.Fix f body)
    unfold Moist.MIR.flattenAll
    match body with
    | .Lam x inner =>
      have h_inner := flattenAll_mirCtxRefines_bwd inner
      show MIRCtxRefines (.Fix f (Moist.MIR.flattenAll (.Lam x inner)))
        (.Fix f (.Lam x inner))
      unfold Moist.MIR.flattenAll
      exact mirCtxRefines_fix_lam h_inner
    | .Var _ | .Lit _ | .Builtin _ | .Error | .Fix _ _ | .App _ _
    | .Force _ | .Delay _ | .Constr _ _ | .Case _ _ | .Let _ _ =>
      refine mirCtxRefines_fix_nonlam_both ?_ ?_
      · exact flattenAll_nonLam _ (by intros; intro h; cases h)
      · intros x inner heq; cases heq
  | .App f x =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.App f x)) (.App f x)
    simp only [Moist.MIR.flattenAll]
    exact mirCtxRefines_app (flattenAll_mirCtxRefines_bwd f)
      (flattenAll_mirCtxRefines_bwd x)
  | .Force inner =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Force inner)) (.Force inner)
    simp only [Moist.MIR.flattenAll]
    exact mirCtxRefines_force (flattenAll_mirCtxRefines_bwd inner)
  | .Delay inner =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Delay inner)) (.Delay inner)
    simp only [Moist.MIR.flattenAll]
    exact mirCtxRefines_delay (flattenAll_mirCtxRefines_bwd inner)
  | .Constr tag args =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Constr tag args)) (.Constr tag args)
    simp only [Moist.MIR.flattenAll]
    exact mirCtxRefines_constr_of_listRel tag
      (flattenAllList_mirCtxRefines_bwd args)
  | .Case scrut alts =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Case scrut alts)) (.Case scrut alts)
    simp only [Moist.MIR.flattenAll]
    exact mirCtxRefines_case (flattenAll_mirCtxRefines_bwd scrut)
      (flattenAllList_mirCtxRefines_bwd alts)
  | .Let binds body =>
    show MIRCtxRefines (Moist.MIR.flattenAll (.Let binds body)) (.Let binds body)
    unfold Moist.MIR.flattenAll
    have h_binds_congr : MIRCtxRefines
        (.Let (Moist.MIR.flattenAllBinds binds) body) (.Let binds body) :=
      mirCtxRefines_let_binds_congr (Moist.MIR.flattenAllBinds binds) binds body
        (flattenAllBinds_mirCtxRefines_bwd binds)
    have h_body_congr : MIRCtxRefines
        (.Let (Moist.MIR.flattenAllBinds binds) (Moist.MIR.flattenAll body))
        (.Let (Moist.MIR.flattenAllBinds binds) body) :=
      mirCtxRefines_let_body (flattenAll_mirCtxRefines_bwd body)
    have h_step : MIRCtxRefines
        (.Let (Moist.MIR.flattenAllBinds binds) (Moist.MIR.flattenAll body))
        (.Let binds body) :=
      mirCtxRefines_trans h_body_congr h_binds_congr
    by_cases hcheck : Moist.MIR.flattenReadyCheck
                        (Moist.MIR.flattenAll body)
                        (Moist.MIR.flattenAllBinds binds) = true
    · rw [if_pos hcheck]
      have hfr : FlattenReady (Moist.MIR.flattenAll body)
          (Moist.MIR.flattenAllBinds binds) :=
        flattenReadyCheck_implies_FlattenReady _ _ hcheck
      have h_flat : MIRCtxRefines
          (.Let (Moist.MIR.flattenLetBinds (Moist.MIR.flattenAllBinds binds))
            (Moist.MIR.flattenAll body))
          (.Let (Moist.MIR.flattenAllBinds binds) (Moist.MIR.flattenAll body)) :=
        mirCtxRefines_flattenLetBinds_bwd _ _ hfr
      exact mirCtxRefines_trans h_flat h_step
    · have hfalse : Moist.MIR.flattenReadyCheck (Moist.MIR.flattenAll body)
          (Moist.MIR.flattenAllBinds binds) = false := by
        cases h' : Moist.MIR.flattenReadyCheck (Moist.MIR.flattenAll body)
                     (Moist.MIR.flattenAllBinds binds)
        · rfl
        · exact absurd h' hcheck
      rw [if_neg (by rw [hfalse]; exact Bool.false_ne_true)]
      exact h_step
termination_by sizeOf e

theorem flattenAllList_mirCtxRefines_fwd (es : List Expr) :
    ListRel MIRCtxRefines es (Moist.MIR.flattenAllList es) := by
  match es with
  | [] =>
    show ListRel MIRCtxRefines [] (Moist.MIR.flattenAllList [])
    unfold Moist.MIR.flattenAllList; exact True.intro
  | e :: rest =>
    show ListRel MIRCtxRefines (e :: rest) (Moist.MIR.flattenAllList (e :: rest))
    unfold Moist.MIR.flattenAllList
    exact ⟨flattenAll_mirCtxRefines_fwd e, flattenAllList_mirCtxRefines_fwd rest⟩
termination_by sizeOf es

theorem flattenAllList_mirCtxRefines_bwd (es : List Expr) :
    ListRel MIRCtxRefines (Moist.MIR.flattenAllList es) es := by
  match es with
  | [] =>
    show ListRel MIRCtxRefines (Moist.MIR.flattenAllList []) []
    unfold Moist.MIR.flattenAllList; exact True.intro
  | e :: rest =>
    show ListRel MIRCtxRefines (Moist.MIR.flattenAllList (e :: rest)) (e :: rest)
    unfold Moist.MIR.flattenAllList
    exact ⟨flattenAll_mirCtxRefines_bwd e, flattenAllList_mirCtxRefines_bwd rest⟩
termination_by sizeOf es

theorem flattenAllBinds_mirCtxRefines_fwd (binds : List (VarId × Expr × Bool)) :
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
      binds (Moist.MIR.flattenAllBinds binds) := by
  match binds with
  | [] =>
    show ListRel _ [] (Moist.MIR.flattenAllBinds [])
    unfold Moist.MIR.flattenAllBinds; exact True.intro
  | (v, e, er) :: rest =>
    show ListRel _ ((v, e, er) :: rest) (Moist.MIR.flattenAllBinds ((v, e, er) :: rest))
    unfold Moist.MIR.flattenAllBinds
    exact ⟨⟨rfl, rfl, flattenAll_mirCtxRefines_fwd e⟩,
      flattenAllBinds_mirCtxRefines_fwd rest⟩
termination_by sizeOf binds

theorem flattenAllBinds_mirCtxRefines_bwd (binds : List (VarId × Expr × Bool)) :
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧ MIRCtxRefines b₁.2.1 b₂.2.1)
      (Moist.MIR.flattenAllBinds binds) binds := by
  match binds with
  | [] =>
    show ListRel _ (Moist.MIR.flattenAllBinds []) []
    unfold Moist.MIR.flattenAllBinds; exact True.intro
  | (v, e, er) :: rest =>
    show ListRel _ (Moist.MIR.flattenAllBinds ((v, e, er) :: rest)) ((v, e, er) :: rest)
    unfold Moist.MIR.flattenAllBinds
    exact ⟨⟨rfl, rfl, flattenAll_mirCtxRefines_bwd e⟩,
      flattenAllBinds_mirCtxRefines_bwd rest⟩
termination_by sizeOf binds

end

/-- **Full pipeline soundness** (unconditional): for any `e`,
    `anfNormalizeFlat e` is contextually equivalent to `e`.

    The pipeline is alpha-rename + core ANF + recursive `flattenAll`
    (the last two are unconditionally sound). Alpha-rename fires only
    when `fixCount e = 0`; for Fix-containing input the alpha-rename
    step is the identity. -/
theorem anfNormalizeFlat_sound (e : Expr) :
    MIRCtxEq e (Moist.MIR.anfNormalizeFlat e) := by
  -- Step 1: get the "renamed" intermediate, case-split on fixCount.
  -- In both branches, the renamed intermediate is `MIRCtxRefines`-equivalent
  -- to `e` in both directions.
  by_cases hFixFree : Moist.MIR.fixCount e = 0
  · -- Fix-free branch: alpha-rename fires and is sound.
    let K : Moist.MIR.FreshState := ⟨Moist.MIR.maxUidExpr e + 1⟩
    have hK : Moist.MIR.maxUidExpr e < K.next := Nat.lt_succ_self _
    let renamed : Expr := (Moist.MIR.alphaRenameTop e K).1
    let K_anf : Moist.MIR.FreshState := ⟨Moist.MIR.maxUidExpr renamed + 1⟩
    let normalized : Expr := (Moist.MIR.anfNormalizeCore renamed K_anf).1
    have halpha_fwd : MIRCtxRefines e renamed :=
      alphaRenameTop_mirCtxRefines_fwd e K hK hFixFree
    have halpha_bwd : MIRCtxRefines renamed e :=
      alphaRenameTop_mirCtxRefines_bwd e K hK hFixFree
    have h_renamed_fresh : FreshGt K_anf renamed := Nat.lt_succ_self _
    have ⟨hanf_fwd, hanf_bwd, _, _⟩ :=
      anfNormalizeCore_mirCtxRefines renamed K_anf h_renamed_fresh
    have h_alpha_anf_fwd : MIRCtxRefines e normalized :=
      mirCtxRefines_trans halpha_fwd hanf_fwd
    have h_alpha_anf_bwd : MIRCtxRefines normalized e :=
      mirCtxRefines_trans hanf_bwd halpha_bwd
    have h_flat_fwd := flattenAll_mirCtxRefines_fwd normalized
    have h_flat_bwd := flattenAll_mirCtxRefines_bwd normalized
    have hfwd : MIRCtxRefines e (Moist.MIR.flattenAll normalized) :=
      mirCtxRefines_trans h_alpha_anf_fwd h_flat_fwd
    have hbwd : MIRCtxRefines (Moist.MIR.flattenAll normalized) e :=
      mirCtxRefines_trans h_flat_bwd h_alpha_anf_bwd
    show MIRCtxEq e (Moist.MIR.anfNormalizeFlat e)
    unfold Moist.MIR.anfNormalizeFlat
    rw [if_pos hFixFree]
    exact mirCtxEq_of_mirCtxRefines_bidir hfwd hbwd
  · -- Fix-containing branch: alpha-rename is the identity (renamed := e).
    let K_anf : Moist.MIR.FreshState := ⟨Moist.MIR.maxUidExpr e + 1⟩
    let normalized : Expr := (Moist.MIR.anfNormalizeCore e K_anf).1
    have h_e_fresh : FreshGt K_anf e := Nat.lt_succ_self _
    have ⟨hanf_fwd, hanf_bwd, _, _⟩ :=
      anfNormalizeCore_mirCtxRefines e K_anf h_e_fresh
    have h_flat_fwd := flattenAll_mirCtxRefines_fwd normalized
    have h_flat_bwd := flattenAll_mirCtxRefines_bwd normalized
    have hfwd : MIRCtxRefines e (Moist.MIR.flattenAll normalized) :=
      mirCtxRefines_trans hanf_fwd h_flat_fwd
    have hbwd : MIRCtxRefines (Moist.MIR.flattenAll normalized) e :=
      mirCtxRefines_trans h_flat_bwd hanf_bwd
    show MIRCtxEq e (Moist.MIR.anfNormalizeFlat e)
    unfold Moist.MIR.anfNormalizeFlat
    rw [if_neg hFixFree]
    exact mirCtxEq_of_mirCtxRefines_bidir hfwd hbwd

/-- **Main `anfNormalize` soundness** (unconditional): the monadic
    pipeline wrapper is contextually equivalent to its input. This
    is the theorem clients in `Moist/MIR/Optimize.lean` rely on. -/
theorem anfNormalize_sound (e : Expr) (s : Moist.MIR.FreshState) :
    MIRCtxEq e (Moist.MIR.anfNormalize e s).1 := by
  -- `anfNormalize e s` unfolds to `(anfNormalizeFlat e, _)` at the result
  -- position; the state bookkeeping only affects the second projection.
  show MIRCtxEq e (Moist.MIR.anfNormalize e s).1
  have h_unfold : (Moist.MIR.anfNormalize e s).1 = Moist.MIR.anfNormalizeFlat e := rfl
  rw [h_unfold]
  exact anfNormalizeFlat_sound e

end Moist.Verified.MIR
