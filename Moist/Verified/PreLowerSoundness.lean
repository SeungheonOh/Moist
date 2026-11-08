import Moist.Verified.InlineSoundness
import Moist.Verified.BuiltinStateSoundness
import Moist.Verified.HygieneSoundness
import Moist.Verified.MIR.Hoist
import Moist.MIR.Optimize.Advanced

variable [sv : Moist.CEK.SemVariant]

/-! # Soundness of pre-lowering inline

`preLowerInlineExpr_refines : MIRCtxRefines e (preLowerInlineExpr e n)`.

Every substitution the pass performs is a UPLC beta reduction of the lowered
redex: capture-avoiding `subst` commutes with lowering whenever the fresh
counter is above every uid (`SubstCommute.subst_lower`), so the contractum
lowers to `substTerm 1 rhs body`. The gate of each substitution is one of the
frontier beta premises: a total pre-lowering value halts without error, a
recursive lambda halts, and anything else is used at the first evaluation
position. A dropped dead binding is a beta reduction whose body ignores the
bound variable.

`preLower_refines_of` lifts certificates of the two other stages to the whole
`Advanced.preLower` fixpoint loop. -/

namespace Moist.Verified.MIR.PreLower

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId FreshState subst lowerTotalExpr lowerTotal expandFix maxUidExpr maxUidExprList
   maxUidExprBinds isTotalPreLowerValue firstEvaluationUse freeVars freeVarsList freeVarsLet
   countOccurrences countOccurrencesList countOccurrencesLet VarSet)
open Moist.Verified (closedAt)
open Moist.Verified.Contextual (CtxRefines)
open Moist.Verified.Equivalence (ListRel)

/-! ## One substitution step -/

/-- Substituting `rhs` for `v` in `e` refines any expression that lowers to
    the redex `(λ. e) rhs`, provided the pass's gate accepted `rhs`. -/
theorem subst_redex_refines {src e rhs : Expr} {v : VarId} {s : FreshState}
    (shape : ∀ env, lowerTotalExpr env src =
      (do let tr ← lowerTotalExpr env rhs
          let tb ← lowerTotalExpr (v :: env) e
          some (.Apply (.Lam 0 tb) tr)))
    (freshE : maxUidExpr e < s.next) (freshR : maxUidExpr rhs < s.next)
    (freshV : v.uid < s.next)
    (gate : isTotalPreLowerValue rhs = true ∨ rhs.isValue = true ∨
      firstEvaluationUse v e = true) :
    MIRCtxRefines src (subst v rhs e s).1 := by
  intro env
  rw [shape env]
  cases hr : lowerTotalExpr env rhs with
  | none => exact ⟨by simp, trivial⟩
  | some tr =>
    cases hb : lowerTotalExpr (v :: env) e with
    | none => exact ⟨by simp, trivial⟩
    | some tb =>
      have hsub := Moist.Verified.InlineSoundness.SubstCommute.subst_lower tr hr e [] s tb
        ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), freshR, freshV⟩ freshE hb
      simp only [List.nil_append, List.length_nil, Nat.zero_add,
        Moist.Verified.BetaValueRefines.iterShift_zero] at hsub
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [hsub]
      refine ⟨fun _ => rfl, ?_⟩
      have hclosedR : closedAt env.length tr = true := lowerTotal_closedAt env _ tr hr
      have hclosedB : closedAt (env.length + 1) tb = true := by
        simpa using lowerTotal_closedAt (v :: env) _ tb hb
      by_cases htotal : isTotalPreLowerValue rhs = true
      · exact Moist.Verified.InlineSoundness.Frontier.beta_ctxRefines_of_halts hclosedB hclosedR
          fun ρ wellFormed _ =>
            Moist.Verified.BuiltinState.isTotalPreLowerValue_halts rhs env tr htotal hr ρ
              fun _ hn hnd =>
                let ⟨value, lookup, _⟩ :=
                  Moist.Verified.BetaValueRefines.envWellFormed_lookup _ wellFormed hn hnd
                ⟨value, lookup⟩
      by_cases hvalue : rhs.isValue = true
      · -- Values that are not total are recursive lambdas.
        have h_canon : ∃ body_l, tr = Moist.MIR.fixLamWrapUplc body_l := by
          cases rhs with
          | Fix f_id fix_body =>
            cases fix_body with
            | Lam x_id inner =>
              have := Moist.MIR.lowerTotalExpr_fix_lam_canonical env f_id x_id inner
              rw [hr] at this
              revert this
              cases lowerTotal _ (Moist.MIR.expandFix inner) with
              | none => simp
              | some bl => simp; intro h; exact ⟨bl, h⟩
            | _ => exfalso; revert hr; simp [lowerTotalExpr, Moist.MIR.expandFix, lowerTotal]
          | _ => simp_all [Moist.MIR.Expr.isValue, isTotalPreLowerValue, Moist.MIR.isPure]
        obtain ⟨body_l, rfl⟩ := h_canon
        exact Moist.Verified.InlineSoundness.Frontier.beta_ctxRefines_of_halts
          hclosedB hclosedR fun ρ _ _ =>
            Moist.Verified.InlineSoundness.SubstCommute.fixLamWrapUplc_halts body_l ρ
      have frontier : firstEvaluationUse v e = true := by
        rcases gate with h | h | h
        · exact absurd h htotal
        · exact absurd h hvalue
        · exact h
      have path := Moist.Verified.InlineSoundness.Frontier.firstEvaluationUse_lowerTotal v [] env
        (expandFix e) tb (by simpa [lowerTotalExpr] using hb)
        (Moist.Verified.InlineSoundness.Frontier.firstEvaluationUse_expandFix v e frontier) rfl
      exact Moist.Verified.InlineSoundness.Frontier.beta_evaluationPath_refines
        (by simpa using path) hclosedB hclosedR

/-! ## Dropping a dead binding -/

omit sv in
private theorem singleton_contains (x v : VarId) :
    (VarSet.singleton x).contains v = (x == v) := by
  simp [VarSet.singleton, VarSet.contains]

omit sv in
private theorem erase_not_contains {s : VarSet} {x v : VarId}
    (h : (x == v) = true ∨ s.contains v = false) : (s.erase x).contains v = false := by
  rcases h with h | h
  · exact VarSet.erase_self_not_contains _ _ _ h
  · exact VarSet.erase_not_contains_fwd _ _ _ h

mutual
  theorem not_free_of_count (v : VarId) : ∀ (e : Expr),
      countOccurrences v e = 0 → (freeVars e).contains v = false
    | .Var x, h => by
      simp only [countOccurrences] at h
      rw [freeVars, singleton_contains]
      cases hx : (x == v) <;> simp_all
    | .Lit _, _ | .Builtin _, _ | .Error, _ => by rw [freeVars]; rfl
    | .Lam x body, h => by
      simp only [countOccurrences] at h
      rw [freeVars]
      cases hx : (x == v)
      · simp only [hx] at h; exact erase_not_contains (.inr (not_free_of_count v body h))
      · exact erase_not_contains (.inl hx)
    | .Fix x body, h => by
      simp only [countOccurrences] at h
      rw [freeVars]
      cases hx : (x == v)
      · simp only [hx] at h; exact erase_not_contains (.inr (not_free_of_count v body h))
      · exact erase_not_contains (.inl hx)
    | .App f a, h => by
      simp only [countOccurrences] at h
      rw [freeVars]
      exact VarSet.union_not_contains_fwd _ _ _ (not_free_of_count v f (by omega))
        (not_free_of_count v a (by omega))
    | .Force e, h | .Delay e, h => by
      simp only [countOccurrences] at h
      rw [freeVars]; exact not_free_of_count v e h
    | .Constr _ args, h => by
      simp only [countOccurrences] at h
      rw [freeVars]; exact not_free_of_countList v args h
    | .Case scrut alts, h => by
      simp only [countOccurrences] at h
      rw [freeVars]
      exact VarSet.union_not_contains_fwd _ _ _ (not_free_of_count v scrut (by omega))
        (not_free_of_countList v alts (by omega))
    | .Let binds body, h => by
      simp only [countOccurrences] at h
      rw [freeVars]; exact not_free_of_countLet v binds body h
  termination_by e => sizeOf e

  theorem not_free_of_countList (v : VarId) : ∀ (es : List Expr),
      countOccurrencesList v es = 0 → (freeVarsList es).contains v = false
    | [], _ => by rw [freeVarsList]; rfl
    | e :: rest, h => by
      simp only [countOccurrencesList] at h
      rw [freeVarsList]
      exact VarSet.union_not_contains_fwd _ _ _ (not_free_of_count v e (by omega))
        (not_free_of_countList v rest (by omega))
  termination_by es => sizeOf es

  theorem not_free_of_countLet (v : VarId) : ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      countOccurrencesLet v binds body = 0 → (freeVarsLet binds body).contains v = false
    | [], body, h => by
      simp only [countOccurrencesLet] at h
      rw [freeVarsLet]; exact not_free_of_count v body h
    | (x, rhs, _) :: rest, body, h => by
      simp only [countOccurrencesLet] at h
      rw [freeVarsLet]
      cases hx : (x == v)
      · simp only [hx] at h
        exact VarSet.union_not_contains_fwd _ _ _ (not_free_of_count v rhs (by simp at h; omega))
          (erase_not_contains (.inr (not_free_of_countLet v rest body (by simp at h; omega))))
      · simp only [hx] at h
        exact VarSet.union_not_contains_fwd _ _ _ (not_free_of_count v rhs h)
          (erase_not_contains (.inl hx))
  termination_by binds body => sizeOf binds + sizeOf body
end

/-- Dropping a total right-hand side whose binder is unused: the redex
    `(λ. ↑t) rhs` reduces to `t`. -/
theorem drop_redex_refines {src e rhs : Expr} {v : VarId}
    (shape : ∀ env, lowerTotalExpr env src =
      (do let tr ← lowerTotalExpr env rhs
          let tb ← lowerTotalExpr (v :: env) e
          some (.Apply (.Lam 0 tb) tr)))
    (unused : (freeVars e).contains v = false)
    (total : isTotalPreLowerValue rhs = true) :
    MIRCtxRefines src e := by
  intro env
  rw [shape env, lowerTotalExpr_prepend_unused env v e unused]
  cases hr : lowerTotalExpr env rhs with
  | none => exact ⟨by simp, trivial⟩
  | some tr =>
    cases he : lowerTotalExpr env e with
    | none => exact ⟨by simp, trivial⟩
    | some t =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some]
      refine ⟨fun _ => rfl, ?_⟩
      have hclosedR : closedAt env.length tr = true := lowerTotal_closedAt env _ tr hr
      have hshift : lowerTotalExpr (v :: env) e =
          some (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t) := by
        rw [lowerTotalExpr_prepend_unused env v e unused, he]; rfl
      have hclosedB : closedAt (env.length + 1)
          (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t) = true := by
        simpa using lowerTotal_closedAt (v :: env) _ _ hshift
      have beta := Moist.Verified.InlineSoundness.Frontier.beta_ctxRefines_of_halts hclosedB hclosedR
          fun ρ wellFormed _ =>
            Moist.Verified.BuiltinState.isTotalPreLowerValue_halts rhs env tr total hr ρ
              fun _ hn hnd =>
                let ⟨value, lookup, _⟩ :=
                  Moist.Verified.BetaValueRefines.envWellFormed_lookup _ wellFormed hn hnd
                ⟨value, lookup⟩
      rwa [Moist.Verified.InlineSoundness.SubstCommute.substTerm_shift_cancel 1 tr (by omega)] at beta

/-! ## Redex shapes -/

omit sv in
theorem let_cons_shape (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
      (do let tr ← lowerTotalExpr env rhs
          let tb ← lowerTotalExpr (v :: env) (.Let rest body)
          some (.Apply (.Lam 0 tb) tr)) :=
  Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons env v rhs er rest body

omit sv in
theorem app_lam_shape (v : VarId) (body x : Expr) (env : List VarId) :
    lowerTotalExpr env (.App (.Lam v body) x) =
      (do let tr ← lowerTotalExpr env x
          let tb ← lowerTotalExpr (v :: env) body
          some (.Apply (.Lam 0 tb) tr)) := by
  rw [lowerTotalExpr_app, lowerTotalExpr_lam]
  cases lowerTotalExpr env x <;> cases lowerTotalExpr (v :: env) body <;> rfl

/-! ## Bookkeeping -/

omit sv in
theorem flattenLet_spec : ∀ e : Expr,
    (∀ env, lowerTotalExpr env (Moist.MIR.flattenLet e) = lowerTotalExpr env e) ∧
      maxUidExpr (Moist.MIR.flattenLet e) ≤ maxUidExpr e
  | .Let [] body => by
    rw [Moist.MIR.flattenLet]
    obtain ⟨ih₁, ih₂⟩ := flattenLet_spec body
    refine ⟨fun env => by rw [ih₁, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_nil], ?_⟩
    simp only [maxUidExpr, maxUidExprBinds]; omega
  | .Let (b :: bs) body => ⟨fun _ => rfl, Nat.le_refl _⟩
  | .Var _ | .Lit _ | .Builtin _ | .Error | .Lam _ _ | .Fix _ _ | .App _ _ | .Force _
  | .Delay _ | .Constr _ _ | .Case _ _ => ⟨fun _ => rfl, Nat.le_refl _⟩

theorem flattenLet_refines (e : Expr) : MIRCtxRefines e (Moist.MIR.flattenLet e) :=
  mirCtxRefines_of_lowerEq fun env => ((flattenLet_spec e).1 env).symm

omit sv in
theorem maxUidExprBinds_append : ∀ (a b : List (VarId × Expr × Bool)),
    maxUidExprBinds (a ++ b) = max (maxUidExprBinds a) (maxUidExprBinds b)
  | [], b => by simp [maxUidExprBinds]
  | (x, e, er) :: a, b => by
    simp only [List.cons_append, maxUidExprBinds, maxUidExprBinds_append a b]; omega

omit sv in
theorem maxUid_let_append (a b : List (VarId × Expr × Bool)) (body : Expr) :
    maxUidExpr (.Let (a ++ b) body) = max (maxUidExprBinds a) (maxUidExpr (.Let b body)) := by
  simp only [maxUidExpr, maxUidExprBinds_append]; omega

omit sv in
theorem lowerTotalExpr_let_split (env : List VarId)
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) =
    lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) := by
  induction binds₁ generalizing env with
  | nil => simp [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  | cons b rest ih =>
    obtain ⟨y, rhs, er⟩ := b
    rw [List.cons_append, Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons,
      Moist.Verified.InlineSoundness.Rename.lowerTotalExpr_let_cons, ih]

theorem let_split_refines (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let (binds₁ ++ binds₂) body) (.Let binds₁ (.Let binds₂ body)) :=
  mirCtxRefines_of_lowerEq fun env => lowerTotalExpr_let_split env binds₁ binds₂ body

theorem let_unsplit_refines (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let binds₁ (.Let binds₂ body)) (.Let (binds₁ ++ binds₂) body) :=
  mirCtxRefines_of_lowerEq fun env => (lowerTotalExpr_let_split env binds₁ binds₂ body).symm

theorem preLowerKeep_spec (acc : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let acc.reverse body) (Moist.MIR.preLowerKeep acc body) ∧
      maxUidExpr (Moist.MIR.preLowerKeep acc body) ≤
        max (maxUidExprBinds acc.reverse) (maxUidExpr body) := by
  unfold Moist.MIR.preLowerKeep
  generalize acc.reverse = kept
  cases kept with
  | nil => exact ⟨mirCtxRefines_let_nil, Nat.le_max_right _ _⟩
  | cons b bs => exact ⟨mirCtxRefines_refl _, by simp only [maxUidExpr]; omega⟩

omit sv in
theorem isTotal_of_atom {e : Expr} (h : e.isAtom = true) : isTotalPreLowerValue e = true := by
  cases e <;> simp_all [Moist.MIR.Expr.isAtom, isTotalPreLowerValue, Moist.MIR.isPure]

theorem usesInScope_unused {v : VarId} {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : Moist.MIR.usesInScope v rest body = 0) : (freeVars (.Let rest body)).contains v = false := by
  cases rest with
  | nil =>
    simp only [Moist.MIR.usesInScope] at h
    rw [freeVars, freeVarsLet]; exact not_free_of_count v body h
  | cons b bs =>
    simp only [Moist.MIR.usesInScope] at h
    exact not_free_of_count v _ h

/-! ## Equations of the pass -/

section Equations
variable (p : Expr → Moist.MIR.FreshM Expr) (s : FreshState)

omit sv in
theorem preLowerList_nil : Moist.MIR.preLowerList p [] s = ([], s) := rfl

omit sv in
theorem preLowerList_cons (e : Expr) (rest : List Expr) :
    Moist.MIR.preLowerList p (e :: rest) s =
      ((p e s).1 :: (Moist.MIR.preLowerList p rest (p e s).2).1,
        (Moist.MIR.preLowerList p rest (p e s).2).2) := rfl

omit sv in
theorem preLowerLet_nil (acc : List (VarId × Expr × Bool)) (body : Expr) :
    Moist.MIR.preLowerLet p [] acc body s =
      (Moist.MIR.preLowerKeep acc (p body s).1, (p body s).2) := rfl

omit sv in
theorem preLowerLet_cons (v : VarId) (rhs : Expr) (er : Bool)
    (rest acc : List (VarId × Expr × Bool)) (body : Expr) (rhs' : Expr) (s₁ : FreshState)
    (h : p rhs s = (rhs', s₁)) :
    Moist.MIR.preLowerLet p ((v, rhs, er) :: rest) acc body s =
      if rhs'.isAtom then
        (Moist.MIR.preLowerKeep acc
          (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
            (subst v rhs' (.Let rest body) s₁).2).1,
          (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
            (subst v rhs' (.Let rest body) s₁).2).2)
      else if Moist.MIR.usesInScope v rest body == 0 && isTotalPreLowerValue rhs' then
        Moist.MIR.preLowerLet p rest acc body s₁
      else if Moist.MIR.usesInScope v rest body == 1 &&
          (rhs'.isValue || isTotalPreLowerValue rhs' || firstEvaluationUse v (.Let rest body)) then
        (Moist.MIR.preLowerKeep acc
          (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
            (subst v rhs' (.Let rest body) s₁).2).1,
          (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
            (subst v rhs' (.Let rest body) s₁).2).2)
      else
        Moist.MIR.preLowerLet p rest ((v, rhs', er) :: acc) body s₁ := by
  show (Moist.MIR.preLowerLet p ((v, rhs, er) :: rest) acc body) s = _
  rw [Moist.MIR.preLowerLet]
  simp only [bind, StateT.bind, h]
  cases rhs'.isAtom <;>
    cases (Moist.MIR.usesInScope v rest body == 0 && isTotalPreLowerValue rhs') <;>
    cases (Moist.MIR.usesInScope v rest body == 1 &&
      (rhs'.isValue || isTotalPreLowerValue rhs' || firstEvaluationUse v (.Let rest body))) <;>
    simp only [Bool.false_eq_true, ite_true, ite_false] <;> rfl


omit sv in
theorem preLowerBeta_cases (f x : Expr) :
    Moist.MIR.preLowerBeta p f x s = (.App f x, s) ∨
    ∃ param body, f = .Lam param body ∧
      (isTotalPreLowerValue x = true ∨ x.isValue = true ∨ firstEvaluationUse param body = true) ∧
      Moist.MIR.preLowerBeta p f x s = p (subst param x body s).1 (subst param x body s).2 := by
  cases f with
  | Lam param body =>
    show (Moist.MIR.preLowerBeta p (.Lam param body) x) s = _ ∨ _
    unfold Moist.MIR.preLowerBeta
    simp only [bind, pure]
    split
    · split
      · exact .inl rfl
      · split
        · exact .inl rfl
        · rename_i h1 h2 h3
          refine .inr ⟨param, body, rfl, ?_, rfl⟩
          revert h1 h2 h3
          cases isTotalPreLowerValue x <;> cases x.isValue <;>
            cases firstEvaluationUse param body <;> simp <;> omega
    · exact .inl rfl
  | _ => exact .inl rfl

end Equations

/-! ## Soundness of the traversal -/

/-- A fresh-name computation that refines its input and keeps every uid
    below the counter. -/
def Sound (p : Expr → Moist.MIR.FreshM Expr) : Prop :=
  ∀ e s, maxUidExpr e < s.next →
    MIRCtxRefines e (p e s).1 ∧ maxUidExpr (p e s).1 < (p e s).2.next ∧ s.next ≤ (p e s).2.next

open Moist.Verified.InlineSoundness.SubstCommute (subst_fresh)
open Moist.Verified.InlineSoundness.Rename (maxUid_let_cons maxUid_list_cons)

theorem preLowerList_sound {p : Expr → Moist.MIR.FreshM Expr} (hp : Sound p) :
    ∀ (es : List Expr) (s : FreshState), maxUidExprList es < s.next →
      ListRel MIRCtxRefines es (Moist.MIR.preLowerList p es s).1 ∧
        maxUidExprList (Moist.MIR.preLowerList p es s).1 < (Moist.MIR.preLowerList p es s).2.next ∧
        s.next ≤ (Moist.MIR.preLowerList p es s).2.next
  | [], s, h => by rw [preLowerList_nil]; exact ⟨trivial, h, Nat.le_refl _⟩
  | e :: rest, s, h => by
    rw [preLowerList_cons]
    dsimp only
    rw [maxUid_list_cons] at h
    obtain ⟨r₁, f₁, l₁⟩ := hp e s (by omega)
    obtain ⟨r₂, f₂, l₂⟩ := preLowerList_sound hp rest (p e s).2 (by omega)
    exact ⟨⟨r₁, r₂⟩, by rw [maxUid_list_cons]; omega, by omega⟩

theorem preLowerBeta_sound {p : Expr → Moist.MIR.FreshM Expr} (hp : Sound p) (f x : Expr)
    (s : FreshState) (ff : maxUidExpr f < s.next) (fx : maxUidExpr x < s.next) :
    MIRCtxRefines (.App f x) (Moist.MIR.preLowerBeta p f x s).1 ∧
      maxUidExpr (Moist.MIR.preLowerBeta p f x s).1 < (Moist.MIR.preLowerBeta p f x s).2.next ∧
      s.next ≤ (Moist.MIR.preLowerBeta p f x s).2.next := by
  rcases preLowerBeta_cases p s f x with h | ⟨param, body, rfl, gate, h⟩
  · rw [h]; exact ⟨mirCtxRefines_refl _, by simp only [maxUidExpr]; omega, Nat.le_refl _⟩
  · rw [h]
    simp only [maxUidExpr] at ff
    obtain ⟨fs, ls⟩ := subst_fresh param x body s (by omega) fx
    obtain ⟨r, f', l'⟩ := hp _ _ fs
    exact ⟨mirCtxRefines_trans
      (subst_redex_refines (app_lam_shape param body x) (by omega) fx (by omega) gate) r,
      f', by omega⟩

theorem preLowerLet_sound {p : Expr → Moist.MIR.FreshM Expr} (hp : Sound p) :
    ∀ (binds acc : List (VarId × Expr × Bool)) (body : Expr) (s : FreshState),
      maxUidExpr (.Let (acc.reverse ++ binds) body) < s.next →
      MIRCtxRefines (.Let (acc.reverse ++ binds) body) (Moist.MIR.preLowerLet p binds acc body s).1 ∧
        maxUidExpr (Moist.MIR.preLowerLet p binds acc body s).1 <
          (Moist.MIR.preLowerLet p binds acc body s).2.next ∧
        s.next ≤ (Moist.MIR.preLowerLet p binds acc body s).2.next
  | [], acc, body, s, fresh => by
    rw [preLowerLet_nil, List.append_nil]
    dsimp only
    simp only [List.append_nil, maxUidExpr] at fresh
    obtain ⟨r, f', l'⟩ := hp body s (by omega)
    obtain ⟨kr, kf⟩ := preLowerKeep_spec acc (p body s).1
    exact ⟨mirCtxRefines_trans (mirCtxRefines_let_body r) kr, by omega, l'⟩
  | (v, rhs, er) :: rest, acc, body, s, fresh => by
    rw [maxUid_let_append, maxUid_let_cons] at fresh
    obtain ⟨rr, rf, rl⟩ := hp rhs s (by omega)
    generalize hres : p rhs s = res at rr rf rl
    obtain ⟨rhs', s₁⟩ := res
    simp only at rr rf rl
    rw [preLowerLet_cons p s v rhs er rest acc body rhs' s₁ hres]
    have stepA : MIRCtxRefines (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
        (.Let acc.reverse (.Let ((v, rhs', er) :: rest) body)) :=
      mirCtxRefines_trans (let_split_refines _ _ _)
        (mirCtxRefines_let_body (mirCtxRefines_let_rhs_head rr))
    have freshScope : maxUidExpr (.Let rest body) < s₁.next := by omega
    have substBranch : (isTotalPreLowerValue rhs' = true ∨ rhs'.isValue = true ∨
        firstEvaluationUse v (.Let rest body) = true) →
        MIRCtxRefines (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
          (Moist.MIR.preLowerKeep acc
            (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
              (subst v rhs' (.Let rest body) s₁).2).1) ∧
        maxUidExpr (Moist.MIR.preLowerKeep acc
            (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
              (subst v rhs' (.Let rest body) s₁).2).1) <
          (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
            (subst v rhs' (.Let rest body) s₁).2).2.next ∧
        s.next ≤ (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
            (subst v rhs' (.Let rest body) s₁).2).2.next := by
      intro gate
      obtain ⟨fs, ls⟩ := subst_fresh v rhs' (.Let rest body) s₁ freshScope rf
      have ff := (flattenLet_spec (subst v rhs' (.Let rest body) s₁).1).2
      obtain ⟨r, f', l'⟩ := hp (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
        (subst v rhs' (.Let rest body) s₁).2 (by omega)
      obtain ⟨kr, kf⟩ := preLowerKeep_spec acc
        (p (Moist.MIR.flattenLet (subst v rhs' (.Let rest body) s₁).1)
          (subst v rhs' (.Let rest body) s₁).2).1
      refine ⟨?_, by omega, by omega⟩
      exact mirCtxRefines_trans stepA (mirCtxRefines_trans
        (mirCtxRefines_let_body (subst_redex_refines (let_cons_shape v rhs' er rest body)
          freshScope rf (by omega) gate))
        (mirCtxRefines_trans (mirCtxRefines_let_body (flattenLet_refines _))
          (mirCtxRefines_trans (mirCtxRefines_let_body r) kr)))
    split
    · rename_i hatom
      exact substBranch (.inl (isTotal_of_atom hatom))
    split
    · rename_i hdrop
      simp only [Bool.and_eq_true, beq_iff_eq] at hdrop
      obtain ⟨ih, ihf, ihl⟩ := preLowerLet_sound hp rest acc body s₁
        (by rw [maxUid_let_append]; omega)
      refine ⟨?_, ihf, by omega⟩
      exact mirCtxRefines_trans stepA (mirCtxRefines_trans
        (mirCtxRefines_let_body (drop_redex_refines (let_cons_shape v rhs' er rest body)
          (usesInScope_unused hdrop.1) hdrop.2))
        (mirCtxRefines_trans (let_unsplit_refines _ _ _) ih))
    split
    · rename_i hsub
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hsub
      rcases hsub.2 with (h | h) | h
      · exact substBranch (.inr (.inl h))
      · exact substBranch (.inl h)
      · exact substBranch (.inr (.inr h))
    · have hshape : acc.reverse ++ (v, rhs', er) :: rest = ((v, rhs', er) :: acc).reverse ++ rest := by
        simp
      obtain ⟨ih, ihf, ihl⟩ := preLowerLet_sound hp rest ((v, rhs', er) :: acc) body s₁
        (by rw [← hshape, maxUid_let_append, maxUid_let_cons]; omega)
      refine ⟨?_, ihf, by omega⟩
      rw [← hshape] at ih
      exact mirCtxRefines_trans stepA (mirCtxRefines_trans (let_unsplit_refines _ _ _) ih)

section FuelEquations
variable (n : Nat) (s : FreshState)

omit sv in
theorem fuel_lam (x : VarId) (b : Expr) : Moist.MIR.preLowerInlineFuel (n + 1) (.Lam x b) s =
    (.Lam x (Moist.MIR.preLowerInlineFuel n b s).1, (Moist.MIR.preLowerInlineFuel n b s).2) := rfl

omit sv in
theorem fuel_fix (f : VarId) (b : Expr) : Moist.MIR.preLowerInlineFuel (n + 1) (.Fix f b) s =
    (.Fix f (Moist.MIR.preLowerInlineFuel n b s).1, (Moist.MIR.preLowerInlineFuel n b s).2) := rfl

omit sv in
theorem fuel_force (b : Expr) : Moist.MIR.preLowerInlineFuel (n + 1) (.Force b) s =
    (.Force (Moist.MIR.preLowerInlineFuel n b s).1, (Moist.MIR.preLowerInlineFuel n b s).2) := rfl

omit sv in
theorem fuel_delay (b : Expr) : Moist.MIR.preLowerInlineFuel (n + 1) (.Delay b) s =
    (.Delay (Moist.MIR.preLowerInlineFuel n b s).1, (Moist.MIR.preLowerInlineFuel n b s).2) := rfl

omit sv in
theorem fuel_app (f x : Expr) : Moist.MIR.preLowerInlineFuel (n + 1) (.App f x) s =
    Moist.MIR.preLowerBeta (Moist.MIR.preLowerInlineFuel n)
      (Moist.MIR.preLowerInlineFuel n f s).1
      (Moist.MIR.preLowerInlineFuel n x (Moist.MIR.preLowerInlineFuel n f s).2).1
      (Moist.MIR.preLowerInlineFuel n x (Moist.MIR.preLowerInlineFuel n f s).2).2 := rfl

omit sv in
theorem fuel_constr (tag : Nat) (args : List Expr) :
    Moist.MIR.preLowerInlineFuel (n + 1) (.Constr tag args) s =
      (.Constr tag (Moist.MIR.preLowerList (Moist.MIR.preLowerInlineFuel n) args s).1,
        (Moist.MIR.preLowerList (Moist.MIR.preLowerInlineFuel n) args s).2) := rfl

omit sv in
theorem fuel_case (scrut : Expr) (alts : List Expr) :
    Moist.MIR.preLowerInlineFuel (n + 1) (.Case scrut alts) s =
      (.Case (Moist.MIR.preLowerInlineFuel n scrut s).1
        (Moist.MIR.preLowerList (Moist.MIR.preLowerInlineFuel n) alts
          (Moist.MIR.preLowerInlineFuel n scrut s).2).1,
        (Moist.MIR.preLowerList (Moist.MIR.preLowerInlineFuel n) alts
          (Moist.MIR.preLowerInlineFuel n scrut s).2).2) := rfl

omit sv in
theorem fuel_let (binds : List (VarId × Expr × Bool)) (body : Expr) :
    Moist.MIR.preLowerInlineFuel (n + 1) (.Let binds body) s =
      Moist.MIR.preLowerLet (Moist.MIR.preLowerInlineFuel n) binds [] body s := rfl

end FuelEquations

theorem preLowerInlineFuel_sound : ∀ n, Sound (Moist.MIR.preLowerInlineFuel n)
  | 0 => fun _ _ h => ⟨mirCtxRefines_refl _, h, Nat.le_refl _⟩
  | n + 1 => by
    have ih := preLowerInlineFuel_sound n
    intro e s fresh
    cases e with
    | Var _ | Lit _ | Builtin _ | Error => exact ⟨mirCtxRefines_refl _, fresh, Nat.le_refl _⟩
    | Lam x body =>
      rw [fuel_lam]
      simp only [maxUidExpr] at fresh ⊢
      obtain ⟨r, f', l'⟩ := ih body s (by omega)
      exact ⟨mirCtxRefines_lam r, by omega, l'⟩
    | Fix f body =>
      rw [fuel_fix]
      simp only [maxUidExpr] at fresh ⊢
      obtain ⟨r, f', l'⟩ := ih body s (by omega)
      refine ⟨?_, by omega, l'⟩
      cases body with
      | Lam x inner =>
        cases n with
        | zero => exact mirCtxRefines_refl _
        | succ m =>
          rw [fuel_lam]
          simp only [maxUidExpr] at fresh
          exact mirCtxRefines_fix_lam (preLowerInlineFuel_sound m inner s (by omega)).1
      | _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; simp)
    | App f x =>
      rw [fuel_app]
      simp only [maxUidExpr] at fresh
      obtain ⟨rf, ff, lf⟩ := ih f s (by omega)
      obtain ⟨rx, fx, lx⟩ := ih x (Moist.MIR.preLowerInlineFuel n f s).2 (by omega)
      obtain ⟨rb, fb, lb⟩ := preLowerBeta_sound ih (Moist.MIR.preLowerInlineFuel n f s).1
        (Moist.MIR.preLowerInlineFuel n x (Moist.MIR.preLowerInlineFuel n f s).2).1
        (Moist.MIR.preLowerInlineFuel n x (Moist.MIR.preLowerInlineFuel n f s).2).2 (by omega) fx
      exact ⟨mirCtxRefines_trans (mirCtxRefines_app rf rx) rb, fb, by omega⟩
    | Force body =>
      rw [fuel_force]
      simp only [maxUidExpr] at fresh ⊢
      obtain ⟨r, f', l'⟩ := ih body s fresh
      exact ⟨mirCtxRefines_force r, f', l'⟩
    | Delay body =>
      rw [fuel_delay]
      simp only [maxUidExpr] at fresh ⊢
      obtain ⟨r, f', l'⟩ := ih body s fresh
      exact ⟨mirCtxRefines_delay r, f', l'⟩
    | Constr tag args =>
      rw [fuel_constr]
      simp only [maxUidExpr] at fresh ⊢
      obtain ⟨r, f', l'⟩ := preLowerList_sound ih args s fresh
      refine ⟨?_, f', l'⟩
      cases args with
      | nil => rw [preLowerList_nil]; exact mirCtxRefines_refl _
      | cons a as =>
        rw [preLowerList_cons] at r ⊢
        exact mirCtxRefines_constr r.1 r.2
    | Case scrut alts =>
      rw [fuel_case]
      simp only [maxUidExpr] at fresh ⊢
      obtain ⟨rs, fs, ls⟩ := ih scrut s (by omega)
      obtain ⟨ra, fa, la⟩ := preLowerList_sound ih alts (Moist.MIR.preLowerInlineFuel n scrut s).2
        (by omega)
      exact ⟨mirCtxRefines_case rs ra, by omega, by omega⟩
    | Let binds body =>
      rw [fuel_let]
      have := preLowerLet_sound ih binds [] body s (by simpa using fresh)
      simpa only [List.reverse_nil, List.nil_append] using this

/-! ## The pass -/

theorem preLowerInline_refines (e : Expr) (s : FreshState) (fresh : maxUidExpr e < s.next) :
    MIRCtxRefines e (Moist.MIR.preLowerInline e s).1 :=
  (preLowerInlineFuel_sound _ e s fresh).1

theorem preLowerInlineExpr_refines (e : Expr) (n : Nat) :
    MIRCtxRefines e (Moist.MIR.preLowerInlineExpr e n) :=
  mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
    (preLowerInline_refines _ ⟨max n (maxUidExpr (Moist.MIR.uniqueOptimizationBinders e) + 1)⟩
      (by show _ < max _ _; omega))

/-! ## The `Advanced.preLower` fixpoint loop -/

section Loop
variable (hsimp : ∀ e, MIRCtxRefines e (Moist.MIR.Advanced.simplify e))
  (hcase : ∀ e, MIRCtxRefines e (Moist.MIR.caseMergePass e).1)
include hsimp hcase

theorem preLower_step_refines_of (e : Expr) :
    MIRCtxRefines e
      (Moist.MIR.preLowerInlineExpr (Moist.MIR.caseMergePass (Moist.MIR.Advanced.simplify e)).1) :=
  mirCtxRefines_trans (hsimp e) (mirCtxRefines_trans (hcase _) (preLowerInlineExpr_refines _ _))

theorem preLower_go_refines_of :
    ∀ (fuel : Nat) (e : Expr), MIRCtxRefines e (Moist.MIR.Advanced.preLower.go fuel e)
  | 0, e => by rw [Moist.MIR.Advanced.preLower.go]; exact mirCtxRefines_refl e
  | fuel + 1, e => by
    rw [Moist.MIR.Advanced.preLower.go]
    split
    · exact preLower_step_refines_of hsimp hcase e
    · exact mirCtxRefines_trans (preLower_step_refines_of hsimp hcase e)
        (preLower_go_refines_of fuel _)

theorem preLower_refines_of (e : Expr) : MIRCtxRefines e (Moist.MIR.Advanced.preLower e) :=
  preLower_go_refines_of hsimp hcase 4 e

end Loop

end Moist.Verified.MIR.PreLower
