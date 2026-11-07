import Moist.Verified.InlineSoundness.Rename
import Moist.Verified.BetaValueRefines

/-! # Substitution commutes with lowering

MIR `subst v rhs` followed by lowering equals lowering with `v` bound and
then substituting the lowered `rhs` at `v`'s de Bruijn position. The only
hypotheses are that `v` and the free variables of `rhs` are not shadowed by
the binders already passed, and that the fresh-name counter exceeds every
uid involved, so the capture-avoiding renamings of `subst` pick names that
are invisible to lowering. -/

namespace Moist.Verified.InlineSoundness.SubstCommute

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (substTerm substTermList renameTerm renameTermList shiftRename)
open Moist.Verified.BetaValueRefines (iterShift iterShift_zero iterShift_succ)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list)
open Moist.Verified.InlineSoundness.Rename

/-! ## The equations of `subst` -/

/-- The binder, body and state `subst` continues with under a binder `x`
    that differs from the substituted variable: a fresh name when `x` would
    capture a free variable of the replacement. -/
def binderStep (repl : Expr) (x : VarId) (body : Expr) (s : FreshState) :
    VarId × Expr × FreshState :=
  if (freeVars repl).contains x then
    (⟨s.next, .gen, x.hint⟩, rename x ⟨s.next, .gen, x.hint⟩ body, ⟨s.next + 1⟩)
  else (x, body, s)

/-- `binderStep` for a let binder, whose scope is the remaining bindings and body. -/
def binderStepLet (repl : Expr) (x : VarId) (rest : List (VarId × Expr × Bool)) (body : Expr)
    (s : FreshState) : VarId × (List (VarId × Expr × Bool) × Expr) × FreshState :=
  if (freeVars repl).contains x then
    (⟨s.next, .gen, x.hint⟩, renameLet x ⟨s.next, .gen, x.hint⟩ rest body, ⟨s.next + 1⟩)
  else (x, (rest, body), s)

theorem binderStepLet_eq (repl : Expr) (x : VarId) (rest : List (VarId × Expr × Bool))
    (body : Expr) (s : FreshState) :
    binderStep repl x (.Let rest body) s =
      ((binderStepLet repl x rest body s).1,
        .Let (binderStepLet repl x rest body s).2.1.1 (binderStepLet repl x rest body s).2.1.2,
        (binderStepLet repl x rest body s).2.2) := by
  unfold binderStep binderStepLet
  split <;> simp [rename]

section Equations

variable (v : VarId) (r : Expr) (s : FreshState)

theorem subst_var (x : VarId) : subst v r (.Var x) s = (if x == v then r else .Var x, s) := by
  rw [subst]; rfl

theorem subst_lit (c) : subst v r (.Lit c) s = (.Lit c, s) := by rw [subst]; rfl
theorem subst_builtin (b) : subst v r (.Builtin b) s = (.Builtin b, s) := by rw [subst]; rfl
theorem subst_error : subst v r .Error s = (.Error, s) := by rw [subst]; rfl

theorem subst_app (f a : Expr) : subst v r (.App f a) s =
    (.App (subst v r f s).1 (subst v r a (subst v r f s).2).1, (subst v r a (subst v r f s).2).2) := by
  rw [subst]; rfl

theorem subst_force (e : Expr) : subst v r (.Force e) s = (.Force (subst v r e s).1, (subst v r e s).2) := by
  rw [subst]; rfl

theorem subst_delay (e : Expr) : subst v r (.Delay e) s = (.Delay (subst v r e s).1, (subst v r e s).2) := by
  rw [subst]; rfl

theorem subst_constr (tag : Nat) (args : List Expr) : subst v r (.Constr tag args) s =
    (.Constr tag (substList v r args s).1, (substList v r args s).2) := by
  rw [subst]; rfl

theorem subst_case (scrut : Expr) (alts : List Expr) : subst v r (.Case scrut alts) s =
    (.Case (subst v r scrut s).1 (substList v r alts (subst v r scrut s).2).1,
      (substList v r alts (subst v r scrut s).2).2) := by
  rw [subst]; rfl

theorem subst_let (binds : List (VarId × Expr × Bool)) (body : Expr) : subst v r (.Let binds body) s =
    (.Let (substLet v r (freeVars r) binds body s).1.1 (substLet v r (freeVars r) binds body s).1.2,
      (substLet v r (freeVars r) binds body s).2) := by
  rw [subst]; rfl

theorem subst_lam_shadow (x : VarId) (b : Expr) (h : (x == v) = true) :
    subst v r (.Lam x b) s = (.Lam x b, s) := by
  rw [subst]; simp only [h]; rfl

theorem subst_lam (x : VarId) (b : Expr) (h : (x == v) = false) :
    subst v r (.Lam x b) s =
      (.Lam (binderStep r x b s).1 (subst v r (binderStep r x b s).2.1 (binderStep r x b s).2.2).1,
        (subst v r (binderStep r x b s).2.1 (binderStep r x b s).2.2).2) := by
  rw [subst]; simp only [h, Bool.false_eq_true, ↓reduceIte, binderStep]; split <;> rfl

theorem subst_fix_shadow (f : VarId) (b : Expr) (h : (f == v) = true) :
    subst v r (.Fix f b) s = (.Fix f b, s) := by
  rw [subst]; simp only [h]; rfl

theorem subst_fix (f : VarId) (b : Expr) (h : (f == v) = false) :
    subst v r (.Fix f b) s =
      (.Fix (binderStep r f b s).1 (subst v r (binderStep r f b s).2.1 (binderStep r f b s).2.2).1,
        (subst v r (binderStep r f b s).2.1 (binderStep r f b s).2.2).2) := by
  rw [subst]; simp only [h, Bool.false_eq_true, ↓reduceIte, binderStep]; split <;> rfl

theorem substList_nil : substList v r [] s = ([], s) := by rw [substList]; rfl

theorem substList_cons (e : Expr) (es : List Expr) : substList v r (e :: es) s =
    ((subst v r e s).1 :: (substList v r es (subst v r e s).2).1,
      (substList v r es (subst v r e s).2).2) := by
  rw [substList]; rfl

theorem substLet_nil (body : Expr) : substLet v r (freeVars r) [] body s =
    (([], (subst v r body s).1), (subst v r body s).2) := by
  rw [substLet]; rfl

theorem substLet_shadow (x : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) (h : (x == v) = true) : substLet v r (freeVars r) ((x, rhs, er) :: rest) body s =
    (((x, (subst v r rhs s).1, er) :: rest, body), (subst v r rhs s).2) := by
  rw [substLet]; simp only [h]; rfl

theorem substLet_cons (x : VarId) (rhs : Expr) (er : Bool) (rest : List (VarId × Expr × Bool))
    (body : Expr) (h : (x == v) = false) :
    substLet v r (freeVars r) ((x, rhs, er) :: rest) body s =
      let p := subst v r rhs s
      let st := binderStepLet r x rest body p.2
      let q := substLet v r (freeVars r) st.2.1.1 st.2.1.2 st.2.2
      (((st.1, p.1, er) :: q.1.1, q.1.2), q.2) := by
  rw [substLet]; simp only [h, Bool.false_eq_true, ↓reduceIte, binderStepLet]; split <;> rfl

end Equations

/-! ## Freshness of the binder step -/

private theorem uid_lt_of_beq_false {a : VarId} {n : Nat} (h : a.uid < n) (b : VarId) (hb : b.uid = n) :
    (a == b) = false :=
  (VarId.beq_false_iff a b).mpr (.inr (by omega))

mutual
  theorem maxUid_rename (x x' : VarId) :
      ∀ (e : Expr), maxUidExpr (rename x x' e) ≤ max (maxUidExpr e) x'.uid
    | .Var z => by simp only [rename]; split <;> simp only [maxUidExpr] <;> omega
    | .Lit _ | .Builtin _ | .Error => by simp [rename, maxUidExpr]
    | .Lam y b => by
      have := maxUid_rename x x' b
      simp only [rename]; split <;> simp only [maxUidExpr] <;> omega
    | .Fix f b => by
      have := maxUid_rename x x' b
      simp only [rename]; split <;> simp only [maxUidExpr] <;> omega
    | .App f a => by
      have := maxUid_rename x x' f; have := maxUid_rename x x' a
      simp only [rename, maxUidExpr]; omega
    | .Force e | .Delay e => by
      have := maxUid_rename x x' e; simp only [rename, maxUidExpr]; omega
    | .Constr _ args => by
      have := maxUidList_rename x x' args; simp only [rename, maxUidExpr]; omega
    | .Case scrut alts => by
      have := maxUid_rename x x' scrut; have := maxUidList_rename x x' alts
      simp only [rename, maxUidExpr]; omega
    | .Let binds body => by
      have := maxUidLet_rename x x' binds body
      simp only [rename]; exact this
  termination_by e => sizeOf e

  theorem maxUidList_rename (x x' : VarId) :
      ∀ (es : List Expr), maxUidExprList (renameList x x' es) ≤ max (maxUidExprList es) x'.uid
    | [] => by simp [renameList, maxUidExprList]
    | e :: es => by
      have := maxUid_rename x x' e; have := maxUidList_rename x x' es
      simp only [renameList, maxUidExprList]; omega
  termination_by es => sizeOf es

  theorem maxUidLet_rename (x x' : VarId) : ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      maxUidExpr (.Let (renameLet x x' binds body).1 (renameLet x x' binds body).2) ≤
        max (maxUidExpr (.Let binds body)) x'.uid
    | [], body => by
      have := maxUid_rename x x' body
      simp only [renameLet, maxUidExpr, maxUidExprBinds]; omega
    | (y, rhs, er) :: rest, body => by
      have := maxUid_rename x x' rhs
      have := maxUidLet_rename x x' rest body
      simp only [maxUidExpr] at this
      simp only [renameLet]
      split <;> simp only [maxUidExpr, maxUidExprBinds] <;> omega
  termination_by binds body => sizeOf binds + sizeOf body
end

/-- What a binder step provides: a binder that captures nothing of the
    replacement, fresh bounds, and an unchanged lowering. -/
theorem binderStep_spec {repl : Expr} {x : VarId} {b : Expr} {s : FreshState}
    (freshBody : maxUidExpr b < s.next) (freshRepl : maxUidExpr repl < s.next)
    (freshBinder : x.uid < s.next) :
    (freeVars repl).contains (binderStep repl x b s).1 = false ∧
    (binderStep repl x b s).1.uid < (binderStep repl x b s).2.2.next ∧
    maxUidExpr (binderStep repl x b s).2.1 < (binderStep repl x b s).2.2.next ∧
    s.next ≤ (binderStep repl x b s).2.2.next ∧
    ((binderStep repl x b s).1 = x ∨ (binderStep repl x b s).1.uid = s.next) ∧
    (∀ Q, lowerTotalExpr ((binderStep repl x b s).1 :: Q) (binderStep repl x b s).2.1 =
      lowerTotalExpr (x :: Q) b) ∧
    (binderStep repl x b s).2.1.nodes = b.nodes := by
  unfold binderStep
  split
  · refine ⟨maxUidExpr_fresh repl _ freshRepl, by simp, ?_, by simp, .inr rfl, fun Q => ?_, by simp⟩
    · have := maxUid_rename x ⟨s.next, .gen, x.hint⟩ b
      simp only at this ⊢; omega
    · exact lowerTotalExpr_rename x _ b [] Q freshBody (by simp)
  · rename_i h
    exact ⟨by simpa using h, freshBinder, freshBody, Nat.le_refl _, .inl rfl, fun _ => rfl, rfl⟩

@[simp] theorem binderStep_nodes (repl : Expr) (x : VarId) (b : Expr) (s : FreshState) :
    (binderStep repl x b s).2.1.nodes = b.nodes := by
  unfold binderStep; split <;> simp

@[simp] theorem binderStepLet_nodes (repl : Expr) (x : VarId) (rest : List (VarId × Expr × Bool))
    (body : Expr) (s : FreshState) :
    Expr.nodesBinds (binderStepLet repl x rest body s).2.1.1 + (binderStepLet repl x rest body s).2.1.2.nodes =
      Expr.nodesBinds rest + body.nodes := by
  unfold binderStepLet; split <;> simp [(Expr.nodesBinds_renameLet _ _ rest body).1,
    (Expr.nodesBinds_renameLet _ _ rest body).2]

/-! ## `subst` keeps every uid below the counter -/

mutual
  theorem subst_fresh (v : VarId) (r : Expr) : ∀ (e : Expr) (s : FreshState),
      maxUidExpr e < s.next → maxUidExpr r < s.next →
      maxUidExpr (subst v r e s).1 < (subst v r e s).2.next ∧ s.next ≤ (subst v r e s).2.next
    | .Var x, s, fe, fr => by
      rw [subst_var]; split
      · exact ⟨fr, Nat.le_refl _⟩
      · exact ⟨fe, Nat.le_refl _⟩
    | .Lit _, s, fe, _ => by rw [subst_lit]; exact ⟨fe, Nat.le_refl _⟩
    | .Builtin _, s, fe, _ => by rw [subst_builtin]; exact ⟨fe, Nat.le_refl _⟩
    | .Error, s, fe, _ => by rw [subst_error]; exact ⟨fe, Nat.le_refl _⟩
    | .Lam x b, s, fe, fr => by
      simp only [maxUidExpr] at fe
      cases hxv : (x == v)
      · rw [subst_lam v r s x b hxv]
        obtain ⟨_, hx, hb, hs, _⟩ := binderStep_spec (repl := r) (x := x) (b := b) (s := s)
          (by omega) fr (by omega)
        obtain ⟨ih, ihs⟩ := subst_fresh v r (binderStep r x b s).2.1 (binderStep r x b s).2.2 hb (by omega)
        simp only [maxUidExpr]; omega
      · rw [subst_lam_shadow v r s x b hxv]; simp only [maxUidExpr]; omega
    | .Fix f b, s, fe, fr => by
      simp only [maxUidExpr] at fe
      cases hfv : (f == v)
      · rw [subst_fix v r s f b hfv]
        obtain ⟨_, hx, hb, hs, _⟩ := binderStep_spec (repl := r) (x := f) (b := b) (s := s)
          (by omega) fr (by omega)
        obtain ⟨ih, ihs⟩ := subst_fresh v r (binderStep r f b s).2.1 (binderStep r f b s).2.2 hb (by omega)
        simp only [maxUidExpr]; omega
      · rw [subst_fix_shadow v r s f b hfv]; simp only [maxUidExpr]; omega
    | .App f a, s, fe, fr => by
      simp only [maxUidExpr] at fe
      rw [subst_app]
      obtain ⟨h₁, s₁⟩ := subst_fresh v r f s (by omega) fr
      obtain ⟨h₂, s₂⟩ := subst_fresh v r a (subst v r f s).2 (by omega) (by omega)
      simp only [maxUidExpr]; omega
    | .Force e, s, fe, fr => by
      simp only [maxUidExpr] at fe
      rw [subst_force]
      obtain ⟨h₁, s₁⟩ := subst_fresh v r e s fe fr
      simp only [maxUidExpr]; omega
    | .Delay e, s, fe, fr => by
      simp only [maxUidExpr] at fe
      rw [subst_delay]
      obtain ⟨h₁, s₁⟩ := subst_fresh v r e s fe fr
      simp only [maxUidExpr]; omega
    | .Constr tag args, s, fe, fr => by
      simp only [maxUidExpr] at fe
      rw [subst_constr]
      obtain ⟨h₁, s₁⟩ := substList_fresh v r args s fe fr
      simp only [maxUidExpr]; omega
    | .Case scrut alts, s, fe, fr => by
      simp only [maxUidExpr] at fe
      rw [subst_case]
      obtain ⟨h₁, s₁⟩ := subst_fresh v r scrut s (by omega) fr
      obtain ⟨h₂, s₂⟩ := substList_fresh v r alts (subst v r scrut s).2 (by omega) (by omega)
      simp only [maxUidExpr]; omega
    | .Let binds body, s, fe, fr => by
      rw [subst_let]
      exact substLet_fresh v r binds body s fe fr
  termination_by e => e.nodes
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega) | (simp at *; omega))

  theorem substList_fresh (v : VarId) (r : Expr) : ∀ (es : List Expr) (s : FreshState),
      maxUidExprList es < s.next → maxUidExpr r < s.next →
      maxUidExprList (substList v r es s).1 < (substList v r es s).2.next ∧
        s.next ≤ (substList v r es s).2.next
    | [], s, fe, _ => by rw [substList_nil]; exact ⟨fe, Nat.le_refl _⟩
    | e :: es, s, fe, fr => by
      rw [maxUid_list_cons] at fe
      rw [substList_cons, maxUid_list_cons]
      obtain ⟨h₁, s₁⟩ := subst_fresh v r e s (by omega) fr
      obtain ⟨h₂, s₂⟩ := substList_fresh v r es (subst v r e s).2 (by omega) (by omega)
      dsimp only; omega
  termination_by es => Expr.nodesList es
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega) | (simp at *; omega))

  theorem substLet_fresh (v : VarId) (r : Expr) : ∀ (binds : List (VarId × Expr × Bool)) (body : Expr)
      (s : FreshState), maxUidExpr (.Let binds body) < s.next → maxUidExpr r < s.next →
      maxUidExpr (.Let (substLet v r (freeVars r) binds body s).1.1
          (substLet v r (freeVars r) binds body s).1.2) < (substLet v r (freeVars r) binds body s).2.next ∧
        s.next ≤ (substLet v r (freeVars r) binds body s).2.next
    | [], body, s, fe, fr => by
      rw [substLet_nil]
      obtain ⟨h₁, s₁⟩ := subst_fresh v r body s (by simp only [maxUidExpr, maxUidExprBinds] at fe; omega) fr
      simp only [maxUidExpr, maxUidExprBinds]; omega
    | (x, rhs, er) :: rest, body, s, fe, fr => by
      rw [maxUid_let_cons] at fe
      cases hxv : (x == v)
      · rw [substLet_cons v r s x rhs er rest body hxv]
        obtain ⟨h₁, s₁⟩ := subst_fresh v r rhs s (by omega) fr
        have spec := binderStep_spec (repl := r) (x := x) (b := .Let rest body)
          (s := (subst v r rhs s).2) (by omega) (by omega) (by omega)
        rw [binderStepLet_eq] at spec
        dsimp only at spec
        obtain ⟨_, hx, hb, hs, _⟩ := spec
        obtain ⟨h₂, s₂⟩ := substLet_fresh v r _ _ _ hb (by omega)
        dsimp only; simp only [maxUid_let_cons]; omega
      · rw [substLet_shadow v r s x rhs er rest body hxv]
        obtain ⟨h₁, s₁⟩ := subst_fresh v r rhs s (by omega) fr
        dsimp only; simp only [maxUid_let_cons]; omega
  termination_by binds body => Expr.nodesBinds binds + body.nodes
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega) | (simp at *; omega))
end

/-! ## Lowering helpers -/

theorem lookup_append (pre env : List VarId) (x : VarId) :
    envLookupT (pre ++ env) x =
      match envLookupT pre x with
      | some j => some j
      | none => (envLookupT env x).map (pre.length + ·) := by
  induction pre with
  | nil =>
    show envLookupT env x = Option.map (fun i => 0 + i) (envLookupT env x)
    cases envLookupT env x <;> simp
  | cons y pre ih =>
    cases hyx : (y == x)
    · rw [List.cons_append, envLookupT_cons_neq y x _ hyx, envLookupT_cons_neq y x _ hyx, ih]
      cases envLookupT pre x <;> cases envLookupT env x <;> simp; omega
    · simp [envLookupT, envLookupT.go, hyx]

/-- Lowering a replacement under binders it does not mention shifts it. -/
theorem lowerTotalExpr_prepend_fresh (pre env : List VarId) (r : Expr) (tr : Term)
    (fresh : ∀ w ∈ pre, (freeVars r).contains w = false) (h : lowerTotalExpr env r = some tr) :
    lowerTotalExpr (pre ++ env) r = some (iterShift pre.length tr) := by
  induction pre with
  | nil => exact h
  | cons w pre ih =>
    have step := lowerTotal_prepend_unused_gen [] (pre ++ env) w (expandFix r)
      (.inl (expandFix_freeVars_not_contains r w (fresh w (.head _))))
      _ (ih fun w' hw' => fresh w' (.tail _ hw'))
    simpa [iterShift_succ] using step

/-- A shadowed variable is unused: lowering without it and shifting agrees. -/
theorem lowerTotalExpr_shadow (ys env : List VarId) (v : VarId) (e : Expr) (t : Term)
    (shadow : ∃ y ∈ ys, (y == v) = true) (h : lowerTotalExpr (ys ++ v :: env) e = some t) :
    ∃ t', lowerTotalExpr (ys ++ env) e = some t' ∧
      t = renameTerm (shiftRename (ys.length + 1)) t' := by
  cases h' : lowerTotalExpr (ys ++ env) e with
  | none =>
    have := lowerTotal_prepend_unused_none_gen ys env v (expandFix e) (.inr shadow) h'
    simp only [lowerTotalExpr] at h; rw [this] at h; cases h
  | some t' =>
    have := lowerTotal_prepend_unused_gen ys env v (expandFix e) (.inr shadow) t' h'
    simp only [lowerTotalExpr] at h; rw [this] at h
    exact ⟨t', rfl, (Option.some.inj h).symm⟩

mutual
  theorem substTerm_shift_cancel (pos : Nat) (r : Term) (hpos : pos ≥ 1) :
      ∀ (t : Term), substTerm pos r (renameTerm (shiftRename pos) t) = t
    | .Var n => by
      simp only [renameTerm, shiftRename]
      split
      · simp only [substTerm]; rw [if_neg (by omega), if_pos (by omega)]; congr 1
      · simp only [substTerm]; rw [if_neg (by omega), if_neg (by omega)]
    | .Constant _ | .Builtin _ | .Error => by simp [renameTerm, substTerm]
    | .Lam name body => by
      simp only [renameTerm, substTerm]
      rw [Moist.Verified.liftRename_shiftRename hpos,
        substTerm_shift_cancel (pos + 1) _ (by omega) body]
    | .Apply f x => by
      simp only [renameTerm, substTerm]
      rw [substTerm_shift_cancel pos r hpos f, substTerm_shift_cancel pos r hpos x]
    | .Force e => by
      simp only [renameTerm, substTerm]; rw [substTerm_shift_cancel pos r hpos e]
    | .Delay e => by
      simp only [renameTerm, substTerm]; rw [substTerm_shift_cancel pos r hpos e]
    | .Constr tag args => by
      simp only [renameTerm, substTerm]; rw [substTermList_shift_cancel pos r hpos args]
    | .Case scrut alts => by
      simp only [renameTerm, substTerm]
      rw [substTerm_shift_cancel pos r hpos scrut, substTermList_shift_cancel pos r hpos alts]
  termination_by t => sizeOf t

  theorem substTermList_shift_cancel (pos : Nat) (r : Term) (hpos : pos ≥ 1) :
      ∀ (ts : List Term), substTermList pos r (renameTermList (shiftRename pos) ts) = ts
    | [] => by simp [renameTermList, substTermList]
    | t :: ts => by
      simp only [renameTermList, substTermList]
      rw [substTerm_shift_cancel pos r hpos t, substTermList_shift_cancel pos r hpos ts]
  termination_by ts => sizeOf ts
end

theorem substTerm_fixLamWrapUplc (pos : Nat) (r t : Term) (hpos : pos ≥ 1) :
    substTerm pos r (fixLamWrapUplc t) = fixLamWrapUplc (substTerm (pos + 3) (iterShift 3 r) t) := by
  simp only [fixLamWrapUplc, substTerm]
  rw [if_neg (show ¬ (1 = pos + 1) by omega), if_neg (show ¬ (1 > pos + 1) by omega),
    if_neg (show ¬ (2 = pos + 2) by omega), if_neg (show ¬ (2 > pos + 2) by omega),
    if_neg (show ¬ (1 = pos + 2) by omega), if_neg (show ¬ (1 > pos + 2) by omega)]
  simp only [iterShift]

theorem iterShift_add (m n : Nat) (t : Term) : iterShift (m + n) t = iterShift m (iterShift n t) := by
  induction m with
  | zero => simp [iterShift_zero]
  | succ k ih => rw [show k + 1 + n = (k + n) + 1 by omega, iterShift_succ, ih, iterShift_succ]

private theorem lowerTotalExpr_lam_inv {env : List VarId} {x : VarId} {b : Expr} {t : Term}
    (h : lowerTotalExpr env (.Lam x b) = some t) :
    ∃ tb, lowerTotalExpr (x :: env) b = some tb ∧ t = .Lam 0 tb := by
  rw [lowerTotalExpr_lam] at h
  cases hb : lowerTotalExpr (x :: env) b with
  | none => rw [hb] at h; cases h
  | some tb => rw [hb] at h; exact ⟨tb, rfl, (Option.some.inj h).symm⟩

private theorem lowerTotalExpr_fix_inv {env : List VarId} {f p : VarId} {inner : Expr} {t : Term}
    (sp : VarId) (fresh : maxUidExpr (expandFix inner) < sp.uid)
    (h : lowerTotalExpr env (.Fix f (.Lam p inner)) = some t) :
    ∃ ti, lowerTotalExpr (p :: f :: sp :: env) inner = some ti ∧ t = fixLamWrapUplc ti := by
  rw [lowerTotalExpr_fix_lam env f p inner sp fresh] at h
  cases hi : lowerTotalExpr (p :: f :: sp :: env) inner with
  | none => rw [hi] at h; cases h
  | some ti => rw [hi] at h; exact ⟨ti, rfl, (Option.some.inj h).symm⟩

private theorem binderStep_lam (repl : Expr) (f p : VarId) (inner : Expr) (s : FreshState) :
    ∃ inner', (binderStep repl f (.Lam p inner) s).2.1 = .Lam p inner' := by
  unfold binderStep
  split
  · simp only [rename]; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem subst_lam_shape (v : VarId) (r : Expr) (p : VarId) (inner : Expr) (s : FreshState) :
    ∃ p' inner', (subst v r (.Lam p inner) s).1 = .Lam p' inner' := by
  cases h : (p == v)
  · rw [subst_lam v r s p inner h]; exact ⟨_, _, rfl⟩
  · rw [subst_lam_shadow v r s p inner h]; exact ⟨_, _, rfl⟩

/-! ## Commutation -/

section Commute

variable (v : VarId) (r : Expr) (tr : Term) (env : List VarId)

/-- Hypotheses shared by every case: `v` and the replacement's free variables
    are not captured by `pre`, and the counter is above every uid. -/
structure Ready (pre : List VarId) (s : FreshState) : Prop where
  unshadowed : ∀ y ∈ pre, (y == v) = false
  uncaptured : ∀ w ∈ pre, (freeVars r).contains w = false
  freshRepl : maxUidExpr r < s.next
  freshVar : v.uid < s.next

variable {v r env}

private theorem Ready.mono {pre : List VarId} {s s' : FreshState} (h : Ready v r pre s)
    (le : s.next ≤ s'.next) : Ready v r pre s' :=
  ⟨h.unshadowed, h.uncaptured, by have := h.freshRepl; omega, by have := h.freshVar; omega⟩

/-- Extending the prefix with the binder a `binderStep` produced. -/
private theorem Ready.step {pre : List VarId} {s : FreshState} {x : VarId} {b : Expr}
    (h : Ready v r pre s) (fb : maxUidExpr b < s.next) (fx : x.uid < s.next)
    (hxv : (x == v) = false) :
    Ready v r ((binderStep r x b s).1 :: pre) (binderStep r x b s).2.2 := by
  obtain ⟨hfree, _, _, hs, hname, _⟩ := binderStep_spec (x := x) fb h.freshRepl fx
  refine ⟨fun y hy => ?_, fun w hw => ?_, by have := h.freshRepl; omega, by have := h.freshVar; omega⟩
  · cases hy with
    | head => rcases hname with hname | hname
              · rw [hname]; exact hxv
              · exact beq_false_of_uid (by have := h.freshVar; omega)
    | tail _ hy => exact h.unshadowed y hy
  · cases hw with
    | head => exact hfree
    | tail _ hw => exact h.uncaptured w hw

private theorem Ready.cons {pre : List VarId} {s : FreshState} {y : VarId} (h : Ready v r pre s)
    (hyv : (y == v) = false) (hy : (freeVars r).contains y = false) : Ready v r (y :: pre) s :=
  ⟨fun z hz => by cases hz with | head => exact hyv | tail _ hz => exact h.unshadowed z hz,
   fun w hw => by cases hw with | head => exact hy | tail _ hw => exact h.uncaptured w hw,
   h.freshRepl, h.freshVar⟩

private theorem substTerm_lam (pos : Nat) (R t : Term) :
    substTerm pos R (.Lam 0 t) = .Lam 0 (substTerm (pos + 1) (renameTerm (shiftRename 1) R) t) := by
  simp only [substTerm]

variable (hr : lowerTotalExpr env r = some tr)
include hr

mutual
  theorem subst_lower : ∀ (e : Expr) (pre : List VarId) (s : FreshState) (t : Term),
      Ready v r pre s → maxUidExpr e < s.next →
      lowerTotalExpr (pre ++ v :: env) e = some t →
      lowerTotalExpr (pre ++ env) (subst v r e s).1 =
        some (substTerm (pre.length + 1) (iterShift pre.length tr) t)
    | .Var x, pre, s, t, ready, _, ht => by
      rw [subst_var]
      rw [lowerTotalExpr_var] at ht
      split
      · rename_i hxv
        have notInPre : ∀ y ∈ pre, (y == x) = false := fun y hy => by
          rw [beq_comm]
          exact beq_false_of_beq (by rw [beq_comm]; exact hxv) (by rw [beq_comm]; exact ready.unshadowed y hy)
        rw [lookup_at_middle pre v x env (by rw [beq_comm]; exact hxv) notInPre] at ht
        cases ht
        rw [lowerTotalExpr_prepend_fresh pre env r tr ready.uncaptured hr]
        simp [substTerm]
      · rename_i hxv
        have hvx : (v == x) = false := by rw [beq_comm]; simpa using hxv
        rw [lowerTotalExpr_var, lookup_append]
        rw [lookup_append, envLookupT_cons_neq v x env hvx] at ht
        cases hpx : envLookupT pre x with
        | some j =>
          rw [hpx] at ht; cases ht
          have := envLookupT_bound pre x j hpx
          simp only [Option.map, substTerm]
          rw [if_neg (by omega), if_neg (by omega)]
        | none =>
          rw [hpx] at ht
          cases hex : envLookupT env x with
          | none => rw [hex] at ht; cases ht
          | some i =>
            rw [hex] at ht; cases ht
            simp only [Option.map, substTerm]
            rw [if_neg (by omega), if_pos (by omega)]
            congr 2
            try omega
    | .Lit (c, ty), pre, s, t, _, _, ht => by
      rw [subst_lit]
      simp only [lowerTotalExpr, expandFix, lowerTotal] at ht ⊢
      cases ht; simp [substTerm]
    | .Builtin b, pre, s, t, _, _, ht => by
      rw [subst_builtin]
      simp only [lowerTotalExpr, expandFix, lowerTotal] at ht ⊢
      cases ht; simp [substTerm]
    | .Error, pre, s, t, _, _, ht => by
      rw [subst_error]
      simp only [lowerTotalExpr, expandFix, lowerTotal] at ht ⊢
      cases ht; simp [substTerm]
    | .Lam x b, pre, s, t, ready, fe, ht => by
      simp only [maxUidExpr] at fe
      obtain ⟨tb, htb, rfl⟩ := lowerTotalExpr_lam_inv ht
      cases hxv : (x == v)
      · rw [subst_lam v r s x b hxv]
        have next := ready.step (b := b) (by omega) (by omega) hxv
        obtain ⟨_, _, hb, _, _, hlow, _⟩ := binderStep_spec (repl := r) (x := x) (b := b) (s := s)
          (by omega) ready.freshRepl (by omega)
        have ih := subst_lower _ ((binderStep r x b s).1 :: pre) (binderStep r x b s).2.2 tb next hb
          ((hlow _).trans htb)
        rw [lowerTotalExpr_lam]
        simp only [List.cons_append, List.length_cons] at ih
        rw [ih, substTerm_lam, ← iterShift_succ]; rfl
      · rw [subst_lam_shadow v r s x b hxv]
        obtain ⟨tb', htb', rfl⟩ := lowerTotalExpr_shadow (x :: pre) env v b tb ⟨x, .head _, hxv⟩ htb
        rw [lowerTotalExpr_lam]
        simp only [List.cons_append] at htb'
        rw [htb', substTerm_lam]
        simp only [Option.map, List.length_cons]
        rw [substTerm_shift_cancel _ _ (by omega)]
    | .Fix f (.Lam p inner), pre, s, t, ready, fe, ht => by
        simp only [maxUidExpr] at fe
        cases hfv : (f == v)
        · rw [subst_fix v r s f _ hfv]
          have next := ready.step (b := .Lam p inner) (by simp only [maxUidExpr]; omega) (by omega) hfv
          obtain ⟨_, _, hb, hs, _, hlow, hnodes⟩ := binderStep_spec (repl := r) (x := f) (b := .Lam p inner)
            (s := s) (by simp only [maxUidExpr]; omega) ready.freshRepl (by omega)
          obtain ⟨inner₁, hB⟩ := binderStep_lam r f p inner s
          generalize hst : binderStep r f (.Lam p inner) s = st at next hb hs hlow hB hnodes
          obtain ⟨f₁, B₁, s₁⟩ := st
          simp only at next hb hs hlow hB hnodes ⊢
          subst hB
          obtain ⟨p₂, inner₂, hres⟩ := subst_lam_shape v r p inner₁ s₁
          rw [hres]
          let sp : VarId := ⟨maxUidExpr (expandFix inner) + maxUidExpr (expandFix inner₂) +
            maxUidExpr r + v.uid + 1, .gen, "s"⟩
          have spInner : maxUidExpr (expandFix inner) < sp.uid := by simp only [sp]; omega
          have spInner₂ : maxUidExpr (expandFix inner₂) < sp.uid := by simp only [sp]; omega
          obtain ⟨ti, hti, rfl⟩ := lowerTotalExpr_fix_inv sp spInner ht
          have ready' : Ready v r (f₁ :: sp :: pre) s₁ := by
            refine ⟨fun y hy => ?_, fun w hw => ?_, next.freshRepl, next.freshVar⟩
            · cases hy with
              | head => exact next.unshadowed f₁ (.head _)
              | tail _ hy =>
                cases hy with
                | head => exact beq_false_of_uid (by simp only [sp]; omega)
                | tail _ hy => exact ready.unshadowed y hy
            · cases hw with
              | head => exact next.uncaptured f₁ (.head _)
              | tail _ hw =>
                cases hw with
                | head => exact maxUidExpr_fresh r sp (by simp only [sp]; omega)
                | tail _ hw => exact ready.uncaptured w hw
          have hbody : lowerTotalExpr ((f₁ :: sp :: pre) ++ v :: env) (.Lam p inner₁) = some (.Lam 0 ti) := by
            simp only [List.cons_append]
            rw [hlow, lowerTotalExpr_lam, hti]; rfl
          have ih := subst_lower _ (f₁ :: sp :: pre) s₁ _ ready' hb hbody
          rw [hres, lowerTotalExpr_lam] at ih
          simp only [List.cons_append, List.length_cons] at ih
          rw [lowerTotalExpr_fix_lam _ f₁ p₂ inner₂ sp spInner₂]
          cases hi : lowerTotalExpr (p₂ :: f₁ :: sp :: (pre ++ env)) inner₂ with
          | none => rw [hi] at ih; cases ih
          | some ti₂ =>
            rw [hi] at ih
            simp only [Option.map, substTerm_lam, Option.some.injEq, Term.Lam.injEq, true_and] at ih
            simp only [Option.map]
            rw [ih, ← iterShift_succ, substTerm_fixLamWrapUplc _ _ _ (by omega), ← iterShift_add,
              show 3 + pre.length = pre.length + 1 + 1 + 1 by omega,
              show pre.length + 1 + 3 = pre.length + 1 + 1 + 1 + 1 by omega]
        · rw [subst_fix_shadow v r s f _ hfv]
          let sc : VarId := ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩
          obtain ⟨ti, hti, rfl⟩ := lowerTotalExpr_fix_inv sc (Nat.lt_succ_self _) ht
          obtain ⟨ti', hti', rfl⟩ := lowerTotalExpr_shadow (p :: f :: sc :: pre) env v inner ti
            ⟨f, .tail _ (.head _), hfv⟩ (by simpa using hti)
          rw [lowerTotalExpr_fix_lam _ f p inner sc (Nat.lt_succ_self _)]
          simp only [List.cons_append] at hti'
          rw [hti']
          simp only [Option.map, List.length_cons]
          rw [substTerm_fixLamWrapUplc _ _ _ (by omega)]
          congr 2
          rw [show pre.length + 1 + 3 = pre.length + 1 + 1 + 1 + 1 by omega,
            substTerm_shift_cancel _ _ (by omega)]
    | .Fix _ (.Var _), _, _, _, _, _, ht | .Fix _ (.Lit _), _, _, _, _, _, ht
    | .Fix _ (.Builtin _), _, _, _, _, _, ht | .Fix _ .Error, _, _, _, _, _, ht
    | .Fix _ (.Fix _ _), _, _, _, _, _, ht | .Fix _ (.App _ _), _, _, _, _, _, ht
    | .Fix _ (.Force _), _, _, _, _, _, ht | .Fix _ (.Delay _), _, _, _, _, _, ht
    | .Fix _ (.Constr _ _), _, _, _, _, _, ht | .Fix _ (.Case _ _), _, _, _, _, _, ht
    | .Fix _ (.Let _ _), _, _, _, _, _, ht => by
      rw [lowerTotalExpr_fix_nonlam _ _ _ (by intros; simp)] at ht; cases ht
    | .App f a, pre, s, t, ready, fe, ht => by
      simp only [maxUidExpr] at fe
      rw [subst_app]
      rw [lowerTotalExpr_app] at ht
      cases hf : lowerTotalExpr (pre ++ v :: env) f with
      | none => rw [hf] at ht; cases ht
      | some tf =>
        cases ha : lowerTotalExpr (pre ++ v :: env) a with
        | none => rw [hf, ha] at ht; cases ht
        | some ta =>
          rw [hf, ha] at ht; cases ht
          have := (subst_fresh v r f s (by omega) ready.freshRepl).2
          rw [lowerTotalExpr_app, subst_lower f pre s tf ready (by omega) hf,
            subst_lower a pre _ ta (ready.mono this) (by omega) ha]
          simp [substTerm]
    | .Force e, pre, s, t, ready, fe, ht => by
      simp only [maxUidExpr] at fe
      rw [subst_force]
      rw [lowerTotalExpr_force] at ht
      cases he : lowerTotalExpr (pre ++ v :: env) e with
      | none => rw [he] at ht; cases ht
      | some te =>
        rw [he] at ht; cases ht
        rw [lowerTotalExpr_force, subst_lower e pre s te ready fe he]; simp [substTerm]
    | .Delay e, pre, s, t, ready, fe, ht => by
      simp only [maxUidExpr] at fe
      rw [subst_delay]
      rw [lowerTotalExpr_delay] at ht
      cases he : lowerTotalExpr (pre ++ v :: env) e with
      | none => rw [he] at ht; cases ht
      | some te =>
        rw [he] at ht; cases ht
        rw [lowerTotalExpr_delay, subst_lower e pre s te ready fe he]; simp [substTerm]
    | .Constr tag args, pre, s, t, ready, fe, ht => by
      simp only [maxUidExpr] at fe
      rw [subst_constr]
      rw [lowerTotalExpr_constr_of_list] at ht
      cases he : lowerTotalExprList (pre ++ v :: env) args with
      | none => rw [he] at ht; cases ht
      | some ts =>
        rw [he] at ht; cases ht
        rw [lowerTotalExpr_constr_of_list, substList_lower args pre s ts ready fe he]; simp [substTerm]
    | .Case scrut alts, pre, s, t, ready, fe, ht => by
      simp only [maxUidExpr] at fe
      rw [subst_case]
      rw [lowerTotalExpr_case_of_list] at ht
      cases hs : lowerTotalExpr (pre ++ v :: env) scrut with
      | none => rw [hs] at ht; cases ht
      | some tsc =>
        cases ha : lowerTotalExprList (pre ++ v :: env) alts with
        | none => rw [hs, ha] at ht; cases ht
        | some tas =>
          rw [hs, ha] at ht; cases ht
          have := (subst_fresh v r scrut s (by omega) ready.freshRepl).2
          rw [lowerTotalExpr_case_of_list, subst_lower scrut pre s tsc ready (by omega) hs,
            substList_lower alts pre _ tas (ready.mono this) (by omega) ha]
          simp [substTerm]
    | .Let binds body, pre, s, t, ready, fe, ht => by
      rw [subst_let]
      exact substLet_lower binds body pre s t ready fe ht
  termination_by e => e.nodes
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega) | (simp at *; omega))

  theorem substList_lower : ∀ (es : List Expr) (pre : List VarId) (s : FreshState) (ts : List Term),
      Ready v r pre s → maxUidExprList es < s.next →
      lowerTotalExprList (pre ++ v :: env) es = some ts →
      lowerTotalExprList (pre ++ env) (substList v r es s).1 =
        some (substTermList (pre.length + 1) (iterShift pre.length tr) ts)
    | [], pre, s, ts, _, _, ht => by
      rw [substList_nil, lowerTotalExprList_nil]
      rw [lowerTotalExprList_nil] at ht; cases ht; simp only [substTermList]
    | e :: es, pre, s, ts, ready, fe, ht => by
      rw [maxUid_list_cons] at fe
      rw [substList_cons]
      rw [lowerTotalExprList_cons] at ht
      cases he : lowerTotalExpr (pre ++ v :: env) e with
      | none => rw [he] at ht; cases ht
      | some te =>
        cases hes : lowerTotalExprList (pre ++ v :: env) es with
        | none => rw [he, hes] at ht; cases ht
        | some tes =>
          rw [he, hes] at ht; cases ht
          have := (subst_fresh v r e s (by omega) ready.freshRepl).2
          rw [lowerTotalExprList_cons, subst_lower e pre s te ready (by omega) he,
            substList_lower es pre _ tes (ready.mono this) (by omega) hes]
          simp [substTermList]
  termination_by es => Expr.nodesList es
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega) | (simp at *; omega))

  theorem substLet_lower : ∀ (binds : List (VarId × Expr × Bool)) (body : Expr) (pre : List VarId)
      (s : FreshState) (t : Term),
      Ready v r pre s → maxUidExpr (.Let binds body) < s.next →
      lowerTotalExpr (pre ++ v :: env) (.Let binds body) = some t →
      lowerTotalExpr (pre ++ env) (.Let (substLet v r (freeVars r) binds body s).1.1
          (substLet v r (freeVars r) binds body s).1.2) =
        some (substTerm (pre.length + 1) (iterShift pre.length tr) t)
    | [], body, pre, s, t, ready, fe, ht => by
      rw [substLet_nil]
      rw [lowerTotalExpr_let_nil] at ht ⊢
      exact subst_lower body pre s t ready (by simp only [maxUidExpr, maxUidExprBinds] at fe; omega) ht
    | (x, rhs, er) :: rest, body, pre, s, t, ready, fe, ht => by
      rw [maxUid_let_cons] at fe
      rw [lowerTotalExpr_let_cons] at ht
      cases hrhs : lowerTotalExpr (pre ++ v :: env) rhs with
      | none => rw [hrhs] at ht; cases ht
      | some trhs =>
        cases hb : lowerTotalExpr (x :: (pre ++ v :: env)) (.Let rest body) with
        | none => rw [hrhs, hb] at ht; cases ht
        | some tb =>
          rw [hrhs, hb] at ht; cases ht
          have ihr := subst_lower rhs pre s trhs ready (by omega) hrhs
          have fs := (subst_fresh v r rhs s (by omega) ready.freshRepl).2
          cases hxv : (x == v)
          · rw [substLet_cons v r s x rhs er rest body hxv]
            dsimp only
            have spec := binderStep_spec (repl := r) (x := x) (b := .Let rest body)
              (s := (subst v r rhs s).2) (by omega) (by have := ready.freshRepl; omega) (by omega)
            have next := (ready.mono fs).step (b := .Let rest body) (by omega) (by omega) hxv
            rw [binderStepLet_eq] at spec next
            dsimp only at spec next
            obtain ⟨_, _, hbody, _, _, hlow, _⟩ := spec
            have ih := substLet_lower _ _ _ _ tb next hbody ((hlow _).trans hb)
            rw [lowerTotalExpr_let_cons, ihr]
            simp only [List.cons_append, List.length_cons] at ih
            rw [ih]
            simp only [Option.bind_eq_bind, Option.bind_some, substTerm, iterShift_succ]
          · rw [substLet_shadow v r s x rhs er rest body hxv]
            obtain ⟨tb', htb', rfl⟩ := lowerTotalExpr_shadow (x :: pre) env v (.Let rest body) tb
              ⟨x, .head _, hxv⟩ hb
            rw [lowerTotalExpr_let_cons, ihr]
            simp only [List.cons_append] at htb'
            rw [htb']
            simp only [Option.bind_eq_bind, Option.bind_some, substTerm, List.length_cons]
            rw [substTerm_shift_cancel _ _ (by omega)]
  termination_by binds body => Expr.nodesBinds binds + body.nodes
  decreasing_by all_goals (simp_wf; all_goals first | omega | (simp; done) | (simp; omega) | (simp at *; omega))
end

end Commute

/-! ## Substituting into the remaining bindings of a let -/

theorem substInBindings_nil (v : VarId) (r : Expr) (s : FreshState) :
    substInBindings v r [] s = (⟨[], rfl⟩, s) := by rw [substInBindings]; rfl

theorem substInBindings_cons_val (v : VarId) (r : Expr) (y : VarId) (e : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (s : FreshState) :
    (substInBindings v r ((y, e, er) :: rest) s).1.val =
      (y, (subst v r e s).1, er) :: (substInBindings v r rest (subst v r e s).2).1.val := by
  rw [substInBindings]; rfl

theorem substInBindings_cons_state (v : VarId) (r : Expr) (y : VarId) (e : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (s : FreshState) :
    (substInBindings v r ((y, e, er) :: rest) s).2 =
      (substInBindings v r rest (subst v r e s).2).2 := by
  rw [substInBindings]; rfl

theorem substInBindings_fresh (v : VarId) (r : Expr) :
    ∀ (rest : List (VarId × Expr × Bool)) (s : FreshState),
      maxUidExprBinds rest < s.next → maxUidExpr r < s.next →
      maxUidExprBinds (substInBindings v r rest s).1.val < (substInBindings v r rest s).2.next ∧
        s.next ≤ (substInBindings v r rest s).2.next
  | [], s, fe, _ => by rw [substInBindings_nil]; exact ⟨fe, Nat.le_refl _⟩
  | (y, e, er) :: rest, s, fe, fr => by
    simp only [maxUidExprBinds] at fe
    rw [substInBindings_cons_val, substInBindings_cons_state]
    obtain ⟨h₁, s₁⟩ := subst_fresh v r e s (by omega) fr
    obtain ⟨h₂, s₂⟩ := substInBindings_fresh v r rest (subst v r e s).2 (by omega) (by omega)
    simp only [maxUidExprBinds]; omega

section Commute
variable {v : VarId} {r : Expr} {tr : Term} {env : List VarId}

/-- Substituting into each remaining binding and, separately, into the body
    lowers like substituting into the whole let, provided the remaining
    binders neither rebind `v` nor capture the replacement. -/
theorem substInBindings_lower (hr : lowerTotalExpr env r = some tr) (body : Expr) (sb : FreshState) :
    ∀ (rest : List (VarId × Expr × Bool)) (pre : List VarId) (s : FreshState) (t : Term),
      Ready v r pre s → Ready v r pre sb →
      (∀ b ∈ rest, (b.1 == v) = false ∧ (freeVars r).contains b.1 = false) →
      maxUidExprBinds rest < s.next → maxUidExpr body < sb.next →
      lowerTotalExpr (pre ++ v :: env) (.Let rest body) = some t →
      lowerTotalExpr (pre ++ env) (.Let (substInBindings v r rest s).1.val (subst v r body sb).1) =
        some (substTerm (pre.length + 1) (iterShift pre.length tr) t)
  | [], pre, s, t, _, readyBody, _, _, fb, ht => by
    rw [substInBindings_nil, lowerTotalExpr_let_nil]
    rw [lowerTotalExpr_let_nil] at ht
    exact subst_lower tr hr body pre sb t readyBody fb ht
  | (y, e, er) :: rest, pre, s, t, ready, readyBody, names, fe, fb, ht => by
    simp only [maxUidExprBinds] at fe
    rw [substInBindings_cons_val, lowerTotalExpr_let_cons]
    rw [lowerTotalExpr_let_cons] at ht
    cases he : lowerTotalExpr (pre ++ v :: env) e with
    | none => rw [he] at ht; cases ht
    | some te =>
      cases hb : lowerTotalExpr (y :: (pre ++ v :: env)) (.Let rest body) with
      | none => rw [he, hb] at ht; cases ht
      | some tb =>
        rw [he, hb] at ht; cases ht
        obtain ⟨hyv, hyr⟩ := names (y, e, er) (.head _)
        have fs := (subst_fresh v r e s (by omega) ready.freshRepl).2
        have ih := substInBindings_lower hr body sb rest (y :: pre) (subst v r e s).2 tb
          ((ready.mono fs).cons hyv hyr) (readyBody.cons hyv hyr)
          (fun b hb => names b (.tail _ hb)) (by omega) fb hb
        simp only [List.cons_append, List.length_cons] at ih
        rw [subst_lower tr hr e pre s te ready (by omega) he, ih]
        simp only [Option.bind_eq_bind, Option.bind_some, substTerm, iterShift_succ]

end Commute

/-- Inlining the head binding of a let lowers to a UPLC beta redex and its
    contractum. -/
theorem inline_head_lower {v : VarId} {rhs : Expr} {er : Bool} {rest : List (VarId × Expr × Bool)}
    {body : Expr} {s : FreshState} {env : List VarId} {t : Term}
    (distinct : distinctBinders ((v, rhs, er) :: rest) = true)
    (names : ∀ b ∈ rest, (freeVars rhs).contains b.1 = false)
    (fresh : maxUidExpr (.Let ((v, rhs, er) :: rest) body) < s.next)
    (h : lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) = some t) :
    ∃ tr tb, lowerTotalExpr env rhs = some tr ∧ lowerTotalExpr (v :: env) (.Let rest body) = some tb ∧
      t = .Apply (.Lam 0 tb) tr ∧
      lowerTotalExpr env (.Let (substInBindings v rhs rest (subst v rhs body s).2).1.val
        (subst v rhs body s).1) = some (substTerm 1 tr tb) := by
  rw [maxUid_let_cons] at fresh
  simp only [maxUidExpr] at fresh
  rw [lowerTotalExpr_let_cons] at h
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at h; cases h
  | some tr =>
    cases hb : lowerTotalExpr (v :: env) (.Let rest body) with
    | none => rw [hr, hb] at h; cases h
    | some tb =>
      rw [hr, hb] at h; cases h
      simp only [distinctBinders, Bool.and_eq_true, List.all_eq_true] at distinct
      have fs := subst_fresh v rhs body s (by omega) (by omega)
      have lowered := substInBindings_lower (v := v) (tr := tr) (env := env) hr body s rest []
        (subst v rhs body s).2 tb
        ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), by omega, by omega⟩
        ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), by omega, by omega⟩
        (fun b hb => ⟨by simpa using distinct.1 b hb, names b hb⟩) (by omega) (by omega) hb
      exact ⟨tr, tb, rfl, rfl, rfl, lowered⟩

end Moist.Verified.InlineSoundness.SubstCommute
