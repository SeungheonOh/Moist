import Moist.MIR.AlphaRename
import Moist.MIR.LowerTotal
import Moist.Verified.Definitions.MIR
import Moist.Verified.MIR.Congruence

/-! # Alpha-rename soundness helpers -/

namespace Moist.Verified.MIR

open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId alphaRename alphaRenameList alphaRenameBinds
   alphaRenameTop substLookup substShadow
   lowerTotal lowerTotalList lowerTotalLet lowerTotalExpr envLookupT
   maxUidExpr maxUidExprList maxUidExprBinds
   freshVar FreshM FreshState runFresh expandFix fixCount)

/-! ## VarId BEq helpers (local re-exposure) -/

theorem VarId_beq_true_iff (a b : VarId) :
    (a == b) = true ↔ a.origin = b.origin ∧ a.uid = b.uid := by
  show (a.origin == b.origin && a.uid == b.uid) = true ↔ _
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨ho, hu⟩
    refine ⟨?_, of_decide_eq_true hu⟩
    revert ho
    cases a.origin <;> cases b.origin <;> intro ho <;> first | rfl | cases ho
  · rintro ⟨ho, hu⟩
    refine ⟨?_, decide_eq_true hu⟩
    rw [ho]; cases b.origin <;> rfl

theorem VarId_beq_false_iff (a b : VarId) :
    (a == b) = false ↔ a.origin ≠ b.origin ∨ a.uid ≠ b.uid := by
  constructor
  · intro hb
    by_cases ho : a.origin = b.origin
    · by_cases hu : a.uid = b.uid
      · exfalso
        have := (VarId_beq_true_iff a b).mpr ⟨ho, hu⟩
        rw [this] at hb; exact Bool.noConfusion hb
      · exact Or.inr hu
    · exact Or.inl ho
  · intro h
    cases hb : (a == b)
    · rfl
    · exfalso
      have ⟨ho, hu⟩ := (VarId_beq_true_iff a b).mp hb
      cases h with
      | inl h' => exact h' ho
      | inr h' => exact h' hu

/-! ## substLookup / substShadow helpers -/

theorem substLookup_cons_match
    (old new : VarId) (rest : List (VarId × VarId)) (v : VarId)
    (h : (old == v) = true) :
    substLookup ((old, new) :: rest) v = new := by
  show (if (old == v) = true then new else substLookup rest v) = new
  rw [if_pos h]

theorem substLookup_cons_nomatch
    (old new : VarId) (rest : List (VarId × VarId)) (v : VarId)
    (h : (old == v) = false) :
    substLookup ((old, new) :: rest) v = substLookup rest v := by
  show (if (old == v) = true then new else substLookup rest v) = substLookup rest v
  rw [if_neg (by simp [h])]

theorem substShadow_nil (v : VarId) : substShadow [] v = [] := rfl

theorem substShadow_cons_match (old new : VarId)
    (rest : List (VarId × VarId)) (v : VarId) (h : (old == v) = true) :
    substShadow ((old, new) :: rest) v = substShadow rest v := by
  simp only [substShadow, if_pos h]

theorem substShadow_cons_nomatch (old new : VarId)
    (rest : List (VarId × VarId)) (v : VarId) (h : (old == v) = false) :
    substShadow ((old, new) :: rest) v = (old, new) :: substShadow rest v := by
  show (if (old == v) = true then substShadow rest v
        else (old, new) :: substShadow rest v) = (old, new) :: substShadow rest v
  rw [if_neg (by simp [h])]

theorem substShadow_mem_iff {σ : List (VarId × VarId)} {v : VarId}
    {p : VarId × VarId} :
    p ∈ substShadow σ v ↔ p ∈ σ ∧ (p.1 == v) = false := by
  induction σ with
  | nil =>
    rw [substShadow_nil]
    constructor
    · intro hm; exact absurd hm List.not_mem_nil
    · intro ⟨hm, _⟩; exact absurd hm List.not_mem_nil
  | cons q rest ih =>
    obtain ⟨old, new⟩ := q
    by_cases hov : (old == v) = true
    · rw [substShadow_cons_match old new rest v hov]
      rw [ih]
      constructor
      · intro ⟨hm, hne⟩; exact ⟨List.mem_cons_of_mem _ hm, hne⟩
      · intro ⟨hm, hne⟩
        rcases List.mem_cons.mp hm with heq | hm'
        · exfalso
          subst heq
          rw [hov] at hne
          exact Bool.noConfusion hne
        · exact ⟨hm', hne⟩
    · have hov' : (old == v) = false := by cases h : (old == v); rfl; exact absurd h hov
      rw [substShadow_cons_nomatch old new rest v hov']
      constructor
      · intro hm
        rcases List.mem_cons.mp hm with heq | hm'
        · rw [heq]
          exact ⟨List.mem_cons_self, hov'⟩
        · obtain ⟨hm'', hne⟩ := ih.mp hm'
          exact ⟨List.mem_cons_of_mem _ hm'', hne⟩
      · intro ⟨hm, hne⟩
        rcases List.mem_cons.mp hm with heq | hm'
        · rw [heq]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih.mpr ⟨hm', hne⟩)

theorem substLookup_identity_of_no_match
    (σ : List (VarId × VarId)) (w : VarId)
    (hnone : ∀ p ∈ σ, (p.1 == w) = false) :
    substLookup σ w = w := by
  induction σ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨old, new⟩ := p
    have hne : (old == w) = false := hnone _ List.mem_cons_self
    rw [substLookup_cons_nomatch old new rest w hne]
    exact ih (fun q hq => hnone q (List.mem_cons_of_mem _ hq))

theorem substLookup_result_in_image_or_self
    (σ : List (VarId × VarId)) (w : VarId) :
    substLookup σ w = w ∨
    ∃ p ∈ σ, substLookup σ w = p.2 := by
  induction σ with
  | nil => exact .inl rfl
  | cons p rest ih =>
    obtain ⟨old, new⟩ := p
    by_cases hov : (old == w) = true
    · right
      refine ⟨(old, new), List.mem_cons_self, ?_⟩
      rw [substLookup_cons_match old new rest w hov]
    · have hov' : (old == w) = false := by cases h : (old == w); rfl; exact absurd h hov
      rw [substLookup_cons_nomatch old new rest w hov']
      rcases ih with heq | ⟨q, hq, hqeq⟩
      · exact .inl heq
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, hqeq⟩

theorem substLookup_substShadow_neq
    (σ : List (VarId × VarId)) (v w : VarId) (h : (v == w) = false) :
    substLookup (substShadow σ v) w = substLookup σ w := by
  induction σ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨old, new⟩ := p
    by_cases hov : (old == v) = true
    · rw [substShadow_cons_match old new rest v hov, ih]
      have hneq : (old == w) = false := by
        -- If old == v and old == w, then v == w (by BEq transitivity).
        cases hw : (old == w)
        · rfl
        · exfalso
          -- old == v (true) means origin+uid match; same for old == w. So v == w.
          have : (v == w) = true := by
            rw [VarId_beq_true_iff] at hov hw
            rw [VarId_beq_true_iff]
            exact ⟨hov.1.symm.trans hw.1, hov.2.symm.trans hw.2⟩
          rw [this] at h; exact Bool.noConfusion h
      exact (substLookup_cons_nomatch old new rest w hneq).symm
    · have hov' : (old == v) = false := by cases h : (old == v); rfl; exact absurd h hov
      rw [substShadow_cons_nomatch old new rest v hov']
      by_cases how : (old == w) = true
      · rw [substLookup_cons_match old new _ w how,
            substLookup_cons_match old new rest w how]
      · have how' : (old == w) = false := by cases h : (old == w); rfl; exact absurd h how
        rw [substLookup_cons_nomatch old new _ w how',
            substLookup_cons_nomatch old new rest w how']
        exact ih

/-! ## envLookupT helpers -/

theorem envLookupT_cons_same_uid (v w : VarId) (env : List VarId)
    (ho : v.origin = w.origin) (h : v.uid = w.uid) :
    envLookupT (v :: env) w = some 0 := by
  have hbeq : (v == w) = true := by
    show (v.origin == w.origin && v.uid == w.uid) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, decide_eq_true h⟩
    rw [ho]
    cases w.origin <;> rfl
  show (if (v == w) = true then some 0
        else envLookupT.go w env (0 + 1)) = some 0
  rw [if_pos hbeq]

theorem envLookupT_cons_diff_uid (v w : VarId) (env : List VarId)
    (h : v.uid ≠ w.uid) :
    envLookupT (v :: env) w = (envLookupT env w).map (· + 1) := by
  have hbeq : (v == w) = false := by
    show (v.origin == w.origin && v.uid == w.uid) = false
    rw [Bool.and_eq_false_iff]
    exact Or.inr (decide_eq_false h)
  exact Moist.MIR.envLookupT_cons_neq v w env hbeq

/-! ## Main soundness theorem -/

/-- An auxiliary equation lemma: running `alphaRename (substShadow σ v) body`
    from state `s` and then wrapping in `.Lam v` gives the same result as
    the do-block for `alphaRename σ (.Lam v body)`. -/
private theorem alphaRename_lam_eq (σ : List (VarId × VarId))
    (v : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Lam v body)) s =
      (.Lam v (alphaRename (substShadow σ v) body s).1,
       (alphaRename (substShadow σ v) body s).2) := by
  show (do
      let body' ← alphaRename (substShadow σ v) body
      pure (Expr.Lam v body')) s = _
  rfl

private theorem alphaRename_fix_eq (σ : List (VarId × VarId))
    (v : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Fix v body)) s =
      (.Fix v (alphaRename (substShadow σ v) body s).1,
       (alphaRename (substShadow σ v) body s).2) := by
  show (do
      let body' ← alphaRename (substShadow σ v) body
      pure (Expr.Fix v body')) s = _
  rfl

private theorem alphaRename_app_eq (σ : List (VarId × VarId))
    (f x : Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.App f x)) s =
      (.App (alphaRename σ f s).1 (alphaRename σ x (alphaRename σ f s).2).1,
       (alphaRename σ x (alphaRename σ f s).2).2) := by
  show (do
      let f' ← alphaRename σ f
      let x' ← alphaRename σ x
      pure (Expr.App f' x')) s = _
  rfl

private theorem alphaRename_force_eq (σ : List (VarId × VarId))
    (e : Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Force e)) s =
      (.Force (alphaRename σ e s).1, (alphaRename σ e s).2) := by
  show (do let e' ← alphaRename σ e; pure (Expr.Force e')) s = _
  rfl

private theorem alphaRename_delay_eq (σ : List (VarId × VarId))
    (e : Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Delay e)) s =
      (.Delay (alphaRename σ e s).1, (alphaRename σ e s).2) := by
  show (do let e' ← alphaRename σ e; pure (Expr.Delay e')) s = _
  rfl

private theorem alphaRename_constr_eq (σ : List (VarId × VarId))
    (tag : Nat) (args : List Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Constr tag args)) s =
      (.Constr tag (alphaRenameList σ args s).1, (alphaRenameList σ args s).2) := by
  show (do let args' ← alphaRenameList σ args; pure (Expr.Constr tag args')) s = _
  rfl

private theorem alphaRename_case_eq (σ : List (VarId × VarId))
    (scrut : Expr) (alts : List Expr) (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Case scrut alts)) s =
      (.Case (alphaRename σ scrut s).1
        (alphaRenameList σ alts (alphaRename σ scrut s).2).1,
       (alphaRenameList σ alts (alphaRename σ scrut s).2).2) := by
  show (do
      let scrut' ← alphaRename σ scrut
      let alts' ← alphaRenameList σ alts
      pure (Expr.Case scrut' alts')) s = _
  rfl

private theorem alphaRename_let_eq (σ : List (VarId × VarId))
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    (alphaRename σ (.Let binds body)) s =
      (let bb := (alphaRenameBinds σ binds s).1
       let s1 := (alphaRenameBinds σ binds s).2
       let br := (alphaRename bb.2 body s1).1
       let s2 := (alphaRename bb.2 body s1).2
       (.Let bb.1 br, s2)) := by
  show (do
      let (binds', subst') ← alphaRenameBinds σ binds
      let body' ← alphaRename subst' body
      pure (Expr.Let binds' body')) s = _
  rfl

private theorem alphaRenameList_nil_eq (σ : List (VarId × VarId))
    (s : Moist.MIR.FreshState) :
    (alphaRenameList σ []) s = (([] : List Expr), s) := rfl

private theorem alphaRenameList_cons_eq (σ : List (VarId × VarId))
    (e : Expr) (rest : List Expr) (s : Moist.MIR.FreshState) :
    (alphaRenameList σ (e :: rest)) s =
      ((alphaRename σ e s).1 :: (alphaRenameList σ rest (alphaRename σ e s).2).1,
       (alphaRenameList σ rest (alphaRename σ e s).2).2) := by
  show (do
      let e' ← alphaRename σ e
      let rest' ← alphaRenameList σ rest
      pure (e' :: rest')) s = _
  rfl

private theorem alphaRenameBinds_nil_eq (σ : List (VarId × VarId))
    (s : Moist.MIR.FreshState) :
    (alphaRenameBinds σ ([] : List (VarId × Expr × Bool))) s = (([], σ), s) := rfl

/-- Unfolding `alphaRenameBinds σ ((v, rhs, er) :: rest) s`:
    the RHS is renamed first, then `v` is renamed to a fresh `v'`,
    then the rest is recursively renamed under the extended subst. -/
private theorem alphaRenameBinds_cons_eq
    (σ : List (VarId × VarId))
    (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) :
    (alphaRenameBinds σ ((v, rhs, er) :: rest)) s =
      ((((⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId),
          (alphaRename σ rhs s).1, er) ::
        (alphaRenameBinds
          ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
          rest ⟨(alphaRename σ rhs s).2.next + 1⟩).1.1,
       (alphaRenameBinds
          ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
          rest ⟨(alphaRename σ rhs s).2.next + 1⟩).1.2),
       (alphaRenameBinds
          ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
          rest ⟨(alphaRename σ rhs s).2.next + 1⟩).2) := by
  show (do
      let rhs' ← alphaRename σ rhs
      let v' ← freshVar v.hint
      let (rest', subst') ← alphaRenameBinds ((v, v') :: σ) rest
      pure ((v', rhs', er) :: rest', subst')) s = _
  rfl

/-! ## Main soundness theorem (mutual induction) -/

/-- Precondition: env1/env2 are compatible under σ for all variables
    whose uid is ≤ B. This is the invariant carried through the
    structural induction. -/
private def Compat (σ : List (VarId × VarId))
    (env1 env2 : List VarId) (B : Nat) : Prop :=
  ∀ w, w.uid ≤ B → envLookupT env1 w = envLookupT env2 (substLookup σ w)

/-- Precondition: subst values have uids strictly between `B` and `s.next`. -/
private def SubstFreshAbove (σ : List (VarId × VarId))
    (s : Moist.MIR.FreshState) (B : Nat) : Prop :=
  ∀ p ∈ σ, B < p.2.uid ∧ p.2.uid < s.next

/-- Extending `Compat` by a `.Lam`/`.Fix` binder (same variable on both
    sides, `substShadow`-ed subst). -/
private theorem Compat_lam
    (σ : List (VarId × VarId)) (env1 env2 : List VarId) (B : Nat)
    (v : VarId) (hv : v.uid ≤ B)
    (hcompat : Compat σ env1 env2 B)
    (hsubst_lo : ∀ p ∈ σ, B < p.2.uid)
    : Compat (substShadow σ v) (v :: env1) (v :: env2) B := by
  intro w hw
  by_cases hvw_beq : (v == w) = true
  · have ⟨ho, hu⟩ := (VarId_beq_true_iff v w).mp hvw_beq
    rw [envLookupT_cons_same_uid v w env1 ho hu]
    have hshad : substLookup (substShadow σ v) w = w := by
      apply substLookup_identity_of_no_match
      intro q hq
      rw [substShadow_mem_iff] at hq
      cases hqw : (q.1 == w)
      · rfl
      · exfalso
        have ⟨ho_qw, hu_qw⟩ := (VarId_beq_true_iff q.1 w).mp hqw
        have hqv : (q.1 == v) = true := by
          rw [VarId_beq_true_iff]
          exact ⟨ho_qw.trans ho.symm, hu_qw.trans hu.symm⟩
        rw [hqv] at hq
        exact Bool.noConfusion hq.2
    rw [hshad, envLookupT_cons_same_uid v w env2 ho hu]
  · have hvw_false : (v == w) = false := by
      cases hb : (v == w); rfl; exact absurd hb hvw_beq
    -- General case: (v == w) = false. LHS = (envLookupT env1 w).map (·+1).
    rw [Moist.MIR.envLookupT_cons_neq v w env1 hvw_false]
    rw [substLookup_substShadow_neq σ v w hvw_false]
    -- Need: envLookupT (v :: env2) (substLookup σ w) = (envLookupT env1 w).map (·+1).
    -- Via Compat: envLookupT env1 w = envLookupT env2 (substLookup σ w).
    -- So reduces to showing (v == substLookup σ w) = false.
    have hv_ne_u : (v == substLookup σ w) = false := by
      rcases substLookup_result_in_image_or_self σ w with heq | ⟨p, hp, hpeq⟩
      · rw [heq]; exact hvw_false
      · rw [hpeq]
        -- v.uid ≤ B < p.2.uid, so v.uid ≠ p.2.uid.
        rw [VarId_beq_false_iff]
        refine Or.inr ?_
        have := hsubst_lo p hp
        omega
    rw [Moist.MIR.envLookupT_cons_neq v (substLookup σ w) env2 hv_ne_u]
    rw [hcompat w hw]

/-- Extending `Compat` by a `.Let` binder (renames `v` to fresh `v'`). -/
private theorem Compat_let
    (σ : List (VarId × VarId)) (env1 env2 : List VarId) (B : Nat)
    (s : Moist.MIR.FreshState) (hs : B < s.next)
    (v v' : VarId) (_hv : v.uid ≤ B) (hv'_uid : v'.uid = s.next)
    (hcompat : Compat σ env1 env2 B)
    (hsubst : SubstFreshAbove σ s B)
    : Compat ((v, v') :: σ) (v :: env1) (v' :: env2) B := by
  intro w hw
  by_cases hvw_beq : (v == w) = true
  · have ⟨ho, hu⟩ := (VarId_beq_true_iff v w).mp hvw_beq
    rw [envLookupT_cons_same_uid v w env1 ho hu]
    rw [substLookup_cons_match v v' σ w hvw_beq]
    rw [envLookupT_cons_same_uid v' v' env2 rfl rfl]
  · have hvw_false : (v == w) = false := by
      cases hb : (v == w); rfl; exact absurd hb hvw_beq
    -- General case: (v == w) = false.
    rw [Moist.MIR.envLookupT_cons_neq v w env1 hvw_false]
    rw [substLookup_cons_nomatch v v' σ w hvw_false]
    -- Need: envLookupT (v' :: env2) (substLookup σ w) = (envLookupT env1 w).map (·+1).
    -- Via Compat: envLookupT env1 w = envLookupT env2 (substLookup σ w).
    -- Reduces to showing (v' == substLookup σ w) = false.
    have hv'_ne_u : (v' == substLookup σ w) = false := by
      rcases substLookup_result_in_image_or_self σ w with heq | ⟨p, hp, hpeq⟩
      · rw [heq]
        -- v'.uid = s.next > B ≥ w.uid, so v'.uid ≠ w.uid.
        rw [VarId_beq_false_iff]
        refine Or.inr ?_
        rw [hv'_uid]
        have : w.uid < s.next := Nat.lt_of_le_of_lt hw hs
        omega
      · rw [hpeq]
        -- v'.uid = s.next, p.2.uid < s.next.
        rw [VarId_beq_false_iff]
        refine Or.inr ?_
        rw [hv'_uid]
        have := (hsubst p hp).2
        omega
    rw [Moist.MIR.envLookupT_cons_neq v' (substLookup σ w) env2 hv'_ne_u]
    rw [hcompat w hw]

/-! ## The main mutual induction -/

mutual

/-- Main alpha-rename soundness: for any `e`, running `alphaRename σ e s`
    yields an expression whose `lowerTotal` matches `lowerTotal env1 e`
    (for envs in σ-compat, assuming a freshness bound `B`). -/
theorem alphaRename_lowerTotal_eq (B : Nat) (e : Expr)
    (σ : List (VarId × VarId)) (s : Moist.MIR.FreshState)
    (env1 env2 : List VarId)
    (he : maxUidExpr e ≤ B)
    (hs : B < s.next)
    (hsubst : SubstFreshAbove σ s B)
    (hcompat : Compat σ env1 env2 B) :
    lowerTotal env1 e = lowerTotal env2 (alphaRename σ e s).1 ∧
    s.next ≤ (alphaRename σ e s).2.next := by
  have hsubst_lo : ∀ p ∈ σ, B < p.2.uid := fun p hp => (hsubst p hp).1
  match e with
  | .Var v =>
    have hv_le : v.uid ≤ B := by
      have hh : maxUidExpr (.Var v) ≤ B := he
      simp only [maxUidExpr] at hh
      exact hh
    refine ⟨?_, Nat.le_refl _⟩
    show lowerTotal env1 (.Var v) = lowerTotal env2 (.Var (substLookup σ v))
    have hcv := hcompat v hv_le
    simp only [lowerTotal.eq_1]
    rw [hcv]
  | .Lit (c, ty) =>
    refine ⟨?_, Nat.le_refl _⟩
    show lowerTotal env1 (.Lit (c, ty)) = lowerTotal env2 (.Lit (c, ty))
    simp only [lowerTotal.eq_2]
  | .Builtin b =>
    refine ⟨?_, Nat.le_refl _⟩
    show lowerTotal env1 (.Builtin b) = lowerTotal env2 (.Builtin b)
    simp only [lowerTotal.eq_3]
  | .Error =>
    refine ⟨?_, Nat.le_refl _⟩
    show lowerTotal env1 .Error = lowerTotal env2 .Error
    simp only [lowerTotal.eq_4]
  | .Lam v body =>
    rw [alphaRename_lam_eq σ v body s]
    have hv_le : v.uid ≤ B := by
      have hh : maxUidExpr (.Lam v body) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have hbody_le : maxUidExpr body ≤ B := by
      have hh : maxUidExpr (.Lam v body) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have hsubst_shad : SubstFreshAbove (substShadow σ v) s B := by
      intro p hp
      rw [substShadow_mem_iff] at hp
      exact hsubst p hp.1
    have hcompat_shad : Compat (substShadow σ v) (v :: env1) (v :: env2) B :=
      Compat_lam σ env1 env2 B v hv_le hcompat hsubst_lo
    have ⟨hbody_eq, hbody_mono⟩ :=
      alphaRename_lowerTotal_eq B body (substShadow σ v) s (v :: env1) (v :: env2)
        hbody_le hs hsubst_shad hcompat_shad
    refine ⟨?_, hbody_mono⟩
    show lowerTotal env1 (.Lam v body) =
         lowerTotal env2 (.Lam v (alphaRename (substShadow σ v) body s).1)
    simp only [lowerTotal.eq_5, hbody_eq]
  | .Fix v body =>
    rw [alphaRename_fix_eq σ v body s]
    have hv_le : v.uid ≤ B := by
      have hh : maxUidExpr (.Fix v body) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have hbody_le : maxUidExpr body ≤ B := by
      have hh : maxUidExpr (.Fix v body) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have hsubst_shad : SubstFreshAbove (substShadow σ v) s B := by
      intro p hp
      rw [substShadow_mem_iff] at hp
      exact hsubst p hp.1
    have hcompat_shad : Compat (substShadow σ v) (v :: env1) (v :: env2) B :=
      Compat_lam σ env1 env2 B v hv_le hcompat hsubst_lo
    have ⟨_, hbody_mono⟩ :=
      alphaRename_lowerTotal_eq B body (substShadow σ v) s (v :: env1) (v :: env2)
        hbody_le hs hsubst_shad hcompat_shad
    refine ⟨?_, hbody_mono⟩
    show lowerTotal env1 (.Fix v body) =
         lowerTotal env2 (.Fix v (alphaRename (substShadow σ v) body s).1)
    simp only [lowerTotal.eq_12]
  | .App f x =>
    rw [alphaRename_app_eq σ f x s]
    have hf_le : maxUidExpr f ≤ B := by
      have hh : maxUidExpr (.App f x) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have hx_le : maxUidExpr x ≤ B := by
      have hh : maxUidExpr (.App f x) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have ⟨hf_eq, hf_mono⟩ :=
      alphaRename_lowerTotal_eq B f σ s env1 env2 hf_le hs hsubst hcompat
    have hs1_lt : B < (alphaRename σ f s).2.next := Nat.lt_of_lt_of_le hs hf_mono
    have hsubst1 : SubstFreshAbove σ (alphaRename σ f s).2 B := by
      intro p hp
      refine ⟨(hsubst p hp).1, ?_⟩
      exact Nat.lt_of_lt_of_le (hsubst p hp).2 hf_mono
    have ⟨hx_eq, hx_mono⟩ :=
      alphaRename_lowerTotal_eq B x σ (alphaRename σ f s).2 env1 env2
        hx_le hs1_lt hsubst1 hcompat
    refine ⟨?_, Nat.le_trans hf_mono hx_mono⟩
    show lowerTotal env1 (.App f x) =
         lowerTotal env2 (.App (alphaRename σ f s).1
           (alphaRename σ x (alphaRename σ f s).2).1)
    simp only [lowerTotal.eq_6, hf_eq, hx_eq]
  | .Force inner =>
    rw [alphaRename_force_eq σ inner s]
    have hi_le : maxUidExpr inner ≤ B := by
      have hh : maxUidExpr (.Force inner) ≤ B := he
      simp only [maxUidExpr] at hh; exact hh
    have ⟨hi_eq, hi_mono⟩ :=
      alphaRename_lowerTotal_eq B inner σ s env1 env2 hi_le hs hsubst hcompat
    refine ⟨?_, hi_mono⟩
    show lowerTotal env1 (.Force inner) =
         lowerTotal env2 (.Force (alphaRename σ inner s).1)
    simp only [lowerTotal.eq_7, hi_eq]
  | .Delay inner =>
    rw [alphaRename_delay_eq σ inner s]
    have hi_le : maxUidExpr inner ≤ B := by
      have hh : maxUidExpr (.Delay inner) ≤ B := he
      simp only [maxUidExpr] at hh; exact hh
    have ⟨hi_eq, hi_mono⟩ :=
      alphaRename_lowerTotal_eq B inner σ s env1 env2 hi_le hs hsubst hcompat
    refine ⟨?_, hi_mono⟩
    show lowerTotal env1 (.Delay inner) =
         lowerTotal env2 (.Delay (alphaRename σ inner s).1)
    simp only [lowerTotal.eq_8, hi_eq]
  | .Constr tag args =>
    rw [alphaRename_constr_eq σ tag args s]
    have ha_le : maxUidExprList args ≤ B := by
      have hh : maxUidExpr (.Constr tag args) ≤ B := he
      simp only [maxUidExpr] at hh; exact hh
    have ⟨ha_eq, ha_mono⟩ :=
      alphaRenameList_lowerTotalList_eq B args σ s env1 env2 ha_le hs hsubst hcompat
    refine ⟨?_, ha_mono⟩
    show lowerTotal env1 (.Constr tag args) =
         lowerTotal env2 (.Constr tag (alphaRenameList σ args s).1)
    simp only [lowerTotal.eq_9, ha_eq]
  | .Case scrut alts =>
    rw [alphaRename_case_eq σ scrut alts s]
    have hscr_le : maxUidExpr scrut ≤ B := by
      have hh : maxUidExpr (.Case scrut alts) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have ha_le : maxUidExprList alts ≤ B := by
      have hh : maxUidExpr (.Case scrut alts) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have ⟨hscr_eq, hscr_mono⟩ :=
      alphaRename_lowerTotal_eq B scrut σ s env1 env2 hscr_le hs hsubst hcompat
    have hs1_lt : B < (alphaRename σ scrut s).2.next := Nat.lt_of_lt_of_le hs hscr_mono
    have hsubst1 : SubstFreshAbove σ (alphaRename σ scrut s).2 B := by
      intro p hp
      refine ⟨(hsubst p hp).1, ?_⟩
      exact Nat.lt_of_lt_of_le (hsubst p hp).2 hscr_mono
    have ⟨ha_eq, ha_mono⟩ :=
      alphaRenameList_lowerTotalList_eq B alts σ (alphaRename σ scrut s).2 env1 env2
        ha_le hs1_lt hsubst1 hcompat
    refine ⟨?_, Nat.le_trans hscr_mono ha_mono⟩
    show lowerTotal env1 (.Case scrut alts) =
         lowerTotal env2 (.Case (alphaRename σ scrut s).1
           (alphaRenameList σ alts (alphaRename σ scrut s).2).1)
    simp only [lowerTotal.eq_10, hscr_eq, ha_eq]
  | .Let binds body =>
    rw [alphaRename_let_eq σ binds body s]
    have hb_le : maxUidExprBinds binds ≤ B := by
      have hh : maxUidExpr (.Let binds body) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have hbody_le : maxUidExpr body ≤ B := by
      have hh : maxUidExpr (.Let binds body) ≤ B := he
      simp only [maxUidExpr] at hh; omega
    have ⟨hlet_eq, hlet_mono⟩ :=
      alphaRenameBinds_lowerTotalLet_eq B binds body σ s env1 env2
        hb_le hbody_le hs hsubst hcompat
    refine ⟨?_, hlet_mono⟩
    show lowerTotal env1 (.Let binds body) =
         lowerTotal env2 (.Let (alphaRenameBinds σ binds s).1.1
           (alphaRename (alphaRenameBinds σ binds s).1.2 body
             (alphaRenameBinds σ binds s).2).1)
    simp only [lowerTotal.eq_11, hlet_eq]
termination_by sizeOf e

/-- List version of alpha-rename soundness. -/
theorem alphaRenameList_lowerTotalList_eq (B : Nat) (es : List Expr)
    (σ : List (VarId × VarId)) (s : Moist.MIR.FreshState)
    (env1 env2 : List VarId)
    (he : maxUidExprList es ≤ B)
    (hs : B < s.next)
    (hsubst : SubstFreshAbove σ s B)
    (hcompat : Compat σ env1 env2 B) :
    lowerTotalList env1 es = lowerTotalList env2 (alphaRenameList σ es s).1 ∧
    s.next ≤ (alphaRenameList σ es s).2.next := by
  match es with
  | [] =>
    refine ⟨?_, Nat.le_refl _⟩
    show lowerTotalList env1 [] = lowerTotalList env2 []
    simp only [lowerTotalList.eq_1]
  | e :: rest =>
    rw [alphaRenameList_cons_eq]
    have he_le : maxUidExpr e ≤ B := by
      have hh : maxUidExprList (e :: rest) ≤ B := he
      simp only [maxUidExprList] at hh; omega
    have hrest_le : maxUidExprList rest ≤ B := by
      have hh : maxUidExprList (e :: rest) ≤ B := he
      simp only [maxUidExprList] at hh; omega
    have ⟨he_eq, he_mono⟩ :=
      alphaRename_lowerTotal_eq B e σ s env1 env2 he_le hs hsubst hcompat
    have hs1_lt : B < (alphaRename σ e s).2.next := Nat.lt_of_lt_of_le hs he_mono
    have hsubst1 : SubstFreshAbove σ (alphaRename σ e s).2 B := by
      intro p hp
      refine ⟨(hsubst p hp).1, ?_⟩
      exact Nat.lt_of_lt_of_le (hsubst p hp).2 he_mono
    have ⟨hr_eq, hr_mono⟩ :=
      alphaRenameList_lowerTotalList_eq B rest σ (alphaRename σ e s).2 env1 env2
        hrest_le hs1_lt hsubst1 hcompat
    refine ⟨?_, Nat.le_trans he_mono hr_mono⟩
    show lowerTotalList env1 (e :: rest) =
         lowerTotalList env2 ((alphaRename σ e s).1 ::
           (alphaRenameList σ rest (alphaRename σ e s).2).1)
    simp only [lowerTotalList.eq_2, he_eq, hr_eq]
termination_by sizeOf es

/-- Let-binds version of alpha-rename soundness: proves the equality
    of `lowerTotalLet env1 binds body` with the renamed counterpart,
    where `body` gets renamed with the *output* subst of `alphaRenameBinds`. -/
theorem alphaRenameBinds_lowerTotalLet_eq (B : Nat)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (σ : List (VarId × VarId)) (s : Moist.MIR.FreshState)
    (env1 env2 : List VarId)
    (hb : maxUidExprBinds binds ≤ B)
    (hbody : maxUidExpr body ≤ B)
    (hs : B < s.next)
    (hsubst : SubstFreshAbove σ s B)
    (hcompat : Compat σ env1 env2 B) :
    lowerTotalLet env1 binds body =
      lowerTotalLet env2
        (alphaRenameBinds σ binds s).1.1
        (alphaRename (alphaRenameBinds σ binds s).1.2 body
          (alphaRenameBinds σ binds s).2).1 ∧
    s.next ≤ (alphaRename (alphaRenameBinds σ binds s).1.2 body
               (alphaRenameBinds σ binds s).2).2.next := by
  match binds with
  | [] =>
    rw [alphaRenameBinds_nil_eq]
    -- alphaRenameBinds σ [] s = (([], σ), s)
    -- Result: lowerTotalLet env1 [] body = lowerTotalLet env2 [] (alphaRename σ body s).1
    have ⟨hbody_eq, hbody_mono⟩ :=
      alphaRename_lowerTotal_eq B body σ s env1 env2 hbody hs hsubst hcompat
    refine ⟨?_, hbody_mono⟩
    show lowerTotalLet env1 [] body =
         lowerTotalLet env2 [] (alphaRename σ body s).1
    simp only [lowerTotalLet.eq_1, hbody_eq]
  | (v, rhs, er) :: rest =>
    rw [alphaRenameBinds_cons_eq σ v rhs er rest s]
    have hv_le : v.uid ≤ B := by
      have hh : maxUidExprBinds ((v, rhs, er) :: rest) ≤ B := hb
      simp only [maxUidExprBinds] at hh; omega
    have hrhs_le : maxUidExpr rhs ≤ B := by
      have hh : maxUidExprBinds ((v, rhs, er) :: rest) ≤ B := hb
      simp only [maxUidExprBinds] at hh; omega
    have hrest_le : maxUidExprBinds rest ≤ B := by
      have hh : maxUidExprBinds ((v, rhs, er) :: rest) ≤ B := hb
      simp only [maxUidExprBinds] at hh; omega
    have ⟨hrhs_eq, hrhs_mono⟩ :=
      alphaRename_lowerTotal_eq B rhs σ s env1 env2 hrhs_le hs hsubst hcompat
    -- Define the fresh v' and the new state s2 explicitly (not via `let`).
    have hs1_lt : B < (alphaRename σ rhs s).2.next := Nat.lt_of_lt_of_le hs hrhs_mono
    have hs2_lt : B < (⟨(alphaRename σ rhs s).2.next + 1⟩ : Moist.MIR.FreshState).next := by
      show B < (alphaRename σ rhs s).2.next + 1
      omega
    have hv'_uid :
        (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId).uid
          = (alphaRename σ rhs s).2.next := rfl
    have hsubst1 : SubstFreshAbove σ (alphaRename σ rhs s).2 B := by
      intro p hp
      refine ⟨(hsubst p hp).1, ?_⟩
      exact Nat.lt_of_lt_of_le (hsubst p hp).2 hrhs_mono
    have hsubst_ext :
        SubstFreshAbove
          ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
          (⟨(alphaRename σ rhs s).2.next + 1⟩ : Moist.MIR.FreshState)
          B := by
      intro q hq
      rcases List.mem_cons.mp hq with heq | hq_rest
      · refine ⟨?_, ?_⟩
        · show B < q.2.uid
          rw [heq]; exact hs1_lt
        · show q.2.uid < (alphaRename σ rhs s).2.next + 1
          rw [heq]; exact Nat.lt_succ_self _
      · refine ⟨(hsubst q hq_rest).1, ?_⟩
        have hh : q.2.uid < s.next := (hsubst q hq_rest).2
        show q.2.uid < (alphaRename σ rhs s).2.next + 1
        have := hrhs_mono
        omega
    have hcompat_ext :
        Compat
          ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
          (v :: env1)
          ((⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId) :: env2) B :=
      Compat_let σ env1 env2 B (alphaRename σ rhs s).2 hs1_lt v
        ⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ hv_le hv'_uid hcompat hsubst1
    have ⟨hrest_eq, hrest_mono⟩ :=
      alphaRenameBinds_lowerTotalLet_eq B rest body
        ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
        ⟨(alphaRename σ rhs s).2.next + 1⟩
        (v :: env1)
        ((⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId) :: env2)
        hrest_le hbody hs2_lt hsubst_ext hcompat_ext
    refine ⟨?_, ?_⟩
    · -- Forward equality. With the projection-based `alphaRenameBinds_cons_eq`
      -- applied, both sides reduce via the IHs.
      simp only [lowerTotalLet.eq_2, hrhs_eq, hrest_eq]
    · -- State monotonicity
      have hmid : (alphaRename σ rhs s).2.next ≤
                  (⟨(alphaRename σ rhs s).2.next + 1⟩ : Moist.MIR.FreshState).next := by
        show (alphaRename σ rhs s).2.next ≤ (alphaRename σ rhs s).2.next + 1
        omega
      exact Nat.le_trans hrhs_mono (Nat.le_trans hmid hrest_mono)
termination_by sizeOf binds + sizeOf body

end

/-! ## Top-level corollaries -/

open Moist.MIR (fixCountList fixCountBinds)

-- `alphaRename` preserves Fix-freedom: it never introduces new Fix nodes.
mutual
theorem alphaRename_fixCount_zero (σ : List (VarId × VarId)) (e : Expr)
    (s : Moist.MIR.FreshState) (hfc : fixCount e = 0) :
    fixCount (Moist.MIR.alphaRename σ e s).1 = 0 := by
  match e with
  | .Var v =>
    show fixCount (.Var (substLookup σ v)) = 0
    show Moist.MIR.fixCount (.Var (substLookup σ v)) = 0
    simp [Moist.MIR.fixCount]
  | .Lit _ =>
    show Moist.MIR.fixCount (.Lit _) = 0
    simp [Moist.MIR.fixCount]
  | .Builtin _ =>
    show Moist.MIR.fixCount (.Builtin _) = 0
    simp [Moist.MIR.fixCount]
  | .Error =>
    show Moist.MIR.fixCount .Error = 0
    simp [Moist.MIR.fixCount]
  | .Lam v body =>
    rw [alphaRename_lam_eq σ v body s]
    show fixCount (.Lam v (alphaRename (substShadow σ v) body s).1) = 0
    have hbody : fixCount body = 0 := by
      simp only [Moist.MIR.fixCount] at hfc; exact hfc
    have := alphaRename_fixCount_zero (substShadow σ v) body s hbody
    simp only [Moist.MIR.fixCount]; exact this
  | .Fix v body =>
    -- Fix has fixCount > 0, contradicting hfc
    simp only [Moist.MIR.fixCount] at hfc; omega
  | .App f x =>
    rw [alphaRename_app_eq σ f x s]
    have hf : fixCount f = 0 := by
      simp only [Moist.MIR.fixCount] at hfc; omega
    have hx : fixCount x = 0 := by
      simp only [Moist.MIR.fixCount] at hfc; omega
    have ihf := alphaRename_fixCount_zero σ f s hf
    have ihx := alphaRename_fixCount_zero σ x (alphaRename σ f s).2 hx
    show fixCount (.App _ _) = 0
    simp only [Moist.MIR.fixCount]; omega
  | .Force inner =>
    rw [alphaRename_force_eq σ inner s]
    have h : fixCount inner = 0 := by simp only [Moist.MIR.fixCount] at hfc; exact hfc
    have ih := alphaRename_fixCount_zero σ inner s h
    show fixCount (.Force _) = 0; simp only [Moist.MIR.fixCount]; exact ih
  | .Delay inner =>
    rw [alphaRename_delay_eq σ inner s]
    have h : fixCount inner = 0 := by simp only [Moist.MIR.fixCount] at hfc; exact hfc
    have ih := alphaRename_fixCount_zero σ inner s h
    show fixCount (.Delay _) = 0; simp only [Moist.MIR.fixCount]; exact ih
  | .Constr tag args =>
    rw [alphaRename_constr_eq σ tag args s]
    have h : fixCountList args = 0 := by simp only [Moist.MIR.fixCount] at hfc; exact hfc
    have ih := alphaRenameList_fixCountList_zero σ args s h
    show fixCount (.Constr _ _) = 0; simp only [Moist.MIR.fixCount]; exact ih
  | .Case scrut alts =>
    rw [alphaRename_case_eq σ scrut alts s]
    have hs : fixCount scrut = 0 := by simp only [Moist.MIR.fixCount] at hfc; omega
    have ha : fixCountList alts = 0 := by simp only [Moist.MIR.fixCount] at hfc; omega
    have ihs := alphaRename_fixCount_zero σ scrut s hs
    have iha := alphaRenameList_fixCountList_zero σ alts (alphaRename σ scrut s).2 ha
    show fixCount (.Case _ _) = 0; simp only [Moist.MIR.fixCount]; omega
  | .Let binds body =>
    rw [alphaRename_let_eq σ binds body s]
    have hb : fixCountBinds binds = 0 := by simp only [Moist.MIR.fixCount] at hfc; omega
    have hbody : fixCount body = 0 := by simp only [Moist.MIR.fixCount] at hfc; omega
    have ihb := alphaRenameBinds_fixCountBinds_zero σ binds s hb
    have ih_body := alphaRename_fixCount_zero
      (alphaRenameBinds σ binds s).1.2 body
      (alphaRenameBinds σ binds s).2 hbody
    show fixCount (.Let _ _) = 0; simp only [Moist.MIR.fixCount]; omega
termination_by sizeOf e

theorem alphaRenameList_fixCountList_zero (σ : List (VarId × VarId)) (es : List Expr)
    (s : Moist.MIR.FreshState) (hfc : fixCountList es = 0) :
    fixCountList (Moist.MIR.alphaRenameList σ es s).1 = 0 := by
  match es with
  | [] =>
    rw [alphaRenameList_nil_eq]; exact hfc
  | e :: rest =>
    rw [alphaRenameList_cons_eq]
    have he : fixCount e = 0 := by simp only [Moist.MIR.fixCountList] at hfc; omega
    have hr : fixCountList rest = 0 := by simp only [Moist.MIR.fixCountList] at hfc; omega
    have ihe := alphaRename_fixCount_zero σ e s he
    have ihr := alphaRenameList_fixCountList_zero σ rest (alphaRename σ e s).2 hr
    show fixCountList (_ :: _) = 0; simp only [Moist.MIR.fixCountList]; omega
termination_by sizeOf es

theorem alphaRenameBinds_fixCountBinds_zero (σ : List (VarId × VarId))
    (binds : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState)
    (hfc : fixCountBinds binds = 0) :
    fixCountBinds (Moist.MIR.alphaRenameBinds σ binds s).1.1 = 0 := by
  match binds with
  | [] =>
    show fixCountBinds (alphaRenameBinds σ [] s).1.1 = 0
    rw [alphaRenameBinds_nil_eq]; exact hfc
  | (v, rhs, er) :: rest =>
    rw [alphaRenameBinds_cons_eq σ v rhs er rest s]
    have hrhs : fixCount rhs = 0 := by
      simp only [Moist.MIR.fixCountBinds] at hfc; omega
    have hrest : fixCountBinds rest = 0 := by
      simp only [Moist.MIR.fixCountBinds] at hfc; omega
    have ihrhs := alphaRename_fixCount_zero σ rhs s hrhs
    have ihrest :=
      alphaRenameBinds_fixCountBinds_zero
        ((v, (⟨(alphaRename σ rhs s).2.next, .gen, v.hint⟩ : VarId)) :: σ)
        rest ⟨(alphaRename σ rhs s).2.next + 1⟩ hrest
    show fixCountBinds (_ :: _) = 0
    simp only [Moist.MIR.fixCountBinds]; omega
termination_by sizeOf binds
end

/-- Top-level corollary: `alphaRenameTop e` starting from a fresh state
    strictly above `maxUidExpr e` produces a term whose `lowerTotal` is
    the same as `e`'s in the same environment. -/
theorem alphaRenameTop_lowerTotal_eq (e : Expr) (K : Moist.MIR.FreshState)
    (hK : maxUidExpr e < K.next) (env : List VarId) :
    lowerTotal env e = lowerTotal env (Moist.MIR.alphaRenameTop e K).1 := by
  have ⟨heq, _⟩ :=
    alphaRename_lowerTotal_eq (maxUidExpr e) e [] K env env
      (Nat.le_refl _)
      hK
      (by intro p hp; exact absurd hp List.not_mem_nil)
      (by intro _ _; rfl)
  exact heq

/-- `alphaRenameTop e K` has the same `lowerTotalExpr` as `e` under
    every environment, for Fix-free `e`. -/
theorem alphaRenameTop_lowerTotalExpr_eq (e : Expr) (K : Moist.MIR.FreshState)
    (hK : maxUidExpr e < K.next)
    (hFixFree : fixCount e = 0)
    (env : List VarId) :
    lowerTotalExpr env e = lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 := by
  have h_rename_fix_free : fixCount (Moist.MIR.alphaRenameTop e K).1 = 0 :=
    alphaRename_fixCount_zero [] e K hFixFree
  have h1 : lowerTotalExpr env e = lowerTotal env e :=
    Moist.MIR.lowerTotalExpr_eq_lowerTotal env e hFixFree
  have h2 : lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 =
            lowerTotal env (Moist.MIR.alphaRenameTop e K).1 :=
    Moist.MIR.lowerTotalExpr_eq_lowerTotal env _ h_rename_fix_free
  rw [h1, h2]
  exact alphaRenameTop_lowerTotal_eq e K hK env

/-- Alpha-rename establishes MIRCtxEq for Fix-free expressions. -/
theorem alphaRenameTop_mirCtxEq (e : Expr) (K : Moist.MIR.FreshState)
    (hK : maxUidExpr e < K.next)
    (hFixFree : fixCount e = 0) :
    MIRCtxEq e (Moist.MIR.alphaRenameTop e K).1 := by
  have h_rename_fix_free : fixCount (Moist.MIR.alphaRenameTop e K).1 = 0 :=
    alphaRename_fixCount_zero [] e K hFixFree
  intro env
  have h1 : lowerTotalExpr env e = lowerTotal env e :=
    Moist.MIR.lowerTotalExpr_eq_lowerTotal env e hFixFree
  have h2 : lowerTotalExpr env (Moist.MIR.alphaRenameTop e K).1 =
            lowerTotal env (Moist.MIR.alphaRenameTop e K).1 :=
    Moist.MIR.lowerTotalExpr_eq_lowerTotal env _ h_rename_fix_free
  have hlow_eq := alphaRenameTop_lowerTotal_eq e K hK env
  refine ⟨?_, ?_⟩
  · rw [h1, h2, hlow_eq]
  · rw [h1, h2, hlow_eq]
    -- Both sides are identical after the rewrites: fold into reflexivity.
    cases h : lowerTotal env (Moist.MIR.alphaRenameTop e K).1 with
    | none => trivial
    | some t => exact Moist.Verified.Contextual.ctxEq_refl t

end Moist.Verified.MIR
