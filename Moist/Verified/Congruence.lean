import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.MIR.LowerTotal
import Moist.Verified.FundamentalLemma

/-! # Congruence lemmas for BehEq and Refines

This module proves that `BehEq` and `Refines` are congruent: if
sub-expressions are related, so are the enclosing expressions.

The proof strategy avoids all CEK-level reasoning by working at the
"identical lowering" level: if two MIR sub-expressions lower to the
**same** UPLC term in every environment, then any enclosing constructor
also lowers identically. This is lifted to `BehEq` / `Refines` via
`behEq_of_lowerTotalExpr_eq`.

## Compositionality

Since `expandFix` computes fresh variables from `maxUidExpr` rather than
threading a counter, `lowerTotalExpr` is fully compositional through all
constructors. Single-child (Force, Delay, Lam) and multi-child (App, Case,
Constr, Let) constructors all decompose without any preconditions.
-/

namespace Moist.Verified.Congruence

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.MIR (lowerTotalExpr lowerTotalExpr_eq_lowerTotal)
open Moist.Verified.Semantics

/-! ## ValueEq monotonicity (re-exported from FundamentalLemma) -/

-- valueEq_mono and listValueEq_mono are now in the mutual block in FundamentalLemma.lean.
-- We re-open them here for backward compatibility with existing imports.

/-! ## Identical lowering implies behavioral equivalence -/

/-- If two MIR expressions lower to the same UPLC term via `lowerTotalExpr`
    in every environment, they are behaviorally equivalent. Since the lowered
    term is literally identical, error/halt agreement is `Iff.rfl` and value
    agreement follows from `valueEq_refl` + `reaches_unique`. -/
theorem behEq_of_lowerTotalExpr_eq (m₁ m₂ : Expr)
    (h : ∀ env, lowerTotalExpr env m₁ = lowerTotalExpr env m₂) : m₁ ≋ m₂ := by
  unfold BehEq; intro env; rw [h env]
  cases lowerTotalExpr env m₂ with
  | none => trivial
  | some t =>
    intro _ _
    exact ⟨Iff.rfl, Iff.rfl, fun k v₁ v₂ h₁ h₂ =>
      reaches_unique h₁ h₂ ▸ valueEq_refl k v₁⟩

/-- Identical lowering via `lowerTotalExpr` implies refinement in both
    directions, hence refinement. -/
theorem refines_of_lowerTotalExpr_eq (m₁ m₂ : Expr)
    (h : ∀ env, lowerTotalExpr env m₁ = lowerTotalExpr env m₂) : m₁ ⊑ m₂ :=
  ⟨fun env hs => by rw [← h env]; exact hs,
   behEq_of_lowerTotalExpr_eq m₁ m₂ h⟩

/-! ## Reflexivity and symmetry -/

/-- Every expression refines itself. -/
theorem refines_refl (e : Expr) : e ⊑ e :=
  refines_of_lowerTotalExpr_eq e e (fun _ => rfl)

/-- BehEq is symmetric. -/
theorem behEq_symm {m₁ m₂ : Expr} (h : m₁ ≋ m₂) : m₂ ≋ m₁ := by
  unfold BehEq at h ⊢; intro env
  have he := h env
  cases h1 : lowerTotalExpr env m₂ with
  | none => split <;> trivial
  | some t2 =>
    cases h2 : lowerTotalExpr env m₁ with
    | none => split <;> trivial
    | some t1 =>
      rw [h2, h1] at he
      intro ρ hwf
      have ⟨herr, hhalt, hval⟩ := he ρ hwf
      exact ⟨herr.symm, hhalt.symm, fun k v₁ v₂ hv₁ hv₂ =>
        valueEq_symm k _ _ (hval k v₂ v₁ hv₂ hv₁)⟩

/-! ## Compositionality of lowerTotalExpr

Since `expandFix` no longer threads a fresh counter between siblings,
`lowerTotalExpr` decomposes cleanly through ALL constructors. No
`fixCount = 0` precondition is needed for any constructor. -/

/-- `expandFix` on Force. -/
private theorem expandFix_force (e : Expr) :
    expandFix (.Force e) = .Force (expandFix e) := by
  simp [expandFix]

/-- `expandFix` on Delay. -/
private theorem expandFix_delay (e : Expr) :
    expandFix (.Delay e) = .Delay (expandFix e) := by
  simp [expandFix]

/-- `expandFix` on Lam. -/
private theorem expandFix_lam (x : VarId) (body : Expr) :
    expandFix (.Lam x body) = .Lam x (expandFix body) := by
  simp [expandFix]

/-- `expandFix` on App. -/
private theorem expandFix_app (f a : Expr) :
    expandFix (.App f a) = .App (expandFix f) (expandFix a) := by
  simp [expandFix]

/-- `expandFix` on Constr. -/
private theorem expandFix_constr (tag : Nat) (args : List Expr) :
    expandFix (.Constr tag args) = .Constr tag (expandFixList args) := by
  simp [expandFix]

/-- `expandFix` on Case. -/
private theorem expandFix_case (s : Expr) (alts : List Expr) :
    expandFix (.Case s alts) = .Case (expandFix s) (expandFixList alts) := by
  simp [expandFix]

/-- `expandFix` on Let. -/
private theorem expandFix_let (binds : List (VarId × Expr × Bool)) (body : Expr) :
    expandFix (.Let binds body) = .Let (expandFixBinds binds) (expandFix body) := by
  simp [expandFix]

/-- `lowerTotalExpr` decomposes through Force. -/
theorem lowerTotalExpr_force (env : List VarId) (e : Expr) :
    lowerTotalExpr env (.Force e) = (lowerTotalExpr env e).bind (fun t => some (.Force t)) := by
  simp only [lowerTotalExpr, expandFix_force]
  simp only [lowerTotal.eq_7, Option.bind_eq_bind]

/-- `lowerTotalExpr` decomposes through Delay. -/
theorem lowerTotalExpr_delay (env : List VarId) (e : Expr) :
    lowerTotalExpr env (.Delay e) = (lowerTotalExpr env e).bind (fun t => some (.Delay t)) := by
  simp only [lowerTotalExpr, expandFix_delay]
  simp only [lowerTotal.eq_8, Option.bind_eq_bind]

/-- `lowerTotalExpr` decomposes through Lam. -/
theorem lowerTotalExpr_lam (env : List VarId) (x : VarId) (body : Expr) :
    lowerTotalExpr env (.Lam x body) =
      (lowerTotalExpr (x :: env) body).bind (fun t => some (.Lam 0 t)) := by
  simp only [lowerTotalExpr, expandFix_lam]
  simp only [lowerTotal.eq_5, Option.bind_eq_bind]

/-- `lowerTotalExpr` decomposes through App. -/
theorem lowerTotalExpr_app (env : List VarId) (f a : Expr) :
    lowerTotalExpr env (.App f a) =
      (lowerTotalExpr env f).bind (fun f' =>
        (lowerTotalExpr env a).bind (fun a' => some (.Apply f' a'))) := by
  simp only [lowerTotalExpr, expandFix_app]
  simp only [lowerTotal.eq_6, Option.bind_eq_bind]

/-- `lowerTotalExpr` decomposes through Constr. -/
theorem lowerTotalExpr_constr (env : List VarId) (tag : Nat) (args : List Expr) :
    lowerTotalExpr env (.Constr tag args) =
      (lowerTotalList env (expandFixList args)).bind (fun args' => some (.Constr tag args')) := by
  simp only [lowerTotalExpr, expandFix_constr]
  simp only [lowerTotal.eq_9, Option.bind_eq_bind]

/-- `lowerTotalExpr` decomposes through Case. -/
theorem lowerTotalExpr_case (env : List VarId) (scrut : Expr) (alts : List Expr) :
    lowerTotalExpr env (.Case scrut alts) =
      (lowerTotalExpr env scrut).bind (fun s' =>
        (lowerTotalList env (expandFixList alts)).bind (fun a' => some (.Case s' a'))) := by
  simp only [lowerTotalExpr, expandFix_case]
  simp only [lowerTotal.eq_10, Option.bind_eq_bind]

/-- `lowerTotalExpr` decomposes through Let. -/
theorem lowerTotalExpr_let (env : List VarId) (binds : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let binds body) =
      lowerTotalLet env (expandFixBinds binds) (expandFix body) := by
  simp only [lowerTotalExpr, expandFix_let]
  simp only [lowerTotal.eq_11]

/-! ## Identical-lowering congruence at the `lowerTotal` level

Each lemma shows: if sub-expressions lower identically via `lowerTotal`
in every environment, the enclosing constructor does too. The proofs are
purely syntactic, using the `lowerTotal` equation lemmas. -/

theorem lowerTotal_force_congr (env : List VarId) (e e' : Expr)
    (h : ∀ env', lowerTotal env' e = lowerTotal env' e') :
    lowerTotal env (.Force e) = lowerTotal env (.Force e') := by
  simp only [lowerTotal.eq_7, h env]

theorem lowerTotal_delay_congr (env : List VarId) (e e' : Expr)
    (h : ∀ env', lowerTotal env' e = lowerTotal env' e') :
    lowerTotal env (.Delay e) = lowerTotal env (.Delay e') := by
  simp only [lowerTotal.eq_8, h env]

theorem lowerTotal_lam_congr (env : List VarId) (x : VarId) (body body' : Expr)
    (h : ∀ env', lowerTotal env' body = lowerTotal env' body') :
    lowerTotal env (.Lam x body) = lowerTotal env (.Lam x body') := by
  simp only [lowerTotal.eq_5, h (x :: env)]

theorem lowerTotal_app_congr (env : List VarId) (f f' a a' : Expr)
    (hf : ∀ env', lowerTotal env' f = lowerTotal env' f')
    (ha : ∀ env', lowerTotal env' a = lowerTotal env' a') :
    lowerTotal env (.App f a) = lowerTotal env (.App f' a') := by
  simp only [lowerTotal.eq_6, hf env, ha env]

theorem lowerTotalList_congr (env : List VarId) (es es' : List Expr)
    (h : ∀ env', lowerTotalList env' es = lowerTotalList env' es') :
    lowerTotalList env es = lowerTotalList env es' := h env

theorem lowerTotal_constr_congr (env : List VarId) (tag : Nat) (args args' : List Expr)
    (h : ∀ env', lowerTotalList env' args = lowerTotalList env' args') :
    lowerTotal env (.Constr tag args) = lowerTotal env (.Constr tag args') := by
  simp only [lowerTotal.eq_9, h env]

theorem lowerTotal_case_congr (env : List VarId) (scrut scrut' : Expr) (alts alts' : List Expr)
    (hs : ∀ env', lowerTotal env' scrut = lowerTotal env' scrut')
    (ha : ∀ env', lowerTotalList env' alts = lowerTotalList env' alts') :
    lowerTotal env (.Case scrut alts) = lowerTotal env (.Case scrut' alts') := by
  simp only [lowerTotal.eq_10, hs env, ha env]

theorem lowerTotalLet_congr (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body body' : Expr)
    (h : ∀ env', lowerTotal env' body = lowerTotal env' body') :
    lowerTotalLet env binds body = lowerTotalLet env binds body' := by
  induction binds generalizing env with
  | nil => simp only [lowerTotalLet.eq_1, h env]
  | cons b rest ih =>
    obtain ⟨x, rhs, er⟩ := b
    simp only [lowerTotalLet.eq_2, ih (x :: env)]

theorem lowerTotal_let_body_congr (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body body' : Expr)
    (h : ∀ env', lowerTotal env' body = lowerTotal env' body') :
    lowerTotal env (.Let binds body) = lowerTotal env (.Let binds body') := by
  simp only [lowerTotal.eq_11]; exact lowerTotalLet_congr env binds body body' h

/-! ## Congruence for lowerTotalList from element-wise lowerTotal equality -/

/-- If each element of two lists lowers identically, the list lowering is identical. -/
theorem lowerTotalList_congr_pointwise (env : List VarId) :
    ∀ (es es' : List Expr),
    List.length es = List.length es' →
    (∀ (i : Nat) (e e' : Expr), es[i]? = some e → es'[i]? = some e' →
      ∀ env', lowerTotal env' e = lowerTotal env' e') →
    lowerTotalList env es = lowerTotalList env es'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | e :: rest, e' :: rest', hlen, helem => by
    simp only [lowerTotalList.eq_2]
    have he : ∀ env', lowerTotal env' e = lowerTotal env' e' :=
      helem 0 e e' rfl rfl
    have hrest : ∀ (i : Nat) (a a' : Expr), rest[i]? = some a → rest'[i]? = some a' →
        ∀ env', lowerTotal env' a = lowerTotal env' a' :=
      fun i a a' ha ha' => helem (i + 1) a a' ha ha'
    rw [he env, lowerTotalList_congr_pointwise env rest rest' (by simpa using hlen) hrest]

/-! ## Lifting to lowerTotalExpr: all constructors (no fixCount needed)

Since `expandFix` is compositional (no counter threading), `lowerTotalExpr`
decomposes cleanly through all constructors. No `fixCount = 0` precondition
is needed for any constructor. -/

/-- Force congruence: identical lowering lifts through Force. -/
theorem lowerTotalExpr_force_congr (e e' : Expr)
    (h : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e') :
    ∀ env, lowerTotalExpr env (.Force e) = lowerTotalExpr env (.Force e') := by
  intro env
  simp only [lowerTotalExpr_force, h env]

/-- Delay congruence: identical lowering lifts through Delay. -/
theorem lowerTotalExpr_delay_congr (e e' : Expr)
    (h : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e') :
    ∀ env, lowerTotalExpr env (.Delay e) = lowerTotalExpr env (.Delay e') := by
  intro env
  simp only [lowerTotalExpr_delay, h env]

/-- Lam congruence: identical lowering lifts through Lam. -/
theorem lowerTotalExpr_lam_congr (x : VarId) (body body' : Expr)
    (h : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    ∀ env, lowerTotalExpr env (.Lam x body) = lowerTotalExpr env (.Lam x body') := by
  intro env
  simp only [lowerTotalExpr_lam, h (x :: env)]

/-- App congruence: identical lowering lifts through App. -/
theorem lowerTotalExpr_app_congr (f f' a a' : Expr)
    (hf : ∀ env, lowerTotalExpr env f = lowerTotalExpr env f')
    (ha : ∀ env, lowerTotalExpr env a = lowerTotalExpr env a') :
    ∀ env, lowerTotalExpr env (.App f a) = lowerTotalExpr env (.App f' a') := by
  intro env
  rw [lowerTotalExpr_app, lowerTotalExpr_app, hf env, ha env]

/-- Case congruence: identical lowering lifts through Case (same alts). -/
theorem lowerTotalExpr_case_scrut_congr (scrut scrut' : Expr) (alts : List Expr)
    (hs : ∀ env, lowerTotalExpr env scrut = lowerTotalExpr env scrut') :
    ∀ env, lowerTotalExpr env (.Case scrut alts) = lowerTotalExpr env (.Case scrut' alts) := by
  intro env
  rw [lowerTotalExpr_case, lowerTotalExpr_case, hs env]

/-- Let body congruence: identical lowering lifts through Let (same bindings). -/
theorem lowerTotalExpr_let_body_congr
    (binds : List (VarId × Expr × Bool)) (body body' : Expr)
    (h : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    ∀ env, lowerTotalExpr env (.Let binds body) = lowerTotalExpr env (.Let binds body') := by
  intro env
  simp only [lowerTotalExpr_let]
  exact lowerTotalLet_congr env (expandFixBinds binds) (expandFix body) (expandFix body') (fun env' => by
    have := h env'; simp only [lowerTotalExpr] at this; exact this)

/-! ## BehEq congruence lemmas

No fixCount precondition needed for any constructor. -/

/-- Force preserves BehEq. -/
theorem behEq_force (e e' : Expr)
    (h : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e') :
    Expr.Force e ≋ Expr.Force e' :=
  behEq_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_force_congr e e' h)

/-- Delay preserves BehEq. -/
theorem behEq_delay (e e' : Expr)
    (h : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e') :
    Expr.Delay e ≋ Expr.Delay e' :=
  behEq_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_delay_congr e e' h)

/-- Lam preserves BehEq. -/
theorem behEq_lam (x : VarId) (body body' : Expr)
    (h : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    Expr.Lam x body ≋ Expr.Lam x body' :=
  behEq_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_lam_congr x body body' h)

/-- App preserves BehEq. -/
theorem behEq_app (f f' a a' : Expr)
    (hf : ∀ env, lowerTotalExpr env f = lowerTotalExpr env f')
    (ha : ∀ env, lowerTotalExpr env a = lowerTotalExpr env a') :
    Expr.App f a ≋ Expr.App f' a' :=
  behEq_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_app_congr f f' a a' hf ha)

/-- Let body preserves BehEq (same bindings). -/
theorem behEq_let_body (binds : List (VarId × Expr × Bool)) (body body' : Expr)
    (h : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    Expr.Let binds body ≋ Expr.Let binds body' :=
  behEq_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_let_body_congr binds body body' h)

/-! ## Refines congruence lemmas -/

/-- Force preserves Refines. -/
theorem refines_force (e e' : Expr)
    (h : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e') :
    Expr.Force e ⊑ Expr.Force e' :=
  refines_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_force_congr e e' h)

/-- Delay preserves Refines. -/
theorem refines_delay (e e' : Expr)
    (h : ∀ env, lowerTotalExpr env e = lowerTotalExpr env e') :
    Expr.Delay e ⊑ Expr.Delay e' :=
  refines_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_delay_congr e e' h)

/-- Lam preserves Refines. -/
theorem refines_lam (x : VarId) (body body' : Expr)
    (h : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    Expr.Lam x body ⊑ Expr.Lam x body' :=
  refines_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_lam_congr x body body' h)

/-- App preserves Refines. -/
theorem refines_app (f f' a a' : Expr)
    (hf : ∀ env, lowerTotalExpr env f = lowerTotalExpr env f')
    (ha : ∀ env, lowerTotalExpr env a = lowerTotalExpr env a') :
    Expr.App f a ⊑ Expr.App f' a' :=
  refines_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_app_congr f f' a a' hf ha)

/-- Let body preserves Refines (same bindings). -/
theorem refines_let_body (binds : List (VarId × Expr × Bool)) (body body' : Expr)
    (h : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    Expr.Let binds body ⊑ Expr.Let binds body' :=
  refines_of_lowerTotalExpr_eq _ _ (lowerTotalExpr_let_body_congr binds body body' h)

/-! ## Fix refinement (vacuous)

`lowerTotal (.Fix _ _) = none`, so Fix is always lowerable only via
`expandFix`. Since `expandFix` transforms the entire Fix node, there
is no compositional lowering equation for Fix. However, if two
expressions have the same `lowerTotalExpr` output, they refine each
other regardless of Fix content. -/

/-- Fix refines itself (instance of reflexivity). -/
theorem refines_fix (f : VarId) (body : Expr) : Expr.Fix f body ⊑ Expr.Fix f body :=
  refines_refl _

/-! ## Let with changed bindings (pointwise RHS equality)

For `Let` where both bindings share the same VarId/Bool structure but
may differ in RHS expressions, we can prove refinement provided
all RHS and body lower identically. -/

/-- Let congruence for changed RHS at the lowerTotal level.
    Both binding lists share the same structure (VarId, Bool), only RHS differs. -/
theorem lowerTotalLet_rhs_body_congr (env : List VarId)
    (binds binds' : List (VarId × Expr × Bool)) (body body' : Expr)
    (hlen : List.length binds = List.length binds')
    (hbinds : ∀ (j : Nat) (x : VarId) (rhs : Expr) (er : Bool) (x' : VarId) (rhs' : Expr) (er' : Bool),
      binds[j]? = some (x, rhs, er) → binds'[j]? = some (x', rhs', er') →
      x = x' ∧ er = er' ∧ ∀ env', lowerTotal env' rhs = lowerTotal env' rhs')
    (hbody : ∀ env', lowerTotal env' body = lowerTotal env' body') :
    lowerTotalLet env binds body = lowerTotalLet env binds' body' := by
  induction binds generalizing binds' env with
  | nil =>
    cases binds' with
    | nil => simp only [lowerTotalLet.eq_1, hbody env]
    | cons _ _ => simp at hlen
  | cons b rest ih =>
    obtain ⟨x, rhs, er⟩ := b
    cases binds' with
    | nil => simp at hlen
    | cons b' rest' =>
      obtain ⟨x', rhs', er'⟩ := b'
      have ⟨hvx, her, hrhs0⟩ := hbinds 0 x rhs er x' rhs' er' rfl rfl
      subst hvx; subst her
      simp only [lowerTotalLet.eq_2, hrhs0 env,
        ih (x :: env) rest' (by simpa using hlen)
          (fun j y r e y' r' e' hy hy' => hbinds (j + 1) y r e y' r' e' hy hy')]

/-- `expandFixBinds` preserves list length. -/
private theorem expandFixBinds_length :
    ∀ (binds : List (VarId × Expr × Bool)),
    (expandFixBinds binds).length = binds.length
  | [] => by simp [expandFixBinds]
  | (_, _, _) :: rest => by simp [expandFixBinds, expandFixBinds_length rest]

/-- `expandFixBinds` preserves the list structure element-wise:
    if `binds[j]? = some (x, rhs, er)` then
    `(expandFixBinds binds)[j]? = some (x, expandFix rhs, er)`. -/
private theorem expandFixBinds_getElem :
    ∀ (binds : List (VarId × Expr × Bool)) (j : Nat)
      (x : VarId) (rhs : Expr) (er : Bool),
    binds[j]? = some (x, rhs, er) →
    (expandFixBinds binds)[j]? = some (x, expandFix rhs, er)
  | [], _, _, _, _, h => by simp at h
  | (v, r, e) :: rest, 0, x, rhs, er, h => by
    simp at h; obtain ⟨hv, hr, he⟩ := h; subst hv; subst hr; subst he
    simp [expandFixBinds]
  | (v, r, e) :: rest, j + 1, x, rhs, er, h => by
    simp [expandFixBinds]
    exact expandFixBinds_getElem rest j x rhs er (by simpa using h)

/-- Reverse direction: if `(expandFixBinds binds)[j]? = some (x, rhs, er)` then
    there exists `origRhs` with `binds[j]? = some (x, origRhs, er)` and
    `rhs = expandFix origRhs`. -/
private theorem expandFixBinds_getElem_inv :
    ∀ (binds : List (VarId × Expr × Bool)) (j : Nat)
      (x : VarId) (rhs : Expr) (er : Bool),
    (expandFixBinds binds)[j]? = some (x, rhs, er) →
    ∃ origRhs, binds[j]? = some (x, origRhs, er) ∧ rhs = expandFix origRhs
  | [], _, _, _, _, h => by simp [expandFixBinds] at h
  | (v, r, e) :: rest, 0, x, rhs, er, h => by
    simp [expandFixBinds] at h; obtain ⟨hv, hr, he⟩ := h; subst hv; subst hr; subst he
    exact ⟨r, by simp, rfl⟩
  | (v, r, e) :: rest, j + 1, x, rhs, er, h => by
    simp [expandFixBinds] at h
    exact expandFixBinds_getElem_inv rest j x rhs er h

/-- Let congruence for Refines with changed bindings.
    Both binding lists share the same VarId/Bool structure, only RHS may differ. -/
theorem refines_let_rhs_pointwise
    (binds binds' : List (VarId × Expr × Bool)) (body body' : Expr)
    (hlen : binds.length = binds'.length)
    (hbinds : ∀ (j : Nat) (x : VarId) (rhs : Expr) (er : Bool) (x' : VarId) (rhs' : Expr) (er' : Bool),
      binds[j]? = some (x, rhs, er) → binds'[j]? = some (x', rhs', er') →
      x = x' ∧ er = er' ∧ ∀ env, lowerTotalExpr env rhs = lowerTotalExpr env rhs')
    (hbody : ∀ env, lowerTotalExpr env body = lowerTotalExpr env body') :
    Expr.Let binds body ⊑ Expr.Let binds' body' := by
  apply refines_of_lowerTotalExpr_eq; intro env
  simp only [lowerTotalExpr_let]
  exact lowerTotalLet_rhs_body_congr env (expandFixBinds binds) (expandFixBinds binds')
    (expandFix body) (expandFix body')
    (by rw [expandFixBinds_length, expandFixBinds_length, hlen])
    (fun j x rhs er x' rhs' er' hj hj' => by
      obtain ⟨origRhs, hOrig, hRhsEq⟩ := expandFixBinds_getElem_inv binds j x rhs er hj
      obtain ⟨origRhs', hOrig', hRhsEq'⟩ := expandFixBinds_getElem_inv binds' j x' rhs' er' hj'
      have ⟨hvx, her, hLower⟩ := hbinds j x origRhs er x' origRhs' er' hOrig hOrig'
      exact ⟨hvx, her, fun env' => by
        rw [hRhsEq, hRhsEq']
        have := hLower env'; simp only [lowerTotalExpr] at this; exact this⟩)
    (fun env' => by have := hbody env'; simp only [lowerTotalExpr] at this; exact this)

/-! ## Behavioral congruence (Refines-preserving)

These are STRONGER than the identical-lowering congruence above: the
hypothesis is `e ⊑ e'` (behavioral refinement), not identical lowering.

### Immediate-value constructors (Delay, Lam)

`Delay` and `Lam` evaluate to a value in exactly 2 steps (no errors
possible), so `error ↔` is trivially `False ↔ False`. The `ValueEq`
clause uses the BehEq hypothesis on the sub-expression.
-/

/-- Helper: extract the BehEq content at a specific env when both sides lower. -/
private theorem refines_behEq_at {e e' : Expr} {env : List VarId} {t t' : Term}
    (h : e ⊑ e') (ht : lowerTotalExpr env e = some t) (ht' : lowerTotalExpr env e' = some t') :
    ∀ ρ : CekEnv, WellSizedEnv env.length ρ →
      (Reaches (.compute [] ρ t) .error ↔ Reaches (.compute [] ρ t') .error) ∧
      (Halts (.compute [] ρ t) ↔ Halts (.compute [] ρ t')) ∧
      ∀ (k : Nat) (v1 v2 : CekValue),
        Reaches (.compute [] ρ t) (.halt v1) →
        Reaches (.compute [] ρ t') (.halt v2) →
        ValueEq k v1 v2 := by
  have hbe := h.2 env; rw [ht, ht'] at hbe; exact hbe

/-- Helper: the compilation clause for a single-child constructor that uses
    `Option.bind`. If `(lowerTotalExpr env e).bind f` is `some`, then
    `lowerTotalExpr env e` is `some`. -/
private theorem isSome_bind_inner {α β : Type} {o : Option α} {f : α → Option β}
    (hs : (o.bind f).isSome) : o.isSome := by
  cases o with
  | none => simp [Option.bind] at hs
  | some _ => simp

/-- Helper: immediately-halting terms never error. -/
private theorem not_error_of_halts {s : State} {v : CekValue}
    (hv : Reaches s (.halt v)) : ¬Reaches s .error :=
  fun herr => reaches_halt_not_error hv herr

/-- Delay preserves Refines (behavioral). `Delay e` halts immediately with
    `VDelay t ρ`, so error-equivalence is vacuous and value-equivalence
    reduces to the BehEq hypothesis on the sub-expression. -/
theorem refines_delay_behEq (e e' : Expr) (h : e ⊑ e') :
    Expr.Delay e ⊑ Expr.Delay e' := by
  refine ⟨?_, ?_⟩
  · -- Compilation clause
    intro env hs
    rw [lowerTotalExpr_delay] at hs ⊢
    have hs_inner := isSome_bind_inner hs
    have := h.1 env hs_inner
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp this
    rw [ht']; simp [Option.bind]
  · -- BehEq clause
    intro env
    simp only [lowerTotalExpr_delay]
    cases he : lowerTotalExpr env e with
    | none => simp [Option.bind_none]
    | some t =>
      cases he' : lowerTotalExpr env e' with
      | none => simp [Option.bind_some, Option.bind_none]
      | some t' =>
        simp only [Option.bind_some]
        intro ρ hwf
        -- Delay t halts in 2 steps with VDelay t ρ; never errors
        have hd : Reaches (.compute [] ρ (.Delay t)) (.halt (.VDelay t ρ)) := ⟨2, rfl⟩
        have hd' : Reaches (.compute [] ρ (.Delay t')) (.halt (.VDelay t' ρ)) := ⟨2, rfl⟩
        refine ⟨⟨fun herr => absurd herr (not_error_of_halts hd),
                  fun herr => absurd herr (not_error_of_halts hd')⟩,
                 ⟨fun _ => ⟨_, hd'⟩, fun _ => ⟨_, hd⟩⟩, ?_⟩
        intro k v1 v2 hv1 hv2
        have heq1 := reaches_unique hv1 hd; subst heq1
        have heq2 := reaches_unique hv2 hd'; subst heq2
        cases k with
        | zero => simp [ValueEq]
        | succ k =>
          unfold ValueEq; intro j hj stk1 stk2 hstk
          sorry -- TODO: needs bounded-step from bisimulation

/-- Lam preserves Refines (behavioral). `Lam x body` halts immediately with
    `VLam t ρ`, so error-equivalence is vacuous and value-equivalence
    reduces to the BehEq hypothesis on the body. -/
theorem refines_lam_behEq (x : VarId) (body body' : Expr) (h : body ⊑ body') :
    Expr.Lam x body ⊑ Expr.Lam x body' := by
  refine ⟨?_, ?_⟩
  · -- Compilation clause
    intro env hs
    rw [lowerTotalExpr_lam] at hs ⊢
    have hs_inner := isSome_bind_inner hs
    have := h.1 (x :: env) hs_inner
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp this
    rw [ht']; simp [Option.bind]
  · -- BehEq clause
    intro env
    simp only [lowerTotalExpr_lam]
    cases he : lowerTotalExpr (x :: env) body with
    | none => simp [Option.bind_none]
    | some t =>
      cases he' : lowerTotalExpr (x :: env) body' with
      | none => simp [Option.bind_some, Option.bind_none]
      | some t' =>
        simp only [Option.bind_some]
        intro ρ hwf
        -- Lam 0 t halts in 2 steps with VLam t ρ; never errors
        have hl : Reaches (.compute [] ρ (.Lam 0 t)) (.halt (.VLam t ρ)) := ⟨2, rfl⟩
        have hl' : Reaches (.compute [] ρ (.Lam 0 t')) (.halt (.VLam t' ρ)) := ⟨2, rfl⟩
        refine ⟨⟨fun herr => absurd herr (not_error_of_halts hl),
                  fun herr => absurd herr (not_error_of_halts hl')⟩,
                 ⟨fun _ => ⟨_, hl'⟩, fun _ => ⟨_, hl⟩⟩, ?_⟩
        intro k v1 v2 hv1 hv2
        have heq1 := reaches_unique hv1 hl; subst heq1
        have heq2 := reaches_unique hv2 hl'; subst heq2
        cases k with
        | zero => simp [ValueEq]
        | succ k =>
          unfold ValueEq; intro j hj arg1 arg2 hargs stk1 stk2 hstk
          sorry -- TODO: needs bounded-step from bisimulation

/-! ### Force decomposition via liftState

Force evaluation: `compute [] ρ (Force te)` steps to
`compute [.force] ρ te = liftState [.force] (compute [] ρ te)` in 1 step.
The liftState machinery from StepLift then decomposes the evaluation
into (a) evaluating `te` and (b) processing the force frame. -/

open Moist.Verified.StepLift (liftState isActive steps_liftState
  liftState_ne_halt liftState_eq_error)

/-- Find the first step index `K ≤ bound` where the state becomes inactive.
    (Copied from StepLift where it is private.) -/
private theorem firstInactive (s : State) (bound : Nat)
    (hex : ∃ k, k ≤ bound ∧ isActive (steps k s) = false) :
    ∃ K, K ≤ bound ∧ isActive (steps K s) = false ∧
         (∀ j, j < K → isActive (steps j s) = true) := by
  induction bound with
  | zero =>
    obtain ⟨k, hk, hinact⟩ := hex
    have : k = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl _, hinact, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ bound ih =>
    by_cases h : ∃ k, k ≤ bound ∧ isActive (steps k s) = false
    · obtain ⟨K, hK_le, hK_inact, hK_min⟩ := ih h
      exact ⟨K, by omega, hK_inact, hK_min⟩
    · have hall : ∀ j, j ≤ bound → isActive (steps j s) = true := by
        intro j hj
        by_cases heq : isActive (steps j s) = true
        · exact heq
        · exfalso; apply h; exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      obtain ⟨k, hk, hinact⟩ := hex
      have hk_eq : k = bound + 1 := by
        by_cases heq : k = bound + 1
        · exact heq
        · exfalso; have hle : k ≤ bound := by omega
          have := hall k hle; simp [hinact] at this
      subst hk_eq
      exact ⟨bound + 1, Nat.le_refl _, hinact, fun j hj => hall j (by omega)⟩

/-- Force decomposition (halt case): if `Force te` halts with `v`, then
    `te` halts with some value `val` and `ret [.force] val` reaches `(.halt v)`. -/
private theorem force_reaches (ρ : CekEnv) (te : Term) (v : CekValue)
    (hreach : Reaches (.compute [] ρ (.Force te)) (.halt v)) :
    ∃ val, Reaches (.compute [] ρ te) (.halt val) ∧
           Reaches (.ret [.force] val) (.halt v) := by
  obtain ⟨N, hN⟩ := hreach
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.force] ρ te) = .halt v := by
    have : N = 1 + (N - 1) := by omega
    rw [this, steps_trans, h1] at hN; exact hN
  have hlift : State.compute [.force] ρ te =
      liftState [.force] (.compute [] ρ te) := by simp [liftState]
  rw [hlift] at hrest
  have h_has_inactive : ∃ k, k ≤ (N - 1) ∧ isActive (steps k (.compute [] ρ te)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ (N - 1) → isActive (steps j (.compute [] ρ te)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ te)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ te)) <;> simp_all⟩
      have h_comm := steps_liftState [.force] (N - 1) (.compute [] ρ te)
        (fun j hj => hall' j (by omega))
      rw [hrest] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ v)
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ te) (N - 1) h_has_inactive
  have h_comm : steps K (liftState [.force] (.compute [] ρ te)) =
      liftState [.force] (steps K (.compute [] ρ te)) :=
    steps_liftState [.force] K (.compute [] ρ te) hK_min
  have h_not_error : steps K (.compute [] ρ te) ≠ .error := by
    intro herr
    have : steps ((N - 1) - K) (liftState [.force] .error) = .halt v := by
      have : N - 1 = K + ((N - 1) - K) := by omega
      rw [this, steps_trans, h_comm, herr] at hrest; exact hrest
    simp [liftState, steps_error] at this
  have ⟨val, h_inner_eq, h_lifted_eq⟩ :
      ∃ val, (steps K (.compute [] ρ te) = .halt val ∨
              steps K (.compute [] ρ te) = .ret [] val) ∧
             liftState [.force] (steps K (.compute [] ρ te)) =
               .ret [.force] val := by
    generalize h_sK : steps K (.compute [] ρ te) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  have h_reaches_te : Reaches (.compute [] ρ te) (.halt val) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  have h_force_frame : steps ((N - 1) - K) (.ret [.force] val) = .halt v := by
    have : N - 1 = K + ((N - 1) - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hrest; exact hrest
  exact ⟨val, h_reaches_te, (N - 1) - K, h_force_frame⟩

/-- Force decomposition (error case): if `Force te` errors, then either
    `te` errors, or `te` halts with some value `val` and
    `ret [.force] val` reaches `.error`. -/
private theorem force_reaches_error (ρ : CekEnv) (te : Term)
    (hreach : Reaches (.compute [] ρ (.Force te)) .error) :
    Reaches (.compute [] ρ te) .error ∨
    ∃ val, Reaches (.compute [] ρ te) (.halt val) ∧
           Reaches (.ret [.force] val) .error := by
  obtain ⟨N, hN⟩ := hreach
  have hge1 : N ≥ 1 := by match N, hN with | 0, hN => simp [steps] at hN | _ + 1, _ => omega
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have hrest : steps (N - 1) (.compute [.force] ρ te) = .error := by
    have : N = 1 + (N - 1) := by omega
    rw [this, steps_trans, h1] at hN; exact hN
  have hlift : State.compute [.force] ρ te =
      liftState [.force] (.compute [] ρ te) := by simp [liftState]
  rw [hlift] at hrest
  have h_has_inactive : ∃ k, k ≤ (N - 1) ∧ isActive (steps k (.compute [] ρ te)) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ (N - 1) → isActive (steps j (.compute [] ρ te)) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] ρ te)) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] ρ te)) <;> simp_all⟩
      have h_comm := steps_liftState [.force] (N - 1) (.compute [] ρ te)
        (fun j hj => hall' j (by omega))
      rw [hrest] at h_comm
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' (N - 1) (Nat.le_refl _)
      rw [h_inner_err] at this; simp [isActive] at this
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ te) (N - 1) h_has_inactive
  have h_comm : steps K (liftState [.force] (.compute [] ρ te)) =
      liftState [.force] (steps K (.compute [] ρ te)) :=
    steps_liftState [.force] K (.compute [] ρ te) hK_min
  by_cases h_is_error : steps K (.compute [] ρ te) = .error
  · left; exact ⟨K, h_is_error⟩
  · right
    have ⟨val, h_inner_eq, h_lifted_eq⟩ :
        ∃ val, (steps K (.compute [] ρ te) = .halt val ∨
                steps K (.compute [] ρ te) = .ret [] val) ∧
               liftState [.force] (steps K (.compute [] ρ te)) =
                 .ret [.force] val := by
      generalize h_sK : steps K (.compute [] ρ te) = sK at hK_inact h_is_error
      match sK with
      | .compute .. => simp [isActive] at hK_inact
      | .ret [] val => exact ⟨val, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK_inact
      | .halt val => exact ⟨val, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error
    have h_reaches_te : Reaches (.compute [] ρ te) (.halt val) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    have h_force_frame : steps ((N - 1) - K) (.ret [.force] val) = .error := by
      have : N - 1 = K + ((N - 1) - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hrest; exact hrest
    exact ⟨val, h_reaches_te, (N - 1) - K, h_force_frame⟩

/-- Force composition (synthesis): given that `te` halts with `val` and
    `ret [.force] val` reaches `s`, compose to show `Force te` reaches `s`. -/
private theorem force_compose (ρ : CekEnv) (te : Term) (val : CekValue) (s : State)
    (hte : Reaches (.compute [] ρ te) (.halt val))
    (hf : Reaches (.ret [.force] val) s) :
    Reaches (.compute [] ρ (.Force te)) s := by
  obtain ⟨Ke, hKe⟩ := hte
  obtain ⟨Kf, hKf⟩ := hf
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have hlift : State.compute [.force] ρ te =
      liftState [.force] (.compute [] ρ te) := by simp [liftState]
  -- Find the first non-active step in te computation (bounded by Ke)
  have h_not_active_Ke : isActive (steps Ke (.compute [] ρ te)) = false := by
    rw [hKe]; rfl
  have h_has_inactive : ∃ k, k ≤ Ke ∧ isActive (steps k (.compute [] ρ te)) = false :=
    ⟨Ke, Nat.le_refl _, h_not_active_Ke⟩
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ te) Ke h_has_inactive
  have h_comm : steps K (liftState [.force] (.compute [] ρ te)) =
      liftState [.force] (steps K (.compute [] ρ te)) :=
    steps_liftState [.force] K (.compute [] ρ te) hK_min
  -- Inner state at K is not error (since te eventually halts)
  have h_not_error : steps K (.compute [] ρ te) ≠ .error := by
    intro herr
    have : steps Ke (.compute [] ρ te) = .error := by
      have : Ke = K + (Ke - K) := by omega
      rw [this, steps_trans, herr, steps_error]
    rw [hKe] at this; exact absurd this (by simp)
  -- Extract val': non-active, non-error => ret [] val' or halt val'
  have ⟨val', h_inner_eq, h_lifted_eq⟩ :
      ∃ val', (steps K (.compute [] ρ te) = .halt val' ∨
               steps K (.compute [] ρ te) = .ret [] val') ∧
              liftState [.force] (steps K (.compute [] ρ te)) =
                .ret [.force] val' := by
    generalize h_sK : steps K (.compute [] ρ te) = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] val' => exact ⟨val', .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt val' => exact ⟨val', .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  -- Show val' = val by determinism
  have h_val_eq : val' = val := by
    have h_halt_val' : steps (K + 1) (.compute [] ρ te) = .halt val' := by
      cases h_inner_eq with
      | inl h => rw [steps_trans, h, steps_halt]
      | inr h => rw [steps_trans, h]; rfl
    by_cases hle : K + 1 ≤ Ke
    · have h_Ke_eq : steps Ke (.compute [] ρ te) = .halt val' := by
        have : Ke = (K + 1) + (Ke - (K + 1)) := by omega
        rw [this, steps_trans, h_halt_val', steps_halt]
      rw [hKe] at h_Ke_eq; exact (State.halt.inj h_Ke_eq).symm
    · have hKeq : K = Ke := by omega
      rw [← hKeq] at hKe
      have : steps (K + 1) (.compute [] ρ te) = .halt val := by
        rw [steps_trans, hKe]; rfl
      rw [h_halt_val'] at this; exact State.halt.inj this
  subst h_val_eq
  -- Compose: 1 + K + Kf steps
  have h_total : steps (1 + K + Kf) (.compute [] ρ (.Force te)) = s := by
    have : 1 + K + Kf = 1 + (K + Kf) := by omega
    rw [this, steps_trans, h1, hlift, steps_trans, h_comm, h_lifted_eq, hKf]
  exact ⟨1 + K + Kf, h_total⟩

/-! ### Stepping through the force frame

These lemmas characterize the one-step behavior of `ret [.force] v`
for each value constructor. -/

/-- Forcing a VDelay: `ret [.force] (VDelay body env)` steps to
    `compute [] env body` in 1 step. -/
private theorem force_delay_step (body : Term) (env : CekEnv) :
    step (.ret [.force] (.VDelay body env)) = .compute [] env body := rfl

/-- Forcing a VCon: `ret [.force] (VCon c)` steps to `.error` in 1 step. -/
private theorem force_vcon_error (c : Const) :
    step (.ret [.force] (.VCon c)) = .error := rfl

/-- Forcing a VLam: `ret [.force] (VLam body env)` steps to `.error` in 1 step. -/
private theorem force_vlam_error (body : Term) (env : CekEnv) :
    step (.ret [.force] (.VLam body env)) = .error := rfl

/-- Forcing a VConstr: `ret [.force] (VConstr tag fields)` steps to `.error` in 1 step. -/
private theorem force_vconstr_error (tag : Nat) (fields : List CekValue) :
    step (.ret [.force] (.VConstr tag fields)) = .error := rfl

/-- Forcing a VDelay to halt: `ret [.force] (VDelay body env)` reaches `.halt v`
    iff `compute [] env body` reaches `.halt v`. -/
private theorem force_delay_halt (body : Term) (env : CekEnv) (v : CekValue) :
    Reaches (.ret [.force] (.VDelay body env)) (.halt v) ↔
    Reaches (.compute [] env body) (.halt v) := by
  constructor
  · intro ⟨n, hn⟩
    cases n with
    | zero => simp [steps] at hn
    | succ n => simp [steps, step] at hn; exact ⟨n, hn⟩
  · intro ⟨n, hn⟩
    exact ⟨n + 1, by simp [steps, step, hn]⟩

/-- Forcing a VDelay to error: `ret [.force] (VDelay body env)` reaches `.error`
    iff `compute [] env body` reaches `.error`. -/
private theorem force_delay_error (body : Term) (env : CekEnv) :
    Reaches (.ret [.force] (.VDelay body env)) .error ↔
    Reaches (.compute [] env body) .error := by
  constructor
  · intro ⟨n, hn⟩
    cases n with
    | zero => simp [steps] at hn
    | succ n => simp [steps, step] at hn; exact ⟨n, hn⟩
  · intro ⟨n, hn⟩
    exact ⟨n + 1, by simp [steps, step, hn]⟩

/-- VCon cannot be forced to a halt. -/
private theorem force_vcon_not_halts (c : Const) : ¬Halts (.ret [.force] (.VCon c)) := by
  intro ⟨v, n, hn⟩; cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_error] at hn

/-- VLam cannot be forced to a halt. -/
private theorem force_vlam_not_halts (b : Term) (e : CekEnv) : ¬Halts (.ret [.force] (.VLam b e)) := by
  intro ⟨v, n, hn⟩; cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_error] at hn

/-- VConstr cannot be forced to a halt. -/
private theorem force_vconstr_not_halts (t : Nat) (fs : List CekValue) : ¬Halts (.ret [.force] (.VConstr t fs)) := by
  intro ⟨v, n, hn⟩; cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_error] at hn

/-- VCon forced is error. -/
private theorem force_vcon_reaches_error (c : Const) : Reaches (.ret [.force] (.VCon c)) .error :=
  ⟨1, by simp [steps, step]⟩

/-- VLam forced is error. -/
private theorem force_vlam_reaches_error (b : Term) (e : CekEnv) : Reaches (.ret [.force] (.VLam b e)) .error :=
  ⟨1, by simp [steps, step]⟩

/-- VConstr forced is error. -/
private theorem force_vconstr_reaches_error (t : Nat) (fs : List CekValue) : Reaches (.ret [.force] (.VConstr t fs)) .error :=
  ⟨1, by simp [steps, step]⟩

/-! ### Force-frame agreement from ValueEq

With the strengthened `ValueEq` that includes error↔ for VDelay/VLam
closures and evalBuiltin none↔ for VBuiltin, the force-frame step
`ret [.force] v` produces agreeing outcomes for ValueEq-related values.

For VDelay: error/halt/value agreement comes directly from ValueEq.
For VCon/VLam/VConstr: forcing always errors (same constructor → same behavior).
For VBuiltin: same `b` and `ea` mean same branching on `ea.head`/`ea.tail`,
and `evalBuiltin` none↔ handles the fully-saturated case. -/

/-- evalBuiltin none↔none for full arg lists under ListValueEq.
    Proved later via extractConsts_cong + evalBuiltinPassThrough isNone;
    stated early for use by force/halts transfer. -/
private theorem evalBuiltin_none_iff_early (k : Nat) (b : BuiltinFun)
    (a1 a2 : List CekValue) (hargs : ListValueEq (k + 1) a1 a2) :
    Moist.CEK.evalBuiltin b a1 = none ↔ Moist.CEK.evalBuiltin b a2 = none := by
  sorry

/-- evalBuiltin value congruence for full arg lists under ListValueEq.
    Proved later via evalBuiltin_full_cong; stated early for use by
    refines_force_behEq. -/
private theorem evalBuiltin_value_cong_early (k : Nat) (b : BuiltinFun)
    (a1 a2 : List CekValue) (hargs : ListValueEq (k + 1) a1 a2)
    (r1 r2 : CekValue)
    (hr1 : Moist.CEK.evalBuiltin b a1 = some r1)
    (hr2 : Moist.CEK.evalBuiltin b a2 = some r2) :
    ValueEq k r1 r2 := by
  sorry

/-- Force-frame error transfer: if `∀ j, ValueEq j v1 v2` and forcing `v1` errors,
    then forcing `v2` also errors. For VDelay, extract the step count N from
    `herr`, pick level N to get the bounded CIU clause covering N-1 steps. -/
private theorem force_frame_error_transfer
    (v1 v2 : CekValue) (hve : ∀ j, ValueEq j v1 v2)
    (herr : Reaches (.ret [.force] v1) .error) :
    Reaches (.ret [.force] v2) .error := by
  match v1, v2 with
  | .VDelay b1 e1, .VDelay b2 e2 =>
    -- Extract step count N from herr
    obtain ⟨N, hN⟩ := herr
    cases N with
    | zero => simp [steps] at hN
    | succ N =>
      -- steps (N+1) (.ret [.force] (VDelay b1 e1)) = .error
      -- After 1 step: steps N (.compute [] e1 b1) = .error
      have hcomp : steps N (.compute [] e1 b1) = .error := by
        simp only [steps, step] at hN; exact hN
      -- Pick level N+1 from hve: ValueEq (N+1) (VDelay b1 e1) (VDelay b2 e2)
      have hveN := hve (N + 1)
      -- VDelay clause: ∀ j ≤ N, ∀ stk1 stk2, StackEqR (ValueEq j) stk1 stk2 →
      --               ∀ n ≤ j, (error ↔) ∧ ...
      unfold ValueEq at hveN
      -- Use j = N, stk1 = stk2 = [] (StackEqR R [] [] = True), n = N
      have hclause := hveN N (Nat.le_refl N) [] [] trivial
      -- hclause.1 : ∀ n, n ≤ N → error → ∃ m, m ≤ N ∧ error
      obtain ⟨m, _, herr2⟩ := hclause.1 N (Nat.le_refl N) hcomp
      -- Compose: steps (m+1) (.ret [.force] (VDelay b2 e2)) = steps m (.compute [] e2 b2)
      exact ⟨m + 1, by simp only [steps, step]; exact herr2⟩
  | .VCon _, .VCon _ => exact force_vcon_reaches_error _
  | .VLam _ _, .VLam _ _ => exact force_vlam_reaches_error _ _
  | .VConstr _ _, .VConstr _ _ => exact force_vconstr_reaches_error _ _
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    have hve1 := hve 1
    unfold ValueEq at hve1
    obtain ⟨hb, hargs_lve, hea⟩ := hve1; subst hb; subst hea
    obtain ⟨n, hn⟩ := herr
    cases n with
    | zero => simp [steps] at hn
    | succ n =>
      simp only [steps, step] at hn
      cases hh : ea.head with
      | argV => exact ⟨1, by simp [steps, step, hh]⟩
      | argQ =>
        rw [hh] at hn
        cases ht : ea.tail with
        | some rest =>
          rw [ht] at hn
          cases n with
          | zero => simp [steps] at hn
          | succ n => simp [steps, step, steps_halt] at hn
        | none =>
          rw [ht] at hn
          cases hev : Moist.CEK.evalBuiltin b a1 with
          | some v =>
            rw [hev] at hn
            cases n with
            | zero => simp [steps] at hn
            | succ n => simp [steps, step, steps_halt] at hn
          | none =>
            have hcong_none := evalBuiltin_none_iff_early 0 b a1 a2 hargs_lve
            have hev2 := hcong_none.mp hev
            exact ⟨1, by simp [steps, step, hh, ht, hev2]⟩
  -- Cross-constructor: impossible (ValueEq at mismatched constructors is False)
  | .VCon _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)

/-- Force-frame halts transfer: if `∀ j, ValueEq j v1 v2` and forcing `v1` halts,
    then forcing `v2` also halts. For VDelay, extract step count N, pick level N
    to get bounded CIU clause, derive halt existence on the other side. -/
private theorem force_frame_halts_transfer
    (v1 v2 : CekValue) (hve : ∀ j, ValueEq j v1 v2)
    (hh : Halts (.ret [.force] v1)) :
    Halts (.ret [.force] v2) := by
  match v1, v2 with
  | .VDelay b1 e1, .VDelay b2 e2 =>
    -- Extract step count and halted value
    obtain ⟨w, N, hN⟩ := hh
    cases N with
    | zero => simp [steps] at hN
    | succ N =>
      -- After 1 step: steps N (.compute [] e1 b1) = .halt w
      have hcomp : steps N (.compute [] e1 b1) = .halt w := by
        simp only [steps, step] at hN; exact hN
      -- Pick level N+1: ValueEq (N+1) gives VDelay clause with j ≤ N
      have hveN := hve (N + 1)
      unfold ValueEq at hveN
      -- Use j = N, stk = [] (trivial), n = N
      have hclause := hveN N (Nat.le_refl N) [] [] trivial
      -- hclause.2.1 : ∀ v1 n, n ≤ N → halt v1 → ∃ v2 m, m ≤ N ∧ halt v2 ∧ ValueEq ...
      obtain ⟨w2, m, _, hw2, _⟩ := hclause.2.1 w N (Nat.le_refl N) hcomp
      exact ⟨w2, m + 1, by simp only [steps, step]; exact hw2⟩
  | .VCon _, .VCon _ => exact absurd hh (force_vcon_not_halts _)
  | .VLam _ _, .VLam _ _ => exact absurd hh (force_vlam_not_halts _ _)
  | .VConstr _ _, .VConstr _ _ => exact absurd hh (force_vconstr_not_halts _ _)
  | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
    have hve1 := hve 1
    unfold ValueEq at hve1
    obtain ⟨hb, hargs_lve, hea⟩ := hve1; subst hb; subst hea
    obtain ⟨w, n, hn⟩ := hh
    cases n with
    | zero => simp [steps] at hn
    | succ n =>
      simp only [steps, step] at hn
      cases hhead : ea.head with
      | argV => rw [hhead] at hn; simp [steps_error] at hn
      | argQ =>
        rw [hhead] at hn
        cases htail : ea.tail with
        | some rest =>
          rw [htail] at hn
          exact ⟨.VBuiltin b a2 rest, 2, by simp [steps, step, hhead, htail]⟩
        | none =>
          rw [htail] at hn
          cases hev1 : Moist.CEK.evalBuiltin b a1 with
          | none => rw [hev1] at hn; simp [steps_error] at hn
          | some v1 =>
            rw [hev1] at hn
            cases hev2 : Moist.CEK.evalBuiltin b a2 with
            | none =>
              have hcong_none := evalBuiltin_none_iff_early 0 b a1 a2 hargs_lve
              exact absurd (hcong_none.mpr hev2) (by rw [hev1]; simp)
            | some v2 => exact ⟨v2, 2, by simp [steps, step, hhead, htail, hev2]⟩
  | .VCon _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VCon _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VLam _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VDelay _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VConstr _ _, .VBuiltin _ _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VCon _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VLam _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VDelay _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)
  | .VBuiltin _ _ _, .VConstr _ _ => exact absurd (hve 1) (by unfold ValueEq; exact id)

/-! ### Force error from sub-expression error -/

/-- If the sub-expression errors, `Force` also errors.
    `Force te` steps to `compute [.force] ρ te`. Error propagates through
    the force frame because `liftState [.force] .error = .error`. -/
private theorem force_sub_error (ρ : CekEnv) (te : Term)
    (herr : Reaches (.compute [] ρ te) .error) :
    Reaches (.compute [] ρ (.Force te)) .error := by
  obtain ⟨n, hn⟩ := herr
  -- Force te takes 1 step to compute [.force] ρ te
  -- The inner computation (compute [] ρ te) reaches error in n steps.
  -- We need: compute [.force] ρ te reaches error.
  -- compute [.force] ρ te = liftState [.force] (compute [] ρ te)
  -- Use liftState machinery: find first inactive, then compose.
  -- But a simpler approach: if inner errors, the lifted version must too.
  -- Specifically, at step n, inner = error. By steps_liftState (if all before n active)
  -- or by firstInactive decomposition, the lifted state reaches error.
  -- Actually, the simplest proof: if .error is reached, liftState .error = .error,
  -- so the lifted reaches .error at the same step if all intermediate are active,
  -- or earlier via firstInactive.
  have h1 : steps 1 (.compute [] ρ (.Force te)) = .compute [.force] ρ te := by
    simp [steps, step]
  have hlift : State.compute [.force] ρ te =
      liftState [.force] (.compute [] ρ te) := by simp [liftState]
  -- Find first inactive
  have h_inner_err : isActive (steps n (.compute [] ρ te)) = false := by
    rw [hn]; rfl
  have h_has_inactive : ∃ k, k ≤ n ∧ isActive (steps k (.compute [] ρ te)) = false :=
    ⟨n, Nat.le_refl _, h_inner_err⟩
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ te) n h_has_inactive
  have h_comm : steps K (liftState [.force] (.compute [] ρ te)) =
      liftState [.force] (steps K (.compute [] ρ te)) :=
    steps_liftState [.force] K (.compute [] ρ te) hK_min
  -- At step K, inner is inactive. Since it eventually reaches error, it must be error
  -- (or halt/ret[]). If it's error, liftState .error = .error.
  -- If it's halt v or ret [] v: steps from halt/ret[] stay halt/ret[].
  -- Since steps n = error, and halt/ret[] don't produce error (halt is absorbing,
  -- ret [] v → halt v), it must be error.
  generalize h_sK : steps K (.compute [] ρ te) = sK at hK_inact h_comm
  match sK with
  | .compute .. => simp [isActive] at hK_inact
  | .ret (_ :: _) _ => simp [isActive] at hK_inact
  | .error =>
    have h_lifted : steps K (liftState [.force] (.compute [] ρ te)) = .error := by
      rw [h_comm]; rfl
    exact ⟨1 + K, by rw [steps_trans, h1, hlift, h_lifted]⟩
  | .halt v =>
    -- Inner halted with v. But inner reaches error eventually. Contradiction.
    exfalso
    have : steps n (.compute [] ρ te) = .halt v := by
      have : n = K + (n - K) := by omega
      rw [this, steps_trans, h_sK, steps_halt]
    rw [hn] at this; simp at this
  | .ret [] v =>
    -- Inner is ret [] v → next step is halt v. But inner reaches error. Contradiction.
    exfalso
    have h_halt : steps (K + 1) (.compute [] ρ te) = .halt v := by
      rw [steps_trans, h_sK]; rfl
    exact reaches_halt_not_error ⟨K + 1, h_halt⟩ ⟨n, hn⟩

/-! ### refines_force_behEq -/

/-- **Force preserves Refines (behavioral).**
    If `e ⊑ e'`, then `Force e ⊑ Force e'`. -/
theorem refines_force_behEq (e e' : Expr) (h : e ⊑ e') :
    Expr.Force e ⊑ Expr.Force e' := by
  refine ⟨?_, ?_⟩
  · -- Compilation clause
    intro env hs
    rw [lowerTotalExpr_force] at hs ⊢
    have hs_inner := isSome_bind_inner hs
    have := h.1 env hs_inner
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp this
    rw [ht']; simp [Option.bind]
  · -- BehEq clause
    intro env
    simp only [lowerTotalExpr_force]
    cases he : lowerTotalExpr env e with
    | none => simp [Option.bind_none]
    | some te =>
      cases he' : lowerTotalExpr env e' with
      | none => simp [Option.bind_some, Option.bind_none]
      | some te' =>
        simp only [Option.bind_some]
        intro ρ hwf
        have ⟨herr_sub, hhalt_sub, hval_sub⟩ := refines_behEq_at h he he' ρ hwf
        refine ⟨?_, ?_, ?_⟩
        -- Error ↔
        · constructor
          · -- Force te errors → Force te' errors
            intro herr
            rcases force_reaches_error ρ te herr with hte_err | ⟨v1, hte_halt, hforce_v1_err⟩
            · exact force_sub_error ρ te' (herr_sub.mp hte_err)
            · -- te halts with v1, forcing v1 errors
              obtain ⟨v2, hte'_halt⟩ := hhalt_sub.mp ⟨v1, hte_halt⟩
              exact force_compose ρ te' v2 .error hte'_halt
                (force_frame_error_transfer v1 v2
                  (fun j => hval_sub j v1 v2 hte_halt hte'_halt) hforce_v1_err)
          · -- Force te' errors → Force te errors (symmetric)
            intro herr
            rcases force_reaches_error ρ te' herr with hte'_err | ⟨v2, hte'_halt, hforce_v2_err⟩
            · exact force_sub_error ρ te (herr_sub.mpr hte'_err)
            · obtain ⟨v1, hte_halt⟩ := hhalt_sub.mpr ⟨v2, hte'_halt⟩
              exact force_compose ρ te v1 .error hte_halt
                (force_frame_error_transfer v2 v1
                  (fun j => valueEq_symm j v1 v2 (hval_sub j v1 v2 hte_halt hte'_halt))
                  hforce_v2_err)
        -- Halts ↔
        · constructor
          · intro ⟨w, hw⟩
            obtain ⟨v1, hte_halt, hforce_v1_halt⟩ := force_reaches ρ te w hw
            obtain ⟨v2, hte'_halt⟩ := hhalt_sub.mp ⟨v1, hte_halt⟩
            obtain ⟨w', hforce_v2_halt⟩ :=
              force_frame_halts_transfer v1 v2
                (fun j => hval_sub j v1 v2 hte_halt hte'_halt) ⟨w, hforce_v1_halt⟩
            exact ⟨w', force_compose ρ te' v2 (.halt w') hte'_halt hforce_v2_halt⟩
          · intro ⟨w, hw⟩
            obtain ⟨v2, hte'_halt, hforce_v2_halt⟩ := force_reaches ρ te' w hw
            obtain ⟨v1, hte_halt⟩ := hhalt_sub.mpr ⟨v2, hte'_halt⟩
            obtain ⟨w', hforce_v1_halt⟩ :=
              force_frame_halts_transfer v2 v1
                (fun j => valueEq_symm j v1 v2 (hval_sub j v1 v2 hte_halt hte'_halt))
                ⟨w, hforce_v2_halt⟩
            exact ⟨w', force_compose ρ te v1 (.halt w') hte_halt hforce_v1_halt⟩
        -- ValueEq k
        · intro k w1 w2 hw1 hw2
          obtain ⟨v1, hte_halt, hforce_v1_halt⟩ := force_reaches ρ te w1 hw1
          obtain ⟨v2, hte'_halt, hforce_v2_halt⟩ := force_reaches ρ te' w2 hw2
          have hveq := hval_sub (k + 1) v1 v2 hte_halt hte'_halt
          -- Case-split on value type
          match v1, v2 with
          | .VDelay b1 e1, .VDelay b2 e2 =>
            -- Extract step counts from forcing
            obtain ⟨N1, hN1⟩ := hforce_v1_halt
            cases N1 with
            | zero => simp [steps] at hN1
            | succ N1 =>
              have hcomp1 : steps N1 (.compute [] e1 b1) = .halt w1 := by
                simp only [steps, step] at hN1; exact hN1
              obtain ⟨N2, hN2⟩ := hforce_v2_halt
              cases N2 with
              | zero => simp [steps] at hN2
              | succ N2 =>
                have hcomp2 : steps N2 (.compute [] e2 b2) = .halt w2 := by
                  simp only [steps, step] at hN2; exact hN2
                -- Pick level N1 + k + 1 from hval_sub
                have hveN := hval_sub (N1 + k + 1) _ _ hte_halt hte'_halt
                unfold ValueEq at hveN
                -- VDelay clause: ∀ j ≤ N1+k, stk, n ≤ j, ...
                -- Use j = N1 + k, stk = [], n = N1
                have hj_le : N1 + k ≤ N1 + k := Nat.le_refl _
                have hn_le : N1 ≤ N1 + k := Nat.le_add_right N1 k
                have hclause := hveN (N1 + k) hj_le [] [] trivial
                -- hclause.2.1 : ∀ v1' n, n ≤ N1+k → steps n (.compute [] e1 b1) = .halt v1' →
                --   ∃ v2' m, m ≤ N1+k ∧ steps m (.compute [] e2 b2) = .halt v2' ∧ ValueEq ((N1+k)-n) v1' v2'
                obtain ⟨w2', m', _, hw2'_halt, hw2'_veq⟩ := hclause.2.1 w1 N1 hn_le hcomp1
                -- (N1+k) - N1 = k
                have hk_eq : N1 + k - N1 = k := by omega
                rw [hk_eq] at hw2'_veq
                -- w2' = w2 by reaches_unique
                have : w2' = w2 := reaches_unique ⟨m', hw2'_halt⟩ ⟨N2, hcomp2⟩
                subst this
                exact hw2'_veq
          | .VCon _, .VCon _ => exact absurd ⟨w1, hforce_v1_halt⟩ (force_vcon_not_halts _)
          | .VLam _ _, .VLam _ _ => exact absurd ⟨w1, hforce_v1_halt⟩ (force_vlam_not_halts _ _)
          | .VConstr _ _, .VConstr _ _ => exact absurd ⟨w1, hforce_v1_halt⟩ (force_vconstr_not_halts _ _)
          | .VBuiltin b a1 ea, .VBuiltin _ a2 _ =>
            unfold ValueEq at hveq
            obtain ⟨hb, hargs, hea⟩ := hveq; subst hb; subst hea
            -- Both force to: match ea.head...
            -- If both halt, the results depend on ea and evalBuiltin.
            -- Need to show ValueEq k for the results.
            -- The force frame halts iff:
            -- 1. ea.head = .argQ, ea.tail = some rest → halt (VBuiltin b a rest)
            -- 2. ea.head = .argQ, ea.tail = none, evalBuiltin = some v → halt v
            -- For case 1: w1 = VBuiltin b a1 rest, w2 = VBuiltin b a2 rest
            --   ValueEq k: b=b, ListValueEq (k-1) a1 a2, rest=rest, evalBuiltin iff
            -- For case 2: w1 from evalBuiltin b a1, w2 from evalBuiltin b a2
            --   Need ValueEq k for evalBuiltin results. This requires more machinery.
            -- For now, handle the common cases:
            obtain ⟨n1, hn1⟩ := hforce_v1_halt
            cases n1 with
            | zero => simp [steps] at hn1
            | succ n1 =>
              simp only [steps, step] at hn1
              cases hhead : ea.head with
              | argV => rw [hhead] at hn1; simp [steps_error] at hn1
              | argQ =>
                rw [hhead] at hn1
                cases htail : ea.tail with
                | some rest =>
                  rw [htail] at hn1
                  -- hn1 : steps n1 (.ret [] (VBuiltin b a1 rest)) = .halt w1
                  -- Extract w1 = VBuiltin b a1 rest
                  have hw1 : w1 = .VBuiltin b a1 rest := by
                    cases n1 with
                    | zero => simp [steps] at hn1
                    | succ n1 => simp [steps, step, steps_halt] at hn1; exact hn1.symm
                  subst hw1
                  obtain ⟨n2, hn2⟩ := hforce_v2_halt
                  cases n2 with
                  | zero => simp [steps] at hn2
                  | succ n2 =>
                    simp only [steps, step, hhead, htail] at hn2
                    -- hn2 : steps n2 (.ret [] (VBuiltin b a2 rest)) = .halt w2
                    have hw2 : w2 = .VBuiltin b a2 rest := by
                      cases n2 with
                      | zero => simp [steps] at hn2
                      | succ n2 => simp [steps, step, steps_halt] at hn2; exact hn2.symm
                    subst hw2
                    -- Goal: ValueEq k (VBuiltin b a1 rest) (VBuiltin b a2 rest)
                    cases k with
                    | zero => simp [ValueEq]
                    | succ k =>
                      have hveq' := hval_sub (k + 1) _ _ hte_halt hte'_halt
                      unfold ValueEq at hveq' ⊢
                      exact ⟨rfl, hveq'.2.1, rfl⟩
                | none =>
                  rw [htail] at hn1
                  cases hev1 : Moist.CEK.evalBuiltin b a1 with
                  | none => rw [hev1] at hn1; simp [steps_error] at hn1
                  | some r1 =>
                    rw [hev1] at hn1
                    -- hn1 : steps n1 (.ret [] r1) = .halt w1
                    -- Extract w1 = r1
                    have hw1 : w1 = r1 := by
                      cases n1 with
                      | zero => simp [steps] at hn1
                      | succ n1 => simp [steps, step, steps_halt] at hn1; exact hn1.symm
                    subst hw1
                    obtain ⟨n2, hn2⟩ := hforce_v2_halt
                    cases n2 with
                    | zero => simp [steps] at hn2
                    | succ n2 =>
                      simp only [steps, step, hhead, htail] at hn2
                      cases hev2 : Moist.CEK.evalBuiltin b a2 with
                      | none => rw [hev2] at hn2; simp [steps_error] at hn2
                      | some r2 =>
                        rw [hev2] at hn2
                        -- hn2 : steps n2 (.ret [] r2) = .halt w2
                        -- Extract w2 = r2
                        have hw2 : w2 = r2 := by
                          cases n2 with
                          | zero => simp [steps] at hn2
                          | succ n2 => simp [steps, step, steps_halt] at hn2; exact hn2.symm
                        subst hw2
                        exact evalBuiltin_value_cong_early k b a1 a2 hargs _ _ hev1 hev2
          | .VCon _, .VLam _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VCon _, .VDelay _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VCon _, .VConstr _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VCon _, .VBuiltin _ _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VLam _ _, .VCon _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VLam _ _, .VDelay _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VLam _ _, .VConstr _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VLam _ _, .VBuiltin _ _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VDelay _ _, .VCon _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VDelay _ _, .VLam _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VDelay _ _, .VConstr _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VDelay _ _, .VBuiltin _ _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VConstr _ _, .VCon _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VConstr _ _, .VLam _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VConstr _ _, .VDelay _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VConstr _ _, .VBuiltin _ _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VBuiltin _ _ _, .VCon _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VBuiltin _ _ _, .VLam _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VBuiltin _ _ _, .VDelay _ _ => exact absurd hveq (by unfold ValueEq; exact id)
          | .VBuiltin _ _ _, .VConstr _ _ => exact absurd hveq (by unfold ValueEq; exact id)

/-! ## App congruence (same argument, function changes)

Decomposed into small independently-provable lemmas. -/

/-- VLam application: if `∀ j, ValueEq j` for VLam closures and same arg,
    the body computations agree on error. Extract step count N from Reaches,
    pick level N+1, instantiate VLam CIU clause with arg=va, stk=[], n=N. -/
private theorem app_step_vlam_error (b1 b2 : Term) (e1 e2 : CekEnv)
    (va : CekValue) (hve : ∀ j, ValueEq j (.VLam b1 e1) (.VLam b2 e2)) :
    Reaches (.compute [] (e1.extend va) b1) .error ↔
    Reaches (.compute [] (e2.extend va) b2) .error := by
  constructor
  · intro ⟨N, hN⟩
    have hveN := hve (N + 1)
    unfold ValueEq at hveN
    -- VLam clause: ∀ i ≤ N, ∀ arg1 arg2, ValueEq i arg1 arg2 → ∀ stk, ... → ∀ n ≤ i, ...
    -- Use i = N, arg1 = arg2 = va, stk = [], n = N
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨m, _, herr2⟩ := hclause.1 N (Nat.le_refl N) hN
    exact ⟨m, herr2⟩
  · intro ⟨N, hN⟩
    have hveN := hve (N + 1)
    unfold ValueEq at hveN
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨m, _, herr1⟩ := hclause.2.2.1 N (Nat.le_refl N) hN
    exact ⟨m, herr1⟩

/-- VLam application: halts agreement. -/
private theorem app_step_vlam_halts (b1 b2 : Term) (e1 e2 : CekEnv)
    (va : CekValue) (hve : ∀ j, ValueEq j (.VLam b1 e1) (.VLam b2 e2)) :
    Halts (.compute [] (e1.extend va) b1) ↔
    Halts (.compute [] (e2.extend va) b2) := by
  constructor
  · intro ⟨w, N, hN⟩
    have hveN := hve (N + 1)
    unfold ValueEq at hveN
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨w2, m, _, hw2, _⟩ := hclause.2.1 w N (Nat.le_refl N) hN
    exact ⟨w2, m, hw2⟩
  · intro ⟨w, N, hN⟩
    have hveN := hve (N + 1)
    unfold ValueEq at hveN
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨w1, m, _, hw1, _⟩ := hclause.2.2.2 w N (Nat.le_refl N) hN
    exact ⟨w1, m, hw1⟩

/-- VLam application: value agreement. Extract N1 from h1, pick level N1+k+1,
    use VLam clause at n=N1 to get ValueEq(N1+k-N1)=ValueEq k for w1 and
    an intermediate w2'. Then w2'=w2 by reaches_unique. -/
private theorem app_step_vlam_value (k : Nat) (b1 b2 : Term) (e1 e2 : CekEnv)
    (va : CekValue) (hve : ∀ j, ValueEq j (.VLam b1 e1) (.VLam b2 e2))
    (v1 v2 : CekValue)
    (h1 : Reaches (.compute [] (e1.extend va) b1) (.halt v1))
    (h2 : Reaches (.compute [] (e2.extend va) b2) (.halt v2)) :
    ValueEq k v1 v2 := by
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  -- Pick level N1 + k + 1
  have hveN := hve (N1 + k + 1)
  unfold ValueEq at hveN
  -- Use i = N1 + k, arg = va, stk = [], n = N1
  have hi_le : N1 + k ≤ N1 + k := Nat.le_refl _
  have hn_le : N1 ≤ N1 + k := Nat.le_add_right N1 k
  have hclause := hveN (N1 + k) hi_le va va (valueEq_refl (N1 + k) va) [] [] trivial
  obtain ⟨w2', m', _, hw2', hveq_w⟩ := hclause.2.1 v1 N1 hn_le hN1
  -- (N1 + k) - N1 = k
  have hk_eq : N1 + k - N1 = k := by omega
  rw [hk_eq] at hveq_w
  -- w2' = v2 by reaches_unique
  have : w2' = v2 := reaches_unique ⟨m', hw2'⟩ ⟨N2, hN2⟩
  subst this
  exact hveq_w

/-- Non-function values: application always errors. -/
private theorem app_step_nonfunction_errors (va : CekValue) (c : Const) :
    Reaches (step (.ret [.funV (.VCon c)] va)) .error := ⟨0, rfl⟩

private theorem app_step_delay_errors (va : CekValue) (b : Term) (e : CekEnv) :
    Reaches (step (.ret [.funV (.VDelay b e)] va)) .error := ⟨0, rfl⟩

private theorem app_step_constr_errors (va : CekValue) (tag : Nat) (fs : List CekValue) :
    Reaches (step (.ret [.funV (.VConstr tag fs)] va)) .error := ⟨0, rfl⟩


/-! ## Halts-and-errors impossibility -/

/-- A state cannot both halt and error. -/
theorem not_halts_and_errors {s : State} (hh : Halts s) (he : Reaches s .error) : False :=
  let ⟨_, hv⟩ := hh; reaches_halt_not_error hv he

/-! ## extractConsts congruence from ListValueEq

If `ListValueEq (k+1) args1 args2`, then `VCon` values at corresponding
positions have equal constants (from `ValueEq (k+1) (VCon c1) (VCon c2) → c1 = c2`).
Non-VCon values cause `extractConsts` to fail on both sides equally. -/

private theorem extractConsts_cong :
    ∀ (k : Nat) (as1 as2 : List CekValue),
    ListValueEq (k + 1) as1 as2 →
    Moist.CEK.extractConsts as1 = Moist.CEK.extractConsts as2
  | _, [], [], _ => rfl
  | k, .VCon c1 :: rest1, .VCon c2 :: rest2, h => by
    simp only [ListValueEq] at h
    have hve := h.1; unfold ValueEq at hve; subst hve
    simp only [Moist.CEK.extractConsts]
    rw [extractConsts_cong k rest1 rest2 h.2]
  | k, .VCon _ :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, .VCon _ :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, .VCon _ :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, .VCon _ :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, (.VLam _ _) :: _, _ => rfl
  | k, (.VLam _ _) :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, (.VDelay _ _) :: _, _ => rfl
  | k, (.VDelay _ _) :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, (.VConstr _ _) :: _, _ => rfl
  | k, (.VConstr _ _) :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VBuiltin _ _ _) :: _, _ => rfl
  | _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
  | _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])

/-! ## evalBuiltin congruence

When `ListValueEq (k+1) args1 args2` and `va` is the same value,
`evalBuiltin b (va :: args1)` and `evalBuiltin b (va :: args2)` agree on
`none` and produce `ValueEq k`-related results when both succeed.

Strategy:
- `extractConsts` produces identical constant lists (from `extractConsts_cong`),
  so the `evalBuiltinConst` path returns identical `VCon` results.
- `evalBuiltinPassThrough` either returns `none` on both sides (same pattern
  match outcome), or returns values from specific positions in the arg list
  which are `ValueEq (k+1)` (hence `ValueEq k` by mono). -/

/-- VCon constant preserved across ValueEq. -/
private theorem vcon_eq_of_valueEq_succ {k : Nat} {c : Const} {v : CekValue}
    (h : ValueEq (k + 1) (.VCon c) v) : v = .VCon c := by
  cases v with
  | VCon c' => simp only [ValueEq] at h; exact (congrArg CekValue.VCon h).symm
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEq] at h

/-- If v1 is not VCon and ValueEq v1 v2, then v2 is not VCon. -/
private theorem not_vcon_of_valueEq_succ {k : Nat} {v1 v2 : CekValue}
    (h : ValueEq (k + 1) v1 v2) (hv1 : ∀ c, v1 ≠ .VCon c) : ∀ c, v2 ≠ .VCon c := by
  intro c hc; subst hc
  cases v1 with
  | VCon c1 => exact absurd rfl (hv1 c1)
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEq] at h

/-- extractConsts congruence for the full list `va :: args`. -/
private theorem extractConsts_cons_cong (k : Nat) (va : CekValue)
    (as1 as2 : List CekValue) (hargs : ListValueEq (k + 1) as1 as2) :
    Moist.CEK.extractConsts (va :: as1) = Moist.CEK.extractConsts (va :: as2) := by
  cases va with
  | VCon c =>
    simp only [Moist.CEK.extractConsts]
    rw [extractConsts_cong k as1 as2 hargs]
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

/-- evalBuiltin congruence: when `ListValueEq (k+1) args1 args2` and `va`
    is the same value, `evalBuiltin b (va :: args1)` and `evalBuiltin b (va :: args2)`
    agree on none and produce `ValueEq k`-related results when both succeed.

    Strategy: `extractConsts (va :: args1) = extractConsts (va :: args2)`, so the
    constant-extraction path returns identical results. For `evalBuiltinPassThrough`,
    the function only inspects VCon constants at specific positions (preserved by
    `ListValueEq (k+1)`) and returns either VCon results (identical) or closures
    from matching positions (`ValueEq (k+1)`, hence `ValueEq k` by mono). -/
theorem evalBuiltin_cong (k : Nat) (b : BuiltinFun)
    (va : CekValue) (args1 args2 : List CekValue)
    (hargs : ListValueEq (k + 1) args1 args2) :
    (Moist.CEK.evalBuiltin b (va :: args1) = none ↔
     Moist.CEK.evalBuiltin b (va :: args2) = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b (va :: args1) = some r1 →
              Moist.CEK.evalBuiltin b (va :: args2) = some r2 →
              ValueEq k r1 r2) := by
  have hec := extractConsts_cons_cong k va args1 args2 hargs
  -- Key helper: evalBuiltinPassThrough isNone agrees on both sides
  have hpt := evalBuiltinPassThrough_isNone_eq k b va args1 args2 hargs
  simp only [Moist.CEK.evalBuiltin]
  cases hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: args1) with
  | some v1 =>
    -- hp1 says isNone = false, so hp2 must also be some
    have hp2_not_none : Moist.CEK.evalBuiltinPassThrough b (va :: args2) ≠ none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args1)).isNone = false from by simp [hp1]] at hpt
      intro h; rw [h] at hpt; simp at hpt
    have ⟨v2, hp2⟩ : ∃ v, Moist.CEK.evalBuiltinPassThrough b (va :: args2) = some v := by
      cases h : Moist.CEK.evalBuiltinPassThrough b (va :: args2) with
      | some v => exact ⟨v, rfl⟩
      | none => contradiction
    rw [hp2]
    constructor; · simp
    · intro r1 r2 h1 h2
      injection h1 with h1; injection h2 with h2; subst h1; subst h2
      exact evalBuiltinPassThrough_valueEq k b va args1 args2 hargs hp1 hp2
  | none =>
    have hp2_none : Moist.CEK.evalBuiltinPassThrough b (va :: args2) = none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args1)).isNone = true from by simp [hp1]] at hpt
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b (va :: args2) with
      | none => rfl
      | some _ => simp [hp2] at hpt
    rw [hp2_none, hec]
    exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact valueEq_refl k r1⟩
where
  listValueEq_same_length : ∀ (k : Nat) (as1 as2 : List CekValue),
      ListValueEq k as1 as2 → as1.length = as2.length
    | _, [], [], _ => rfl
    | k, _ :: as1', _ :: as2', h => by
      simp only [ListValueEq] at h
      simp only [List.length_cons]
      exact congrArg Nat.succ (listValueEq_same_length k as1' as2' h.2)
    | _, [], _ :: _, h => by simp [ListValueEq] at h
    | _, _ :: _, [], h => by simp [ListValueEq] at h
  evalBuiltinPassThrough_isNone_eq (k : Nat) (b : BuiltinFun) (va : CekValue)
      (as1 as2 : List CekValue)
      (hargs : ListValueEq (k + 1) as1 as2) :
      (Moist.CEK.evalBuiltinPassThrough b (va :: as1)).isNone =
      (Moist.CEK.evalBuiltinPassThrough b (va :: as2)).isNone := by
    -- For non-passthrough builtins: `cases b <;> try simp [evalBuiltinPassThrough]`
    -- closes all non-passthrough goals. For each passthrough builtin we case-split
    -- as1 and as2 simultaneously (using listValueEq_same_length to eliminate
    -- cross-length pairs via omega), then simp [evalBuiltinPassThrough] closes
    -- wrong-length cases, and explicit `cases` on the deciding VCon element handle
    -- the matching case.
    cases b <;> try simp [Moist.CEK.evalBuiltinPassThrough]
    -- IfThenElse: exact match on [elseV, thenV, VCon (Bool cond)] (as1 = [thenV, VCon(Bool cond)])
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨y1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- Only remaining: as1 = [x1, y1], as2 = [x2, y2]
      simp only [ListValueEq] at hargs
      cases y1 with
      | VCon c1 =>
        cases y2 with
        | VCon c2 =>
          have hc : c1 = c2 := by have := hargs.2.1; simp only [ValueEq] at this; exact this
          subst hc; cases c1 <;> simp [Moist.CEK.evalBuiltinPassThrough]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.2.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases y2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.2.1.elim
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
    -- ChooseUnit: exact match on [result, VCon Unit] (as1 = [VCon Unit])
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- Only remaining: as1 = [x1], as2 = [x2]
      simp only [ListValueEq] at hargs
      cases x1 with
      | VCon c1 =>
        cases x2 with
        | VCon c2 =>
          have hc : c1 = c2 := by simp only [ValueEq] at hargs; exact hargs.1
          subst hc; cases c1 <;> simp [Moist.CEK.evalBuiltinPassThrough]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases x2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.1.elim
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
    -- Trace: exact match on [result, VCon (String _)] (as1 = [VCon (String _)])
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- Only remaining: as1 = [x1], as2 = [x2]
      simp only [ListValueEq] at hargs
      cases x1 with
      | VCon c1 =>
        cases x2 with
        | VCon c2 =>
          have hc : c1 = c2 := by simp only [ValueEq] at hargs; exact hargs.1
          subst hc; cases c1 <;> simp [Moist.CEK.evalBuiltinPassThrough]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases x2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.1.elim
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
    -- ChooseList: exact match on [consCase, nilCase, VCon (ConstDataList/ConstList l)]
    -- as1 must have 2 elements; deciding element is as1[1]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨y1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- Only remaining: as1 = [x1, y1], as2 = [x2, y2]
      simp only [ListValueEq] at hargs
      cases y1 with
      | VCon c1 =>
        cases y2 with
        | VCon c2 =>
          have hc : c1 = c2 := by have := hargs.2.1; simp only [ValueEq] at this; exact this
          subst hc; cases c1 <;> simp [Moist.CEK.evalBuiltinPassThrough]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.2.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases y2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.2.1.elim
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
    -- MkCons: match on [VCon (ConstList tail), elem] — va itself decides
    · cases va with
      | VCon c =>
        cases c with
        | ConstList tail =>
          have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
          rcases as1 with _ | ⟨x1, _ | ⟨_, _⟩⟩ <;>
          rcases as2 with _ | ⟨x2, _ | ⟨_, _⟩⟩ <;>
          (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
          try simp [Moist.CEK.evalBuiltinPassThrough]
          -- Only remaining: as1 = [x1], as2 = [x2]
          simp only [ListValueEq] at hargs
          cases x1 with
          | VCon c1 =>
            cases x2 with
            | VCon c2 =>
              have hc : c1 = c2 := by simp only [ValueEq] at hargs; exact hargs.1
              subst hc; simp [Moist.CEK.evalBuiltinPassThrough]
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              simp only [ValueEq] at hargs; exact hargs.1.elim
          | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
            cases x2 with
            | VCon _ => simp only [ValueEq] at hargs; exact hargs.1.elim
            | _ => simp [Moist.CEK.evalBuiltinPassThrough]
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
      | _ => simp [Moist.CEK.evalBuiltinPassThrough]
    -- ChooseData: exact match on [bCase,iCase,listCase,mapCase,constrCase,VCon(Data d)]
    -- as1 must have 5 elements; deciding element is as1[4]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨x1, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      rcases as2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨x2, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- Only remaining: as1 = [a0,a1,a2,a3,x1], as2 = [b0,b1,b2,b3,x2]
      simp only [ListValueEq] at hargs
      cases x1 with
      | VCon c1 =>
        cases x2 with
        | VCon c2 =>
          have hc : c1 = c2 := by have := hargs.2.2.2.2.1; simp only [ValueEq] at this; exact this
          subst hc; cases c1 with
          | Data d => cases d <;> simp [Moist.CEK.evalBuiltinPassThrough]
          | _ => simp [Moist.CEK.evalBuiltinPassThrough]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.2.2.2.2.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases x2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.2.2.2.2.1.elim
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
  evalBuiltinPassThrough_valueEq (k : Nat) (b : BuiltinFun) (va : CekValue)
      (as1 as2 : List CekValue)
      (hargs : ListValueEq (k + 1) as1 as2)
      {r1 r2 : CekValue}
      (hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: as1) = some r1)
      (hp2 : Moist.CEK.evalBuiltinPassThrough b (va :: as2) = some r2) :
      ValueEq k r1 r2 := by
    -- For non-passthrough builtins: hp1 becomes none=some r1 via simp → False.
    -- For passthrough builtins: case-split as1 and as2 simultaneously (using
    -- listValueEq_same_length + omega to kill cross-length pairs); simp at hp1
    -- closes wrong-length cases; then use vcon_eq_of_valueEq_succ to prove
    -- the as2 deciding element equals the as1 one, and extract the return value.
    cases b <;> try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
    -- IfThenElse: [elseV=va, thenV=as1[0], VCon(Bool cond)=as1[1]]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨a1_1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨a2_1, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0, a1_1], as2 = [a2_0, a2_1]
      -- hp1/hp2 were simplified but may have conditions; handle by cases
      simp only [ListValueEq] at hargs
      cases a1_1 with
      | VCon c1 =>
        cases c1 with
        | Bool cond =>
          have ha2_1 := vcon_eq_of_valueEq_succ hargs.2.1
          subst ha2_1
          cases cond with
          | true =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) a1_0 a2_0 hargs.1
          | false =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_refl k va
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- ChooseUnit: [result=va, VCon Unit=as1[0]] → r1 = va = r2
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0], as2 = [a2_0]
      simp only [ListValueEq] at hargs
      cases a1_0 with
      | VCon c1 =>
        cases c1 with
        | Unit =>
          have ha2_0 := vcon_eq_of_valueEq_succ hargs.1
          subst ha2_0
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          subst hp1; subst hp2
          exact valueEq_refl k va
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- Trace: [result=va, VCon(String s)=as1[0]] → r1 = va = r2
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0], as2 = [a2_0]
      simp only [ListValueEq] at hargs
      cases a1_0 with
      | VCon c1 =>
        cases c1 with
        | String _ =>
          have ha2_0 := vcon_eq_of_valueEq_succ hargs.1
          subst ha2_0
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          subst hp1; subst hp2
          exact valueEq_refl k va
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- ChooseList: [consCase=va, nilCase=as1[0], VCon(ConstDataList/ConstList l)=as1[1]]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨a1_1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨a2_1, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0, a1_1], as2 = [a2_0, a2_1]
      simp only [ListValueEq] at hargs
      cases a1_1 with
      | VCon c1 =>
        have ha2_1 := vcon_eq_of_valueEq_succ hargs.2.1
        subst ha2_1
        cases c1 with
        | ConstDataList l =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hargs.1
          | false =>
            simp only [h, ite_false] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_refl k va
        | ConstList l =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hargs.1
          | false =>
            simp only [h, ite_false] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_refl k va
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- MkCons: va = VCon (ConstList tail), elem = as1[0] = VCon c1 → r = VCon (ConstList (c1::tail))
    · cases va with
      | VCon c =>
        cases c with
        | ConstList tail =>
          have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
          rcases as1 with _ | ⟨a1_0, _ | ⟨_, _⟩⟩ <;>
          rcases as2 with _ | ⟨a2_0, _ | ⟨_, _⟩⟩ <;>
          (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          -- Only remaining: as1 = [a1_0], as2 = [a2_0]
          simp only [ListValueEq] at hargs
          cases a1_0 with
          | VCon c1 =>
            have ha2_0 := vcon_eq_of_valueEq_succ hargs.1
            subst ha2_0
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_refl k (.VCon (.ConstList (c1 :: tail)))
          | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- ChooseData: [bCase=va, iCase=as1[0], ..., constrCase=as1[3], VCon(Data d)=as1[4]]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨a1_1, _ | ⟨a1_2, _ | ⟨a1_3, _ | ⟨a1_4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨a2_1, _ | ⟨a2_2, _ | ⟨a2_3, _ | ⟨a2_4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0,a1_1,a1_2,a1_3,a1_4], as2 = [a2_0,...,a2_4]
      simp only [ListValueEq] at hargs
      cases a1_4 with
      | VCon c1 =>
        cases c1 with
        | Data d =>
          have ha2_4 := vcon_eq_of_valueEq_succ hargs.2.2.2.2.1
          subst ha2_4
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          obtain ⟨hv0, hv1, hv2, hv3, _, _⟩ := hargs
          cases d with
          | Constr _ _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv3
          | Map _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv2
          | List _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv1
          | I _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv0
          | B _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_refl k va
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1

/-! ## App congruence: same argument, function changes -/

open Moist.Verified.StepLift (apply_reaches apply_reaches_error apply_compose)

/-- `ret [] v` halts with `v` in exactly 1 step. -/
private theorem ret_nil_halts (v : CekValue) :
    Reaches (.ret [] v) (.halt v) := ⟨1, rfl⟩

/-- `ret [] v` never errors. -/
private theorem ret_nil_not_error (v : CekValue)
    (h : Reaches (.ret [] v) .error) : False := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_halt] at hn

/-- Extract value from `Reaches (.ret [] v) (.halt w)`: `w = v`. -/
private theorem ret_nil_halt_eq (v w : CekValue)
    (h : Reaches (.ret [] v) (.halt w)) : w = v := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_halt] at hn; exact hn.symm

/-- If `tf` errors, `Apply tf ta` errors.
    Build manually via liftState machinery (cannot use apply_compose since ta may not halt). -/
private theorem apply_error_of_fn_error (ρ : CekEnv) (tf ta : Term)
    (herr : Reaches (.compute [] ρ tf) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error := by
  obtain ⟨n, hn⟩ := herr
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) =
      .compute [.arg ta ρ] ρ tf := by simp [steps, step]
  have hlift : State.compute [.arg ta ρ] ρ tf =
      liftState [.arg ta ρ] (.compute [] ρ tf) := by simp [liftState]
  have h_inner_err : isActive (steps n (.compute [] ρ tf)) = false := by rw [hn]; rfl
  obtain ⟨K, _, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ tf) n ⟨n, Nat.le_refl _, h_inner_err⟩
  have h_comm := steps_liftState [.arg ta ρ] K (.compute [] ρ tf) hK_min
  generalize h_sK : steps K (.compute [] ρ tf) = sK at hK_inact h_comm
  match sK with
  | .compute .. => simp [isActive] at hK_inact
  | .ret (_ :: _) _ => simp [isActive] at hK_inact
  | .error =>
    exact ⟨1 + K, by rw [steps_trans, h1, hlift, h_comm]; simp [liftState]⟩
  | .halt v =>
    exfalso; have : steps n (.compute [] ρ tf) = .halt v := by
      have : n = K + (n - K) := by omega
      rw [this, steps_trans, h_sK, steps_halt]
    rw [hn] at this; simp at this
  | .ret [] v =>
    exfalso; exact reaches_halt_not_error ⟨K + 1, by rw [steps_trans, h_sK]; rfl⟩ ⟨n, hn⟩

/-- If `tf` halts with `vf` and `ta` errors, `Apply tf ta` errors.
    Proof: compose the tf halting phase, the 1-step arg-frame transition,
    and the ta error phase using liftState. -/
private theorem apply_error_of_arg_error (ρ : CekEnv) (tf ta : Term)
    (vf : CekValue) (hf_halt : Reaches (.compute [] ρ tf) (.halt vf))
    (ha_err : Reaches (.compute [] ρ ta) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error := by
  -- Phase 1: show compute [funV vf] ρ ta reaches error
  -- (embed ta-error into the [funV vf] context via liftState)
  obtain ⟨Na, hNa⟩ := ha_err
  have hlift_a : State.compute [.funV vf] ρ ta =
      liftState [.funV vf] (.compute [] ρ ta) := by simp [liftState]
  have h_a_inact : isActive (steps Na (.compute [] ρ ta)) = false := by rw [hNa]; rfl
  obtain ⟨Ka, _, hKa_inact, hKa_min⟩ :=
    firstInactive (.compute [] ρ ta) Na ⟨Na, Nat.le_refl _, h_a_inact⟩
  have h_comm_a := steps_liftState [.funV vf] Ka (.compute [] ρ ta) hKa_min
  generalize h_sKa : steps Ka (.compute [] ρ ta) = sKa at hKa_inact h_comm_a
  have h_lifted_a_err : Reaches (.compute [.funV vf] ρ ta) .error := by
    match sKa with
    | .compute .. => simp [isActive] at hKa_inact
    | .ret (_ :: _) _ => simp [isActive] at hKa_inact
    | .error =>
      exact ⟨Ka, by rw [hlift_a, h_comm_a]; simp [liftState]⟩
    | .halt va =>
      exfalso
      have : steps Na (.compute [] ρ ta) = .halt va := by
        have : Na = Ka + (Na - Ka) := by omega
        rw [this, steps_trans, h_sKa, steps_halt]
      rw [hNa] at this; simp at this
    | .ret [] va =>
      exfalso
      exact reaches_halt_not_error ⟨Ka + 1, by rw [steps_trans, h_sKa]; rfl⟩ ⟨Na, hNa⟩
  -- Phase 2: ret [arg ta ρ] vf reaches error
  -- (one step to compute [funV vf] ρ ta, then error)
  obtain ⟨me, hme⟩ := h_lifted_a_err
  have h_ret_err : Reaches (.ret [.arg ta ρ] vf) .error :=
    ⟨1 + me, by rw [steps_trans]; simp [steps, step, hme]⟩
  -- Phase 3: embed tf-halt into the [arg ta ρ] context via liftState,
  -- then chain with h_ret_err to get the full Apply reaching error
  obtain ⟨Nf, hNf⟩ := hf_halt
  have hlift_f : State.compute [.arg ta ρ] ρ tf =
      liftState [.arg ta ρ] (.compute [] ρ tf) := by simp [liftState]
  have h_f_inact : isActive (steps Nf (.compute [] ρ tf)) = false := by rw [hNf]; rfl
  obtain ⟨Kf, hKf_le, hKf_inact, hKf_min⟩ :=
    firstInactive (.compute [] ρ tf) Nf ⟨Nf, Nat.le_refl _, h_f_inact⟩
  have h_comm_f := steps_liftState [.arg ta ρ] Kf (.compute [] ρ tf) hKf_min
  have h_not_error_f : steps Kf (.compute [] ρ tf) ≠ .error := by
    intro herr
    have : steps Nf (.compute [] ρ tf) = .error := by
      have : Nf = Kf + (Nf - Kf) := by omega
      rw [this, steps_trans, herr, steps_error]
    rw [hNf] at this; simp at this
  obtain ⟨mr, hmr⟩ := h_ret_err
  generalize h_sKf : steps Kf (.compute [] ρ tf) = sKf at hKf_inact h_comm_f h_not_error_f
  match sKf with
  | .compute .. => simp [isActive] at hKf_inact
  | .ret (_ :: _) _ => simp [isActive] at hKf_inact
  | .error => exact absurd rfl h_not_error_f
  | .halt vf' =>
    have hvf_eq : vf' = vf := reaches_unique ⟨Kf, h_sKf⟩ ⟨Nf, hNf⟩
    subst hvf_eq
    exact ⟨1 + Kf + mr, by
      have : 1 + Kf + mr = 1 + (Kf + mr) := by omega
      rw [this, steps_trans]; simp [steps, step]
      rw [hlift_f, steps_trans, h_comm_f]; simp [liftState, hmr]⟩
  | .ret [] vf' =>
    have hvf_eq : vf' = vf :=
      reaches_unique ⟨Kf + 1, by rw [steps_trans, h_sKf]; rfl⟩ ⟨Nf, hNf⟩
    subst hvf_eq
    exact ⟨1 + Kf + mr, by
      have : 1 + Kf + mr = 1 + (Kf + mr) := by omega
      rw [this, steps_trans]; simp [steps, step]
      rw [hlift_f, steps_trans, h_comm_f]; simp [liftState, hmr]⟩

private theorem app_step_error_transfer (vf vf' va : CekValue)
    (hveq : ∀ j, ValueEq j vf vf')
    (herr : Reaches (step (.ret [.funV vf] va)) .error) :
    Reaches (step (.ret [.funV vf'] va)) .error := by
  match vf, vf' with
  | .VLam b1 e1, .VLam b2 e2 =>
    simp only [step] at herr ⊢
    exact (app_step_vlam_error b1 b2 e1 e2 va hveq).mp herr
  | .VCon c1, .VCon _ =>
    exact app_step_nonfunction_errors va c1 |>.elim (fun n hn => by
      simp only [step] at herr; exact ⟨0, rfl⟩)
  | .VDelay b e, .VDelay _ _ =>
    simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VConstr tag fs, .VConstr _ _ =>
    simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2 =>
    have hve2 : ValueEq 2 (.VBuiltin b1 args1 ea1) (.VBuiltin b2 args2 ea2) := hveq 2
    unfold ValueEq at hve2
    obtain ⟨hb, hargs, hea⟩ := hve2
    subst hb; subst hea
    cases hhead : ea1.head with
    | argQ =>
      simp only [step, hhead] at herr ⊢; exact ⟨0, rfl⟩
    | argV =>
      cases htail : ea1.tail with
      | some rest =>
        simp only [step, hhead, htail] at herr
        exact absurd herr (ret_nil_not_error _)
      | none =>
        simp only [step, hhead, htail] at herr ⊢
        have hargs1 := listValueEq_mono 1 2 (by omega) _ _ hargs
        have ⟨hcong, _⟩ := evalBuiltin_cong 0 b1 va args1 args2 hargs1
        cases hev1 : Moist.CEK.evalBuiltin b1 (va :: args1) with
        | none =>
          rw [hcong.mp hev1]; exact ⟨0, rfl⟩
        | some v1 =>
          simp only [hev1] at herr
          exact absurd herr (ret_nil_not_error v1)
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _
  | .VCon _, .VConstr _ _ | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _
  | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VConstr _ _, .VCon _ | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VLam _ _
  | .VBuiltin _ _ _, .VDelay _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd (hveq 1) (by simp [ValueEq])

private theorem app_step_halts_transfer (vf vf' va v : CekValue)
    (hveq : ∀ j, ValueEq j vf vf')
    (hh : Reaches (step (.ret [.funV vf] va)) (.halt v)) :
    ∃ v', Reaches (step (.ret [.funV vf'] va)) (.halt v') := by
  match vf, vf' with
  | .VLam b1 e1, .VLam b2 e2 =>
    simp only [step] at hh ⊢
    obtain ⟨w, hw⟩ := (app_step_vlam_halts b1 b2 e1 e2 va hveq).mp ⟨v, hh⟩
    exact ⟨w, hw⟩
  | .VCon c, .VCon _ =>
    exact (reaches_halt_not_error hh (app_step_nonfunction_errors va c)).elim
  | .VDelay b e, .VDelay _ _ =>
    exact (reaches_halt_not_error hh (app_step_delay_errors va b e)).elim
  | .VConstr tag fs, .VConstr _ _ =>
    exact (reaches_halt_not_error hh (app_step_constr_errors va tag fs)).elim
  | .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2 =>
    have hve2 : ValueEq 2 (.VBuiltin b1 args1 ea1) (.VBuiltin b2 args2 ea2) := hveq 2
    unfold ValueEq at hve2
    obtain ⟨hb, hargs, hea⟩ := hve2
    subst hb; subst hea
    cases hhead : ea1.head with
    | argQ =>
      have herr : Reaches (step (.ret [.funV (.VBuiltin b1 args1 ea1)] va)) .error :=
        ⟨0, by simp only [steps, step, hhead]⟩
      exact (reaches_halt_not_error hh herr).elim
    | argV =>
      cases htail : ea1.tail with
      | some rest =>
        simp only [step, hhead, htail] at hh ⊢
        have heq := ret_nil_halt_eq _ v hh
        subst heq
        exact ⟨_, ret_nil_halts (.VBuiltin b1 (va :: args2) rest)⟩
      | none =>
        simp only [step, hhead, htail] at hh ⊢
        have hargs1 := listValueEq_mono 1 2 (by omega) _ _ hargs
        have ⟨hcong, _⟩ := evalBuiltin_cong 0 b1 va args1 args2 hargs1
        cases hev1 : Moist.CEK.evalBuiltin b1 (va :: args1) with
        | none =>
          simp only [hev1] at hh
          exact (reaches_halt_not_error hh ⟨0, rfl⟩).elim
        | some r1 =>
          simp only [hev1] at hh
          cases hev2 : Moist.CEK.evalBuiltin b1 (va :: args2) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 => simp only [hev2]; exact ⟨r2, ret_nil_halts r2⟩
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _
  | .VCon _, .VConstr _ _ | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _
  | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VConstr _ _, .VCon _ | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VLam _ _
  | .VBuiltin _ _ _, .VDelay _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd (hveq 1) (by simp [ValueEq])

private theorem app_step_value_agreement (k : Nat) (vf vf' va : CekValue)
    (hveq : ValueEq (k + 1) vf vf')
    (hveq_all : ∀ j, ValueEq j vf vf')
    (v1 v2 : CekValue)
    (h1 : Reaches (step (.ret [.funV vf] va)) (.halt v1))
    (h2 : Reaches (step (.ret [.funV vf'] va)) (.halt v2)) :
    ValueEq k v1 v2 := by
  match vf, vf' with
  | .VLam b1 e1, .VLam b2 e2 =>
    simp only [step] at h1 h2
    exact app_step_vlam_value k b1 b2 e1 e2 va hveq_all v1 v2 h1 h2
  | .VCon c, .VCon _ =>
    exact (reaches_halt_not_error h1 (app_step_nonfunction_errors va c)).elim
  | .VDelay b e, .VDelay _ _ =>
    exact (reaches_halt_not_error h1 (app_step_delay_errors va b e)).elim
  | .VConstr tag fs, .VConstr _ _ =>
    exact (reaches_halt_not_error h1 (app_step_constr_errors va tag fs)).elim
  | .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2 =>
    -- Use hveq_all (k+2) to get ListValueEq (k+1) args1 args2 for evalBuiltin_cong k
    have hve_hi : ValueEq (k + 2) (.VBuiltin b1 args1 ea1) (.VBuiltin b2 args2 ea2) :=
      hveq_all (k + 2)
    unfold ValueEq at hve_hi
    obtain ⟨hb, hargs, hea⟩ := hve_hi
    subst hb; subst hea
    -- Also unfold hveq at k+1 to get same structure
    unfold ValueEq at hveq
    obtain ⟨_, hargs2, _⟩ := hveq
    cases hhead : ea1.head with
    | argQ =>
      have herr : Reaches (step (.ret [.funV (.VBuiltin b1 args1 ea1)] va)) .error :=
        ⟨0, by simp only [steps, step, hhead]⟩
      exact (reaches_halt_not_error h1 herr).elim
    | argV =>
      cases htail : ea1.tail with
      | some rest =>
        simp only [step, hhead, htail] at h1 h2
        -- h1 : Reaches (.ret [] (.VBuiltin b1 (va::args1) rest)) (.halt v1)
        -- h2 : Reaches (.ret [] (.VBuiltin b1 (va::args2) rest)) (.halt v2)
        have hv1 := ret_nil_halt_eq _ v1 h1
        have hv2 := ret_nil_halt_eq _ v2 h2
        subst hv1; subst hv2
        -- Need ValueEq k (VBuiltin b1 (va::args1) rest) (VBuiltin b1 (va::args2) rest)
        cases k with
        | zero => simp [ValueEq]
        | succ k' =>
          -- hargs : ListValueEq (k'+2+1) args1 args2 (VBuiltin at k+2 stores k+2, k=k'+2)
          unfold ValueEq
          refine ⟨rfl, ?_, rfl⟩
          simp only [ListValueEq]
          exact ⟨valueEq_refl (k' + 1) va, listValueEq_mono (k' + 1) (k' + 2 + 1) (by omega) _ _ hargs⟩
      | none =>
        simp only [step, hhead, htail] at h1 h2
        have hargs_k1 := listValueEq_mono (k + 1) (k + 2) (by omega) _ _ hargs
        have ⟨hcong, hval⟩ := evalBuiltin_cong k b1 va args1 args2 hargs_k1
        cases hev1 : Moist.CEK.evalBuiltin b1 (va :: args1) with
        | none =>
          simp only [hev1] at h1
          exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
        | some r1 =>
          simp only [hev1] at h1
          cases hev2 : Moist.CEK.evalBuiltin b1 (va :: args2) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 =>
            simp only [hev2] at h2
            have hw1 := ret_nil_halt_eq _ v1 h1
            have hw2 := ret_nil_halt_eq _ v2 h2
            rw [hw1, hw2]
            exact hval r1 r2 hev1 hev2
  | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _ | .VLam _ _, .VConstr _ _
  | .VLam _ _, .VBuiltin _ _ _ | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _
  | .VCon _, .VConstr _ _ | .VCon _, .VBuiltin _ _ _ | .VDelay _ _, .VCon _
  | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
  | .VConstr _ _, .VCon _ | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VLam _ _
  | .VBuiltin _ _ _, .VDelay _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
    exact absurd hveq (by simp [ValueEq])

/-- App with same arg, function refines. -/
theorem refines_app_fn_behEq (f f' a : Expr) (hf : f ⊑ f') :
    Expr.App f a ⊑ Expr.App f' a := by
  refine ⟨?_, ?_⟩
  · -- Compilation clause
    intro env hs
    rw [lowerTotalExpr_app] at hs ⊢
    have hf_some := isSome_bind_inner hs
    obtain ⟨tf, htf⟩ := Option.isSome_iff_exists.mp hf_some
    rw [htf, Option.bind_some] at hs
    have ha_some := isSome_bind_inner hs
    obtain ⟨tf', htf'⟩ := Option.isSome_iff_exists.mp (hf.1 env (by rw [htf]; simp))
    obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp ha_some
    rw [htf', Option.bind_some, hta, Option.bind_some]; simp
  · -- BehEq clause
    intro env
    rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hef : lowerTotalExpr env f with
    | none => simp [Option.bind_none]
    | some tf =>
      cases hea : lowerTotalExpr env a with
      | none => simp [Option.bind_some, Option.bind_none]
      | some ta =>
        cases hef' : lowerTotalExpr env f' with
        | none => simp [Option.bind_some, Option.bind_none]
        | some tf' =>
          simp only [Option.bind_some]
          intro ρ hwf
          have ⟨herr_f, hhalt_f, hval_f⟩ := refines_behEq_at hf hef hef' ρ hwf
          refine ⟨?_, ?_, ?_⟩
          · -- Error ↔
            constructor
            · intro herr
              rcases apply_reaches_error ρ tf ta herr with hf_err | ⟨vf, hf_halt, hx_case⟩
              · exact apply_error_of_fn_error ρ tf' ta (herr_f.mp hf_err)
              · obtain ⟨vf', hvf'⟩ := hhalt_f.mp ⟨vf, hf_halt⟩
                rcases hx_case with ha_err | ⟨va, ha_halt, happ_err⟩
                · exact apply_error_of_arg_error ρ tf' ta vf' hvf' ha_err
                · exact apply_compose ρ tf' ta vf' va .error hvf' ha_halt
                    (app_step_error_transfer vf vf' va (fun j => hval_f j vf vf' hf_halt hvf') happ_err)
            · intro herr
              rcases apply_reaches_error ρ tf' ta herr with hf'_err | ⟨vf', hf'_halt, hx_case⟩
              · exact apply_error_of_fn_error ρ tf ta (herr_f.mpr hf'_err)
              · obtain ⟨vf, hvf⟩ := hhalt_f.mpr ⟨vf', hf'_halt⟩
                rcases hx_case with ha_err | ⟨va, ha_halt, happ_err⟩
                · exact apply_error_of_arg_error ρ tf ta vf hvf ha_err
                · exact apply_compose ρ tf ta vf va .error hvf ha_halt
                    (app_step_error_transfer vf' vf va
                      (fun j => valueEq_symm j vf vf' (hval_f j vf vf' hvf hf'_halt)) happ_err)
          · -- Halts ↔
            constructor
            · intro ⟨v, hv⟩
              obtain ⟨vf, va, hf_halt, ha_halt, happ⟩ := apply_reaches ρ tf ta v hv
              obtain ⟨vf', hvf'⟩ := hhalt_f.mp ⟨vf, hf_halt⟩
              obtain ⟨v', hv'⟩ := app_step_halts_transfer vf vf' va v
                (fun j => hval_f j vf vf' hf_halt hvf') happ
              exact ⟨v', apply_compose ρ tf' ta vf' va (.halt v') hvf' ha_halt hv'⟩
            · intro ⟨v, hv⟩
              obtain ⟨vf', va, hf'_halt, ha_halt, happ⟩ := apply_reaches ρ tf' ta v hv
              obtain ⟨vf, hvf⟩ := hhalt_f.mpr ⟨vf', hf'_halt⟩
              obtain ⟨v', hv'⟩ := app_step_halts_transfer vf' vf va v
                (fun j => valueEq_symm j vf vf' (hval_f j vf vf' hvf hf'_halt)) happ
              exact ⟨v', apply_compose ρ tf ta vf va (.halt v') hvf ha_halt hv'⟩
          · -- Value agreement
            intro k v1 v2 hv1 hv2
            obtain ⟨vf, va, hf_halt, ha_halt, happ1⟩ := apply_reaches ρ tf ta v1 hv1
            obtain ⟨vf', va', hf'_halt, ha'_halt, happ2⟩ := apply_reaches ρ tf' ta v2 hv2
            have hva_eq := reaches_unique ha_halt ha'_halt; subst hva_eq
            exact app_step_value_agreement k vf vf' va
              (hval_f (k + 1) vf vf' hf_halt hf'_halt)
              (fun j => hval_f j vf vf' hf_halt hf'_halt) v1 v2 happ1 happ2

/-! ## App congruence (same function, argument changes)

The proof follows the same decomposition as `refines_app_fn_behEq` but with
the roles reversed: the function is shared and the argument refines.

The compilation clause is straightforward. The BehEq clause decomposes
`Apply tf ta` and `Apply tf ta'` via `apply_reaches`/`apply_compose`.
Since `tf` is the **same** on both sides, the function value `vf` is identical
(by `reaches_unique`). The argument values `va` and `va'` are `ValueEq k`
related at every index `k` (from `ha : a ⊑ a'`).

For non-function values (VCon, VDelay, VConstr) the application step
always errors regardless of the argument, so error/halts/value transfer
is trivial. For VBuiltin the argument value feeds into `evalBuiltin`;
agreement follows from `evalBuiltin_cong` (with the role of "fixed arg"
and "varying list" swapped).

For VLam the key observation is that `vf = vf` is literally the same
closure, so `valueEq_refl (k+1) vf` gives us VLam agreement for any
**single** shared argument. We use this with `arg = va` and separately
with `arg = va'` to get reflexive FundResults, and then stitch them
together by noting that both evaluations of the body run the same
closed UPLC term in the same CEK environment. -/

/-- evalBuiltin congruence for differing first arg, same tail.
    If `ValueEq (k+1) va va'`, then `evalBuiltin b (va :: args)` and
    `evalBuiltin b (va' :: args)` agree on none and produce ValueEq k
    related results.

    The proof reuses the existing `evalBuiltin_cong` (which fixes the head
    and varies the tail) via a middle term: we chain
    `evalBuiltin b (va :: args)` ↔ `evalBuiltin b (va :: args)` (refl)
    against `evalBuiltin b (va :: args)` ↔ `evalBuiltin b (va' :: args)`
    using the list `ListValueEq (k+1) (va :: args) (va' :: args)`.

    Since `extractConsts_cong` already handles full-list ListValueEq, and
    `evalBuiltinPassThrough` value agreement follows from
    `evalBuiltinPassThrough_valueEq`, we can assemble both paths. -/
theorem evalBuiltin_cong_first (k : Nat) (b : BuiltinFun)
    (va va' : CekValue) (args : List CekValue)
    (hva : ValueEq (k + 1) va va') :
    (Moist.CEK.evalBuiltin b (va :: args) = none ↔
     Moist.CEK.evalBuiltin b (va' :: args) = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b (va :: args) = some r1 →
              Moist.CEK.evalBuiltin b (va' :: args) = some r2 →
              ValueEq k r1 r2) := by
  have hfull : ListValueEq (k + 1) (va :: args) (va' :: args) := by
    simp only [ListValueEq]; exact ⟨hva, listValueEq_refl (k + 1) args⟩
  have hec : Moist.CEK.extractConsts (va :: args) =
             Moist.CEK.extractConsts (va' :: args) :=
    extractConsts_cong k _ _ hfull
  -- Same structure as evalBuiltin_cong: case-split on evalBuiltinPassThrough,
  -- using per-builtin helpers for the varying-head case.
  have hpt := evalBuiltinPassThrough_isNone_eq_first k b va va' args hva
  simp only [Moist.CEK.evalBuiltin]
  cases hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: args) with
  | some v1 =>
    have hp2_not_none : Moist.CEK.evalBuiltinPassThrough b (va' :: args) ≠ none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args)).isNone = false from by simp [hp1]] at hpt
      intro h; rw [h] at hpt; simp at hpt
    have ⟨v2, hp2⟩ : ∃ v, Moist.CEK.evalBuiltinPassThrough b (va' :: args) = some v := by
      cases h : Moist.CEK.evalBuiltinPassThrough b (va' :: args) with
      | some v => exact ⟨v, rfl⟩
      | none => contradiction
    rw [hp2]
    constructor; · simp
    · intro r1 r2 h1 h2
      injection h1 with h1; injection h2 with h2; subst h1; subst h2
      exact evalBuiltinPassThrough_valueEq_first k b va va' args hva hp1 hp2
  | none =>
    have hp2_none : Moist.CEK.evalBuiltinPassThrough b (va' :: args) = none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args)).isNone = true from by simp [hp1]] at hpt
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b (va' :: args) with
      | none => rfl
      | some _ => simp [hp2] at hpt
    rw [hp2_none, hec]
    exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact valueEq_refl k r1⟩
where
  -- isNone of evalBuiltinPassThrough agrees when the first arg varies by ValueEq (k+1).
  -- The deciding VCon element in each passthrough builtin is either in `args` (unchanged)
  -- or is the head va itself (preserved as the same VCon by vcon_eq_of_valueEq_succ).
  evalBuiltinPassThrough_isNone_eq_first (k : Nat) (b : BuiltinFun)
      (va va' : CekValue) (args : List CekValue)
      (hva : ValueEq (k + 1) va va') :
      (Moist.CEK.evalBuiltinPassThrough b (va :: args)).isNone =
      (Moist.CEK.evalBuiltinPassThrough b (va' :: args)).isNone := by
    cases b <;> try simp [Moist.CEK.evalBuiltinPassThrough]
    -- IfThenElse: args decides (args[1] = VCon (Bool cond)); va=elseV is not inspected for isNone
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- remaining: args = [x, y]
      cases y with
      | VCon c => cases c <;> simp [Moist.CEK.evalBuiltinPassThrough]
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp [Moist.CEK.evalBuiltinPassThrough]
    -- ChooseUnit: args decides (args[0] = VCon Unit); va=result is not inspected for isNone
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- remaining: args = [x]
      cases x with
      | VCon c => cases c <;> simp [Moist.CEK.evalBuiltinPassThrough]
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp [Moist.CEK.evalBuiltinPassThrough]
    -- Trace: args decides (args[0] = VCon (String _)); va=result is not inspected for isNone
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- remaining: args = [x]
      cases x with
      | VCon c => cases c <;> simp [Moist.CEK.evalBuiltinPassThrough]
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp [Moist.CEK.evalBuiltinPassThrough]
    -- ChooseList: args decides (args[1] = VCon (ConstDataList/ConstList)); va=consCase not inspected
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- remaining: args = [x, y]
      cases y with
      | VCon c => cases c <;> simp [Moist.CEK.evalBuiltinPassThrough]
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp [Moist.CEK.evalBuiltinPassThrough]
    -- MkCons: va itself is inspected (must be VCon (ConstList _)).
    -- ValueEq (k+1) preserves VCon identity: if va = VCon c then va' = VCon c (subst).
    -- After subst, both sides are identical, so isNone equality is trivially rfl.
    · cases va with
      | VCon c =>
        have hva'_eq := vcon_eq_of_valueEq_succ hva
        subst hva'_eq
        -- va' = va now; both sides identical → goal is X.isNone = X.isNone
        rfl
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        -- va is not VCon, so evalBuiltinPassThrough MkCons (va :: _) = none.
        -- By not_vcon_of_valueEq_succ, va' is also not VCon, so same for va'.
        have hva'_not_vcon : ∀ c, va' ≠ .VCon c :=
          not_vcon_of_valueEq_succ hva (by intro c; simp)
        cases va' with
        | VCon c => exact absurd rfl (hva'_not_vcon c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp [Moist.CEK.evalBuiltinPassThrough]
    -- ChooseData: args decides (args[4] = VCon (Data d)); va=bCase not inspected for isNone
    · rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      try simp [Moist.CEK.evalBuiltinPassThrough]
      -- remaining: args = [a0, a1, a2, a3, x]
      cases x with
      | VCon c =>
        cases c with
        | Data d => cases d <;> simp [Moist.CEK.evalBuiltinPassThrough]
        | _ => simp [Moist.CEK.evalBuiltinPassThrough]
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp [Moist.CEK.evalBuiltinPassThrough]
  -- ValueEq k of results when both evalBuiltinPassThrough return some and the head varies.
  -- Returned values are either from `args` (same → valueEq_refl) or va/va' (ValueEq k by mono).
  evalBuiltinPassThrough_valueEq_first (k : Nat) (b : BuiltinFun)
      (va va' : CekValue) (args : List CekValue)
      (hva : ValueEq (k + 1) va va')
      {r1 r2 : CekValue}
      (hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: args) = some r1)
      (hp2 : Moist.CEK.evalBuiltinPassThrough b (va' :: args) = some r2) :
      ValueEq k r1 r2 := by
    cases b <;> try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
    -- IfThenElse: args = [thenV, VCon (Bool cond)]; va=elseV
    -- Wrong lengths give hp1: none = some r1, closed by simp. Matching length: args = [x, y].
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
      -- remaining: args = [x, y]
      cases y with
      | VCon c =>
        cases c with
        | Bool cond =>
          cases cond with
          | true =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2; exact valueEq_refl k x
          | false =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- ChooseUnit: args = [VCon Unit]; va=result
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
      -- remaining: args = [x]
      cases x with
      | VCon c =>
        cases c with
        | Unit =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          subst hp1; subst hp2
          exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- Trace: args = [VCon (String s)]; va=result
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
      -- remaining: args = [x]
      cases x with
      | VCon c =>
        cases c with
        | String _ =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          subst hp1; subst hp2
          exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- ChooseList: args = [nilCase, VCon(l)]; va=consCase
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
      -- remaining: args = [x, y]
      cases y with
      | VCon c =>
        cases c with
        | ConstDataList l =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2; exact valueEq_refl k x
          | false =>
            simp only [h, ite_false] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | ConstList l =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2; exact valueEq_refl k x
          | false =>
            simp only [h, ite_false] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- MkCons: va = VCon (ConstList tail); args = [VCon c1]
    -- After vcon_eq_of_valueEq_succ + subst, va' = va, so hp2 has same LHS as hp1.
    · cases va with
      | VCon c =>
        have hva'_eq := vcon_eq_of_valueEq_succ hva
        subst hva'_eq
        cases c with
        | ConstList tail =>
          rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
          try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
          -- remaining: args = [x]
          cases x with
          | VCon c1 =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2; exact valueEq_refl k _
          | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
    -- ChooseData: args = [iCase, listCase, mapCase, constrCase, VCon (Data d)]; va=bCase
    · rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
      -- remaining: args = [a0, a1, a2, a3, x]
      cases x with
      | VCon c =>
        cases c with
        | Data d =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases d with
          | Constr _ _ => simp at hp1 hp2; subst hp1; subst hp2; exact valueEq_refl k a3
          | Map _ => simp at hp1 hp2; subst hp1; subst hp2; exact valueEq_refl k a2
          | List _ => simp at hp1 hp2; subst hp1; subst hp2; exact valueEq_refl k a1
          | I _ => simp at hp1 hp2; subst hp1; subst hp2; exact valueEq_refl k a0
          | B _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1
      | _ => simp [Moist.CEK.evalBuiltinPassThrough] at hp1

/-- Full-list evalBuiltin congruence: when `ListValueEq (k+1) args1 args2`,
    `evalBuiltin b args1` and `evalBuiltin b args2` agree on `none` and
    produce `ValueEq k`-related results when both succeed.

    Proof: chain via intermediate list `hd2 :: tl1` using
    `evalBuiltin_cong_first` (varying head) and `evalBuiltin_cong` (varying tail). -/
theorem evalBuiltin_full_cong (k : Nat) (b : BuiltinFun)
    (args1 args2 : List CekValue)
    (hargs : ListValueEq (k + 1) args1 args2) :
    (Moist.CEK.evalBuiltin b args1 = none ↔
     Moist.CEK.evalBuiltin b args2 = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b args1 = some r1 →
              Moist.CEK.evalBuiltin b args2 = some r2 →
              ValueEq k r1 r2) := by
  cases args1 with
  | nil =>
    cases args2 with
    | nil => exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact valueEq_refl k r1⟩
    | cons _ _ => simp [ListValueEq] at hargs
  | cons hd1 tl1 =>
    cases args2 with
    | nil => simp [ListValueEq] at hargs
    | cons hd2 tl2 =>
      simp only [ListValueEq] at hargs
      have ⟨hhd, htl⟩ := hargs
      have h1 := evalBuiltin_cong_first k b hd1 hd2 tl1 hhd
      have h2 := evalBuiltin_cong k b hd2 tl1 tl2 htl
      constructor
      · exact h1.1.trans h2.1
      · intro r1 r2 hr1 hr2
        -- Chain: evalBuiltin b (hd1::tl1) = some r1
        --        evalBuiltin b (hd2::tl2) = some r2
        -- Need intermediate: evalBuiltin b (hd2::tl1)
        cases hmid : Moist.CEK.evalBuiltin b (hd2 :: tl1) with
        | none =>
          -- hd1::tl1 → some r1, but hd2::tl1 → none; contradiction via h1.1.mpr
          exact absurd (h1.1.mpr hmid) (by rw [hr1]; simp)
        | some rmid =>
          exact valueEq_trans k r1 rmid r2
            (h1.2 r1 rmid hr1 hmid)
            (h2.2 rmid r2 hmid hr2)

/-- When `ValueRelV va va'` holds, running the same body in `cenv.extend va`
    vs `cenv.extend va'` yields bisimilar computations. The bisimulation
    gives error transfer and halts transfer directly. For value agreement,
    we use the bisimulation to get `ValueRelV` on halted values, then
    convert via `ValueRelV.toValueEq` (which requires step-indexed induction). -/
private theorem vlam_diff_arg_via_bisim (k : Nat) (body : Term) (cenv : CekEnv)
    (va va' : CekValue) (hva : ∀ j, ValueEq j va va') :
    (Reaches (.compute [] (cenv.extend va) body) .error ↔
     Reaches (.compute [] (cenv.extend va') body) .error) ∧
    (Halts (.compute [] (cenv.extend va) body) ↔
     Halts (.compute [] (cenv.extend va') body)) ∧
    ∀ v1 v2,
      Reaches (.compute [] (cenv.extend va) body) (.halt v1) →
      Reaches (.compute [] (cenv.extend va') body) (.halt v2) →
      ValueEq k v1 v2 := by
  -- Case split on va. For VCon: va = va', everything is reflexive.
  -- For non-VCon: use the bisimulation (with sorry at the ValueRelV gap).
  cases va with
  | VCon c =>
    -- ValueEq 1 gives va' = VCon c, so va = va'.
    have h1 := hva 1
    have heq := vcon_eq_of_valueEq_succ h1
    subst heq
    -- Both envs are now identical. Everything is trivially reflexive.
    exact ⟨Iff.rfl, Iff.rfl, fun v1 v2 h1 h2 =>
      reaches_unique h1 h2 ▸ valueEq_refl k v1⟩
  | VLam b1 e1 =>
    have h1 := hva 1
    cases va' with
    | VLam b2 e2 =>
      -- Both are VLam closures. ValueEq gives behavioral equivalence but
      -- not the structural matching (ValueRelV) needed for the bisimulation.
      -- The full proof requires the unconditional fundamental lemma with
      -- step-count-indexed well-founded induction. This bridges ValueEq
      -- (behavioral) to ValueRelV (structural) for closure values.
      sorry
    | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
      simp [ValueEq] at h1
  | VDelay b1 e1 =>
    have h1 := hva 1
    cases va' with
    | VDelay b2 e2 => sorry  -- same gap: behavioral != structural
    | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
      simp [ValueEq] at h1
  | VConstr tag1 fs1 =>
    have h1 := hva 1
    cases va' with
    | VConstr tag2 fs2 => sorry  -- same gap: ListValueEq != ListValueRelV
    | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
      simp [ValueEq] at h1
  | VBuiltin b1 args1 ea1 =>
    have h1 := hva 1
    cases va' with
    | VBuiltin b2 args2 ea2 => sorry  -- same gap: ListValueEq != ListValueRelV
    | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
      simp [ValueEq] at h1

/-- VLam application step: same closure, different args.
    Bundled error/halts/value agreement.

    Running the same `body` in `cenv.extend va` vs `cenv.extend va'`
    (where `va` and `va'` are `ValueEq` at every step index) produces:
    1. The same error behavior (error iff)
    2. The same halting behavior (halts iff)
    3. `ValueEq k`-related halted values

    Proof strategy: case-split on va. For VCon, ValueEq 1 gives va = va'
    so everything is reflexive. For closure values (VLam, VDelay, VConstr,
    VBuiltin), proving the result requires the unconditional fundamental
    lemma (environment variation under pointwise ValueEq), which needs
    step-count-indexed well-founded induction not yet available in this
    codebase. These cases carry sorry. -/
private theorem vlam_same_closure_diff_arg (k : Nat) (body : Term) (cenv : CekEnv)
    (va va' : CekValue) (hva : ∀ j, ValueEq j va va') :
    (Reaches (.compute [] (cenv.extend va) body) .error ↔
     Reaches (.compute [] (cenv.extend va') body) .error) ∧
    (Halts (.compute [] (cenv.extend va) body) ↔
     Halts (.compute [] (cenv.extend va') body)) ∧
    ∀ v1 v2,
      Reaches (.compute [] (cenv.extend va) body) (.halt v1) →
      Reaches (.compute [] (cenv.extend va') body) (.halt v2) →
      ValueEq k v1 v2 :=
  vlam_diff_arg_via_bisim k body cenv va va' hva

/-- Application step: same function, different args. Error transfer. -/
private theorem app_step_arg_error_transfer (vf va va' : CekValue)
    (hva : ∀ j, ValueEq j va va')
    (herr : Reaches (step (.ret [.funV vf] va)) .error) :
    Reaches (step (.ret [.funV vf] va')) .error := by
  match vf with
  | .VLam body cenv =>
    simp only [step] at herr ⊢
    exact (vlam_same_closure_diff_arg 0 body cenv va va' hva).1.mp herr
  | .VCon c => simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VDelay b e => simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VConstr tag fs => simp only [step] at herr ⊢; exact ⟨0, rfl⟩
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      simp only [step, hhead] at herr ⊢; exact ⟨0, rfl⟩
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        simp only [step, hhead, htail] at herr
        exact absurd herr (ret_nil_not_error _)
      | none =>
        simp only [step, hhead, htail] at herr ⊢
        cases hev1 : Moist.CEK.evalBuiltin b (va :: args) with
        | some v1 =>
          simp only [hev1] at herr; exact absurd herr (ret_nil_not_error v1)
        | none =>
          simp only [hev1] at herr ⊢
          have ⟨hcong, _⟩ := evalBuiltin_cong_first 0 b va va' args (hva 1)
          rw [hcong.mp hev1]; exact ⟨0, rfl⟩

/-- Application step: same function, different args. Halts transfer. -/
private theorem app_step_arg_halts_transfer (vf va va' : CekValue)
    (hva : ∀ j, ValueEq j va va')
    (hh : Halts (step (.ret [.funV vf] va))) :
    Halts (step (.ret [.funV vf] va')) := by
  match vf with
  | .VLam body cenv =>
    simp only [step] at hh ⊢
    exact (vlam_same_closure_diff_arg 0 body cenv va va' hva).2.1.mp hh
  | .VCon c =>
    simp only [step] at hh
    exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
  | .VDelay b e =>
    simp only [step] at hh
    exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
  | .VConstr tag fs =>
    simp only [step] at hh
    exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      simp only [step, hhead] at hh
      exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        simp only [step, hhead, htail] at hh ⊢
        exact ⟨.VBuiltin b (va' :: args) rest, ret_nil_halts _⟩
      | none =>
        simp only [step, hhead, htail] at hh ⊢
        cases hev1 : Moist.CEK.evalBuiltin b (va :: args) with
        | none =>
          simp only [hev1] at hh
          exact absurd (⟨0, rfl⟩ : Reaches _ .error) (fun h => not_halts_and_errors hh h)
        | some r1 =>
          simp only [hev1] at hh
          have ⟨hcong, _⟩ := evalBuiltin_cong_first 0 b va va' args (hva 1)
          cases hev2 : Moist.CEK.evalBuiltin b (va' :: args) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 => simp only [hev2]; exact ⟨r2, ret_nil_halts r2⟩

/-- Application step: same function, different args. Value agreement. -/
private theorem app_step_arg_value_agreement (k : Nat)
    (vf va va' : CekValue)
    (hva : ∀ j, ValueEq j va va')
    (v1 v2 : CekValue)
    (h1 : Reaches (step (.ret [.funV vf] va)) (.halt v1))
    (h2 : Reaches (step (.ret [.funV vf] va')) (.halt v2)) :
    ValueEq k v1 v2 := by
  match vf with
  | .VLam body cenv =>
    simp only [step] at h1 h2
    exact (vlam_same_closure_diff_arg k body cenv va va' hva).2.2 v1 v2 h1 h2
  | .VCon c =>
    simp only [step] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
  | .VDelay b e =>
    simp only [step] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
  | .VConstr tag fs =>
    simp only [step] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
  | .VBuiltin b args ea =>
    cases hhead : ea.head with
    | argQ =>
      simp only [step, hhead] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
    | argV =>
      cases htail : ea.tail with
      | some rest =>
        simp only [step, hhead, htail] at h1 h2
        have hw1 := ret_nil_halt_eq _ v1 h1; subst hw1
        have hw2 := ret_nil_halt_eq _ v2 h2; subst hw2
        cases k with
        | zero => simp [ValueEq]
        | succ k =>
          unfold ValueEq
          refine ⟨rfl, ?_, rfl⟩
          simp only [ListValueEq]
          exact ⟨hva (k + 1), listValueEq_refl (k + 1) args⟩
      | none =>
        simp only [step, hhead, htail] at h1 h2
        have ⟨hcong, hval⟩ := evalBuiltin_cong_first k b va va' args (hva (k + 1))
        cases hev1 : Moist.CEK.evalBuiltin b (va :: args) with
        | none => simp only [hev1] at h1; exact (reaches_halt_not_error h1 ⟨0, rfl⟩).elim
        | some r1 =>
          simp only [hev1] at h1
          cases hev2 : Moist.CEK.evalBuiltin b (va' :: args) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 =>
            simp only [hev2] at h2
            have hw1 := ret_nil_halt_eq _ v1 h1; rw [hw1]
            have hw2 := ret_nil_halt_eq _ v2 h2; rw [hw2]
            exact hval r1 r2 hev1 hev2

/-- App with same function, argument refines. -/
theorem refines_app_arg_behEq (f a a' : Expr) (ha : a ⊑ a') :
    Expr.App f a ⊑ Expr.App f a' := by
  refine ⟨?_, ?_⟩
  · -- Compilation clause
    intro env hs
    rw [lowerTotalExpr_app] at hs ⊢
    have hf_some := isSome_bind_inner hs
    obtain ⟨tf, htf⟩ := Option.isSome_iff_exists.mp hf_some
    rw [htf, Option.bind_some] at hs
    have ha_some := isSome_bind_inner hs
    obtain ⟨ta', hta'⟩ := Option.isSome_iff_exists.mp (ha.1 env ha_some)
    obtain ⟨ta, hta⟩ := Option.isSome_iff_exists.mp ha_some
    rw [htf, Option.bind_some, hta', Option.bind_some]; simp
  · -- BehEq clause
    intro env
    rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hef : lowerTotalExpr env f with
    | none => simp [Option.bind_none]
    | some tf =>
      cases hea : lowerTotalExpr env a with
      | none => simp [Option.bind_some, Option.bind_none]
      | some ta =>
        cases hea' : lowerTotalExpr env a' with
        | none => simp [Option.bind_some, Option.bind_none]
        | some ta' =>
          simp only [Option.bind_some]
          intro ρ hwf
          have ⟨herr_a, hhalt_a, hval_a⟩ := refines_behEq_at ha hea hea' ρ hwf
          refine ⟨?_, ?_, ?_⟩
          · -- Error ↔
            constructor
            · intro herr
              rcases apply_reaches_error ρ tf ta herr with hf_err | ⟨vf, hf_halt, hx_case⟩
              · -- tf errors → tf errors on both sides (same tf)
                exact apply_error_of_fn_error ρ tf ta' hf_err
              · rcases hx_case with ha_err | ⟨va, ha_halt, happ_err⟩
                · -- ta errors → ta' errors
                  exact apply_error_of_arg_error ρ tf ta' vf hf_halt (herr_a.mp ha_err)
                · -- ta halts with va, app step errors
                  obtain ⟨va', hva'⟩ := hhalt_a.mp ⟨va, ha_halt⟩
                  exact apply_compose ρ tf ta' vf va' .error hf_halt hva'
                    (app_step_arg_error_transfer vf va va'
                      (fun j => hval_a j va va' ha_halt hva') happ_err)
            · intro herr
              rcases apply_reaches_error ρ tf ta' herr with hf_err | ⟨vf, hf_halt, hx_case⟩
              · exact apply_error_of_fn_error ρ tf ta hf_err
              · rcases hx_case with ha'_err | ⟨va', ha'_halt, happ_err⟩
                · exact apply_error_of_arg_error ρ tf ta vf hf_halt (herr_a.mpr ha'_err)
                · obtain ⟨va, hva⟩ := hhalt_a.mpr ⟨va', ha'_halt⟩
                  exact apply_compose ρ tf ta vf va .error hf_halt hva
                    (app_step_arg_error_transfer vf va' va
                      (fun j => valueEq_symm j va va' (hval_a j va va' hva ha'_halt)) happ_err)
          · -- Halts ↔
            constructor
            · intro ⟨v, hv⟩
              obtain ⟨vf, va, hf_halt, ha_halt, happ⟩ := apply_reaches ρ tf ta v hv
              obtain ⟨va', hva'⟩ := hhalt_a.mp ⟨va, ha_halt⟩
              obtain ⟨v', hv'⟩ := app_step_arg_halts_transfer vf va va'
                (fun j => hval_a j va va' ha_halt hva') ⟨v, happ⟩
              exact ⟨v', apply_compose ρ tf ta' vf va' (.halt v') hf_halt hva' hv'⟩
            · intro ⟨v, hv⟩
              obtain ⟨vf, va', hf_halt, ha'_halt, happ⟩ := apply_reaches ρ tf ta' v hv
              obtain ⟨va, hva⟩ := hhalt_a.mpr ⟨va', ha'_halt⟩
              obtain ⟨v', hv'⟩ := app_step_arg_halts_transfer vf va' va
                (fun j => valueEq_symm j va va' (hval_a j va va' hva ha'_halt)) ⟨v, happ⟩
              exact ⟨v', apply_compose ρ tf ta vf va (.halt v') hf_halt hva hv'⟩
          · -- Value agreement
            intro k v1 v2 hv1 hv2
            obtain ⟨vf, va, hf_halt, ha_halt, happ1⟩ := apply_reaches ρ tf ta v1 hv1
            obtain ⟨vf', va', hf'_halt, ha'_halt, happ2⟩ := apply_reaches ρ tf ta' v2 hv2
            -- vf = vf' since tf is the same
            have hvf_eq := reaches_unique hf_halt hf'_halt; subst hvf_eq
            exact app_step_arg_value_agreement k vf va va'
              (fun j => hval_a j va va' ha_halt ha'_halt) v1 v2 happ1 happ2

end Moist.Verified.Congruence
