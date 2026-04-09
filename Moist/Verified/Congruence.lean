import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.MIR.LowerTotal
import Moist.Verified.ValueEqMono
import Moist.Verified.BuiltinCong
import Moist.Verified.ValueEq

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
open Moist.Verified.BuiltinCong (not_halts_and_errors
  vcon_eq_of_valueEq_succ evalBuiltin_cong
  evalBuiltin_cong_first evalBuiltin_full_cong ret_nil_halts
  ret_nil_not_error ret_nil_halt_eq apply_error_of_fn_error
  apply_error_of_arg_error)

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
theorem refines_behEq_at {e e' : Expr} {env : List VarId} {t t' : Term}
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
theorem isSome_bind_inner {α β : Type} {o : Option α} {f : α → Option β}
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
          -- Goal: the VDelay clause for `(compute stk1 ρ t)` vs
          -- `(compute stk2 ρ t')` at bound `j`, where `t, t'` are lowerings
          -- of `e, e'` and `h : e ⊑ e'`.
          --
          -- Proof strategy (to be implemented): decompose each stacked
          -- computation via `liftState stk (compute [] ρ t)` and the
          -- `steps_liftState` / `firstInactive` machinery from
          -- `StepLift.lean`. Use `refines_behEq_at h he he' ρ hwf` to get
          -- empty-stack behavioral equivalence, then bridge via
          -- `stateEq_stateRelated` applied to the `StateEq.ret` constructor
          -- (using `hstk` for the stack relation and the refines-derived
          -- `∀ k, ValueEq k ve1 ve2` for the halt-value relation).
          sorry

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
          -- Goal: the VLam clause for `(compute stk1 (ρ.extend arg1) t)` vs
          -- `(compute stk2 (ρ.extend arg2) t')` at bound `j`, where `t, t'`
          -- are lowerings of `body, body'` and `h : body ⊑ body'`.
          --
          -- Proof strategy (to be implemented): same as `refines_delay_behEq`
          -- but with extended environments. Use `refines_behEq_at` at the
          -- extended environment `ρ.extend arg1` / `ρ.extend arg2` (which
          -- requires checking `WellSizedEnv` on the extension), then bridge
          -- via `liftState` + `stateEq_stateRelated` on the `StateEq.ret`
          -- state with `hargs` threaded through.
          sorry

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
      -- hclause.1 : (∃ n ≤ N, error s1) ↔ (∃ m ≤ N, error s2)
      obtain ⟨m, _, herr2⟩ := hclause.1.mp ⟨N, Nat.le_refl N, hcomp⟩
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
            have hcong_none :=
              (evalBuiltin_full_cong 0 b (fun v => valueEq_refl 1 v)
                (valueEq_trans 0) a1 a2 hargs_lve).1
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
      -- hclause.2.1 : (∃ n v, n ≤ N ∧ halt v on s1) ↔ (∃ m v, m ≤ N ∧ halt v on s2)
      obtain ⟨m, w2, _, hw2⟩ := hclause.2.1.mp ⟨N, w, Nat.le_refl N, hcomp⟩
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
              have hcong_none :=
                (evalBuiltin_full_cong 0 b (fun v => valueEq_refl 1 v)
                  (valueEq_trans 0) a1 a2 hargs_lve).1
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
                -- Use hval_sub at level `k + max N1 N2 + 1` so the VDelay clause
                -- unfolds at `j = k + max N1 N2 ≥ max N1 N2` and the value clause
                -- at (N1, N2) yields `ValueEq (j - max N1 N2) w1 w2 = ValueEq k w1 w2`.
                have hveN := hval_sub (k + max N1 N2 + 1) _ _ hte_halt hte'_halt
                unfold ValueEq at hveN
                have hN1_le_j : N1 ≤ k + max N1 N2 :=
                  Nat.le_trans (Nat.le_max_left N1 N2) (Nat.le_add_left _ k)
                have hN2_le_j : N2 ≤ k + max N1 N2 :=
                  Nat.le_trans (Nat.le_max_right N1 N2) (Nat.le_add_left _ k)
                have ⟨_, _, hveclause⟩ :=
                  hveN (k + max N1 N2) (Nat.le_refl _) [] [] (by trivial : StackEqR _ [] [])
                have hresult :=
                  hveclause N1 N2 hN1_le_j hN2_le_j w1 w2 hcomp1 hcomp2
                -- hresult : ValueEq ((k + max N1 N2) - max N1 N2) w1 w2
                have hlvl : k + max N1 N2 - max N1 N2 = k := by omega
                rw [hlvl] at hresult
                exact hresult
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
                        exact (evalBuiltin_full_cong k b
                          (fun v => valueEq_refl (k + 1) v)
                          (valueEq_trans k) a1 a2 hargs).2 _ _ hev1 hev2
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
    -- VLam clause: ∀ i ≤ N, ∀ arg1 arg2, ValueEq i arg1 arg2 → ∀ stk, ... →
    --   (err iff) ∧ (halt iff) ∧ (value relate)
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨m, _, herr2⟩ := hclause.1.mp ⟨N, Nat.le_refl N, hN⟩
    exact ⟨m, herr2⟩
  · intro ⟨N, hN⟩
    have hveN := hve (N + 1)
    unfold ValueEq at hveN
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨m, _, herr1⟩ := hclause.1.mpr ⟨N, Nat.le_refl N, hN⟩
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
    obtain ⟨m, w2, _, hw2⟩ := hclause.2.1.mp ⟨N, w, Nat.le_refl N, hN⟩
    exact ⟨w2, m, hw2⟩
  · intro ⟨w, N, hN⟩
    have hveN := hve (N + 1)
    unfold ValueEq at hveN
    have hclause := hveN N (Nat.le_refl N) va va (valueEq_refl N va) [] [] trivial
    obtain ⟨m, w1, _, hw1⟩ := hclause.2.1.mpr ⟨N, w, Nat.le_refl N, hN⟩
    exact ⟨w1, m, hw1⟩

/-- VLam application: value agreement. Extract N1, N2 from the halt witnesses,
    use `hve` at level `k + max N1 N2 + 1` so the VLam clause unfolds at
    level `j = k + max N1 N2`. The value clause at step counts (N1, N2) then
    yields `ValueEq (j - max N1 N2) v1 v2 = ValueEq k v1 v2`. -/
private theorem app_step_vlam_value (k : Nat) (b1 b2 : Term) (e1 e2 : CekEnv)
    (va : CekValue) (hve : ∀ j, ValueEq j (.VLam b1 e1) (.VLam b2 e2))
    (v1 v2 : CekValue)
    (h1 : Reaches (.compute [] (e1.extend va) b1) (.halt v1))
    (h2 : Reaches (.compute [] (e2.extend va) b2) (.halt v2)) :
    ValueEq k v1 v2 := by
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  have hveN := hve (k + max N1 N2 + 1)
  unfold ValueEq at hveN
  have hN1_le : N1 ≤ k + max N1 N2 :=
    Nat.le_trans (Nat.le_max_left N1 N2) (Nat.le_add_left _ k)
  have hN2_le : N2 ≤ k + max N1 N2 :=
    Nat.le_trans (Nat.le_max_right N1 N2) (Nat.le_add_left _ k)
  have ⟨_, _, hval⟩ :=
    hveN (k + max N1 N2) (Nat.le_refl _) va va
      (valueEq_refl (k + max N1 N2) va) [] [] (by trivial : StackEqR _ [] [])
  have hresult := hval N1 N2 hN1_le hN2_le v1 v2 hN1 hN2
  have hlvl : k + max N1 N2 - max N1 N2 = k := by omega
  rw [hlvl] at hresult
  exact hresult

/-- Non-function values: application always errors. -/
private theorem app_step_nonfunction_errors (va : CekValue) (c : Const) :
    Reaches (step (.ret [.funV (.VCon c)] va)) .error := ⟨0, rfl⟩

private theorem app_step_delay_errors (va : CekValue) (b : Term) (e : CekEnv) :
    Reaches (step (.ret [.funV (.VDelay b e)] va)) .error := ⟨0, rfl⟩

private theorem app_step_constr_errors (va : CekValue) (tag : Nat) (fs : List CekValue) :
    Reaches (step (.ret [.funV (.VConstr tag fs)] va)) .error := ⟨0, rfl⟩


/-! ## App congruence: same argument, function changes -/

open Moist.Verified.StepLift (apply_reaches apply_reaches_error apply_compose)


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
        have ⟨hcong, _⟩ := evalBuiltin_cong 0 b1 (fun v => valueEq_refl 1 v)
          va args1 args2 hargs1
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
        have ⟨hcong, _⟩ := evalBuiltin_cong 0 b1 (fun v => valueEq_refl 1 v)
          va args1 args2 hargs1
        cases hev1 : Moist.CEK.evalBuiltin b1 (va :: args1) with
        | none =>
          simp only [hev1] at hh
          exact (reaches_halt_not_error hh ⟨0, rfl⟩).elim
        | some r1 =>
          simp only [hev1] at hh
          cases hev2 : Moist.CEK.evalBuiltin b1 (va :: args2) with
          | none => exact absurd (hcong.mpr hev2) (by simp [hev1])
          | some r2 => simp only; exact ⟨r2, ret_nil_halts r2⟩
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
        have ⟨hcong, hval⟩ := evalBuiltin_cong k b1
          (fun v => valueEq_refl (k + 1) v) va args1 args2 hargs_k1
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
      | none => simp [Option.bind_none]
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

end Moist.Verified.Congruence
