import Moist.Verified.MIR
import Moist.Verified.MIR.Congruence
import Moist.Verified.MIR.Primitives.Iterated
import Moist.Verified.DCESoundness
import Moist.Verified.DeadLet
import Moist.MIR.Canonicalize
import Moist.MIR.Optimize.Inline

/-! # Soundness of MIR Inlining Pass

Proves `inline_soundness : MIRCtxRefines e (inlinePass e s).1.1` for every
MIR expression `e` and every fresh-variable state `s`.

## Overview

The inlining pass walks the AST bottom-up and performs:

1. **Recursive descent** into sub-expressions (IH cases).
2. **Let-binding inlining** via `inlineLetBindings`: for each
   `let v = rhs in body`, decides to substitute the RHS into the body
   (and remaining RHS's) per `shouldInline`.
3. **Beta reduction** via `betaReduce`: applies
   `(.App (.Lam x body) arg) → subst x arg body` when `arg.isAtom`.

## Proof Strategy

* **Structural / congruence cases** (`Var`, `Lit`, `Builtin`, `Error`, `Lam`,
  `Fix`, `Force`, `Delay`, `Constr`, `Case`): compose through the matching
  `mirCtxRefines_*` congruence lemma from `Verified/MIR/Congruence.lean` and
  `Verified/DCESoundness.lean`.
* **App case**: `mirCtxRefines_app` + `betaReduce_soundness` helper.
* **Let case**: `mirCtxRefines_let_binds_congr` + `mirCtxRefines_let_body`
  + `inlineLetBindings_soundness` helper.

## Substitution-Based Sub-Theorem (Single Sorry Point)

Both `betaReduce_soundness` (Lam+atom case) and `inlineLetBindings_soundness`
(inline branches) are now fully proved *modulo* a single shared core lemma:

  `substInBindings_body_inline_mirCtxRefines` — the substitution-inline
  preservation fact that `MIRCtxRefines` holds from `.Let ((v,rhs,er) :: rest) body`
  to the post-substitution form produced by `inlineLetGo` (body substituted
  plus `substInBindings` over the remaining bindings).

This single remaining `sorry` admits the substitution-preservation fact.
Proving it requires:
 * UPLC-level substitution preservation (~1000+ lines), OR
 * MIR-level alpha-equivalence preservation for `subst` + `canonicalize`
   bridge (~3000+ lines), OR
 * Direct semantic argument via stack-discipline inversion (DeadLet style).

All the structural scaffolding around the inline pass — the decision loop
`inlineLetGo` walk, the beta-reduction structure, the `.App (.Lam _) _`
to `.Let [_] _` UPLC-level equivalence, the accumulator generalization,
and the composition through `mirCtxRefines_let_body` / `mirCtxRefines_trans`
— is fully proven. -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId inlinePass inlinePassList inlineBindings
   inlineLetBindings inlineLetGo betaReduce substInBindings
   shouldInline countOccurrences occursUnderFix
   lowerTotalExpr lowerTotal freeVars subst substList)
open Moist.Verified.Contextual
  (Context fill ObsRefines CtxRefines
   ctxRefines_refl ctxRefines_trans)
open Moist.Verified.Equivalence (ListRel)

--------------------------------------------------------------------------------
-- 1. Definitional unfolding equations for `inlinePass` (on the `.1.1` projection)
--
-- The mutual `inlinePass` definition uses a catch-all for leaf cases
-- (Var/Lit/Builtin/Error), which can't be unfolded with `simp only
-- [inlinePass.eq_N]` directly — we use the catch-all `eq_9` with
-- proofs that the input is not a composite form.
--------------------------------------------------------------------------------

/-- Catch-all unfolding: for a leaf expression `e` (not Let/Lam/Fix/App/
    Force/Delay/Constr/Case), `inlinePass e s = ((e, false), s)`. -/
private theorem inlinePass_leaf {e : Expr}
    (hlet : ∀ bs b, e ≠ .Let bs b)
    (hlam : ∀ x b, e ≠ .Lam x b)
    (hfix : ∀ f b, e ≠ .Fix f b)
    (happ : ∀ f x, e ≠ .App f x)
    (hforce : ∀ inner, e ≠ .Force inner)
    (hdelay : ∀ inner, e ≠ .Delay inner)
    (hconstr : ∀ t args, e ≠ .Constr t args)
    (hcase : ∀ sc alts, e ≠ .Case sc alts)
    (s : Moist.MIR.FreshState) :
    inlinePass e s = ((e, false), s) := by
  rw [Moist.MIR.inlinePass.eq_9 e
        (fun bs b heq => hlet bs b heq)
        (fun x b heq => hlam x b heq)
        (fun f b heq => hfix f b heq)
        (fun f x heq => happ f x heq)
        (fun inner heq => hforce inner heq)
        (fun inner heq => hdelay inner heq)
        (fun t args heq => hconstr t args heq)
        (fun sc alts heq => hcase sc alts heq)]
  rfl

private theorem inlinePass_var_eq (v : VarId) (s : Moist.MIR.FreshState) :
    inlinePass (.Var v) s = ((.Var v, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

private theorem inlinePass_lit_eq (c) (s : Moist.MIR.FreshState) :
    inlinePass (.Lit c) s = ((.Lit c, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

private theorem inlinePass_builtin_eq (b) (s : Moist.MIR.FreshState) :
    inlinePass (.Builtin b) s = ((.Builtin b, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

private theorem inlinePass_error_eq (s : Moist.MIR.FreshState) :
    inlinePass .Error s = ((.Error, false), s) :=
  inlinePass_leaf
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h)
    (by intros; intro h; cases h) (by intros; intro h; cases h) s

/-- Simplified projection: for a leaf expression, the result is unchanged. -/
private theorem inlinePass_var (v : VarId) (s : Moist.MIR.FreshState) :
    (inlinePass (.Var v) s).1.1 = .Var v := by
  rw [inlinePass_var_eq]

private theorem inlinePass_lit (c) (s : Moist.MIR.FreshState) :
    (inlinePass (.Lit c) s).1.1 = .Lit c := by
  rw [inlinePass_lit_eq]

private theorem inlinePass_builtin (b) (s : Moist.MIR.FreshState) :
    (inlinePass (.Builtin b) s).1.1 = .Builtin b := by
  rw [inlinePass_builtin_eq]

private theorem inlinePass_error (s : Moist.MIR.FreshState) :
    (inlinePass .Error s).1.1 = .Error := by
  rw [inlinePass_error_eq]

private theorem inlinePass_lam (x : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Lam x body) s).1.1 = .Lam x (inlinePass body s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_2]
  rfl

private theorem inlinePass_fix (f : VarId) (body : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Fix f body) s).1.1 = .Fix f (inlinePass body s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_3]
  rfl

private theorem inlinePass_force (e : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Force e) s).1.1 = .Force (inlinePass e s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_5]
  rfl

private theorem inlinePass_delay (e : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.Delay e) s).1.1 = .Delay (inlinePass e s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_6]
  rfl

private theorem inlinePass_constr (tag : Nat) (args : List Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePass (.Constr tag args) s).1.1 = .Constr tag (inlinePassList args s).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_7]
  rfl

private theorem inlinePass_case (scrut : Expr) (alts : List Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePass (.Case scrut alts) s).1.1 =
      .Case (inlinePass scrut s).1.1
            (inlinePassList alts (inlinePass scrut s).2).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_8]
  rfl

private theorem inlinePass_app (f x : Expr) (s : Moist.MIR.FreshState) :
    (inlinePass (.App f x) s).1.1 =
      (betaReduce (inlinePass f s).1.1
        (inlinePass x (inlinePass f s).2).1.1
        (inlinePass x (inlinePass f s).2).2).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_4]
  rfl

private theorem inlinePass_let (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePass (.Let binds body) s).1.1 =
      (inlineLetBindings (inlineBindings binds s).1.1
        (inlinePass body (inlineBindings binds s).2).1.1
        (inlinePass body (inlineBindings binds s).2).2).1.1 := by
  simp only [Moist.MIR.inlinePass.eq_1]
  rfl

-- inlinePassList unfolding

private theorem inlinePassList_nil (s : Moist.MIR.FreshState) :
    (inlinePassList ([] : List Expr) s).1.1 = [] := by
  rw [Moist.MIR.inlinePassList.eq_1]; rfl

private theorem inlinePassList_cons_eq (e : Expr) (rest : List Expr)
    (s : Moist.MIR.FreshState) :
    (inlinePassList (e :: rest) s).1.1 =
      (inlinePass e s).1.1 ::
        (inlinePassList rest (inlinePass e s).2).1.1 := by
  simp only [Moist.MIR.inlinePassList.eq_2]
  rfl

-- inlineBindings unfolding

private theorem inlineBindings_nil (s : Moist.MIR.FreshState) :
    (inlineBindings ([] : List (VarId × Expr × Bool)) s).1.1 = [] := by
  rw [Moist.MIR.inlineBindings.eq_1]; rfl

private theorem inlineBindings_cons_eq (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (s : Moist.MIR.FreshState) :
    (inlineBindings ((v, rhs, er) :: rest) s).1.1 =
      (v, (inlinePass rhs s).1.1, er) ::
        (inlineBindings rest (inlinePass rhs s).2).1.1 := by
  simp only [Moist.MIR.inlineBindings.eq_2]
  rfl

--------------------------------------------------------------------------------
-- 1b. Utility: MIRCtxRefines from universal lowerTotalExpr equality
--------------------------------------------------------------------------------

/-- If two MIR expressions have the same lowering in every environment,
    they are `MIRCtxRefines`-equivalent (both directions). -/
private theorem mirCtxRefines_of_lowerEq {m₁ m₂ : Expr}
    (h : ∀ env, lowerTotalExpr env m₁ = lowerTotalExpr env m₂) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  rw [h env]
  refine ⟨id, ?_⟩
  cases hlow : lowerTotalExpr env m₂ with
  | none => trivial
  | some t => exact ctxRefines_refl t

--------------------------------------------------------------------------------
-- 2. Shared substitution-inline sub-theorem (`sorry`)
--
-- Both `betaReduce_soundness` (Lam+atom case) and
-- `inlineLetBindings_soundness` (inline branches) reduce to the same
-- core fact: substituting a single `let v = rhs in body` binding
-- contextually refines the let form.
--
-- ## Scope Assessment (2026-04-17)
--
-- This is the single remaining deep substitution-preservation fact in
-- the inlining soundness chain. Closing it requires building, essentially
-- from scratch, one of three alternative infrastructures. All three are
-- very substantial engineering efforts, summarized below with realistic
-- line-count estimates based on prior investigations recorded in
-- `~/.claude/agent-memory/lean4-theorem-prover/`.
--
-- ### Option A: Alpha-equivalence bridge (recommended approach)
--
-- This is the cleanest approach if a full Lean4 MIR semantics including
-- alpha-equivalence is desired.
--
-- Phase 1 — `AlphaEq.lean` (MIR-level alpha-equivalence) infrastructure:
--   * `AlphaEq` inductive relation parameterized by dual env's.
--   * `alphaEq_lowerTotal_eq`: alpha-equivalent expressions have equal
--     lowerings under corresponding envs. ~500 lines.
--   * `env_raise` / `env_raise_prefix`: lifting AlphaEq under fresh
--     prefix additions. ~300 lines.
--   * `fresh_rename_alphaEq`: `AlphaEq [a] [b] (rename x a e) (rename x b e)`
--     for fresh `a`, `b`. ~400 lines.
--   * `rename_cross_alphaEq_gen`: prefix-generalized cross-rename. ~1500 lines.
--   * `alphaEq_cons_no_capture`: diagonal extend with "not-free or
--     shadowed" disjunctive hypothesis. ~500 lines.
--   * `subst_not_free_alphaEq_refl`: if `v` not free in `e`, then
--     `e` alpha-equivalent to `subst v R e`. ~2500 lines (non-Let
--     cases ~650, Let case ~1500, mutual binds+let). This in turn needs
--     ~300 lines for `subst_preserves_maxUid` and related bounds.
--   * `subst_preserves_alphaEq`: the alpha-congruence of subst —
--     subst is AlphaEq-preserving when env's are noShadow and v is
--     disjoint from env uids. ~2500-3300 lines; Lam case ~530, Fix
--     case ~515, Let case ~500, main mutual scaffold + helpers ~1000.
--   Subtotal for Phase 1: **7,500-9,000 lines**.
--
-- Phase 2 — `expandFix_subst_comm` (lowerTotal-wrapped commutation):
--   Statement: `lowerTotal env (expandFix (subst v rhs body).1) =
--              lowerTotal env (subst v (expandFix rhs) (expandFix body)).1`
--   under freshness + noShadow preconditions.
--   * Main theorem: ~2500-3000 lines covering 13 constructors * 3-4
--     sub-cases each. Fix-Lam Z-combinator case is the hardest
--     (~800 lines alone).
--   * Infrastructure: `noShadowExprProp_expandFix`, `maxUidExpr_expandFix_le`.
--     ~350 lines.
--   * Phase 2 subtotal: **2,850-3,350 lines**.
--
-- Phase 3 — Application (this file):
--   * `subst_lower_commutes`: ~60 lines (direct use of `expandFix_subst_comm`
--     and `lowerTotal_subst_fixfree`).
--   * `lowerTotal_subst_fixfree`: ~200 lines (UPLC-level substitution
--     commutation for Fix-free expressions). Requires intrinsic de Bruijn
--     manipulation infrastructure.
--   * `value_inline_mirCtxRefines`: value case composes
--     `subst_lower_commutes` with the classical UPLC `beta_value` rule
--     (`Apply (Lam 0 body') val ⊑ substTerm 1 val body'`). ~80 lines
--     once the helpers exist. The UPLC beta_value rule itself is
--     standard (~150 lines for `uplc_beta_value_ctxRefines`).
--   * `impure_inline_mirCtxRefines`: requires the MUCH harder
--     `cek_beta_single_strict_openRefines` — UPLC-level single-occurrence,
--     strict-position beta reduction — which involves MIR-analysis→CEK
--     evaluation-order lifting. Estimated ~1,000+ lines of step-indexed
--     logical-relation work to bridge MIR's `countOccurrences` and
--     `occursInDeferred` to CEK's evaluation order.
--   * `substInBindings_body_inline_mirCtxRefines` itself, chaining the
--     above through `substLet_vs_separate` (capture-avoidance bridge
--     between `substLet` and `substInBindings+subst`): ~500-1000 lines.
--     The capture-avoidance bridge is itself non-trivial because
--     `substLet` does `rhs' ← subst rhs` THEN recurses with state
--     threading, while `substInBindings + subst body` does the two
--     halves separately with different state threading.
--   * Phase 3 subtotal: **2,000-3,000 lines**.
--
-- **Option A grand total**: **12,000-15,000 lines** of verified Lean.
--
-- ### Option B: Direct UPLC-level substitution preservation
--
-- Skip MIR-level alpha-equivalence; work directly on UPLC de Bruijn
-- substitution. This requires proving, via a step-indexed logical
-- relation or observational equivalence, that:
--   `CtxRefines (Apply (Lam 0 body') rhs') (substTerm 1 rhs' body')`
-- when appropriate conditions hold. The `value` case is standard
-- (~500 lines). The impure `single-occurrence strict-position` case
-- involves a MIR-to-UPLC evaluation-order bridge that is ~2,000+ lines.
-- MIR-to-UPLC substitution commutation (`subst_lower_commutes`) is
-- *still* needed. Option B saves the alpha-equivalence infrastructure
-- (~7000-9000 lines) but replaces it with (a) the UPLC-level step-indexed
-- refinement (~2000+ lines) and (b) the de Bruijn substitution
-- commutation (~2000+ lines) and (c) the evaluation-order lift
-- (~1000+ lines). Net savings: ~2000-4000 lines, but the step-indexed
-- work is generally harder than alpha-equivalence infrastructure.
-- **Option B total**: **9,000-12,000 lines**.
--
-- ### Option C: Direct semantic argument via CEK stack-discipline inversion
--
-- Similar to `DeadLet` — prove the refinement directly by constructing
-- a simulation between the two evaluation traces. For each `let` form,
-- a single beta-reduction step in the CEK machine produces the
-- substituted form; show this step is "invisible" to any observer.
-- Problems: (i) the beta step in CEK requires a *value* as argument,
-- which is exactly the hypothesis we're trying to avoid
-- (`shouldInline`'s impure branch); (ii) the simulation must account
-- for MIR→UPLC→CEK translation layers, which makes the bookkeeping
-- substantially more complex than `DeadLet`.
-- **Option C total**: **6,000-10,000 lines**, with higher risk of
-- unforeseen complications.
--
-- ## Current Action (2026-04-17)
--
-- The 3000-line budget for this single task is insufficient for any
-- of the three options by a factor of 3-5x. The entire `Verified/` tree
-- (AlphaRenameSoundness + DCESoundness + DeadLet + Congruence combined)
-- is only ~3100 lines, so this single theorem would dominate the
-- Verified tree by itself.
--
-- The theorem is left as `sorry` with this detailed documentation.
-- Progress on this theorem should be scheduled as a multi-session,
-- multi-phase effort using the Option A decomposition above:
--
--   Session 1 (Phase 1a): AlphaEq relation + `alphaEq_lowerTotal_eq`
--                         + env_raise + fresh_rename_alphaEq. ~1800 lines.
--   Session 2 (Phase 1b): rename_cross_alphaEq_gen + helpers. ~1500 lines.
--   Session 3 (Phase 1c): subst_not_free_alphaEq_refl. ~2500 lines.
--   Session 4 (Phase 1d): subst_preserves_alphaEq. ~2500 lines.
--   Session 5 (Phase 2): expandFix_subst_comm + noShadowExpr_expandFix
--                        + maxUidExpr_expandFix_le. ~2800 lines.
--   Session 6 (Phase 3): substInBindings_body_inline_mirCtxRefines
--                        + value_inline + impure_inline + callers.
--                        ~2500 lines.
--
-- Per the memory notes, even Session 4 alone (`subst_preserves_alphaEq`
-- standalone) was previously scoped as 2500-3300 lines (at or over
-- budget) — so this is legitimately a 6+ session effort.
--------------------------------------------------------------------------------

/-- Core substitution-inline sub-theorem (unified form). For every
    `let ((v, rhs, er) :: rest) in body`, the split-substitution form
    that `inlineLetGo` produces (substituting `rhs` into `body` directly
    and into each `rest` RHS via `substInBindings`) is contextually
    refined by the let form.

    This is the direction used by the inlining pass: the original let is
    refined by its substituted form. Under call-by-value, this is sound
    exactly when `shouldInline` returns true (atomic / small value / pure
    single use) — the `inlineLetGo` loop applies `shouldInline` as a
    gating predicate to ensure this condition holds, but at the level of
    `MIRCtxRefines` (which is halt- and error-preservation, one-
    directional), the inlining direction is always sound regardless of
    the gating. This is the direction the theorem captures.

    The special case with `rest = []` handles the beta-reduction sorry
    in `betaReduce_soundness`: when `rest = []`, `substInBindings v rhs []`
    returns `([], rfl)` and the let reduces to just the body substitution.

    **Status**: admitted (`sorry`). See the section 2 header above for
    the full scope analysis. A brief summary:

    * The proof needs either (Option A) MIR-level AlphaEq infrastructure
      or (Option B) UPLC-level logical-relation substitution preservation
      or (Option C) a direct CEK simulation argument.
    * Minimum viable scope: **6,000 lines** (Option C with the strictest
      prerequisites); realistic scope: **12,000-15,000 lines** for the
      cleanest/recommended Option A.
    * This proof belongs in a dedicated series of follow-up sessions;
      a single 3,000-line budget is insufficient by a factor of 3-5x.
    * Memory notes `feedback_subst_preserves_alphaEq_scope_2500budget.md`
      and `feedback_expandFix_subst_comm_post_subst_preserves.md` record
      the per-phase line-count investigations. -/
theorem substInBindings_body_inline_mirCtxRefines (v : VarId) (rhs body : Expr)
    (er : Bool) (rest : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) :
    MIRCtxRefines
      (.Let ((v, rhs, er) :: rest) body)
      (.Let (Moist.MIR.substInBindings v rhs rest
              (Moist.MIR.subst v rhs body s).2).1.val
            (Moist.MIR.subst v rhs body s).1) := by
  sorry

/-- Specialization: when `rest = []`, the inline form reduces to just
    the body substitution. -/
private theorem subst_body_inline_mirCtxRefines (v : VarId) (rhs body : Expr)
    (er : Bool) (s : Moist.MIR.FreshState) :
    MIRCtxRefines (.Let [(v, rhs, er)] body) (Moist.MIR.subst v rhs body s).1 := by
  have h := substInBindings_body_inline_mirCtxRefines v rhs body er [] s
  -- substInBindings v rhs [] = pure ⟨[], rfl⟩, so the result is .Let [] body'
  -- where body' = (subst v rhs body s).1. This is MIRCtxRefines to body' via
  -- mirCtxRefines_let_nil.
  have heq : (Moist.MIR.substInBindings v rhs []
              (Moist.MIR.subst v rhs body s).2).1.val = ([] : List (VarId × Expr × Bool)) := by
    -- substInBindings v rhs [] s = pure ⟨[], rfl⟩
    show (Moist.MIR.substInBindings v rhs [] _).1.val = _
    rfl
  rw [heq] at h
  -- h : MIRCtxRefines (.Let [(v, rhs, er)] body) (.Let [] (subst v rhs body s).1)
  exact mirCtxRefines_trans h mirCtxRefines_let_nil

/-- Equivalence between `.App (.Lam p body) x` and `.Let [(p, x, false)] body`
    at the `MIRCtxRefines` level: they have *identical* lowerings (both
    reduce to `.Apply (.Lam 0 body_lowered) x_lowered`), modulo the order
    of bindings in the `do`-notation. -/
private theorem mirCtxRefines_app_lam_to_let (p : VarId) (body x : Expr) :
    MIRCtxRefines (.App (.Lam p body) x) (.Let [(p, x, false)] body) := by
  intro env
  have heq : lowerTotalExpr env (.App (.Lam p body) x) =
             lowerTotalExpr env (.Let [(p, x, false)] body) := by
    -- Both sides expand to the same UPLC term via expandFix + lowerTotal,
    -- but the do-bindings have different orders; unfold fully and case-split.
    simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
      Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
    cases h_body : Moist.MIR.lowerTotal (p :: env) (Moist.MIR.expandFix body) with
    | none => simp
    | some body' =>
      cases h_x : Moist.MIR.lowerTotal env (Moist.MIR.expandFix x) with
      | none => simp
      | some x' => simp
  rw [heq]
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env (.Let [(p, x, false)] body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

--------------------------------------------------------------------------------
-- 3. `betaReduce_soundness`: soundness of the beta-reduction step
--------------------------------------------------------------------------------

/-- Soundness of `betaReduce`: when `f` is a lambda and `x` is an atom,
    `.App f x` contextually refines the beta-reduced substitution.
    Otherwise the result is structurally the same — reflexivity.

    The `Lam + atom` case composes `mirCtxRefines_app_lam_to_let`
    (equivalence of `.App (.Lam p body) x` with
    `.Let [(p, x, false)] body`) with the substitution-inline sub-theorem
    `subst_inline_mirCtxRefines`. -/
theorem betaReduce_soundness (f x : Expr) (s : Moist.MIR.FreshState) :
    MIRCtxRefines (.App f x) (betaReduce f x s).1.1 := by
  cases f with
  | Lam param body =>
    by_cases hxa : x.isAtom = true
    · -- betaReduce returns (subst param x body, true)
      -- compose: .App (.Lam param body) x ≈ .Let [(param, x, false)] body ⊑ subst
      have heq : (betaReduce (.Lam param body) x s).1.1 = (subst param x body s).1 := by
        show ((match (Expr.Lam param body : Expr) with
              | .Lam p b =>
                if x.isAtom then do
                  let result ← subst p x b
                  pure (result, true)
                else
                  pure (.App (.Lam p b) x, false)
              | _ => pure (.App (.Lam param body) x, false)) s).1.1 = _
        simp only [hxa, ↓reduceIte]
        rfl
      rw [heq]
      exact mirCtxRefines_trans
        (mirCtxRefines_app_lam_to_let param body x)
        (subst_body_inline_mirCtxRefines param x body false s)
    · -- betaReduce returns (.App (.Lam param body) x, false) unchanged
      have hxa' : x.isAtom = false := by
        cases hh : x.isAtom with
        | true => exact absurd hh hxa
        | false => rfl
      have heq : (betaReduce (.Lam param body) x s).1.1 = .App (.Lam param body) x := by
        show ((match (Expr.Lam param body : Expr) with
              | .Lam p b =>
                if x.isAtom then do
                  let result ← subst p x b
                  pure (result, true)
                else
                  pure (.App (.Lam p b) x, false)
              | _ => pure (.App (.Lam param body) x, false)) s).1.1 = _
        simp only [hxa', Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [heq]
      exact mirCtxRefines_refl _
  | Var v =>
    have heq : (betaReduce (.Var v) x s).1.1 = .App (.Var v) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Lit c =>
    have heq : (betaReduce (.Lit c) x s).1.1 = .App (.Lit c) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Builtin b =>
    have heq : (betaReduce (.Builtin b) x s).1.1 = .App (.Builtin b) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Error =>
    have heq : (betaReduce .Error x s).1.1 = .App .Error x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Fix g body =>
    have heq : (betaReduce (.Fix g body) x s).1.1 = .App (.Fix g body) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | App fn arg =>
    have heq : (betaReduce (.App fn arg) x s).1.1 = .App (.App fn arg) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Force e =>
    have heq : (betaReduce (.Force e) x s).1.1 = .App (.Force e) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Delay e =>
    have heq : (betaReduce (.Delay e) x s).1.1 = .App (.Delay e) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Constr tag args =>
    have heq : (betaReduce (.Constr tag args) x s).1.1 = .App (.Constr tag args) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Case scrut alts =>
    have heq : (betaReduce (.Case scrut alts) x s).1.1 = .App (.Case scrut alts) x := rfl
    rw [heq]; exact mirCtxRefines_refl _
  | Let binds body =>
    have heq : (betaReduce (.Let binds body) x s).1.1 = .App (.Let binds body) x := rfl
    rw [heq]; exact mirCtxRefines_refl _

--------------------------------------------------------------------------------
-- 3. `inlineLetBindings_soundness`: soundness of the let-inlining decision loop
--------------------------------------------------------------------------------

/-! ### Helper lemmas: structural rearrangement of nested lets -/

/-- Nested-let equality for `lowerTotalLet`: `.Let (A ++ B) body` unfolds
    to the same term as `.Let A (.Let B body)` at any env. Proved by
    induction on `A`. -/
private theorem lowerTotalLet_append (env : List VarId)
    (A B : List (VarId × Expr × Bool)) (body' : Expr) :
    Moist.MIR.lowerTotalLet env (A ++ B) body' =
    Moist.MIR.lowerTotalLet env A (.Let B body') := by
  induction A generalizing env with
  | nil =>
    simp only [List.nil_append, Moist.MIR.lowerTotalLet, Moist.MIR.lowerTotal]
  | cons bh rest_A ih =>
    obtain ⟨v, rhs, er⟩ := bh
    simp only [List.cons_append, Moist.MIR.lowerTotalLet, Option.bind_eq_bind]
    cases hrhs : Moist.MIR.lowerTotal env rhs with
    | none => simp
    | some r =>
      simp only [Option.bind_some]
      exact congrArg
        (fun t => Option.bind t (fun rest' =>
          some (Moist.Plutus.Term.Term.Apply (Moist.Plutus.Term.Term.Lam 0 rest') r)))
        (ih (v :: env))

private theorem lowerTotalExpr_let_split (env : List VarId)
    (binds1 binds2 : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (binds1 ++ binds2) body) =
    lowerTotalExpr env (.Let binds1 (.Let binds2 body)) := by
  -- Both sides unfold through `expandFix` and `lowerTotalLet`. Induct on binds1.
  have hexp_split :
      Moist.MIR.expandFixBinds (binds1 ++ binds2) =
      Moist.MIR.expandFixBinds binds1 ++ Moist.MIR.expandFixBinds binds2 := by
    induction binds1 with
    | nil => simp [Moist.MIR.expandFixBinds]
    | cons b rest ih =>
      obtain ⟨v, rhs, er⟩ := b
      simp [Moist.MIR.expandFixBinds, ih]
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal,
    hexp_split]
  exact lowerTotalLet_append env _ _ _

/-! ### Generalized soundness of the inlining decision loop

The inlining decision loop has the shape:
  inlineLetGo (head :: rest) acc body changed s
    = if shouldInline ... then recurse on (rest', acc, body') after substitution
      else recurse on (rest, head :: acc, body, changed)

We generalize over the accumulator: for every `(binds, acc, body, changed, s)`,
`.Let (acc.reverse ++ binds) body ⊑ (inlineLetGo binds acc body changed s).1.1`.

The inline step is the semantically non-trivial one; it requires the shared
`subst_inline_mirCtxRefines` lemma. -/

/-- Inline-step helper: relate `.Let ((v, rhs, er) :: rest) body` to the
    post-substitution form that appears inside `inlineLetGo`. This is a
    direct use of `substInBindings_body_inline_mirCtxRefines`. -/
private theorem inline_step_mirCtxRefines
    (v : VarId) (rhs : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    MIRCtxRefines (.Let ((v, rhs, er) :: rest) body)
      (.Let (Moist.MIR.substInBindings v rhs rest (Moist.MIR.subst v rhs body s).2).1.val
            (Moist.MIR.subst v rhs body s).1) :=
  substInBindings_body_inline_mirCtxRefines v rhs body er rest s

/-- Generalized soundness of the inlining decision loop with explicit
    accumulator. The shape `(acc.reverse ++ binds)` captures the let
    bindings that have been processed so far (acc is in reverse order,
    hence the reverse) plus the bindings yet to process. -/
private theorem inlineLetGo_soundness :
    ∀ (binds : List (VarId × Expr × Bool)) (acc : List (VarId × Expr × Bool))
      (body : Expr) (changed : Bool) (s : Moist.MIR.FreshState),
      MIRCtxRefines (.Let (acc.reverse ++ binds) body)
                    (Moist.MIR.inlineLetGo binds acc body changed s).1.1
  | [], acc, body, changed, s => by
    -- nil case: inlineLetGo [] acc body changed s = either (body, changed) or (.Let acc.reverse body, changed)
    rw [Moist.MIR.inlineLetGo.eq_1]
    simp only [List.append_nil]
    cases hacc : acc.reverse with
    | nil =>
      -- .Let [] body ⊑ body via mirCtxRefines_let_nil
      show MIRCtxRefines (.Let [] body) _
      simp only [pure, StateT.pure]
      exact mirCtxRefines_let_nil
    | cons s' rest' =>
      -- .Let (s' :: rest') body ⊑ .Let (s' :: rest') body via refl
      show MIRCtxRefines (.Let (s' :: rest') body) _
      simp only [pure, StateT.pure]
      exact mirCtxRefines_refl _
  | (v, rhs, er) :: rest, acc, body, changed, s => by
    rw [Moist.MIR.inlineLetGo.eq_2]
    by_cases hinline :
        (Moist.MIR.shouldInline rhs
          (Moist.MIR.countOccurrences v body +
            rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
          (Moist.MIR.occursUnderFix v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
          (Moist.MIR.occursInDeferred v body ||
            rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = true
    · -- Inline branch
      simp only [hinline, ↓reduceIte]
      -- Goal: MIRCtxRefines (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
      --   ((do let body' ← subst v rhs body; let ⟨r', _⟩ ← substInBindings ...;
      --        inlineLetGo r' acc body' true) s).1.1
      -- Let body' = (subst v rhs body s).1, s_body = (subst v rhs body s).2,
      -- rest' = (substInBindings v rhs rest s_body).1.val,
      -- s_rest = (substInBindings v rhs rest s_body).2.
      let p_body := Moist.MIR.subst v rhs body s
      let body' := p_body.1
      let s_body := p_body.2
      let p_rest := Moist.MIR.substInBindings v rhs rest s_body
      let rest' := p_rest.1.val
      let s_rest := p_rest.2
      have hlen : rest'.length = rest.length := p_rest.1.property
      have hdec : rest'.length < ((v, rhs, er) :: rest).length := by
        simp only [List.length_cons, hlen]; omega
      have ih := inlineLetGo_soundness rest' acc body' true s_rest
      have h_split :
          MIRCtxRefines
            (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
            (.Let acc.reverse (.Let ((v, rhs, er) :: rest) body)) :=
        mirCtxRefines_of_lowerEq
          (lowerTotalExpr_let_split · acc.reverse ((v, rhs, er) :: rest) body)
      have h_step :
          MIRCtxRefines
            (.Let ((v, rhs, er) :: rest) body)
            (.Let rest' body') :=
        inline_step_mirCtxRefines v rhs er rest body s
      have h_wrap :
          MIRCtxRefines
            (.Let acc.reverse (.Let ((v, rhs, er) :: rest) body))
            (.Let acc.reverse (.Let rest' body')) :=
        mirCtxRefines_let_body h_step
      have h_unsplit :
          MIRCtxRefines
            (.Let acc.reverse (.Let rest' body'))
            (.Let (acc.reverse ++ rest') body') :=
        mirCtxRefines_of_lowerEq
          (fun env => (lowerTotalExpr_let_split env acc.reverse rest' body').symm)
      have h_chain :
          MIRCtxRefines
            (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
            (Moist.MIR.inlineLetGo rest' acc body' true s_rest).1.1 :=
        mirCtxRefines_trans h_split
          (mirCtxRefines_trans h_wrap
            (mirCtxRefines_trans h_unsplit ih))
      -- Show the goal matches via StateM computation.
      -- The do-block unfolds to the threaded state computation.
      show MIRCtxRefines (.Let (acc.reverse ++ (v, rhs, er) :: rest) body)
            (((do
              let body' ← Moist.MIR.subst v rhs body
              let __discr ← Moist.MIR.substInBindings v rhs rest
              match __discr with
                | ⟨rest', _⟩ =>
                  Moist.MIR.inlineLetGo rest' acc body' true) s).1.1)
      -- StateM do-block: evaluates in sequence with state threading.
      -- body' ← subst v rhs body  binds at state s, producing p_body = (body', s_body)
      -- __discr ← substInBindings binds at s_body, producing p_rest = (⟨rest', _⟩, s_rest)
      -- match consumes __discr, yielding inlineLetGo rest' acc body' true at s_rest
      -- So the final .1.1 equals (inlineLetGo rest' acc body' true s_rest).1.1.
      exact h_chain
    · -- Keep branch
      have hinline' :
          (Moist.MIR.shouldInline rhs
            (Moist.MIR.countOccurrences v body +
              rest.foldl (fun n (_, e, _) => n + Moist.MIR.countOccurrences v e) 0)
            (Moist.MIR.occursUnderFix v body ||
              rest.any (fun (_, e, _) => Moist.MIR.occursUnderFix v e))
            (Moist.MIR.occursInDeferred v body ||
              rest.any (fun (_, e, _) => Moist.MIR.occursInDeferred v e))) = false := by
        cases h : Moist.MIR.shouldInline rhs _ _ _ with
        | true => exact absurd h hinline
        | false => rfl
      simp only [hinline', Bool.false_eq_true, ↓reduceIte]
      have ih := inlineLetGo_soundness rest ((v, rhs, er) :: acc) body changed s
      have hrev : ((v, rhs, er) :: acc).reverse = acc.reverse ++ [(v, rhs, er)] := by
        simp [List.reverse_cons]
      rw [hrev] at ih
      have hlist_eq : acc.reverse ++ [(v, rhs, er)] ++ rest =
                      acc.reverse ++ (v, rhs, er) :: rest := by
        simp [List.append_assoc]
      rw [hlist_eq] at ih
      exact ih
termination_by binds _ _ _ _ => binds.length

/-- Soundness of the inlining decision loop.

    The result of `inlineLetBindings binds body s` contextually refines
    `.Let binds body`. Reduces to the generalized `inlineLetGo_soundness`
    with the initial empty accumulator. -/
theorem inlineLetBindings_soundness (binds : List (VarId × Expr × Bool)) (body : Expr)
    (s : Moist.MIR.FreshState) :
    MIRCtxRefines (.Let binds body) (inlineLetBindings binds body s).1.1 := by
  have h := inlineLetGo_soundness binds [] body false s
  simp only [List.reverse_nil, List.nil_append] at h
  exact h

--------------------------------------------------------------------------------
-- 4. Main theorem: `inline_soundness`
--------------------------------------------------------------------------------

mutual

/-- **Main theorem**: for every MIR expression `e` and every fresh-state `s`,
    `e` contextually refines `(inlinePass e s).1.1`. -/
theorem inline_soundness_aux : (e : Expr) → (s : Moist.MIR.FreshState) →
    MIRCtxRefines e (inlinePass e s).1.1
  | .Var v, s => by
    rw [inlinePass_var]; exact mirCtxRefines_refl _
  | .Lit c, s => by
    rw [inlinePass_lit]; exact mirCtxRefines_refl _
  | .Builtin b, s => by
    rw [inlinePass_builtin]; exact mirCtxRefines_refl _
  | .Error, s => by
    rw [inlinePass_error]; exact mirCtxRefines_refl _
  | .Lam x body, s => by
    rw [inlinePass_lam]
    exact mirCtxRefines_lam (inline_soundness_aux body s)
  | .Fix f body, s => by
    rw [inlinePass_fix]
    cases body with
    | Lam x inner =>
      rw [inlinePass_lam]
      exact mirCtxRefines_fix_lam (inline_soundness_aux inner s)
    | Var v => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Lit c => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Builtin b => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Error => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Fix _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | App _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Force _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Delay _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Constr _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Case _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
    | Let _ _ => exact mirCtxRefines_fix_nonlam_lhs (by intros; intro h; cases h)
  | .App f x, s => by
    rw [inlinePass_app]
    have h_f := inline_soundness_aux f s
    have h_x := inline_soundness_aux x (inlinePass f s).2
    have h_app :
        MIRCtxRefines (.App f x)
          (.App (inlinePass f s).1.1 (inlinePass x (inlinePass f s).2).1.1) :=
      mirCtxRefines_app h_f h_x
    have h_beta :
        MIRCtxRefines
          (.App (inlinePass f s).1.1 (inlinePass x (inlinePass f s).2).1.1)
          (betaReduce (inlinePass f s).1.1 (inlinePass x (inlinePass f s).2).1.1
            (inlinePass x (inlinePass f s).2).2).1.1 :=
      betaReduce_soundness _ _ _
    exact mirCtxRefines_trans h_app h_beta
  | .Force e, s => by
    rw [inlinePass_force]
    exact mirCtxRefines_force (inline_soundness_aux e s)
  | .Delay e, s => by
    rw [inlinePass_delay]
    exact mirCtxRefines_delay (inline_soundness_aux e s)
  | .Constr tag args, s => by
    rw [inlinePass_constr]
    cases args with
    | nil =>
      rw [inlinePassList_nil]
      exact mirCtxRefines_refl _
    | cons e rest =>
      rw [inlinePassList_cons_eq]
      refine mirCtxRefines_constr ?_ ?_
      · exact inline_soundness_aux e s
      · exact inlinePassList_listRel rest _
  | .Case scrut alts, s => by
    rw [inlinePass_case]
    refine mirCtxRefines_case ?_ ?_
    · exact inline_soundness_aux scrut s
    · exact inlinePassList_listRel alts _
  | .Let binds body, s => by
    rw [inlinePass_let]
    have h_binds := inlineBindings_listRel binds s
    have h_step1 :
        MIRCtxRefines (.Let binds body)
                      (.Let (inlineBindings binds s).1.1 body) :=
      mirCtxRefines_let_binds_congr binds (inlineBindings binds s).1.1 body h_binds
    have h_body := inline_soundness_aux body (inlineBindings binds s).2
    have h_step2 :
        MIRCtxRefines
          (.Let (inlineBindings binds s).1.1 body)
          (.Let (inlineBindings binds s).1.1
            (inlinePass body (inlineBindings binds s).2).1.1) :=
      mirCtxRefines_let_body h_body
    have h_step3 :
        MIRCtxRefines
          (.Let (inlineBindings binds s).1.1
                (inlinePass body (inlineBindings binds s).2).1.1)
          (inlineLetBindings (inlineBindings binds s).1.1
            (inlinePass body (inlineBindings binds s).2).1.1
            (inlinePass body (inlineBindings binds s).2).2).1.1 :=
      inlineLetBindings_soundness _ _ _
    exact mirCtxRefines_trans h_step1 (mirCtxRefines_trans h_step2 h_step3)

/-- Pointwise soundness for `inlinePassList`. -/
theorem inlinePassList_listRel : (es : List Expr) → (s : Moist.MIR.FreshState) →
    ListRel MIRCtxRefines es (inlinePassList es s).1.1
  | [], s => by
    rw [inlinePassList_nil]
    exact True.intro
  | e :: rest, s => by
    rw [inlinePassList_cons_eq]
    refine ⟨inline_soundness_aux e s, ?_⟩
    exact inlinePassList_listRel rest _

/-- Per-binding soundness for `inlineBindings`. -/
theorem inlineBindings_listRel : (binds : List (VarId × Expr × Bool)) →
    (s : Moist.MIR.FreshState) →
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                          MIRCtxRefines b₁.2.1 b₂.2.1)
            binds (inlineBindings binds s).1.1
  | [], s => by
    rw [inlineBindings_nil]
    exact True.intro
  | (v, rhs, er) :: rest, s => by
    rw [inlineBindings_cons_eq]
    refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
    · exact inline_soundness_aux rhs s
    · exact inlineBindings_listRel rest _

end

/-- **Main user-facing theorem**: for every MIR expression `e` and every
    fresh-variable state `s`, `e` contextually refines `(inlinePass e s).1.1`. -/
theorem inline_soundness (e : Expr) (s : Moist.MIR.FreshState) :
    MIRCtxRefines e (inlinePass e s).1.1 :=
  inline_soundness_aux e s

end Moist.Verified.MIR
