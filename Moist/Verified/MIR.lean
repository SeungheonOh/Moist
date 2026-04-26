import Moist.Verified.Equivalence
import Moist.Verified.ClosedAt
import Moist.Verified.Contextual
import Moist.Verified.Contextual.Congruence
import Moist.Verified.Contextual.Soundness
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Definitions.MIR
import Moist.MIR.LowerTotal

/-! # MIR-Level Equivalence and Refinement

Lifts the unidirectional step-indexed logical relation from UPLC terms
(defined in `Contextual/SoundnessRefines.lean`) to MIR expressions via
`lowerTotalExpr`.

The relations `MIROpenRefK` / `MIROpenRef` / `MIRRefines` quantify over
arbitrary environments (no `WellSizedEnv` guard) and are unidirectional
(refinement, not equivalence). They plug directly into
`soundness_refines_d` to yield `CtxRefines` on the lowered terms at
arbitrary depth — giving a clean `MIRRefines → MIRCtxRefines` bridge
via `mirRefines_to_mirCtxRefines` (defined below in section 5).
-/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.Verified (closedAt)
open Moist.Verified.Contextual
  (Context fill closedAt_mono fill_closedAt_iff ObsRefines
   CtxEq CtxRefines
   ctxEq_refl ctxEq_symm ctxEq_trans ctxRefines_refl ctxRefines_trans
   ctxEq_lam ctxEq_delay ctxEq_force ctxEq_app
   ctxEq_constr_one ctxEq_constr ctxEq_case_scrut ctxEq_case_one_alt ctxEq_case
   ctxRefines_lam ctxRefines_delay ctxRefines_force ctxRefines_app
   ctxRefines_constr_one ctxRefines_constr ctxRefines_case_scrut
   ctxRefines_case_one_alt ctxRefines_case)
open Moist.Verified.Equivalence (ObsEq ListRel)
open Moist.Verified.Contextual.Soundness (soundness)
open Moist.Verified.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK OpenRefinesK OpenRefines
   soundness_refines obsRefines_of_openRefines)

/-! ## `lowerTotal` preserves `closedAt`

Bridging lemmas connecting `Moist.MIR.lowerTotal` with the
`Moist.Verified.closedAt` predicate. Used by `lowerTotalExpr_closedAt`
below (and indirectly by the dead-let refinement proof). -/

open Moist.MIR (envLookupT_bound lowerTotalList) in
mutual
  theorem lowerTotal_closedAt (env : List VarId) (e : Expr) (t : Moist.Plutus.Term.Term)
      (h : Moist.MIR.lowerTotal env e = some t) : closedAt env.length t = true := by
    match e with
    | .Var x =>
      simp only [Moist.MIR.lowerTotal.eq_1] at h; split at h
      · rename_i idx hlook; injection h with h; subst h; simp [closedAt]
        have := envLookupT_bound env x idx hlook; omega
      · injection h
    | .Lit (c, ty) =>
      simp only [Moist.MIR.lowerTotal.eq_2] at h; injection h with h; subst h; simp [closedAt]
    | .Builtin b =>
      simp only [Moist.MIR.lowerTotal.eq_3] at h; injection h with h; subst h; simp [closedAt]
    | .Error =>
      simp only [Moist.MIR.lowerTotal.eq_4] at h; injection h with h; subst h; simp [closedAt]
    | .Lam x body =>
      simp only [Moist.MIR.lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨body', hbody, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; have := lowerTotal_closedAt (x :: env) body body' hbody
      simp at this; exact this
    | .App f x =>
      simp only [Moist.MIR.lowerTotal.eq_6, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f', hf, x', hx, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env f f' hf, lowerTotal_closedAt env x x' hx⟩
    | .Force inner =>
      simp only [Moist.MIR.lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Delay inner =>
      simp only [Moist.MIR.lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Constr tag args =>
      simp only [Moist.MIR.lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨args', hargs, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotalList_closedAtList env args args' hargs
    | .Case scrut alts =>
      simp only [Moist.MIR.lowerTotal.eq_10, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨scrut', hscrut, alts', halts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env scrut scrut' hscrut,
             lowerTotalList_closedAtList env alts alts' halts⟩
    | .Let binds body =>
      simp only [Moist.MIR.lowerTotal.eq_11] at h; exact lowerTotalLet_closedAt env binds body t h
    | .Fix _ _ => simp only [Moist.MIR.lowerTotal.eq_12] at h; injection h
  termination_by sizeOf e

  theorem lowerTotalList_closedAtList (env : List VarId) (es : List Expr)
      (ts : List Moist.Plutus.Term.Term) (h : Moist.MIR.lowerTotalList env es = some ts) :
      Moist.Verified.closedAtList env.length ts = true := by
    match es with
    | [] => simp only [Moist.MIR.lowerTotalList.eq_1] at h; injection h with h; subst h; simp [Moist.Verified.closedAtList]
    | e :: rest =>
      simp only [Moist.MIR.lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ts', hts, heq⟩ := h; injection heq with heq; subst heq
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env e t ht, lowerTotalList_closedAtList env rest ts' hts⟩
  termination_by sizeOf es

  theorem lowerTotalLet_closedAt (env : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Moist.Plutus.Term.Term)
      (h : Moist.MIR.lowerTotalLet env binds body = some t) :
      closedAt env.length t = true := by
    match binds with
    | [] => simp only [Moist.MIR.lowerTotalLet.eq_1] at h; exact lowerTotal_closedAt env body t h
    | (x, rhs, _) :: rest =>
      simp only [Moist.MIR.lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rhs', hrhs, rest', hrest, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      have := lowerTotalLet_closedAt (x :: env) rest body rest' hrest
      simp at this; exact ⟨this, lowerTotal_closedAt env rhs rhs' hrhs⟩
  termination_by sizeOf binds + sizeOf body
end

/-- Lift `lowerTotal_closedAt` through `lowerTotalExpr`'s extra `expandFix`
    step: if `lowerTotalExpr env e = some t`, then `t` is closed at
    `env.length`. -/
theorem lowerTotalExpr_closedAt {env : List VarId} {e : Expr} {t : Moist.Plutus.Term.Term}
    (h : lowerTotalExpr env e = some t) : closedAt env.length t = true := by
  simp only [Moist.MIR.lowerTotalExpr] at h
  exact lowerTotal_closedAt env (Moist.MIR.expandFix e) t h

--------------------------------------------------------------------------------
-- 1. LIFTING `OpenRefines` TO MIR
--
-- The relations `MIROpenRefK`, `MIROpenRef`, `MIRRefines` are now defined
-- in `Moist.Verified.Definitions.MIR`. Basic properties stay here.
--------------------------------------------------------------------------------

private theorem mirOpenRefK_lower {k d : Nat} {m₁ m₂ : Expr} {env : List VarId}
    {t₁ t₂ : Moist.Plutus.Term.Term}
    (h : MIROpenRefK k d m₁ m₂) (hlen : env.length = d)
    (h₁ : lowerTotalExpr env m₁ = some t₁) (h₂ : lowerTotalExpr env m₂ = some t₂) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      BehRefinesK ValueRefinesK j ρ₁ ρ₂ t₁ t₂ := by
  have := h env hlen; simp only [h₁, h₂] at this; exact this

theorem mirOpenRefK_mono {j k d : Nat} {m₁ m₂ : Expr}
    (hjk : j ≤ k) (h : MIROpenRefK k d m₁ m₂) : MIROpenRefK j d m₁ m₂ := by
  intro env hlen
  cases h₁ : lowerTotalExpr env m₁ <;> cases h₂ : lowerTotalExpr env m₂ <;>
    simp only [] <;> try trivial
  have := mirOpenRefK_lower h hlen h₁ h₂
  exact fun j' hj' => this j' (by omega)

--------------------------------------------------------------------------------
-- 2. CONTEXTUAL EQUIVALENCE & REFINEMENT
--
-- `MIRCtxEq` and `MIRCtxRefines` are defined in
-- `Moist.Verified.Definitions.MIR`. Their theorems stay here.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 3. BASIC PROPERTIES OF MIRCtxEq / MIRCtxRefines
--------------------------------------------------------------------------------

/-- Reflexivity of `MIRCtxRefines`. -/
theorem mirCtxRefines_refl (m : Expr) : MIRCtxRefines m m := by
  intro env
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env m with
  | none => trivial
  | some _ => exact ctxRefines_refl _

/-- Transitivity of `MIRCtxRefines`. Thanks to the new `CtxRefines` shape
    (closedness preservation bundled into the relation), this is a clean
    composition — no middle-closedness side condition needed. -/
theorem mirCtxRefines_trans {m₁ m₂ m₃ : Expr} :
    MIRCtxRefines m₁ m₂ → MIRCtxRefines m₂ m₃ → MIRCtxRefines m₁ m₃ := by
  intro h12 h23 env
  obtain ⟨hsome12, hctx12⟩ := h12 env
  obtain ⟨hsome23, hctx23⟩ := h23 env
  refine ⟨hsome23 ∘ hsome12, ?_⟩
  cases h₁ : lowerTotalExpr env m₁ with
  | none => trivial
  | some t₁ =>
    cases h₃ : lowerTotalExpr env m₃ with
    | none => trivial
    | some t₃ =>
      have hsome2 : (lowerTotalExpr env m₂).isSome := hsome12 (by rw [h₁]; trivial)
      cases h₂ : lowerTotalExpr env m₂ with
      | none => rw [h₂] at hsome2; exact absurd hsome2 (by simp)
      | some t₂ =>
        rw [h₁, h₂] at hctx12
        rw [h₂, h₃] at hctx23
        -- hctx12 : CtxRefines t₁ t₂, hctx23 : CtxRefines t₂ t₃
        show CtxRefines t₁ t₃
        exact ctxRefines_trans hctx12 hctx23

/-- Reflexivity of `MIRCtxEq`. -/
theorem mirCtxEq_refl (m : Expr) : MIRCtxEq m m := by
  intro env
  refine ⟨Iff.rfl, ?_⟩
  cases h : lowerTotalExpr env m with
  | none => trivial
  | some _ => exact ctxEq_refl _

/-- Symmetry of `MIRCtxEq`. Uses `ctxEq_symm` from `Contextual.lean`. -/
theorem mirCtxEq_symm {m₁ m₂ : Expr} :
    MIRCtxEq m₁ m₂ → MIRCtxEq m₂ m₁ := by
  intro h env
  obtain ⟨hiff, hctx⟩ := h env
  refine ⟨hiff.symm, ?_⟩
  cases h₁ : lowerTotalExpr env m₁ with
  | none =>
    cases h₂ : lowerTotalExpr env m₂ with
    | none => trivial
    | some _ => trivial
  | some t₁ =>
    cases h₂ : lowerTotalExpr env m₂ with
    | none => trivial
    | some t₂ =>
      rw [h₁, h₂] at hctx
      -- hctx : CtxEq t₁ t₂
      show CtxEq t₂ t₁
      exact ctxEq_symm hctx

/-- Transitivity of `MIRCtxEq`. Takes the same middle-closedness side
    condition as `ctxEq_trans` in `Contextual.lean` (since `CtxEq` is
    closedness-agnostic and can't derive middle closedness on its own). -/
theorem mirCtxEq_trans {m₁ m₂ m₃ : Expr}
    (h_closed_mid : ∀ env C,
      (∀ t₁, lowerTotalExpr env m₁ = some t₁ → closedAt 0 (fill C t₁) = true) →
      (∀ t₃, lowerTotalExpr env m₃ = some t₃ → closedAt 0 (fill C t₃) = true) →
      ∀ t₂, lowerTotalExpr env m₂ = some t₂ → closedAt 0 (fill C t₂) = true) :
    MIRCtxEq m₁ m₂ → MIRCtxEq m₂ m₃ → MIRCtxEq m₁ m₃ := by
  intro h12 h23 env
  obtain ⟨hiff12, hctx12⟩ := h12 env
  obtain ⟨hiff23, hctx23⟩ := h23 env
  refine ⟨hiff12.trans hiff23, ?_⟩
  cases h₁ : lowerTotalExpr env m₁ with
  | none => trivial
  | some t₁ =>
    cases h₃ : lowerTotalExpr env m₃ with
    | none => trivial
    | some t₃ =>
      have hsome2 : (lowerTotalExpr env m₂).isSome := hiff12.mp (by rw [h₁]; trivial)
      cases h₂ : lowerTotalExpr env m₂ with
      | none => rw [h₂] at hsome2; exact absurd hsome2 (by simp)
      | some t₂ =>
        rw [h₁, h₂] at hctx12
        rw [h₂, h₃] at hctx23
        -- hctx12 : CtxEq t₁ t₂, hctx23 : CtxEq t₂ t₃
        show CtxEq t₁ t₃
        refine ctxEq_trans ?_ hctx12 hctx23
        intro C hC1 hC3
        exact h_closed_mid env C
          (fun _ heq => by cases heq.symm.trans h₁; exact hC1)
          (fun _ heq => by cases heq.symm.trans h₃; exact hC3)
          t₂ h₂

--------------------------------------------------------------------------------
-- 4. MIRCtxEq ↔ bidirectional MIRCtxRefines
--------------------------------------------------------------------------------

/-- Bidirectional `MIRCtxRefines` collapses to `MIRCtxEq`.

    (The converse `MIRCtxEq → bidirectional MIRCtxRefines` is *not*
    automatic: the new `CtxRefines` bundles closedness preservation, but
    `CtxEq` is closedness-agnostic by design — so the forward direction
    would need additional external closedness-preservation hypotheses.
    Removed for simplicity; downstream consumers that need it can bridge
    via `CtxEq.toCtxRefines` + their own closedness preservation.) -/
theorem mirCtxEq_of_mirCtxRefines_bidir {m₁ m₂ : Expr}
    (h12 : MIRCtxRefines m₁ m₂) (h21 : MIRCtxRefines m₂ m₁) :
    MIRCtxEq m₁ m₂ := by
  intro env
  obtain ⟨hsome12, hctx12⟩ := h12 env
  obtain ⟨hsome21, hctx21⟩ := h21 env
  refine ⟨⟨hsome12, hsome21⟩, ?_⟩
  cases h₁ : lowerTotalExpr env m₁ with
  | none =>
    cases h₂ : lowerTotalExpr env m₂ with
    | none => trivial
    | some _ => trivial
  | some t₁ =>
    cases h₂ : lowerTotalExpr env m₂ with
    | none => trivial
    | some t₂ =>
      rw [h₁, h₂] at hctx12
      rw [h₁, h₂] at hctx21
      -- hctx12 : CtxRefines t₁ t₂, hctx21 : CtxRefines t₂ t₁
      intro C hC1 hC2
      obtain ⟨_, ref12⟩ := hctx12 C hC1
      obtain ⟨_, ref21⟩ := hctx21 C hC2
      exact ObsEq.mk
        (Iff.intro ref12.halt ref21.halt)
        (Iff.intro ref12.error ref21.error)

--------------------------------------------------------------------------------
-- 5. BRIDGE: `MIRRefines` → `MIRCtxRefines`.
--
-- `MIRRefines` is unidirectional and provides `MIROpenRef d` at every
-- depth. For each env, we extract `MIROpenRef env.length`, derive
-- `OpenRefines env.length` on the `env`-lowerings, and feed it through
-- `soundness_refines_d` (which now supports arbitrary `d`) to obtain
-- `ObsRefines` under any closing context.
--------------------------------------------------------------------------------

/-- From `MIRRefines m₁ m₂` to `MIRCtxRefines m₁ m₂`, via
    `soundness_refines_d` at depth `env.length`. Requires an external
    closedness-preservation hypothesis since `MIRRefines` is a purely
    semantic relation and the new `MIRCtxRefines` (backed by the strict
    `CtxRefines`) bundles closedness preservation into its observation
    clause.

    The closedness-preservation hypothesis is stated at the "free-variable
    horizon" (a depth `k : Nat`) rather than over contexts, since
    `closedAt 0 (fill C t) ↔ C.closedAt 0 ∧ closedAt C.binders t`
    (from `fill_closedAt_iff`) — the `C` drops out and what matters is
    that `closedAt k t₁ → closedAt k t₂` at every depth `k`. -/
theorem mirRefines_to_mirCtxRefines {m₁ m₂ : Expr} (h : MIRRefines m₁ m₂)
    (h_close_pres : ∀ env k t₁ t₂,
      lowerTotalExpr env m₁ = some t₁ → lowerTotalExpr env m₂ = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  refine ⟨h.1 env, ?_⟩
  cases hlow₁ : lowerTotalExpr env m₁ with
  | none => trivial
  | some t₁ =>
    cases hlow₂ : lowerTotalExpr env m₂ with
    | none => trivial
    | some t₂ =>
      show CtxRefines t₁ t₂
      intro C hC1
      -- Split hC1 into `C.closedAt 0` and `closedAt C.binders t₁`,
      -- transport the latter through `h_close_pres` at k = C.binders,
      -- then rebuild `closedAt 0 (fill C t₂)`.
      have hd1 := (fill_closedAt_iff C t₁ 0).mp hC1
      simp only [Nat.zero_add] at hd1
      have hC_outer := hd1.1
      have ht₂ : closedAt C.binders t₂ = true :=
        h_close_pres env C.binders t₁ t₂ hlow₁ hlow₂ hd1.2
      have hC2 : closedAt 0 (fill C t₂) = true :=
        (fill_closedAt_iff C t₂ 0).mpr ⟨hC_outer, by simpa [Nat.zero_add] using ht₂⟩
      refine ⟨hC2, ?_⟩
      have hopenRef : MIROpenRef env.length m₁ m₂ := h.2 env.length
      have h_open : OpenRefines env.length t₁ t₂ := by
        intro k j hj ρ₁ ρ₂ henv
        have := hopenRef k env rfl
        rw [hlow₁, hlow₂] at this
        exact this j hj ρ₁ ρ₂ henv
      exact obsRefines_of_openRefines h_open C hC1 hC2

--------------------------------------------------------------------------------
-- 6. Helpers for MIR-level congruences
--
-- The congruence theorems themselves (`mirCtxEq_*`, `mirCtxRefines_*`) now
-- live in `Moist.Verified.MIR.Congruence`. What stays here are the
-- `lowerTotalExpr` compositional decomposition lemmas, the `toCtxEq` /
-- `toCtxRefines` projections, and the list-level helpers (all shared
-- scaffolding used by the congruence file and by other downstream
-- clients).
--------------------------------------------------------------------------------

/-! ### 6a. `lowerTotalExpr` compositional decomposition -/

/-- `lowerTotalExpr` commutes with `.Force`. -/
theorem lowerTotalExpr_force (env : List VarId) (t : Expr) :
    lowerTotalExpr env (.Force t) = (lowerTotalExpr env t).map .Force := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotal env (Moist.MIR.expandFix t) <;> rfl

/-- `lowerTotalExpr` commutes with `.Delay`. -/
theorem lowerTotalExpr_delay (env : List VarId) (t : Expr) :
    lowerTotalExpr env (.Delay t) = (lowerTotalExpr env t).map .Delay := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotal env (Moist.MIR.expandFix t) <;> rfl

/-- `lowerTotalExpr` commutes with `.Lam` (shifting `x` onto the env). -/
theorem lowerTotalExpr_lam (env : List VarId) (x : VarId) (body : Expr) :
    lowerTotalExpr env (.Lam x body) =
      (lowerTotalExpr (x :: env) body).map (.Lam 0) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotal (x :: env) (Moist.MIR.expandFix body) <;> rfl

/-- `lowerTotalExpr` commutes with `.App`. -/
theorem lowerTotalExpr_app (env : List VarId) (f a : Expr) :
    lowerTotalExpr env (.App f a) =
      (do let f' ← lowerTotalExpr env f
          let a' ← lowerTotalExpr env a
          some (.Apply f' a')) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

/-- `lowerTotalExpr` commutes with `.Constr`. -/
theorem lowerTotalExpr_constr (env : List VarId) (tag : Nat) (args : List Expr) :
    lowerTotalExpr env (.Constr tag args) =
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList args)).map (.Constr tag) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList args) <;> rfl

/-- `lowerTotalExpr` commutes with `.Case`. -/
theorem lowerTotalExpr_case (env : List VarId) (scrut : Expr) (alts : List Expr) :
    lowerTotalExpr env (.Case scrut alts) =
      (do let s ← lowerTotalExpr env scrut
          let a ← Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts)
          some (.Case s a)) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

/-! ### 6b. Projections from `MIRCtxEq` -/

/-- Extract `CtxEq` on the lowered UPLC terms from `MIRCtxEq` at a specific
    env, given that both sides lower successfully. -/
theorem MIRCtxEq.toCtxEq {m₁ m₂ : Expr} {env : List VarId}
    {t₁ t₂ : Moist.Plutus.Term.Term}
    (h : MIRCtxEq m₁ m₂)
    (hlow₁ : lowerTotalExpr env m₁ = some t₁)
    (hlow₂ : lowerTotalExpr env m₂ = some t₂) : CtxEq t₁ t₂ := by
  have ⟨_, hctx⟩ := h env
  rw [hlow₁, hlow₂] at hctx
  exact hctx

/-- Extract the compile-status iff from `MIRCtxEq` at a specific env. -/
theorem MIRCtxEq.toIff {m₁ m₂ : Expr} (env : List VarId) (h : MIRCtxEq m₁ m₂) :
    (lowerTotalExpr env m₁).isSome ↔ (lowerTotalExpr env m₂).isSome :=
  (h env).1

/-! ### 6c. Unary / binary constructor congruences for `MIRCtxEq`
    → moved to `Moist.Verified.MIR.Congruence`. -/

/-! ### 6d. List-level helpers for Constr/Case congruences -/

/-- Unwrapped `lowerTotalList ∘ expandFixList` — the list counterpart of
    `lowerTotalExpr`. -/
def lowerTotalExprList (env : List VarId) (es : List Expr) : Option (List Moist.Plutus.Term.Term) :=
  Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList es)

theorem lowerTotalExprList_nil (env : List VarId) :
    lowerTotalExprList env [] = some [] := by
  simp only [lowerTotalExprList, Moist.MIR.expandFixList, Moist.MIR.lowerTotalList]

theorem lowerTotalExprList_cons (env : List VarId) (e : Expr) (es : List Expr) :
    lowerTotalExprList env (e :: es) =
      (do let t ← lowerTotalExpr env e
          let ts ← lowerTotalExprList env es
          some (t :: ts)) := by
  simp only [lowerTotalExprList, lowerTotalExpr,
             Moist.MIR.expandFixList, Moist.MIR.lowerTotalList]

/-- `MIRCtxEq`-related lists have matching `lowerTotalExprList` success. -/
theorem listRel_mirCtxEq_isSome_iff :
    ∀ {args₁ args₂ : List Expr},
      ListRel MIRCtxEq args₁ args₂ →
      ∀ env, (lowerTotalExprList env args₁).isSome ↔ (lowerTotalExprList env args₂).isSome
  | [], [], _, _ => by simp [lowerTotalExprList_nil]
  | _ :: _, [], h, _ => absurd h id
  | [], _ :: _, h, _ => absurd h id
  | e₁ :: es₁, e₂ :: es₂, ⟨hhead, htail⟩, env => by
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons]
      have hhead_iff := hhead.toIff env
      have htail_iff := listRel_mirCtxEq_isSome_iff htail env
      cases h₁ : lowerTotalExpr env e₁ with
      | none =>
        have hf₂ : lowerTotalExpr env e₂ = none := by
          cases heq : lowerTotalExpr env e₂
          · rfl
          · exfalso
            have : (lowerTotalExpr env e₁).isSome := hhead_iff.mpr (by rw [heq]; rfl)
            rw [h₁] at this; exact absurd this (by simp)
        rw [hf₂]; simp
      | some t₁ =>
        have hsome₂ : (lowerTotalExpr env e₂).isSome :=
          hhead_iff.mp (by rw [h₁]; rfl)
        cases h₂ : lowerTotalExpr env e₂ with
        | none => rw [h₂] at hsome₂; exact absurd hsome₂ (by simp)
        | some t₂ =>
          -- After binding both heads, the goal depends only on the tails
          cases hr₁ : lowerTotalExprList env es₁ with
          | none =>
            have hn₂ : lowerTotalExprList env es₂ = none := by
              cases heq : lowerTotalExprList env es₂
              · rfl
              · exfalso
                have : (lowerTotalExprList env es₁).isSome :=
                  htail_iff.mpr (by rw [heq]; rfl)
                rw [hr₁] at this; exact absurd this (by simp)
            rw [hn₂]; simp
          | some tr₁ =>
            have hsome_r₂ : (lowerTotalExprList env es₂).isSome :=
              htail_iff.mp (by rw [hr₁]; rfl)
            cases hr₂ : lowerTotalExprList env es₂ with
            | none => rw [hr₂] at hsome_r₂; exact absurd hsome_r₂ (by simp)
            | some tr₂ => simp

/-- From `ListRel MIRCtxEq args₁ args₂` and both lists lowering, get
    `ListRel CtxEq` on the lowered lists. -/
theorem listRel_mirCtxEq_toListCtxEq :
    ∀ {args₁ args₂ : List Expr} {env : List VarId}
      {ts₁ ts₂ : List Moist.Plutus.Term.Term},
      ListRel MIRCtxEq args₁ args₂ →
      lowerTotalExprList env args₁ = some ts₁ →
      lowerTotalExprList env args₂ = some ts₂ →
      ListRel CtxEq ts₁ ts₂
  | [], [], env, ts₁, ts₂, _, hlow₁, hlow₂ => by
      simp only [lowerTotalExprList_nil, Option.some.injEq] at hlow₁ hlow₂
      subst hlow₁; subst hlow₂
      exact True.intro
  | _ :: _, [], _, _, _, h, _, _ => absurd h id
  | [], _ :: _, _, _, _, h, _, _ => absurd h id
  | e₁ :: es₁, e₂ :: es₂, env, ts₁, ts₂, ⟨hhead, htail⟩, hlow₁, hlow₂ => by
      rw [lowerTotalExprList_cons] at hlow₁ hlow₂
      cases hlow_e₁ : lowerTotalExpr env e₁ with
      | none => rw [hlow_e₁] at hlow₁; simp at hlow₁
      | some t_e₁ =>
        cases hlow_es₁ : lowerTotalExprList env es₁ with
        | none => rw [hlow_e₁, hlow_es₁] at hlow₁; simp at hlow₁
        | some t_es₁ =>
          cases hlow_e₂ : lowerTotalExpr env e₂ with
          | none => rw [hlow_e₂] at hlow₂; simp at hlow₂
          | some t_e₂ =>
            cases hlow_es₂ : lowerTotalExprList env es₂ with
            | none => rw [hlow_e₂, hlow_es₂] at hlow₂; simp at hlow₂
            | some t_es₂ =>
              rw [hlow_e₁, hlow_es₁] at hlow₁
              rw [hlow_e₂, hlow_es₂] at hlow₂
              -- hlow₁ : some (t_e₁ :: t_es₁) = some ts₁
              -- hlow₂ : some (t_e₂ :: t_es₂) = some ts₂
              cases hlow₁
              cases hlow₂
              exact ⟨hhead.toCtxEq hlow_e₁ hlow_e₂,
                     listRel_mirCtxEq_toListCtxEq htail hlow_es₁ hlow_es₂⟩

/-! ### 6e. Constr / Case congruences -/

/-- `lowerTotalExpr` on `.Constr` in terms of `lowerTotalExprList`. -/
theorem lowerTotalExpr_constr_of_list (env : List VarId) (tag : Nat)
    (args : List Expr) :
    lowerTotalExpr env (.Constr tag args) =
      (lowerTotalExprList env args).map (.Constr tag) := by
  rw [lowerTotalExpr_constr]; rfl

/-- `lowerTotalExpr` on `.Case` in terms of `lowerTotalExprList`. -/
theorem lowerTotalExpr_case_of_list (env : List VarId) (scrut : Expr)
    (alts : List Expr) :
    lowerTotalExpr env (.Case scrut alts) =
      (do let s ← lowerTotalExpr env scrut
          let a ← lowerTotalExprList env alts
          some (.Case s a)) := by
  rw [lowerTotalExpr_case]; rfl

/-! Constr / Case congruences for `MIRCtxEq` have been moved to
    `Moist.Verified.MIR.Congruence`. -/

--------------------------------------------------------------------------------
-- 7. MIR-level congruences for `MIRCtxRefines`
--
-- Direct ports of the `MIRCtxEq` congruences with `CtxEq` → `CtxRefines`.
-- The new `CtxRefines` bundles closedness preservation in its conclusion,
-- so each congruence proof just relies on the corresponding UPLC-level
-- `ctxRefines_*` congruence from `Contextual.lean`.
--------------------------------------------------------------------------------

/-! ### 7a. Projections from `MIRCtxRefines` -/

/-- Extract `CtxRefines` on the lowered UPLC terms from `MIRCtxRefines` at
    a specific env, given that both sides lower successfully. -/
theorem MIRCtxRefines.toCtxRefines {m₁ m₂ : Expr} {env : List VarId}
    {t₁ t₂ : Moist.Plutus.Term.Term}
    (h : MIRCtxRefines m₁ m₂)
    (hlow₁ : lowerTotalExpr env m₁ = some t₁)
    (hlow₂ : lowerTotalExpr env m₂ = some t₂) : CtxRefines t₁ t₂ := by
  have ⟨_, hctx⟩ := h env
  rw [hlow₁, hlow₂] at hctx
  exact hctx

/-- Extract the compile-status implication from `MIRCtxRefines` at a
    specific env. -/
theorem MIRCtxRefines.toImp {m₁ m₂ : Expr} (env : List VarId) (h : MIRCtxRefines m₁ m₂) :
    (lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome :=
  (h env).1

/-! ### 7b. Unary / binary constructor congruences for `MIRCtxRefines`
    → moved to `Moist.Verified.MIR.Congruence`. -/

/-! ### 7c. List-level helpers for Constr/Case congruences for Refines -/

/-- `MIRCtxRefines`-related lists have matching `lowerTotalExprList` success
    (forward direction). -/
theorem listRel_mirCtxRefines_isSome_imp :
    ∀ {args₁ args₂ : List Expr},
      ListRel MIRCtxRefines args₁ args₂ →
      ∀ env, (lowerTotalExprList env args₁).isSome →
             (lowerTotalExprList env args₂).isSome
  | [], [], _, _, _ => by simp [lowerTotalExprList_nil]
  | _ :: _, [], h, _, _ => absurd h id
  | [], _ :: _, h, _, _ => absurd h id
  | e₁ :: es₁, e₂ :: es₂, ⟨hhead, htail⟩, env, h_some => by
      rw [lowerTotalExprList_cons] at h_some ⊢
      cases hlow_e₁ : lowerTotalExpr env e₁ with
      | none => rw [hlow_e₁] at h_some; simp at h_some
      | some t₁ =>
        have hsome₂ : (lowerTotalExpr env e₂).isSome :=
          hhead.toImp env (by rw [hlow_e₁]; rfl)
        cases hlow_e₂ : lowerTotalExpr env e₂ with
        | none => rw [hlow_e₂] at hsome₂; exact absurd hsome₂ (by simp)
        | some t₂ =>
          cases hlow_es₁ : lowerTotalExprList env es₁ with
          | none => rw [hlow_e₁, hlow_es₁] at h_some; simp at h_some
          | some ts₁ =>
            have hts₂ : (lowerTotalExprList env es₂).isSome :=
              listRel_mirCtxRefines_isSome_imp htail env (by rw [hlow_es₁]; rfl)
            cases hlow_es₂ : lowerTotalExprList env es₂ with
            | none => rw [hlow_es₂] at hts₂; exact absurd hts₂ (by simp)
            | some ts₂ => simp

/-- From `ListRel MIRCtxRefines args₁ args₂` and both lists lowering, get
    `ListRel CtxRefines` on the lowered lists. -/
theorem listRel_mirCtxRefines_toListCtxRefines :
    ∀ {args₁ args₂ : List Expr} {env : List VarId}
      {ts₁ ts₂ : List Moist.Plutus.Term.Term},
      ListRel MIRCtxRefines args₁ args₂ →
      lowerTotalExprList env args₁ = some ts₁ →
      lowerTotalExprList env args₂ = some ts₂ →
      ListRel CtxRefines ts₁ ts₂
  | [], [], env, ts₁, ts₂, _, hlow₁, hlow₂ => by
      simp only [lowerTotalExprList_nil, Option.some.injEq] at hlow₁ hlow₂
      subst hlow₁; subst hlow₂
      exact True.intro
  | _ :: _, [], _, _, _, h, _, _ => absurd h id
  | [], _ :: _, _, _, _, h, _, _ => absurd h id
  | e₁ :: es₁, e₂ :: es₂, env, ts₁, ts₂, ⟨hhead, htail⟩, hlow₁, hlow₂ => by
      rw [lowerTotalExprList_cons] at hlow₁ hlow₂
      cases hlow_e₁ : lowerTotalExpr env e₁ with
      | none => rw [hlow_e₁] at hlow₁; simp at hlow₁
      | some t_e₁ =>
        cases hlow_es₁ : lowerTotalExprList env es₁ with
        | none => rw [hlow_e₁, hlow_es₁] at hlow₁; simp at hlow₁
        | some t_es₁ =>
          cases hlow_e₂ : lowerTotalExpr env e₂ with
          | none => rw [hlow_e₂] at hlow₂; simp at hlow₂
          | some t_e₂ =>
            cases hlow_es₂ : lowerTotalExprList env es₂ with
            | none => rw [hlow_e₂, hlow_es₂] at hlow₂; simp at hlow₂
            | some t_es₂ =>
              rw [hlow_e₁, hlow_es₁] at hlow₁
              rw [hlow_e₂, hlow_es₂] at hlow₂
              cases hlow₁; cases hlow₂
              exact ⟨hhead.toCtxRefines hlow_e₁ hlow_e₂,
                     listRel_mirCtxRefines_toListCtxRefines htail hlow_es₁ hlow_es₂⟩

/-! ### 7d. Constr / Case / Fix-Lam congruences for `MIRCtxRefines`
    → moved to `Moist.Verified.MIR.Congruence`. -/

end Moist.Verified.MIR
