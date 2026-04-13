import Moist.VerifiedNewNew.Equivalence
import Moist.VerifiedNewNew.Rename
import Moist.VerifiedNewNew.Contextual
import Moist.VerifiedNewNew.Contextual.Soundness
import Moist.VerifiedNewNew.Contextual.SoundnessRefines
import Moist.VerifiedNewNew.DeadLet
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

namespace Moist.VerifiedNewNew.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.VerifiedNewNew (closedAt)
open Moist.VerifiedNewNew.Contextual
  (Context fill closedAt_mono fill_closedAt_iff ObsRefines
   CtxEq CtxRefines
   ctxEq_refl ctxEq_symm ctxEq_trans ctxRefines_refl ctxRefines_trans
   ctxEq_lam ctxEq_delay ctxEq_force ctxEq_app
   ctxEq_constr_one ctxEq_constr ctxEq_case_scrut ctxEq_case_one_alt ctxEq_case
   ctxRefines_lam ctxRefines_delay ctxRefines_force ctxRefines_app
   ctxRefines_constr_one ctxRefines_constr ctxRefines_case_scrut
   ctxRefines_case_one_alt ctxRefines_case)
open Moist.VerifiedNewNew.Equivalence (ObsEq ListRel)
open Moist.VerifiedNewNew.Contextual.Soundness (soundness)
open Moist.VerifiedNewNew.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK OpenRefinesK OpenRefines
   soundness_refines obsRefines_of_openRefines)

/-- Lift `lowerTotal_closedAt` through `lowerTotalExpr`'s extra `expandFix`
    step: if `lowerTotalExpr env e = some t`, then `t` is closed at
    `env.length`. -/
private theorem lowerTotalExpr_closedAt {env : List VarId} {e : Expr} {t : Moist.Plutus.Term.Term}
    (h : lowerTotalExpr env e = some t) : closedAt env.length t = true := by
  simp only [Moist.MIR.lowerTotalExpr] at h
  exact Moist.VerifiedNewNew.DeadLet.lowerTotal_closedAt env (Moist.MIR.expandFix e) t h

--------------------------------------------------------------------------------
-- 1. LIFTING `OpenRefines` TO MIR
--------------------------------------------------------------------------------

/-- Open MIR refinement at step-index `k` and depth `d`. Quantifies over *all*
    `EnvRefinesK`-related environments (no `WellSizedEnv` guard) and uses the
    unidirectional `BehRefinesK ValueRefinesK` from `SoundnessRefines`. -/
def MIROpenRefK (k d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId), env.length = d →
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
        BehRefinesK ValueRefinesK j ρ₁ ρ₂ t₁ t₂
    | _, _ => True

/-- Step-index-free open refinement: holds at every step index. -/
def MIROpenRef (d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ k, MIROpenRefK k d m₁ m₂

/-- MIR-level refinement: compile preservation + `MIROpenRef` at every depth. -/
def MIRRefines (m₁ m₂ : Expr) : Prop :=
  (∀ env, (lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
  ∀ d, MIROpenRef d m₁ m₂

@[inherit_doc]
scoped infix:50 " ⊑ᴹ " => MIRRefines

--------------------------------------------------------------------------------
-- 1b. BASIC PROPERTIES
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
-- The contextual analogues of `MIROpenRef`/`MIRRefines`. Compile-status
-- preservation is universally quantified over variable environments (useful
-- for compositional reasoning), while the contextual observation obligation
-- is pinned to the empty-env lowering — the canonical "fully closed"
-- semantics of a top-level MIR program. Restricting to the empty-env
-- lowering makes the bridge from `MIRRefines` via `soundness_refines_d`
-- fully provable without the `env.length > 0` edge cases that would
-- require preloading the CEK initial env with context binders.
--
-- The compile-status conjuncts make `MIRCtxEq` and `MIRCtxRefines` symmetric
-- and asymmetric respectively in the natural way: equivalence requires both
-- sides to compile or both to fail (under every env); refinement requires
-- that whenever the left compiles, the right does too.
--------------------------------------------------------------------------------

/-- Contextual equivalence of MIR expressions: for every variable
    environment `env`, the two expressions have the same compile status,
    and (when both compile) their lowered UPLC terms are in the `CtxEq`
    relation. The observation clause uses the *same* `env` as the
    compile-status clause — the lowering is sensitive to the env, so
    pinning to `[]` would miss equivalences that only hold under
    non-empty envs. -/
def MIRCtxEq (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId),
    ((lowerTotalExpr env m₁).isSome ↔ (lowerTotalExpr env m₂).isSome) ∧
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => CtxEq t₁ t₂
    | _, _ => True

scoped infix:50 " ≈Ctxᴹ " => MIRCtxEq

/-- Contextual refinement of MIR expressions: for every variable
    environment `env`, compile status is preserved (left compiles → right
    compiles), and (when both compile) the lowered UPLC terms are in the
    strict `CtxRefines` relation (closedness preservation + halt/error
    refinement bundled). -/
def MIRCtxRefines (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId),
    ((lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => CtxRefines t₁ t₂
    | _, _ => True

scoped infix:50 " ⊑Ctxᴹ " => MIRCtxRefines

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
-- 6. MIR-level congruences for `MIRCtxEq`
--
-- Port of the UPLC `ctxEq_*` congruences to the MIR level. For each MIR
-- constructor, we:
--   (a) show how `lowerTotalExpr env` decomposes compositionally, and
--   (b) plug the component-level `CtxEq`s into the corresponding UPLC
--       `ctxEq_*` to get the compound `CtxEq`.
--
-- Only `MIRCtxEq` versions are provided here; the `MIRCtxRefines`
-- counterparts fall out of `mirCtxEq_iff_refines_bidir`.
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

/-! ### 6c. Unary / binary constructor congruences -/

/-- Force congruence for `MIRCtxEq`. -/
theorem mirCtxEq_force {t₁ t₂ : Expr} (h : MIRCtxEq t₁ t₂) :
    MIRCtxEq (.Force t₁) (.Force t₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · -- Compile-status iff via `lowerTotalExpr_force`
    rw [lowerTotalExpr_force, lowerTotalExpr_force]
    simp only [Option.isSome_map]
    exact h.toIff env
  · -- Observation via `ctxEq_force`
    rw [lowerTotalExpr_force, lowerTotalExpr_force]
    cases hlow₁ : lowerTotalExpr env t₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr env t₂ with
      | none =>
        simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxEq_force (h.toCtxEq hlow₁ hlow₂)

/-- Delay congruence for `MIRCtxEq`. -/
theorem mirCtxEq_delay {t₁ t₂ : Expr} (h : MIRCtxEq t₁ t₂) :
    MIRCtxEq (.Delay t₁) (.Delay t₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_delay, lowerTotalExpr_delay]
    simp only [Option.isSome_map]
    exact h.toIff env
  · rw [lowerTotalExpr_delay, lowerTotalExpr_delay]
    cases hlow₁ : lowerTotalExpr env t₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr env t₂ with
      | none =>
        simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxEq_delay (h.toCtxEq hlow₁ hlow₂)

/-- Lambda congruence for `MIRCtxEq`. The hypothesis on `body₁ ≈Ctxᴹ body₂`
    is used under the extended env `(x :: env)`. -/
theorem mirCtxEq_lam {x : VarId} {body₁ body₂ : Expr} (h : MIRCtxEq body₁ body₂) :
    MIRCtxEq (.Lam x body₁) (.Lam x body₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
    simp only [Option.isSome_map]
    exact h.toIff (x :: env)
  · rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
    cases hlow₁ : lowerTotalExpr (x :: env) body₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr (x :: env) body₂ with
      | none =>
        simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxEq_lam 0 (h.toCtxEq hlow₁ hlow₂)

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

/-- Application congruence for `MIRCtxEq`. -/
theorem mirCtxEq_app {f₁ f₂ a₁ a₂ : Expr}
    (hf : MIRCtxEq f₁ f₂) (ha : MIRCtxEq a₁ a₂) :
    MIRCtxEq (.App f₁ a₁) (.App f₂ a₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hlow_f₁ : lowerTotalExpr env f₁ with
    | none =>
      have hn : lowerTotalExpr env f₂ = none := by
        have := hf.toIff env
        rw [hlow_f₁] at this
        cases heq : lowerTotalExpr env f₂
        · rfl
        · rw [heq] at this; exact absurd this.mpr (by simp)
      rw [hn]; simp
    | some t_f₁ =>
      have hsome_f₂ : (lowerTotalExpr env f₂).isSome :=
        (hf.toIff env).mp (by rw [hlow_f₁]; rfl)
      cases hlow_f₂ : lowerTotalExpr env f₂ with
      | none => rw [hlow_f₂] at hsome_f₂; exact absurd hsome_f₂ (by simp)
      | some t_f₂ =>
        cases hlow_a₁ : lowerTotalExpr env a₁ with
        | none =>
          have hn : lowerTotalExpr env a₂ = none := by
            have := ha.toIff env
            rw [hlow_a₁] at this
            cases heq : lowerTotalExpr env a₂
            · rfl
            · rw [heq] at this; exact absurd this.mpr (by simp)
          rw [hn]; simp
        | some t_a₁ =>
          have hsome_a₂ : (lowerTotalExpr env a₂).isSome :=
            (ha.toIff env).mp (by rw [hlow_a₁]; rfl)
          cases hlow_a₂ : lowerTotalExpr env a₂ with
          | none => rw [hlow_a₂] at hsome_a₂; exact absurd hsome_a₂ (by simp)
          | some t_a₂ => simp
  · rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hlow_f₁ : lowerTotalExpr env f₁ with
    | none => simp
    | some tf₁ =>
      cases hlow_f₂ : lowerTotalExpr env f₂ with
      | none => simp
      | some tf₂ =>
        cases hlow_a₁ : lowerTotalExpr env a₁ with
        | none => simp
        | some ta₁ =>
          cases hlow_a₂ : lowerTotalExpr env a₂ with
          | none => simp
          | some ta₂ =>
            show CtxEq (.Apply tf₁ ta₁) (.Apply tf₂ ta₂)
            exact ctxEq_app (hf.toCtxEq hlow_f₁ hlow_f₂)
                            (ha.toCtxEq hlow_a₁ hlow_a₂)

/-! ### 6e. Constr / Case congruences -/

/-- `lowerTotalExpr` on `.Constr` in terms of `lowerTotalExprList`. -/
private theorem lowerTotalExpr_constr_of_list (env : List VarId) (tag : Nat)
    (args : List Expr) :
    lowerTotalExpr env (.Constr tag args) =
      (lowerTotalExprList env args).map (.Constr tag) := by
  rw [lowerTotalExpr_constr]; rfl

/-- `lowerTotalExpr` on `.Case` in terms of `lowerTotalExprList`. -/
private theorem lowerTotalExpr_case_of_list (env : List VarId) (scrut : Expr)
    (alts : List Expr) :
    lowerTotalExpr env (.Case scrut alts) =
      (do let s ← lowerTotalExpr env scrut
          let a ← lowerTotalExprList env alts
          some (.Case s a)) := by
  rw [lowerTotalExpr_case]; rfl

/-- Constr congruence for `MIRCtxEq`. Takes the head-tail split (matching
    `ctxEq_constr`). -/
theorem mirCtxEq_constr {tag : Nat} {m₁ m₂ : Expr} {ms₁ ms₂ : List Expr}
    (hm : MIRCtxEq m₁ m₂) (hms : ListRel MIRCtxEq ms₁ ms₂) :
    MIRCtxEq (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  intro env
  have hrel : ListRel MIRCtxEq (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have hlist_iff := listRel_mirCtxEq_isSome_iff hrel env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    simp only [Option.isSome_map]
    exact hlist_iff
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    cases hlow₁ : lowerTotalExprList env (m₁ :: ms₁) with
    | none => simp
    | some ts₁ =>
      cases hlow₂ : lowerTotalExprList env (m₂ :: ms₂) with
      | none => simp
      | some ts₂ =>
        show CtxEq (.Constr tag ts₁) (.Constr tag ts₂)
        -- From ts₁ = t_m₁ :: t_ms₁ and ts₂ = t_m₂ :: t_ms₂, recover via
        -- the list-level relation and apply ctxEq_constr.
        rw [lowerTotalExprList_cons] at hlow₁ hlow₂
        cases ht_m₁ : lowerTotalExpr env m₁ with
        | none => rw [ht_m₁] at hlow₁; simp at hlow₁
        | some t_m₁ =>
          cases ht_ms₁ : lowerTotalExprList env ms₁ with
          | none => rw [ht_m₁, ht_ms₁] at hlow₁; simp at hlow₁
          | some t_ms₁ =>
            cases ht_m₂ : lowerTotalExpr env m₂ with
            | none => rw [ht_m₂] at hlow₂; simp at hlow₂
            | some t_m₂ =>
              cases ht_ms₂ : lowerTotalExprList env ms₂ with
              | none => rw [ht_m₂, ht_ms₂] at hlow₂; simp at hlow₂
              | some t_ms₂ =>
                rw [ht_m₁, ht_ms₁] at hlow₁
                rw [ht_m₂, ht_ms₂] at hlow₂
                cases hlow₁; cases hlow₂
                exact ctxEq_constr (hm.toCtxEq ht_m₁ ht_m₂)
                  (listRel_mirCtxEq_toListCtxEq hms ht_ms₁ ht_ms₂)

/-- Case scrutinee-swap congruence for `MIRCtxEq`. -/
theorem mirCtxEq_case_scrut {scrut₁ scrut₂ : Expr} {alts : List Expr}
    (hscrut : MIRCtxEq scrut₁ scrut₂) :
    MIRCtxEq (.Case scrut₁ alts) (.Case scrut₂ alts) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases hlow_s₁ : lowerTotalExpr env scrut₁ with
    | none =>
      have hn : lowerTotalExpr env scrut₂ = none := by
        cases heq : lowerTotalExpr env scrut₂
        · rfl
        · exfalso
          have : (lowerTotalExpr env scrut₁).isSome :=
            (hscrut.toIff env).mpr (by rw [heq]; rfl)
          rw [hlow_s₁] at this; exact absurd this (by simp)
      rw [hn]
    | some ts₁ =>
      have hsome_s₂ : (lowerTotalExpr env scrut₂).isSome :=
        (hscrut.toIff env).mp (by rw [hlow_s₁]; rfl)
      cases hlow_s₂ : lowerTotalExpr env scrut₂ with
      | none => rw [hlow_s₂] at hsome_s₂; exact absurd hsome_s₂ (by simp)
      | some ts₂ =>
        cases hlow_alts : lowerTotalExprList env alts with
        | none => simp
        | some t_alts => simp
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases hlow_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some ts₁ =>
      cases hlow_s₂ : lowerTotalExpr env scrut₂ with
      | none => simp
      | some ts₂ =>
        cases hlow_alts : lowerTotalExprList env alts with
        | none => simp
        | some t_alts =>
          show CtxEq (.Case ts₁ t_alts) (.Case ts₂ t_alts)
          exact ctxEq_case_scrut (hscrut.toCtxEq hlow_s₁ hlow_s₂)

/-- Case alts-list congruence for `MIRCtxEq` (fixed scrutinee). -/
theorem mirCtxEq_case_alts {scrut : Expr} {alts₁ alts₂ : List Expr}
    (halts : ListRel MIRCtxEq alts₁ alts₂) :
    MIRCtxEq (.Case scrut alts₁) (.Case scrut alts₂) := by
  intro env
  have halts_iff := listRel_mirCtxEq_isSome_iff halts env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases hlow_s : lowerTotalExpr env scrut with
    | none => simp
    | some ts =>
      cases hlow_a₁ : lowerTotalExprList env alts₁ with
      | none =>
        have hn : lowerTotalExprList env alts₂ = none := by
          cases heq : lowerTotalExprList env alts₂
          · rfl
          · exfalso
            have : (lowerTotalExprList env alts₁).isSome :=
              halts_iff.mpr (by rw [heq]; rfl)
            rw [hlow_a₁] at this; exact absurd this (by simp)
        rw [hn]
      | some t_a₁ =>
        have hsome_a₂ : (lowerTotalExprList env alts₂).isSome :=
          halts_iff.mp (by rw [hlow_a₁]; rfl)
        cases hlow_a₂ : lowerTotalExprList env alts₂ with
        | none => rw [hlow_a₂] at hsome_a₂; exact absurd hsome_a₂ (by simp)
        | some t_a₂ => simp
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases hlow_s : lowerTotalExpr env scrut with
    | none => simp
    | some ts =>
      cases hlow_a₁ : lowerTotalExprList env alts₁ with
      | none => simp
      | some t_a₁ =>
        cases hlow_a₂ : lowerTotalExprList env alts₂ with
        | none => simp
        | some t_a₂ =>
          show CtxEq (.Case ts t_a₁) (.Case ts t_a₂)
          -- Build CtxEq via `ctxEq_case` with scrut reflexivity on the UPLC side.
          -- We need `ListRel CtxEq t_a₁ t_a₂`.
          have hlist_ctx : ListRel CtxEq t_a₁ t_a₂ :=
            listRel_mirCtxEq_toListCtxEq halts hlow_a₁ hlow_a₂
          -- ctxEq_case requires CtxEq on the scrutinee too; use reflexivity.
          exact ctxEq_case (Contextual.ctxEq_refl ts) hlist_ctx

/-- General Case congruence for `MIRCtxEq`: swap both the scrutinee and the
    alts list. Composes `mirCtxEq_case_scrut` and `mirCtxEq_case_alts` via
    `mirCtxEq_trans` (which requires a middle-closedness side condition). -/
theorem mirCtxEq_case {scrut₁ scrut₂ : Expr} {alts₁ alts₂ : List Expr}
    (hscrut : MIRCtxEq scrut₁ scrut₂)
    (halts : ListRel MIRCtxEq alts₁ alts₂) :
    MIRCtxEq (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · -- compile-status iff via chained iff's
    rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    have h_scrut_iff := hscrut.toIff env
    have h_alts_iff := listRel_mirCtxEq_isSome_iff halts env
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none =>
      have hn : lowerTotalExpr env scrut₂ = none := by
        cases heq : lowerTotalExpr env scrut₂
        · rfl
        · exfalso
          have : (lowerTotalExpr env scrut₁).isSome :=
            h_scrut_iff.mpr (by rw [heq]; rfl)
          rw [h_s₁] at this; exact absurd this (by simp)
      rw [hn]; simp
    | some _ =>
      have : (lowerTotalExpr env scrut₂).isSome := h_scrut_iff.mp (by rw [h_s₁]; rfl)
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => rw [h_s₂] at this; exact absurd this (by simp)
      | some _ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none =>
          have hn : lowerTotalExprList env alts₂ = none := by
            cases heq : lowerTotalExprList env alts₂
            · rfl
            · exfalso
              have : (lowerTotalExprList env alts₁).isSome :=
                h_alts_iff.mpr (by rw [heq]; rfl)
              rw [h_a₁] at this; exact absurd this (by simp)
          rw [hn]; simp
        | some _ =>
          have : (lowerTotalExprList env alts₂).isSome :=
            h_alts_iff.mp (by rw [h_a₁]; rfl)
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => rw [h_a₂] at this; exact absurd this (by simp)
          | some _ => simp
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some ts₁ =>
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => simp
      | some ts₂ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some t_a₁ =>
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => simp
          | some t_a₂ =>
            show CtxEq (.Case ts₁ t_a₁) (.Case ts₂ t_a₂)
            have hlist_ctx : ListRel CtxEq t_a₁ t_a₂ :=
              listRel_mirCtxEq_toListCtxEq halts h_a₁ h_a₂
            exact ctxEq_case (hscrut.toCtxEq h_s₁ h_s₂) hlist_ctx

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

/-! ### 7b. Unary / binary constructor congruences -/

/-- Force congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_force {t₁ t₂ : Expr} (h : MIRCtxRefines t₁ t₂) :
    MIRCtxRefines (.Force t₁) (.Force t₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_force, lowerTotalExpr_force]
    simp only [Option.isSome_map]
    exact h.toImp env
  · rw [lowerTotalExpr_force, lowerTotalExpr_force]
    cases hlow₁ : lowerTotalExpr env t₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr env t₂ with
      | none => simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxRefines_force (h.toCtxRefines hlow₁ hlow₂)

/-- Delay congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_delay {t₁ t₂ : Expr} (h : MIRCtxRefines t₁ t₂) :
    MIRCtxRefines (.Delay t₁) (.Delay t₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_delay, lowerTotalExpr_delay]
    simp only [Option.isSome_map]
    exact h.toImp env
  · rw [lowerTotalExpr_delay, lowerTotalExpr_delay]
    cases hlow₁ : lowerTotalExpr env t₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr env t₂ with
      | none => simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxRefines_delay (h.toCtxRefines hlow₁ hlow₂)

/-- Lambda congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_lam {x : VarId} {body₁ body₂ : Expr} (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Lam x body₁) (.Lam x body₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
    simp only [Option.isSome_map]
    exact h.toImp (x :: env)
  · rw [lowerTotalExpr_lam, lowerTotalExpr_lam]
    cases hlow₁ : lowerTotalExpr (x :: env) body₁ with
    | none => simp [Option.map]
    | some u₁ =>
      cases hlow₂ : lowerTotalExpr (x :: env) body₂ with
      | none => simp only [Option.map_some, Option.map_none]
      | some u₂ =>
        simp only [Option.map_some]
        exact ctxRefines_lam 0 (h.toCtxRefines hlow₁ hlow₂)

/-- Application congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_app {f₁ f₂ a₁ a₂ : Expr}
    (hf : MIRCtxRefines f₁ f₂) (ha : MIRCtxRefines a₁ a₂) :
    MIRCtxRefines (.App f₁ a₁) (.App f₂ a₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hlow_f₁ : lowerTotalExpr env f₁ with
    | none => simp
    | some t_f₁ =>
      have hsome_f₂ : (lowerTotalExpr env f₂).isSome :=
        hf.toImp env (by rw [hlow_f₁]; rfl)
      cases hlow_f₂ : lowerTotalExpr env f₂ with
      | none => rw [hlow_f₂] at hsome_f₂; exact absurd hsome_f₂ (by simp)
      | some t_f₂ =>
        cases hlow_a₁ : lowerTotalExpr env a₁ with
        | none => simp
        | some t_a₁ =>
          have hsome_a₂ : (lowerTotalExpr env a₂).isSome :=
            ha.toImp env (by rw [hlow_a₁]; rfl)
          cases hlow_a₂ : lowerTotalExpr env a₂ with
          | none => rw [hlow_a₂] at hsome_a₂; exact absurd hsome_a₂ (by simp)
          | some t_a₂ => simp
  · rw [lowerTotalExpr_app, lowerTotalExpr_app]
    cases hlow_f₁ : lowerTotalExpr env f₁ with
    | none => simp
    | some tf₁ =>
      cases hlow_f₂ : lowerTotalExpr env f₂ with
      | none => simp
      | some tf₂ =>
        cases hlow_a₁ : lowerTotalExpr env a₁ with
        | none => simp
        | some ta₁ =>
          cases hlow_a₂ : lowerTotalExpr env a₂ with
          | none => simp
          | some ta₂ =>
            show CtxRefines (.Apply tf₁ ta₁) (.Apply tf₂ ta₂)
            exact ctxRefines_app (hf.toCtxRefines hlow_f₁ hlow_f₂)
                                 (ha.toCtxRefines hlow_a₁ hlow_a₂)

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

/-! ### 7d. Constr / Case congruences for `MIRCtxRefines` -/

/-- Constr congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_constr {tag : Nat} {m₁ m₂ : Expr} {ms₁ ms₂ : List Expr}
    (hm : MIRCtxRefines m₁ m₂) (hms : ListRel MIRCtxRefines ms₁ ms₂) :
    MIRCtxRefines (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  intro env
  have hrel : ListRel MIRCtxRefines (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have hlist_imp := listRel_mirCtxRefines_isSome_imp hrel env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    simp only [Option.isSome_map]
    exact hlist_imp
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    cases hlow₁ : lowerTotalExprList env (m₁ :: ms₁) with
    | none => simp
    | some ts₁ =>
      cases hlow₂ : lowerTotalExprList env (m₂ :: ms₂) with
      | none => simp
      | some ts₂ =>
        show CtxRefines (.Constr tag ts₁) (.Constr tag ts₂)
        rw [lowerTotalExprList_cons] at hlow₁ hlow₂
        cases ht_m₁ : lowerTotalExpr env m₁ with
        | none => rw [ht_m₁] at hlow₁; simp at hlow₁
        | some t_m₁ =>
          cases ht_ms₁ : lowerTotalExprList env ms₁ with
          | none => rw [ht_m₁, ht_ms₁] at hlow₁; simp at hlow₁
          | some t_ms₁ =>
            cases ht_m₂ : lowerTotalExpr env m₂ with
            | none => rw [ht_m₂] at hlow₂; simp at hlow₂
            | some t_m₂ =>
              cases ht_ms₂ : lowerTotalExprList env ms₂ with
              | none => rw [ht_m₂, ht_ms₂] at hlow₂; simp at hlow₂
              | some t_ms₂ =>
                rw [ht_m₁, ht_ms₁] at hlow₁
                rw [ht_m₂, ht_ms₂] at hlow₂
                cases hlow₁; cases hlow₂
                exact ctxRefines_constr (hm.toCtxRefines ht_m₁ ht_m₂)
                  (listRel_mirCtxRefines_toListCtxRefines hms ht_ms₁ ht_ms₂)

/-- General Case congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_case {scrut₁ scrut₂ : Expr} {alts₁ alts₂ : List Expr}
    (hscrut : MIRCtxRefines scrut₁ scrut₂)
    (halts : ListRel MIRCtxRefines alts₁ alts₂) :
    MIRCtxRefines (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    have h_scrut_imp := hscrut.toImp env
    have h_alts_imp := listRel_mirCtxRefines_isSome_imp halts env
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some _ =>
      have : (lowerTotalExpr env scrut₂).isSome := h_scrut_imp (by rw [h_s₁]; rfl)
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => rw [h_s₂] at this; exact absurd this (by simp)
      | some _ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some _ =>
          have : (lowerTotalExprList env alts₂).isSome := h_alts_imp (by rw [h_a₁]; rfl)
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => rw [h_a₂] at this; exact absurd this (by simp)
          | some _ => simp
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some ts₁ =>
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => simp
      | some ts₂ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some t_a₁ =>
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => simp
          | some t_a₂ =>
            show CtxRefines (.Case ts₁ t_a₁) (.Case ts₂ t_a₂)
            have hlist_ctx : ListRel CtxRefines t_a₁ t_a₂ :=
              listRel_mirCtxRefines_toListCtxRefines halts h_a₁ h_a₂
            exact ctxRefines_case (hscrut.toCtxRefines h_s₁ h_s₂) hlist_ctx

/-! ### 7d. Fix-Lam congruence for `MIRCtxRefines`

The Fix-Lam case leverages the canonical form lemma
`lowerTotalExpr_fix_lam_with_fresh` to factor both sides through a common
fresh `s` variable, then applies UPLC-level congruences to lift through
the Z-combinator wrapper.
-/

/-- Fix-Lam congruence for `MIRCtxRefines`. The Z combinator expansion
    produces a fixed UPLC wrapper around the inner body lowering; the
    congruence follows by picking a common fresh variable and applying
    Apply/Lam congruences through the wrapper. -/
theorem mirCtxRefines_fix_lam {f x : VarId} {body₁ body₂ : Expr}
    (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Fix f (.Lam x body₁)) (.Fix f (.Lam x body₂)) := by
  intro env
  -- Canonical fresh `s` variable that avoids both expanded bodies
  let body₁' := Moist.MIR.expandFix body₁
  let body₂' := Moist.MIR.expandFix body₂
  let s_common : VarId :=
    ⟨max (Moist.MIR.maxUidExpr body₁') (Moist.MIR.maxUidExpr body₂') + 1, "s"⟩
  have hs₁ : (Moist.MIR.freeVars body₁').contains s_common = false :=
    Moist.MIR.maxUidExpr_fresh body₁' s_common (by simp [s_common]; omega)
  have hs₂ : (Moist.MIR.freeVars body₂').contains s_common = false :=
    Moist.MIR.maxUidExpr_fresh body₂' s_common (by simp [s_common]; omega)
  -- Both sides reduce to a map over `lowerTotal (x :: f :: s_common :: env) body_i'`
  have hlhs : lowerTotalExpr env (.Fix f (.Lam x body₁)) =
      (Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₁').map
        Moist.MIR.fixLamWrapUplc :=
    Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x body₁ s_common hs₁
  have hrhs : lowerTotalExpr env (.Fix f (.Lam x body₂)) =
      (Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₂').map
        Moist.MIR.fixLamWrapUplc :=
    Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x body₂ s_common hs₂
  -- Apply IH at the common env
  have ih := h (x :: f :: s_common :: env)
  refine ⟨?_, ?_⟩
  · -- isSome part (implication)
    rw [hlhs, hrhs]
    simp only [Option.isSome_map]
    -- Goal: (lowerTotal ... body₁').isSome → (lowerTotal ... body₂').isSome
    -- lowerTotal env' body_i' = lowerTotalExpr env' body_i by definition
    exact ih.1
  · -- CtxRefines part
    rw [hlhs, hrhs]
    cases hb₁ : Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₁' with
    | none => simp
    | some t₁ =>
      cases hb₂ : Moist.MIR.lowerTotal (x :: f :: s_common :: env) body₂' with
      | none => simp
      | some t₂ =>
        simp only [Option.map_some]
        -- Get CtxRefines t₁ t₂ from ih (by definition lowerTotalExpr unfolds to lowerTotal ∘ expandFix)
        have hlow₁ : lowerTotalExpr (x :: f :: s_common :: env) body₁ = some t₁ := hb₁
        have hlow₂ : lowerTotalExpr (x :: f :: s_common :: env) body₂ = some t₂ := hb₂
        have hctx : CtxRefines t₁ t₂ := h.toCtxRefines hlow₁ hlow₂
        -- Lift through the UPLC wrapper using Apply/Lam congruences
        -- fixLamWrapUplc b =
        --   .Apply (.Lam 0 (.Apply (.Var 1) (.Var 1)))
        --          (.Lam 0 (.Apply (.Lam 0 (.Lam 0 b))
        --                          (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))))
        show CtxRefines (Moist.MIR.fixLamWrapUplc t₁) (Moist.MIR.fixLamWrapUplc t₂)
        unfold Moist.MIR.fixLamWrapUplc
        -- Build the congruence step by step
        have h_inner : CtxRefines
            (Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₁))
            (Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₂)) :=
          ctxRefines_lam 0 (ctxRefines_lam 0 hctx)
        have h_fixed_refl : CtxRefines
            (Moist.Plutus.Term.Term.Lam 0
              (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                (Moist.Plutus.Term.Term.Var 1)))
            (Moist.Plutus.Term.Term.Lam 0
              (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                (Moist.Plutus.Term.Term.Var 1))) :=
          ctxRefines_refl _
        have h_app_inner : CtxRefines
            ((Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₁)).Apply
              (Moist.Plutus.Term.Term.Lam 0
                (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                  (Moist.Plutus.Term.Term.Var 1))))
            ((Moist.Plutus.Term.Term.Lam 0 (Moist.Plutus.Term.Term.Lam 0 t₂)).Apply
              (Moist.Plutus.Term.Term.Lam 0
                (((Moist.Plutus.Term.Term.Var 2).Apply (Moist.Plutus.Term.Term.Var 2)).Apply
                  (Moist.Plutus.Term.Term.Var 1)))) :=
          ctxRefines_app h_inner h_fixed_refl
        have h_lam_outer := ctxRefines_lam 0 h_app_inner
        have h_z_refl : CtxRefines
            (Moist.Plutus.Term.Term.Lam 0
              ((Moist.Plutus.Term.Term.Var 1).Apply (Moist.Plutus.Term.Term.Var 1)))
            (Moist.Plutus.Term.Term.Lam 0
              ((Moist.Plutus.Term.Term.Var 1).Apply (Moist.Plutus.Term.Term.Var 1))) :=
          ctxRefines_refl _
        exact ctxRefines_app h_z_refl h_lam_outer

end Moist.VerifiedNewNew.MIR
