import Moist.VerifiedNewNew.Equivalence
import Moist.VerifiedNewNew.Rename
import Moist.VerifiedNewNew.Contextual
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
open Moist.VerifiedNewNew.Contextual (Context fill closedAt_mono fill_closedAt_iff ObsRefines)
open Moist.VerifiedNewNew.Equivalence (ObsEq)
open Moist.VerifiedNewNew.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK OpenRefinesK OpenRefines
   soundness_refines_d)

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

/-- Contextual equivalence of MIR expressions: compile status agrees under
    every variable environment, and (when both compile under the empty env)
    the closed lowered UPLC terms are observationally equivalent under any
    closing context. -/
def MIRCtxEq (m₁ m₂ : Expr) : Prop :=
  (∀ (env : List VarId),
    (lowerTotalExpr env m₁).isSome ↔ (lowerTotalExpr env m₂).isSome) ∧
  match lowerTotalExpr [] m₁, lowerTotalExpr [] m₂ with
  | some t₁, some t₂ =>
    ∀ (C : Context),
      closedAt 0 (fill C t₁) = true →
      closedAt 0 (fill C t₂) = true →
      ObsEq (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂))
  | _, _ => True

scoped infix:50 " ≈Ctxᴹ " => MIRCtxEq

/-- Contextual refinement of MIR expressions: compile preservation under
    every variable environment, and (when both compile under the empty env)
    halt/error refinement of the closed lowered UPLC terms under any closing
    context. -/
def MIRCtxRefines (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId),
    ((lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
  match lowerTotalExpr env m₁, lowerTotalExpr [] m₂ with
  | some t₁, some t₂ =>
    ∀ (C : Context),
      closedAt 0 (fill C t₁) = true →
      closedAt 0 (fill C t₂) = true →
      ObsRefines (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂))
  | _, _ => True

scoped infix:50 " ⊑Ctxᴹ " => MIRCtxRefines

--------------------------------------------------------------------------------
-- 3. BASIC PROPERTIES OF MIRCtxEq / MIRCtxRefines
--------------------------------------------------------------------------------

/-- Middle-closedness bridge: given closedness of `fill C t₁` at depth 0 and
    a lowering `lowerTotalExpr [] m₂ = some t₂` (so `t₂` is closed at 0),
    `fill C t₂` is also closed at depth 0. Used in the transitivity proofs
    of both `mirCtxEq_trans` and `mirCtxRefines_trans`. -/
private theorem mir_fill_closed_mid {m₂ : Expr}
    {t₁ t₂ : Moist.Plutus.Term.Term} {C : Context}
    (h₂ : lowerTotalExpr [] m₂ = some t₂)
    (hC1 : closedAt 0 (fill C t₁) = true) :
    closedAt 0 (fill C t₂) = true := by
  have hd_t₂ : closedAt ([] : List VarId).length t₂ = true := lowerTotalExpr_closedAt h₂
  have hCb_t₂ : closedAt C.binders t₂ = true := closedAt_mono hd_t₂ (Nat.zero_le _)
  have hC_outer : Context.closedAt 0 C = true := ((fill_closedAt_iff C t₁ 0).mp hC1).1
  exact (fill_closedAt_iff C t₂ 0).mpr ⟨hC_outer, by simpa [Nat.zero_add] using hCb_t₂⟩

/-- Reflexivity of `MIRCtxRefines`. -/
theorem mirCtxRefines_refl (m : Expr) : MIRCtxRefines m m := by
  refine ⟨fun _ => id, ?_⟩
  cases h : lowerTotalExpr [] m with
  | none => trivial
  | some _ =>
    intro _ _ _
    exact ObsRefines.mk (fun h => h) (fun h => h)

/-- Transitivity of `MIRCtxRefines`. -/
theorem mirCtxRefines_trans {m₁ m₂ m₃ : Expr} :
    MIRCtxRefines m₁ m₂ → MIRCtxRefines m₂ m₃ → MIRCtxRefines m₁ m₃ := by
  intro h12 h23
  obtain ⟨hsome12, hctx12⟩ := h12
  obtain ⟨hsome23, hctx23⟩ := h23
  refine ⟨fun env => hsome23 env ∘ hsome12 env, ?_⟩
  cases h₁ : lowerTotalExpr [] m₁ with
  | none => trivial
  | some t₁ =>
    cases h₃ : lowerTotalExpr [] m₃ with
    | none => trivial
    | some t₃ =>
      have hsome2 : (lowerTotalExpr [] m₂).isSome := hsome12 [] (by rw [h₁]; trivial)
      cases h₂ : lowerTotalExpr [] m₂ with
      | none => rw [h₂] at hsome2; exact absurd hsome2 (by simp)
      | some t₂ =>
        rw [h₁, h₂] at hctx12; rw [h₂, h₃] at hctx23
        intro C hC1 hC3
        have hC2 := mir_fill_closed_mid h₂ hC1
        have r12 := hctx12 C hC1 hC2
        have r23 := hctx23 C hC2 hC3
        exact ObsRefines.mk
          (fun h_t1 => r23.halt (r12.halt h_t1))
          (fun h_t1 => r23.error (r12.error h_t1))

/-- Reflexivity of `MIRCtxEq`. -/
theorem mirCtxEq_refl (m : Expr) : MIRCtxEq m m := by
  refine ⟨fun _ => Iff.rfl, ?_⟩
  cases h : lowerTotalExpr [] m with
  | none => trivial
  | some _ =>
    intro _ _ _
    exact ObsEq.mk Iff.rfl Iff.rfl

/-- Symmetry of `MIRCtxEq`. -/
theorem mirCtxEq_symm {m₁ m₂ : Expr} :
    MIRCtxEq m₁ m₂ → MIRCtxEq m₂ m₁ := by
  intro h
  obtain ⟨hiff, hctx⟩ := h
  refine ⟨fun env => (hiff env).symm, ?_⟩
  cases h₁ : lowerTotalExpr [] m₁ with
  | none =>
    cases h₂ : lowerTotalExpr [] m₂ with
    | none => trivial
    | some _ => trivial
  | some t₁ =>
    cases h₂ : lowerTotalExpr [] m₂ with
    | none => trivial
    | some t₂ =>
      rw [h₁, h₂] at hctx
      intro C hC2 hC1
      have obs := hctx C hC1 hC2
      exact ObsEq.mk obs.halt.symm obs.error.symm

/-- Transitivity of `MIRCtxEq`. Uses `mir_fill_closed_mid` to discharge the
    middle-term closedness side condition via `lowerTotalExpr_closedAt` +
    `closedAt_mono`. -/
theorem mirCtxEq_trans {m₁ m₂ m₃ : Expr} :
    MIRCtxEq m₁ m₂ → MIRCtxEq m₂ m₃ → MIRCtxEq m₁ m₃ := by
  intro h12 h23
  obtain ⟨hiff12, hctx12⟩ := h12
  obtain ⟨hiff23, hctx23⟩ := h23
  refine ⟨fun env => (hiff12 env).trans (hiff23 env), ?_⟩
  cases h₁ : lowerTotalExpr [] m₁ with
  | none => trivial
  | some t₁ =>
    cases h₃ : lowerTotalExpr [] m₃ with
    | none => trivial
    | some t₃ =>
      have hsome2 : (lowerTotalExpr [] m₂).isSome := (hiff12 []).mp (by rw [h₁]; trivial)
      cases h₂ : lowerTotalExpr [] m₂ with
      | none => rw [h₂] at hsome2; exact absurd hsome2 (by simp)
      | some t₂ =>
        rw [h₁, h₂] at hctx12; rw [h₂, h₃] at hctx23
        intro C hC1 hC3
        have hC2 := mir_fill_closed_mid h₂ hC1
        have eq12 := hctx12 C hC1 hC2
        have eq23 := hctx23 C hC2 hC3
        exact ObsEq.mk (Iff.trans eq12.halt eq23.halt) (Iff.trans eq12.error eq23.error)

--------------------------------------------------------------------------------
-- 4. MIRCtxEq ↔ bidirectional MIRCtxRefines
--------------------------------------------------------------------------------

theorem mirCtxEq_iff_refines_bidir {m₁ m₂ : Expr} :
    MIRCtxEq m₁ m₂ ↔ MIRCtxRefines m₁ m₂ ∧ MIRCtxRefines m₂ m₁ := by
  constructor
  · -- (⇒) MIRCtxEq → bidirectional MIRCtxRefines
    intro h
    obtain ⟨hiff, hctx⟩ := h
    refine ⟨?_, ?_⟩
    · refine ⟨fun env => (hiff env).mp, ?_⟩
      cases h₁ : lowerTotalExpr [] m₁ with
      | none => trivial
      | some t₁ =>
        cases h₂ : lowerTotalExpr [] m₂ with
        | none => trivial
        | some t₂ =>
          rw [h₁, h₂] at hctx
          intro C hC1 hC2
          have obs := hctx C hC1 hC2
          exact ObsRefines.mk obs.halt.mp obs.error.mp
    · refine ⟨fun env => (hiff env).mpr, ?_⟩
      cases h₂ : lowerTotalExpr [] m₂ with
      | none => trivial
      | some t₂ =>
        cases h₁ : lowerTotalExpr [] m₁ with
        | none => trivial
        | some t₁ =>
          rw [h₁, h₂] at hctx
          intro C hC2 hC1
          have obs := hctx C hC1 hC2
          exact ObsRefines.mk obs.halt.mpr obs.error.mpr
  · -- (⇐) bidirectional MIRCtxRefines → MIRCtxEq
    intro ⟨h12, h21⟩
    obtain ⟨hsome12, hctx12⟩ := h12
    obtain ⟨hsome21, hctx21⟩ := h21
    refine ⟨fun env => ⟨hsome12 env, hsome21 env⟩, ?_⟩
    cases h₁ : lowerTotalExpr [] m₁ with
    | none =>
      cases h₂ : lowerTotalExpr [] m₂ with
      | none => trivial
      | some _ => trivial
    | some t₁ =>
      cases h₂ : lowerTotalExpr [] m₂ with
      | none => trivial
      | some t₂ =>
        rw [h₁, h₂] at hctx12; rw [h₁, h₂] at hctx21
        intro C hC1 hC2
        have ref12 := hctx12 C hC1 hC2
        have ref21 := hctx21 C hC2 hC1
        exact ObsEq.mk
          (Iff.intro ref12.halt ref21.halt)
          (Iff.intro ref12.error ref21.error)

--------------------------------------------------------------------------------
-- 5. BRIDGE: `MIRRefines` → `MIRCtxRefines`.
--
-- `MIRRefines` is unidirectional and provides `MIROpenRef d` at every
-- depth. The compile-preservation conjunct comes directly from `h.1`.
-- For the closed-lowering observation conjunct we extract `MIROpenRef 0`,
-- derive `OpenRefines 0` on the empty-env lowerings, and feed it through
-- `soundness_refines_d` to obtain unconditional `ObsRefines` under any
-- closing context. Because `MIRCtxRefines` pins its observation clause
-- to the empty env, no further case analysis is needed.
--------------------------------------------------------------------------------

/-- From `MIRRefines m₁ m₂` to `MIRCtxRefines m₁ m₂`, via
    `soundness_refines_d`. -/
theorem mirRefines_to_mirCtxRefines {m₁ m₂ : Expr} (h : MIRRefines m₁ m₂) :
    MIRCtxRefines m₁ m₂ := by
  refine ⟨h.1, ?_⟩
  cases hlow₁ : lowerTotalExpr [] m₁ with
  | none => trivial
  | some t₁ =>
    cases hlow₂ : lowerTotalExpr [] m₂ with
    | none => trivial
    | some t₂ =>
      intro C _hC1 _hC2
      have hopenRef : MIROpenRef 0 m₁ m₂ := h.2 0
      have h_open : OpenRefines 0 t₁ t₂ := by
        intro k j hj ρ₁ ρ₂ henv
        have := hopenRef k [] rfl
        rw [hlow₁, hlow₂] at this
        exact this j hj ρ₁ ρ₂ henv
      exact soundness_refines_d h_open C

end Moist.VerifiedNewNew.MIR
