import Moist.VerifiedNewNew.Equivalence
import Moist.VerifiedNewNew.Rename
import Moist.VerifiedNewNew.Contextual
import Moist.VerifiedNewNew.Contextual.SoundnessRefines
import Moist.MIR.LowerTotal

/-! # MIR-Level Equivalence and Refinement

Lifts the unidirectional step-indexed logical relation from UPLC terms
(defined in `Contextual/SoundnessRefines.lean`) to MIR expressions via
`lowerTotalExpr`.

The relations `MIROpenRefK` / `MIROpenRef` / `MIRRefines` quantify over
arbitrary environments (no `WellSizedEnv` guard) and are unidirectional
(refinement, not equivalence). They plug directly into
`soundness_refines_d` to yield `CtxRefines` on the lowered terms at
arbitrary depth — giving a clean `MIRRefines → MIRCtxRefines d` bridge
via `MIRCongruence.mirRefines_to_mirCtxRefines`.
-/

namespace Moist.VerifiedNewNew.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.VerifiedNewNew.Contextual (CtxEq CtxRefines ctxRefines_refl ctxRefines_trans
  ctxRefines_antisymm)
open Moist.VerifiedNewNew.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK OpenRefinesK OpenRefines
   soundness_refines_d)

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
-- 2. CONTEXTUAL EQUIVALENCE & REFINEMENT (lifted from UPLC `CtxEq`/`CtxRefines`)
--
-- The contextual analogues of `MIROpenRef`/`MIRRefines`. These:
--
--   * obtain composability through `Iff.trans` rather than EnvEqK plumbing,
--   * are equivalent (via `Iff.intro`) to bidirectional `MIRCtxRefines`, and
--   * sit on top of `Moist.VerifiedNewNew.Contextual`'s open-context
--     `CtxEq`/`CtxRefines`.
--
-- The compile-status conjuncts make `MIRCtxEq` and `MIRCtxRefines` symmetric
-- and asymmetric respectively in the natural way: equivalence requires both
-- sides to compile or both to fail; refinement requires that whenever the
-- left compiles, the right does too.
--------------------------------------------------------------------------------

/-- Contextual equivalence of MIR expressions: under every variable
    environment of length `d`, both expressions either both compile or both
    fail, and (when both compile) the lowered UPLC terms are `CtxEq`. -/
def MIRCtxEq (d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId), env.length = d →
    ((lowerTotalExpr env m₁).isSome ↔ (lowerTotalExpr env m₂).isSome) ∧
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => CtxEq t₁ t₂
    | _, _ => True

scoped infix:50 " ≈Ctxᴹ " => MIRCtxEq

/-- Contextual refinement of MIR expressions: under every variable
    environment of length `d`, if `m₁` compiles then `m₂` compiles, and (when
    both compile) the lowered UPLC terms satisfy `CtxRefines`. -/
def MIRCtxRefines (d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId), env.length = d →
    ((lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => CtxRefines t₁ t₂
    | _, _ => True

scoped infix:50 " ⊑Ctxᴹ " => MIRCtxRefines

--------------------------------------------------------------------------------
-- 3. BASIC PROPERTIES OF MIRCtxEq / MIRCtxRefines
--------------------------------------------------------------------------------

/-- Reflexivity of `MIRCtxRefines`. -/
theorem mirCtxRefines_refl (d : Nat) (m : Expr) : MIRCtxRefines d m m := by
  intro env _
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env m
  · trivial
  · exact ctxRefines_refl _

/-- Transitivity of `MIRCtxRefines`. -/
theorem mirCtxRefines_trans {d : Nat} {m₁ m₂ m₃ : Expr} :
    MIRCtxRefines d m₁ m₂ → MIRCtxRefines d m₂ m₃ → MIRCtxRefines d m₁ m₃ := by
  intro h12 h23 env hlen
  obtain ⟨hsome12, hctx12⟩ := h12 env hlen
  obtain ⟨hsome23, hctx23⟩ := h23 env hlen
  refine ⟨hsome23 ∘ hsome12, ?_⟩
  -- Branch on the compile status of m₁ and m₃
  cases h₁ : lowerTotalExpr env m₁ with
  | none => trivial
  | some t₁ =>
    cases h₃ : lowerTotalExpr env m₃ with
    | none => trivial
    | some t₃ =>
      -- m₁ compiles, hence m₂ compiles, hence m₃ compiles. Pull out t₂.
      have hsome2 : (lowerTotalExpr env m₂).isSome := hsome12 (by rw [h₁]; trivial)
      cases h₂ : lowerTotalExpr env m₂ with
      | none => rw [h₂] at hsome2; exact absurd hsome2 (by simp)
      | some t₂ =>
        rw [h₁, h₂] at hctx12; rw [h₂, h₃] at hctx23
        exact ctxRefines_trans hctx12 hctx23

/-- Reflexivity of `MIRCtxEq`. -/
theorem mirCtxEq_refl (d : Nat) (m : Expr) : MIRCtxEq d m m := by
  intro env _
  refine ⟨Iff.rfl, ?_⟩
  cases h : lowerTotalExpr env m
  · trivial
  · exact fun _ => ⟨Iff.rfl, Iff.rfl⟩

/-- Symmetry of `MIRCtxEq`. -/
theorem mirCtxEq_symm {d : Nat} {m₁ m₂ : Expr} :
    MIRCtxEq d m₁ m₂ → MIRCtxEq d m₂ m₁ := by
  intro h env hlen
  obtain ⟨hiff, hctx⟩ := h env hlen
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
      intro C; exact ⟨(hctx C).1.symm, (hctx C).2.symm⟩

/-- Transitivity of `MIRCtxEq` — follows directly from the iff lemma below
    plus `mirCtxRefines_trans`. -/
theorem mirCtxEq_trans {d : Nat} {m₁ m₂ m₃ : Expr} :
    MIRCtxEq d m₁ m₂ → MIRCtxEq d m₂ m₃ → MIRCtxEq d m₁ m₃ := by
  intro h12 h23 env hlen
  obtain ⟨hiff12, hctx12⟩ := h12 env hlen
  obtain ⟨hiff23, hctx23⟩ := h23 env hlen
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
        rw [h₁, h₂] at hctx12; rw [h₂, h₃] at hctx23
        intro C
        exact ⟨Iff.trans (hctx12 C).1 (hctx23 C).1, Iff.trans (hctx12 C).2 (hctx23 C).2⟩

--------------------------------------------------------------------------------
-- 4. MIRCtxEq ↔ bidirectional MIRCtxRefines
--------------------------------------------------------------------------------

theorem mirCtxEq_iff_refines_bidir {d : Nat} {m₁ m₂ : Expr} :
    MIRCtxEq d m₁ m₂ ↔ MIRCtxRefines d m₁ m₂ ∧ MIRCtxRefines d m₂ m₁ := by
  constructor
  · -- (⇒) MIRCtxEq → bidirectional MIRCtxRefines
    intro h
    refine ⟨?_, ?_⟩ <;> intro env hlen
    · obtain ⟨hiff, hctx⟩ := h env hlen
      refine ⟨hiff.mp, ?_⟩
      cases h₁ : lowerTotalExpr env m₁ with
      | none => trivial
      | some t₁ =>
        cases h₂ : lowerTotalExpr env m₂ with
        | none => trivial
        | some t₂ =>
          rw [h₁, h₂] at hctx; exact hctx.toCtxRefines
    · obtain ⟨hiff, hctx⟩ := h env hlen
      refine ⟨hiff.mpr, ?_⟩
      cases h₂ : lowerTotalExpr env m₂ with
      | none => trivial
      | some t₂ =>
        cases h₁ : lowerTotalExpr env m₁ with
        | none => trivial
        | some t₁ =>
          rw [h₁, h₂] at hctx; exact hctx.toCtxRefines_symm
  · -- (⇐) bidirectional MIRCtxRefines → MIRCtxEq
    intro ⟨h12, h21⟩ env hlen
    obtain ⟨hsome12, hctx12⟩ := h12 env hlen
    obtain ⟨hsome21, hctx21⟩ := h21 env hlen
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
        rw [h₁, h₂] at hctx12; rw [h₁, h₂] at hctx21
        exact ctxRefines_antisymm hctx12 hctx21

end Moist.VerifiedNewNew.MIR
