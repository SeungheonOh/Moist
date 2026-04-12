import Moist.VerifiedNewNew.MIR
import Moist.VerifiedNewNew.Contextual
import Moist.VerifiedNewNew.Contextual.SoundnessRefines

/-! # MIR-Level Contextual Refinement Congruences and Bridges

This file provides:

1. The bridge from `MIRRefines` to the contextual `MIRCtxRefines` at
   arbitrary depth `d`, using `soundness_refines_d` from
   `Contextual/SoundnessRefines`.

2. Structural MIR-level congruence theorems (`mirCtxRefines_lam`,
   `mirCtxRefines_app`, etc.), lifted from the UPLC-level congruences in
   `Contextual.lean`. (To be added.)

3. Let splitting/unsplitting lemmas. (To be added.)

These are the primitives DCE (and other optimizer proofs) consume.
-/

namespace Moist.VerifiedNewNew.MIRCongruence

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal lowerTotalLet)
open Moist.Plutus.Term (Term)
open Moist.VerifiedNewNew.Contextual
open Moist.VerifiedNewNew.Contextual.SoundnessRefines
open Moist.VerifiedNewNew.MIR

--------------------------------------------------------------------------------
-- 1. BRIDGE: `MIRRefines` → `MIRCtxRefines d` at arbitrary depth.
--
-- `MIRRefines` is unidirectional and quantifies over arbitrary environments,
-- so we can directly feed `MIROpenRef d m₁ m₂` into `soundness_refines_d`
-- and obtain `CtxRefines` on the lowered terms.
--------------------------------------------------------------------------------

/-- From `MIRRefines m₁ m₂` to `MIRCtxRefines d m₁ m₂` at any depth `d`,
    via `soundness_refines_d`. -/
theorem mirRefines_to_mirCtxRefines (d : Nat) {m₁ m₂ : Expr} (h : MIRRefines m₁ m₂) :
    MIRCtxRefines d m₁ m₂ := by
  intro env hlen
  refine ⟨?_, ?_⟩
  · exact h.1 env
  · cases hlow₁ : lowerTotalExpr env m₁ with
    | none => trivial
    | some t₁ =>
      cases hlow₂ : lowerTotalExpr env m₂ with
      | none => trivial
      | some t₂ =>
        have hopenRef : MIROpenRef d m₁ m₂ := h.2 d
        have h_open : OpenRefines d t₁ t₂ := by
          intro k j hj ρ₁ ρ₂ henv
          have := hopenRef k env hlen
          rw [hlow₁, hlow₂] at this
          exact this j hj ρ₁ ρ₂ henv
        exact soundness_refines_d h_open

end Moist.VerifiedNewNew.MIRCongruence
