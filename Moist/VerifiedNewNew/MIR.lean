import Moist.VerifiedNewNew.Equivalence
import Moist.VerifiedNewNew.Rename
import Moist.MIR.LowerTotal

/-! # MIR-Level Equivalence and Refinement

Lifts the biorthogonal step-indexed logical relation from UPLC terms
(defined in `Equivalence.lean`) to MIR expressions via `lowerTotalExpr`.

The key definitions:
- `MIROpenEqK k d m₁ m₂`: two MIR expressions are equivalent at step-index
  `k` and depth `d` when their lowerings (if they exist) are `OpenEqK`.
- `MIROpenEq d m₁ m₂`: the step-index-free version (for all `k`).
- `MIRRefines m₁ m₂`: `m₂` refines `m₁` — wherever `m₁` lowers, `m₂`
  also lowers and the results are equivalent.

All definitions degrade gracefully: if either side fails to lower
(`lowerTotalExpr` returns `none`), the relation holds vacuously.
-/

namespace Moist.VerifiedNewNew.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.VerifiedNewNew.Equivalence

--------------------------------------------------------------------------------
-- 1. LIFTING OpenEqK TO MIR
--------------------------------------------------------------------------------

/-- Two MIR expressions are open-equivalent at step-index `k` and depth `d`
    when, for every variable environment `env` of length `d`, their lowerings
    (if both succeed) are `OpenEqK`-related at level `k` and depth `d`.

    If either side fails to lower, the relation holds vacuously. -/
def MIROpenEqK (k d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId), env.length = d →
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ => OpenEqK k d t₁ t₂
    | _, _ => True

/-- Step-index-free open equivalence: holds at every step index. -/
def MIROpenEq (d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ k, MIROpenEqK k d m₁ m₂

/-- Closed equivalence: open equivalence at depth 0. -/
def MIRClosedEq (m₁ m₂ : Expr) : Prop := MIROpenEq 0 m₁ m₂

scoped infix:50 " ≈ᴹ " => MIRClosedEq

--------------------------------------------------------------------------------
-- 2. REFINEMENT
--------------------------------------------------------------------------------

/-- `m₂` refines `m₁`: wherever `m₁` lowers successfully, `m₂` also
    lowers, and their lowerings are open-equivalent at every depth and
    step index. This is the appropriate notion for proving MIR-to-MIR
    optimizations correct.

    The lowering-preservation condition ensures that `m₂` does not
    introduce new `Fix` nodes or other constructs that `lowerTotalExpr`
    rejects. -/
def MIRRefines (m₁ m₂ : Expr) : Prop :=
  (∀ env, (lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
  ∀ d, MIROpenEq d m₁ m₂

scoped infix:50 " ⊑ᴹ " => MIRRefines

--------------------------------------------------------------------------------
-- 3. BASIC PROPERTIES
--------------------------------------------------------------------------------

/-- Helper: extract the UPLC-level OpenEqK from MIROpenEqK when both sides lower. -/
private theorem mirOpenEqK_lower {k d : Nat} {m₁ m₂ : Expr} {env : List VarId}
    {t₁ t₂ : Moist.Plutus.Term.Term}
    (h : MIROpenEqK k d m₁ m₂) (hlen : env.length = d)
    (h₁ : lowerTotalExpr env m₁ = some t₁) (h₂ : lowerTotalExpr env m₂ = some t₂) :
    OpenEqK k d t₁ t₂ := by
  have := h env hlen; simp only [h₁, h₂] at this; exact this

/-- MIROpenEqK is monotone in k: fewer steps to check means easier. -/
theorem mirOpenEqK_mono {j k d : Nat} {m₁ m₂ : Expr}
    (hjk : j ≤ k) (h : MIROpenEqK k d m₁ m₂) : MIROpenEqK j d m₁ m₂ := by
  intro env hlen
  cases h₁ : lowerTotalExpr env m₁ <;> cases h₂ : lowerTotalExpr env m₂ <;>
    simp only [] <;> try trivial
  have := mirOpenEqK_lower h hlen h₁ h₂
  exact fun j' hj' => this j' (by omega)

theorem mirOpenEq_symm {d : Nat} {m₁ m₂ : Expr}
    (h : MIROpenEq d m₁ m₂) : MIROpenEq d m₂ m₁ := by
  intro k env hlen
  cases h₁ : lowerTotalExpr env m₁ <;> cases h₂ : lowerTotalExpr env m₂ <;>
    simp only [] <;> try trivial
  rename_i t₁ t₂
  have h' : OpenEq d t₁ t₂ := fun k' =>
    mirOpenEqK_lower (h k') hlen h₁ h₂
  exact openEq_symm h' k

theorem mirClosedEq_symm {m₁ m₂ : Expr}
    (h : m₁ ≈ᴹ m₂) : m₂ ≈ᴹ m₁ :=
  mirOpenEq_symm h

theorem mirRefines_refl (m : Expr)
    (hclosed : ∀ env d, env.length = d → ∀ t, lowerTotalExpr env m = some t →
      Moist.VerifiedNewNew.closedAt d t = true) :
    m ⊑ᴹ m :=
  ⟨fun _ h => h, fun d k env hlen => by
    cases h : lowerTotalExpr env m <;> simp only []
    exact openEq_refl d _ (hclosed env d hlen _ h) k⟩

end Moist.VerifiedNewNew.MIR
