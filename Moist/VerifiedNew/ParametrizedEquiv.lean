import Moist.Verified.Semantics
import Moist.Verified.ClosedAt
import Moist.Verified.StepLift

set_option linter.unusedSimpArgs false

namespace Moist.Verified.Equivalence

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics

/-- Pointwise relation on lists: all corresponding elements are related by `R`. -/
inductive Pointwise (R : α → β → Prop) : List α → List β → Prop where
  | nil : Pointwise R [] []
  | cons : R x y → Pointwise R xs ys → Pointwise R (x :: xs) (y :: ys)

-- ============================================================================
-- PHASE 1: Parametrized Equivalences (The POPL 2012 "Marriage" Architecture)
-- We define equivalences parameterized by an arbitrary relation `R`.
-- This completely bypasses Step-Indexing and Howe's Method.
-- ============================================================================

/--
  Computation Equivalence parameterized by `R`.
  Evaluates terms using unbounded `Reaches` (Cost-Erasure). When the machine
  halts, it delegates the equivalence of the results to the parameter `R`.
-/
def CompEqF (R : CekValue → CekValue → Prop) (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  (Reaches (.compute [] ρ₁ t₁) .error ↔ Reaches (.compute [] ρ₂ t₂) .error) ∧
  (∀ v₁, Reaches (.compute [] ρ₁ t₁) (.halt v₁) →
    ∃ v₂, Reaches (.compute [] ρ₂ t₂) (.halt v₂) ∧ R v₁ v₂) ∧
  (∀ v₂, Reaches (.compute [] ρ₂ t₂) (.halt v₂) →
    ∃ v₁, Reaches (.compute [] ρ₁ t₁) (.halt v₁) ∧ R v₁ v₂)

/--
  Value Equivalence parameterized by `R`.
  This is the Generator / Monotone Operator.
  Notice how Congruence is baked directly into the `.VLam` rule.
-/
def ValueEqF (R : CekValue → CekValue → Prop) (v₁ v₂ : CekValue) : Prop :=
  match v₁, v₂ with
  | .VCon c₁, .VCon c₂ => c₁ = c₂

  | .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      -- MAGIC: We demand `arg1` and `arg2` are related by `R`.
      -- This eliminates the need for Howe's artificial AST closure!
      ∀ (arg₁ arg₂ : CekValue), R arg₁ arg₂ →
        CompEqF R (ρ₁.extend arg₁) (ρ₂.extend arg₂) b₁ b₂

  | .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      CompEqF R ρ₁ ρ₂ b₁ b₂

  | .VConstr tag₁ vs₁, .VConstr tag₂ vs₂ =>
      tag₁ = tag₂ ∧ Pointwise R vs₁ vs₂

  | .VBuiltin f₁ args₁ exp₁, .VBuiltin f₂ args₂ exp₂ =>
      f₁ = f₂ ∧ exp₁ = exp₂ ∧ Pointwise R args₁ args₂

  | _, _ => False


-- ============================================================================
-- PHASE 2: Relational Algebra (No Mathlib)
-- ============================================================================

/-- A relation is a simulation if it satisfies the ValueEqF operator. -/
def IsValueSimulation (R : CekValue → CekValue → Prop) : Prop :=
  ∀ v₁ v₂, R v₁ v₂ → ValueEqF R v₁ v₂

/-- Manual Relational Composition (R ∘ S) -/
def RelComp (R S : CekValue → CekValue → Prop) (v₁ v₃ : CekValue) : Prop :=
  ∃ v₂, R v₁ v₂ ∧ S v₂ v₃

/--
  The Transitivity Engine.
  Proof Strategy: Unfold ValueEqF, and because CEK evaluation is deterministic,
  the intermediate halting states (v₂') perfectly align to satisfy both R and S.
-/
theorem sim_comp_is_sim {R S : CekValue → CekValue → Prop}
  (hR : IsValueSimulation R) (hS : IsValueSimulation S) :
  IsValueSimulation (RelComp R S) := by sorry


-- ============================================================================
-- PHASE 3: The Greatest Fixed Point (Contextual Equivalence)
-- ============================================================================

/--
  Value Equivalence: The existential GFP encoding.
  Two values are equivalent if there exists SOME relation `R` that validates them.
-/
def ValueEq (v₁ v₂ : CekValue) : Prop :=
  ∃ R, IsValueSimulation R ∧ R v₁ v₂

/-- Value equivalence is transitive (compiler passes compose). -/
theorem ValueEq_trans {v₁ v₂ v₃ : CekValue} :
  ValueEq v₁ v₂ → ValueEq v₂ v₃ → ValueEq v₁ v₃ := by
  intro ⟨R, hSimR, hR⟩ ⟨S, hSimS, hS⟩
  exact ⟨RelComp R S, sim_comp_is_sim hSimR hSimS, ⟨v₂, hR, hS⟩⟩

/--
  Because ValueEq is the union of all simulations, we can prove that
  ValueEq satisfies its own generator (the unfolding lemma).
-/
theorem ValueEq_unfold {v₁ v₂ : CekValue} :
  ValueEq v₁ v₂ → ValueEqF ValueEq v₁ v₂ := by sorry


-- ============================================================================
-- PHASE 4: Open Extensions & Compiler Targets
-- ============================================================================

/-- Computation Equivalence is just CompEqF specialized to the GFP ValueEq. -/
def CompEq (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  CompEqF ValueEq ρ₁ ρ₂ t₁ t₂

/-- Environment Equivalence (Pointwise) -/
def EnvEq (d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEq v₁ v₂
    | none, none => True
    | _, _ => False

/-- Open Equivalence: Safe to substitute related environments. -/
def OpenEq (d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ ρ₁ ρ₂, EnvEq d ρ₁ ρ₂ → CompEq ρ₁ ρ₂ t₁ t₂

/-- Behavioral Equivalence for closed programs. -/
def BehEq (m1 m2 : Term) : Prop :=
  OpenEq 0 m1 m2

scoped infix:50 " ≋ " => BehEq

/-- The final target for compiler passes. -/
def Refines (m1 m2 : Term) : Prop :=
  BehEq m1 m2

scoped infix:50 " ⊑ " => Refines


-- ============================================================================
-- PHASE 5: Trivial Congruence Lemmas
-- ============================================================================

/--
  Example: Application is safe under Refines.
  Proof Strategy: Because the GFP natively demands `R arg₁ arg₂` inside `.VLam`,
  you do not need a massive Simulation Lemma. You just unfold `ValueEq`, apply
  the deterministic machine steps to extract the closures, and the hypothesis
  `ha` satisfies the argument requirement natively!
-/
theorem refines_app_arg_behEq (f a a' : Term) (ha : a ⊑ a') :
    .Apply f a ⊑ .Apply f a' := by sorry

theorem refines_lam_behEq (n : Nat) (body body' : Term) (h : body ⊑ body') :
    .Lam n body ⊑ .Lam n body' := by sorry

end Moist.Verified.Equivalence
