import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Term
import Moist.VerifiedNewNew.Equivalence

namespace Moist.VerifiedNewNew.Contextual

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew.Equivalence

--------------------------------------------------------------------------------
-- 1. SYNTACTIC CONTEXTS
--------------------------------------------------------------------------------

/--
  A program context: an AST with exactly one `Hole`.
  This mirrors the `Term` inductive type.
-/
inductive Context
  | Hole : Context
  | Lam : String → Context → Context
  | AppLeft : Context → Term → Context
  | AppRight : Term → Context → Context
  | Delay : Context → Context
  | Force : Context → Context
  | Constr : Nat → List Term → Context → List Term → Context
  | Case : Context → List Term → Context
  | Builtin : BuiltinFun → List Term → Context → List Term → Context

--------------------------------------------------------------------------------
-- 2. THE FILL OPERATOR (Capture-Permitting Substitution)
--------------------------------------------------------------------------------

/--
  Plugs a term into the context hole.
  Variable capture is strictly permitted to simulate adversarial environments.
-/
def fill : Context → Term → Term
  | .Hole, t => t
  | .Lam x C, t => .Lam x (fill C t)
  | .AppLeft C e, t => .Apply (fill C t) e
  | .AppRight e C, t => .Apply e (fill C t)
  | .Delay C, t => .Delay (fill C t)
  | .Force C, t => .Force (fill C t)
  | .Constr tag lefts C rights, t => .Constr tag (lefts ++ [fill C t] ++ rights)
  | .Case C alts, t => .Case (fill C t) alts
  | .Builtin b lefts C rights, t => .Builtin b (lefts ++ [fill C t] ++ rights)

--------------------------------------------------------------------------------
-- 3. CONTEXTUAL EQUIVALENCE & TRANSITIVITY
--------------------------------------------------------------------------------

/--
  Two terms are contextually equivalent if, when placed in any syntax tree
  and evaluated in the empty machine, their unbounded termination behavior matches.
-/
def CtxEq (t₁ t₂ : Term) : Prop :=
  ∀ (C : Context),
    ObsEq (.compute [] (fun _ => none) (fill C t₁))
          (.compute [] (fun _ => none) (fill C t₂))

/--
  The Transitivity of Contextual Equivalence.
  Because it operates purely on syntax and logical bi-implication, this is a free theorem.
-/
theorem ctxEq_trans {t₁ t₂ t₃ : Term} :
  CtxEq t₁ t₂ → CtxEq t₂ t₃ → CtxEq t₁ t₃ := by
  intro h1 h2 C
  exact Iff.trans (h1 C) (h2 C)

--------------------------------------------------------------------------------
-- 4. THE SOUNDNESS BRIDGE (Biorthogonality → Contextual)
--------------------------------------------------------------------------------

/--
  The Fundamental Theorem of Logical Relations: OpenEq is a Congruence.
  You will prove this using your `compat_*` step lemmas from the Equivalence module.
-/
theorem openEq_contextual_closure {t₁ t₂ : Term} (C : Context) {d : Nat} :
  OpenEq d t₁ t₂ → OpenEq d (fill C t₁) (fill C t₂) := by
  intro h
  induction C with
  | Hole => exact h
  | Lam x C ih => sorry -- apply compat_lam ih
  | AppLeft C e ih => sorry -- apply compat_app ih (openEq_refl e)
  | AppRight e C ih => sorry -- apply compat_app (openEq_refl e) ih
  | Delay C ih => sorry -- apply compat_delay ih
  | Force C ih => sorry -- apply compat_force ih
  | Constr tag lefts C rights ih => sorry
  | Case C alts ih => sorry
  | Builtin b lefts C rights ih => sorry

/--
  SOUNDNESS: If terms survive the CEK machine (OpenEq), they survive all syntax (CtxEq).
  Proof strategy: Apply closure, instantiate universal quantifiers with empty env/stack,
  and take the unbounded limit.
-/
theorem soundness (t₁ t₂ : Term) : OpenEq 0 t₁ t₂ → CtxEq t₁ t₂ := by
  intro h_open C
  sorry

--------------------------------------------------------------------------------
-- 5. THE COMPLETENESS BRIDGE (Contextual → Biorthogonality)
--------------------------------------------------------------------------------

-- The Definability Tax: You must prove that raw CEK states can be simulated
-- by pure Plutus Core syntax trees.

/-- Synthesizes a nested `let` Context that reconstructs a CEK environment. -/
axiom env_to_context (ρ : CekEnv) : Context

/-- Synthesizes a Context that mimics the continuation of a CEK stack. -/
axiom stack_to_context (π : Stack) : Context

/--
  The Definability Lemma:
  Plugging a term into the synthesized contexts is observationally equivalent
  to directly evaluating it under the original CEK environment and stack.
-/
axiom definability_lemma (π : Stack) (ρ : CekEnv) (t : Term) :
  ObsEq (.compute π ρ t)
        (.compute [] (fun _ => none) (fill (stack_to_context π) (fill (env_to_context ρ) t)))

/--
  COMPLETENESS: If terms survive all syntax (CtxEq), they survive the CEK machine (OpenEq).
  Proof strategy: Reify π and ρ into contexts, apply CtxEq, and un-reify via definability.
-/
theorem completeness (t₁ t₂ : Term) : CtxEq t₁ t₂ → OpenEq 0 t₁ t₂ := by
  intro h_ctx
  sorry

end Moist.VerifiedNewNew.Contextual
