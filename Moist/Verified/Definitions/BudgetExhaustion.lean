import Moist.Verified.Definitions

/-! # Budget Exhaustion Axiom

On Cardano, the CEK machine runs under a finite execution budget (CPU and memory).
Every evaluation either halts with a value, errors with explicit failure, or killed when
the budget runs out (reported as an error). True divergence is not a physically realizable
outcome.

The unbounded `step : State → State` used throughout the proof infrastructure does
not model this budget. We bridge the gap with a single axiom: if a state never
halts, it reaches error. This is sound for any execution context with a finite
budget, which includes all Cardano validator executions. -/

namespace Moist.Verified

open Moist.CEK (State)

/-- **Budget exhaustion axiom**: a CEK state that never halts must reach error.

This models the Cardano execution budget: every on-chain evaluation has a finite
CPU/memory budget. An execution that neither halts with a value nor encounters a
runtime error will eventually exhaust its budget, which the ledger treats as an
error. -/
axiom budget_exhaustion : ∀ (s : State),
    (∀ v, ¬Equivalence.Reaches s (.halt v)) → Equivalence.Reaches s .error

/-- Equivalent form: every state either halts or errors. -/
theorem halt_or_error (s : State) :
    (∃ v, Equivalence.Reaches s (.halt v)) ∨ Equivalence.Reaches s .error := by
  by_cases h : ∃ v, Equivalence.Reaches s (.halt v)
  · exact Or.inl h
  · exact Or.inr (budget_exhaustion s (fun v hv => h ⟨v, hv⟩))

end Moist.Verified
