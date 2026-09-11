import Moist.Verified.Definitions

/-! # Unresolved, unsound budget-exhaustion axiom

WARNING: this axiom is false for the unbounded Reaches relation. The CEK step
function has no budget-exhaustion transition; a finite ledger execution budget
does not justify the proposition below. Test.MIR.Opt.BudgetModel independently
proves its negation using a closed self-application cycle.

The declaration remains for proof-API compatibility pending removal or a genuine
semantic proof repair. Any theorem depending on it is not a sound certificate.
See docs/MIR-Optimization-Audit.md for the affected theorem chain. -/

namespace Moist.Verified

open Moist.CEK (State)

/-- Unsound legacy axiom: non-halting does not imply an explicit CEK error.
Do not use this declaration to certify optimization correctness. -/
axiom budget_exhaustion : ∀ (s : State),
    (∀ v, ¬Equivalence.Reaches s (.halt v)) → Equivalence.Reaches s .error

/-- Equivalent form: every state either halts or errors. -/
theorem halt_or_error (s : State) :
    (∃ v, Equivalence.Reaches s (.halt v)) ∨ Equivalence.Reaches s .error := by
  by_cases h : ∃ v, Equivalence.Reaches s (.halt v)
  · exact Or.inl h
  · exact Or.inr (budget_exhaustion s (fun v hv => h ⟨v, hv⟩))

end Moist.Verified
