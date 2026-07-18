import Moist.SMT.Soundness.OutputAnalysis

/-!
# Generated SMT output contract

This is the small proof-carrying boundary consumed by the checked compiler.
The executable output analysis lives under `Moist.SMT.Compiler`; its exact
equivalence to the transparent renderer and sort validators is proved in
`Moist.SMT.Soundness.OutputAnalysis`.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.SMT.Compiler.OutputAnalysis

/-- Kernel-checked facts about the exact generated script.  All four
independent checks remain visible at the public boundary. -/
structure GeneratedOutputContract (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Type where
  commandsSafe : generatedCommandsSafe declarations script = true
  solverControlSafe : generatedSolverControlSafe script = true
  rendererSafe : generatedAssertionsRendererSafe script = true
  sortSafe : generatedAssertionsSortSafe declarations script = true

namespace GeneratedOutputContract

/-- Fail closed when compiler output leaves the reviewed command, control,
renderer, or sort fragment. -/
def check (declarations : List SymDecl) (script : Moist.SMT.Script) :
    Option (GeneratedOutputContract declarations script) :=
  if hCommands : generatedCommandsSafe declarations script = true then
    if hControl : generatedSolverControlSafe script = true then
      if hsafe : generatedAssertionsOutputSafe declarations script = true then
        have hreference : generatedAssertionsRendererSafe script = true ∧
            generatedAssertionsSortSafe declarations script = true := by
          rw [OutputAnalysis.generatedAssertionsOutputSafe_eq] at hsafe
          exact Bool.and_eq_true_iff.mp hsafe
        some ⟨hCommands, hControl, hreference.1, hreference.2⟩
      else
        none
    else
      none
  else
    none

@[simp] theorem check_isSome (declarations : List SymDecl)
    (script : Moist.SMT.Script) :
    (check declarations script).isSome =
      (generatedCommandsSafe declarations script &&
        generatedSolverControlSafe script &&
        generatedAssertionsRendererSafe script &&
        generatedAssertionsSortSafe declarations script) := by
  by_cases hCommands : generatedCommandsSafe declarations script = true <;>
    by_cases hControl : generatedSolverControlSafe script = true <;>
    by_cases hRenderer : generatedAssertionsRendererSafe script = true <;>
    by_cases hSort : generatedAssertionsSortSafe declarations script = true <;>
    simp_all [check, OutputAnalysis.generatedAssertionsOutputSafe_eq]

end GeneratedOutputContract

end Moist.SMT.UPLC.Soundness
