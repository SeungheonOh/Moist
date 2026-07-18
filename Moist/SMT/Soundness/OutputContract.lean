import Moist.SMT.Compiler.Checked
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

/-- The proof-free production check is exactly the conjunction of all four
transparent output-contract facts. -/
theorem outputAccepted_eq (declarations : List SymDecl)
    (script : Moist.SMT.Script) :
    Moist.SMT.Compiler.outputAccepted declarations script =
      (generatedCommandsSafe declarations script &&
        generatedSolverControlSafe script &&
        generatedAssertionsRendererSafe script &&
        generatedAssertionsSortSafe declarations script) := by
  rw [Moist.SMT.Compiler.outputAccepted,
    OutputAnalysis.generatedAssertionsOutputSafe_eq]
  simp only [Bool.and_assoc]

/-- Turn successful proof-free output validation into all four independent
kernel facts about the exact same script. -/
def ofOutputAccepted {declarations : List SymDecl}
    {script : Moist.SMT.Script}
    (accepted : Moist.SMT.Compiler.outputAccepted declarations script = true) :
    GeneratedOutputContract declarations script := by
  rw [outputAccepted_eq] at accepted
  simp only [Bool.and_eq_true] at accepted
  exact
    { commandsSafe := accepted.1.1.1
      solverControlSafe := accepted.1.1.2
      rendererSafe := accepted.1.2
      sortSafe := accepted.2 }

/-- Fail closed when compiler output leaves the reviewed command, control,
renderer, or sort fragment.  This proof wrapper delegates acceptance to the
same executable predicate used by the proof-free compiler. -/
def check (declarations : List SymDecl) (script : Moist.SMT.Script) :
    Option (GeneratedOutputContract declarations script) :=
  if accepted : Moist.SMT.Compiler.outputAccepted declarations script = true then
    some (ofOutputAccepted accepted)
  else
    none

@[simp] theorem check_isSome (declarations : List SymDecl)
    (script : Moist.SMT.Script) :
    (check declarations script).isSome =
      (generatedCommandsSafe declarations script &&
        generatedSolverControlSafe script &&
        generatedAssertionsRendererSafe script &&
        generatedAssertionsSortSafe declarations script) := by
  rw [← outputAccepted_eq]
  by_cases accepted :
      Moist.SMT.Compiler.outputAccepted declarations script = true <;>
    simp [check, accepted]

end GeneratedOutputContract

end Moist.SMT.UPLC.Soundness
