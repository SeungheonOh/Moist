import Moist.SMT.Soundness.OutputContract

/-!
# Certification of the fully checked proof-free compiler

The portable compiler validates caller input and its exact generated output,
then returns only `Option Script`.  This module proves what a successful result
contains and attaches erased kernel evidence to that same stored script.
Certification never invokes symbolic evaluation or output analysis again.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term

namespace CheckedCompiler

theorem inputAccepted_components (declarations : List SymDecl) (term : Term)
    (h : Moist.SMT.Compiler.inputAccepted declarations term = true) :
    symEnvNoOpaqueForSoundness (envOf declarations) = true ∧
      declarationsRendererSafe declarations = true ∧
      declarationsSortSafe declarations = true ∧
      declarationsInputSafe declarations = true ∧
      declarationNamesDistinct declarations = true ∧
      termUsesOpaqueBuiltinForSoundness term = false := by
  simp only [Moist.SMT.Compiler.inputAccepted, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hOpaque, hRenderer⟩, hSort⟩, hInput⟩, hDistinct⟩, hTerm⟩
  have hTerm' : termUsesOpaqueBuiltinForSoundness term = false := by
    cases hValue : termUsesOpaqueBuiltinForSoundness term <;> simp_all
  exact ⟨hOpaque, hRenderer, hSort, hInput, hDistinct, hTerm'⟩

/-- A successful portable compilation is exactly the canonical script and
its caller-controlled input passed every fail-closed check. -/
theorem compileInputChecked_some {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {term : Term} {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term = some script) :
    Moist.SMT.Compiler.inputAccepted declarations term = true ∧
      script = Moist.SMT.Compiler.scriptFor kind fuel declarations term := by
  by_cases hInput : Moist.SMT.Compiler.inputAccepted declarations term = true
  · have hScript : script = Moist.SMT.Compiler.scriptFor kind fuel declarations term := by
      simpa [Moist.SMT.Compiler.compileInputChecked?, hInput] using h.symm
    exact ⟨hInput, hScript⟩
  · simp [Moist.SMT.Compiler.compileInputChecked?, hInput] at h

@[simp] theorem compileInputChecked_isSome
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term).isSome =
      Moist.SMT.Compiler.inputAccepted declarations term := by
  by_cases hInput : Moist.SMT.Compiler.inputAccepted declarations term = true <;>
    simp [Moist.SMT.Compiler.compileInputChecked?, hInput]

/-- A successful fully checked compilation passed the input gate, is exactly
the canonical script, and passed generated-output validation on that same
script. -/
theorem compile_some {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {term : Term} {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compile? kind fuel declarations term = some script) :
    Moist.SMT.Compiler.inputAccepted declarations term = true ∧
      script = Moist.SMT.Compiler.scriptFor kind fuel declarations term ∧
      Moist.SMT.Compiler.outputAccepted declarations script = true := by
  by_cases hInput : Moist.SMT.Compiler.inputAccepted declarations term = true
  · by_cases hOutput : Moist.SMT.Compiler.outputAccepted declarations
        (Moist.SMT.Compiler.scriptFor kind fuel declarations term) = true
    · have hScript :
          script = Moist.SMT.Compiler.scriptFor kind fuel declarations term := by
        simpa [Moist.SMT.Compiler.compile?,
          Moist.SMT.Compiler.compileInputChecked?, hInput,
          Moist.SMT.Compiler.outputChecked?, hOutput] using h.symm
      subst script
      exact ⟨hInput, rfl, hOutput⟩
    · simp [Moist.SMT.Compiler.compile?,
        Moist.SMT.Compiler.compileInputChecked?, hInput,
        Moist.SMT.Compiler.outputChecked?, hOutput] at h
  · simp [Moist.SMT.Compiler.compile?,
      Moist.SMT.Compiler.compileInputChecked?, hInput] at h

/-- The proof-free production API accepts exactly the caller-input gate and
all four transparent output-contract predicates. -/
@[simp] theorem compile_isSome (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (Moist.SMT.Compiler.compile? kind fuel declarations term).isSome =
      (Moist.SMT.Compiler.inputAccepted declarations term &&
        generatedCommandsSafe declarations
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) &&
        generatedSolverControlSafe
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) &&
        generatedAssertionsRendererSafe
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) &&
        generatedAssertionsSortSafe declarations
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term)) := by
  calc
    (Moist.SMT.Compiler.compile? kind fuel declarations term).isSome =
        (Moist.SMT.Compiler.inputAccepted declarations term &&
          Moist.SMT.Compiler.outputAccepted declarations
            (Moist.SMT.Compiler.scriptFor kind fuel declarations term)) := by
      by_cases hInput :
          Moist.SMT.Compiler.inputAccepted declarations term = true <;>
        by_cases hOutput : Moist.SMT.Compiler.outputAccepted declarations
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) = true <;>
        simp [Moist.SMT.Compiler.compile?,
          Moist.SMT.Compiler.compileInputChecked?,
          Moist.SMT.Compiler.outputChecked?, hInput, hOutput]
    _ = _ := by
      rw [GeneratedOutputContract.outputAccepted_eq]
      simp only [Bool.and_assoc]

end CheckedCompiler

/-- Kernel evidence attached to the exact script returned by the portable
compiler and accepted by the generated-output contract.  Every proof field is
erased at runtime. -/
structure CertifiedCompilation (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) where
  script : Moist.SMT.Script
  script_eq : script = Moist.SMT.Compiler.scriptFor kind fuel declarations term
  declarationsNoOpaque :
    symEnvNoOpaqueForSoundness (envOf declarations) = true
  declarationsRendererSafe : declarationsRendererSafe declarations = true
  declarationsSortSafe : declarationsSortSafe declarations = true
  declarationsInputSafe : declarationsInputSafe declarations = true
  declarationNamesDistinct : declarationNamesDistinct declarations = true
  termNoOpaque : termUsesOpaqueBuiltinForSoundness term = false
  output : GeneratedOutputContract declarations script

namespace CertifiedCompilation

private def certifySome {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {term : Term} {script : Moist.SMT.Script}
    (hResult : Moist.SMT.Compiler.compile? kind fuel declarations term = some script) :
    CertifiedCompilation kind fuel declarations term :=
  have hResultComponents := CheckedCompiler.compile_some hResult
  have hInput := CheckedCompiler.inputAccepted_components declarations term
    hResultComponents.1
  { script
    script_eq := hResultComponents.2.1
    declarationsNoOpaque := hInput.1
    declarationsRendererSafe := hInput.2.1
    declarationsSortSafe := hInput.2.2.1
    declarationsInputSafe := hInput.2.2.2.1
    declarationNamesDistinct := hInput.2.2.2.2.1
    termNoOpaque := hInput.2.2.2.2.2
    output := GeneratedOutputContract.ofOutputAccepted hResultComponents.2.2 }

/-- Certify the result returned by the proof-free compiler without
reconstructing its script or invoking symbolic evaluation again. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    Option (CertifiedCompilation kind fuel declarations term) :=
  match hResult : Moist.SMT.Compiler.compile? kind fuel declarations term with
  | none => none
  | some _script => some (certifySome hResult)

/-- Erasing certification yields exactly the fully checked proof-free compiler
result.  There is no second compilation or proof-side acceptance path. -/
@[simp] theorem compile_map_script (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (compile? kind fuel declarations term).map (·.script) =
      Moist.SMT.Compiler.compile? kind fuel declarations term := by
  unfold compile?
  split <;> simp_all [certifySome]

@[simp] theorem compile_isSome (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (compile? kind fuel declarations term).isSome =
      (Moist.SMT.Compiler.inputAccepted declarations term &&
        generatedCommandsSafe declarations
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) &&
        generatedSolverControlSafe
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) &&
        generatedAssertionsRendererSafe
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term) &&
        generatedAssertionsSortSafe declarations
          (Moist.SMT.Compiler.scriptFor kind fuel declarations term)) := by
  calc
    (compile? kind fuel declarations term).isSome =
        ((compile? kind fuel declarations term).map (·.script)).isSome := by
      simp only [Option.isSome_map]
    _ = (Moist.SMT.Compiler.compile? kind fuel declarations term).isSome :=
      congrArg Option.isSome (compile_map_script kind fuel declarations term)
    _ = _ := CheckedCompiler.compile_isSome kind fuel declarations term

end CertifiedCompilation

end Moist.SMT.UPLC.Soundness
