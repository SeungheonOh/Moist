import Moist.SMT.Compiler.InputChecked
import Moist.SMT.Soundness.OutputContract

/-!
# Certification of the proof-free compiler

The portable compiler returns only `Option Script` and does not expand its
generated assertion DAG for a redundant structural validation pass.  This
module proves what a successful result contains, then postchecks that exact
stored script before lifting it into the proof-carrying CEK boundary.  Neither
certification nor postchecking invokes symbolic evaluation again.
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

@[simp] theorem compile_isSome (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term).isSome =
      Moist.SMT.Compiler.inputAccepted declarations term := by
  by_cases hInput : Moist.SMT.Compiler.inputAccepted declarations term = true <;>
    simp [Moist.SMT.Compiler.compileInputChecked?, hInput]

/-- The proof boundary's explicit generated-output postcheck.  Keeping this
separate from `Moist.SMT.Compiler.compileInputChecked?` avoids a tree walk on
the input-checked hot path.  This postcheck still structurally traverses the
generated assertions and may be costly for shared DAGs; it consumes the exact
returned script and never recompiles it. -/
def postcheck? (declarations : List SymDecl)
    (result : Option Moist.SMT.Script) : Option Moist.SMT.Script := do
  let script ← result
  let _ ← GeneratedOutputContract.check declarations script
  pure script

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
    (hResult : Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term = some script) :
    Option (CertifiedCompilation kind fuel declarations term) :=
  match GeneratedOutputContract.check declarations script with
  | none => none
  | some output =>
      have hResultComponents := CheckedCompiler.compileInputChecked_some hResult
      have hInput := CheckedCompiler.inputAccepted_components declarations term
        hResultComponents.1
      some
        { script
          script_eq := hResultComponents.2
          declarationsNoOpaque := hInput.1
          declarationsRendererSafe := hInput.2.1
          declarationsSortSafe := hInput.2.2.1
          declarationsInputSafe := hInput.2.2.2.1
          declarationNamesDistinct := hInput.2.2.2.2.1
          termNoOpaque := hInput.2.2.2.2.2
          output }

/-- Certify the result returned by the proof-free compiler without
reconstructing its script or invoking symbolic evaluation again. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    Option (CertifiedCompilation kind fuel declarations term) :=
  match hResult : Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term with
  | none => none
  | some _script => certifySome hResult

/-- Certification is exactly portable compilation followed by the existing
generated-output contract; its mapped script cannot differ. -/
@[simp] theorem compile_map_script (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (compile? kind fuel declarations term).map (·.script) =
      CheckedCompiler.postcheck? declarations
        (Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term) := by
  unfold compile?
  split
  · simp_all [CheckedCompiler.postcheck?]
  · rename_i script hResult
    unfold certifySome CheckedCompiler.postcheck?
    split <;> simp_all

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
    _ = (CheckedCompiler.postcheck? declarations
        (Moist.SMT.Compiler.compileInputChecked? kind fuel declarations term)).isSome :=
      congrArg Option.isSome (compile_map_script kind fuel declarations term)
    _ = _ := by
      by_cases hInput : Moist.SMT.Compiler.inputAccepted declarations term = true
      <;> simp [CheckedCompiler.postcheck?,
        Moist.SMT.Compiler.compileInputChecked?, Option.isSome_bind,
        GeneratedOutputContract.check_isSome, hInput]

end CertifiedCompilation

end Moist.SMT.UPLC.Soundness
