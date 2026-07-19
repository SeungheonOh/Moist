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

/-! ## Certification for UPLC assertion queries -/

namespace CheckedCompiler

/-- Successful validation of an assertion list yields the supported-fragment
fact for every original UPLC term. -/
theorem assertionsAccepted_member (assertions : List UplcAssertion)
    (hAccepted : Moist.SMT.Compiler.assertionsAccepted assertions = true)
    (assertion : UplcAssertion) (hMember : assertion ∈ assertions) :
    termUsesOpaqueBuiltinForSoundness assertion.term = false := by
  have hAssertion :=
    List.all_eq_true.mp hAccepted assertion hMember
  cases hUses : termUsesOpaqueBuiltinForSoundness assertion.term <;>
    simp_all [Moist.SMT.Compiler.assertionsAccepted]

theorem inputWithAssertionsAccepted_components
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term)
    (h : Moist.SMT.Compiler.inputWithAssertionsAccepted
      declarations assertions term = true) :
    symEnvNoOpaqueForSoundness (envOf declarations) = true ∧
      declarationsRendererSafe declarations = true ∧
      declarationsSortSafe declarations = true ∧
      declarationsInputSafe declarations = true ∧
      declarationNamesDistinct declarations = true ∧
      termUsesOpaqueBuiltinForSoundness term = false ∧
      (∀ assertion, assertion ∈ assertions →
        termUsesOpaqueBuiltinForSoundness assertion.term = false) := by
  simp only [Moist.SMT.Compiler.inputWithAssertionsAccepted,
    Bool.and_eq_true] at h
  have hInput := inputAccepted_components declarations term h.1
  exact ⟨hInput.1, hInput.2.1, hInput.2.2.1, hInput.2.2.2.1,
    hInput.2.2.2.2.1, hInput.2.2.2.2.2,
    fun assertion hMember =>
      assertionsAccepted_member assertions h.2 assertion hMember⟩

theorem assertionSetInputAccepted_components
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (h : Moist.SMT.Compiler.assertionSetInputAccepted
      declarations assertions = true) :
    symEnvNoOpaqueForSoundness (envOf declarations) = true ∧
      declarationsRendererSafe declarations = true ∧
      declarationsSortSafe declarations = true ∧
      declarationsInputSafe declarations = true ∧
      declarationNamesDistinct declarations = true ∧
      (∀ assertion, assertion ∈ assertions →
        termUsesOpaqueBuiltinForSoundness assertion.term = false) := by
  simp only [Moist.SMT.Compiler.assertionSetInputAccepted,
    Bool.and_eq_true] at h
  rcases h with
    ⟨⟨⟨⟨⟨hOpaque, hRenderer⟩, hSort⟩, hInput⟩, hDistinct⟩,
      hAssertions⟩
  exact ⟨hOpaque, hRenderer, hSort, hInput, hDistinct,
    fun assertion hMember =>
      assertionsAccepted_member assertions hAssertions assertion hMember⟩

theorem compileWithAssertionsInputChecked_some
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {term : Term} {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileWithAssertionsInputChecked?
      kind fuel declarations assertions term = some script) :
    Moist.SMT.Compiler.inputWithAssertionsAccepted
        declarations assertions term = true ∧
      script = Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations assertions term := by
  by_cases hInput : Moist.SMT.Compiler.inputWithAssertionsAccepted
      declarations assertions term = true
  · have hScript : script = Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations assertions term := by
      simpa [Moist.SMT.Compiler.compileWithAssertionsInputChecked?, hInput]
        using h.symm
    exact ⟨hInput, hScript⟩
  · simp [Moist.SMT.Compiler.compileWithAssertionsInputChecked?, hInput] at h

theorem compileWithAssertions_some
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {term : Term} {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileWithAssertions?
      kind fuel declarations assertions term = some script) :
    Moist.SMT.Compiler.inputWithAssertionsAccepted
        declarations assertions term = true ∧
      script = Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations assertions term ∧
      Moist.SMT.Compiler.outputAccepted declarations script = true := by
  by_cases hInput : Moist.SMT.Compiler.inputWithAssertionsAccepted
      declarations assertions term = true
  · by_cases hOutput : Moist.SMT.Compiler.outputAccepted declarations
        (Moist.SMT.Compiler.scriptForWithAssertions
          kind fuel declarations assertions term) = true
    · have hScript : script = Moist.SMT.Compiler.scriptForWithAssertions
          kind fuel declarations assertions term := by
        simpa [Moist.SMT.Compiler.compileWithAssertions?,
          Moist.SMT.Compiler.compileWithAssertionsInputChecked?, hInput,
          Moist.SMT.Compiler.outputChecked?, hOutput] using h.symm
      subst script
      exact ⟨hInput, rfl, hOutput⟩
    · simp [Moist.SMT.Compiler.compileWithAssertions?,
        Moist.SMT.Compiler.compileWithAssertionsInputChecked?, hInput,
        Moist.SMT.Compiler.outputChecked?, hOutput] at h
  · simp [Moist.SMT.Compiler.compileWithAssertions?,
      Moist.SMT.Compiler.compileWithAssertionsInputChecked?, hInput] at h

theorem compileAssertionsSatisfiable_some
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {script : Moist.SMT.Script}
    (h : Moist.SMT.Compiler.compileAssertionsSatisfiable?
      declarations assertions = some script) :
    Moist.SMT.Compiler.assertionSetInputAccepted declarations assertions = true ∧
      script = scriptForAssertionsSatisfiable declarations assertions ∧
      Moist.SMT.Compiler.outputAccepted declarations script = true := by
  by_cases hInput : Moist.SMT.Compiler.assertionSetInputAccepted
      declarations assertions = true
  · by_cases hOutput : Moist.SMT.Compiler.outputAccepted declarations
        (scriptForAssertionsSatisfiable declarations assertions) = true
    · have hScript : script =
          scriptForAssertionsSatisfiable declarations assertions := by
        simpa [Moist.SMT.Compiler.compileAssertionsSatisfiable?,
          Moist.SMT.Compiler.compileAssertionsSatisfiableInputChecked?, hInput,
          Moist.SMT.Compiler.outputChecked?, hOutput] using h.symm
      subst script
      exact ⟨hInput, rfl, hOutput⟩
    · simp [Moist.SMT.Compiler.compileAssertionsSatisfiable?,
        Moist.SMT.Compiler.compileAssertionsSatisfiableInputChecked?, hInput,
        Moist.SMT.Compiler.outputChecked?, hOutput] at h
  · simp [Moist.SMT.Compiler.compileAssertionsSatisfiable?,
      Moist.SMT.Compiler.compileAssertionsSatisfiableInputChecked?, hInput] at h

theorem inputWithAssertionsAccepted_assertionSet
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term)
    (h : Moist.SMT.Compiler.inputWithAssertionsAccepted
      declarations assertions term = true) :
    Moist.SMT.Compiler.assertionSetInputAccepted
      declarations assertions = true := by
  have components :=
    inputWithAssertionsAccepted_components declarations assertions term h
  simp only [Moist.SMT.Compiler.assertionSetInputAccepted,
    Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨components.1, components.2.1⟩,
    components.2.2.1⟩, components.2.2.2.1⟩,
    components.2.2.2.2.1⟩, by
      apply List.all_eq_true.mpr
      intro assertion hMember
      simpa using components.2.2.2.2.2.2 assertion hMember⟩

theorem compileAssertionQueries_some
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {term : Term} {scripts : Moist.SMT.Compiler.AssertionQueryScripts}
    (h : Moist.SMT.Compiler.compileAssertionQueries?
      kind fuel declarations assertions term = some scripts) :
    Moist.SMT.Compiler.inputWithAssertionsAccepted
        declarations assertions term = true ∧
      scripts = Moist.SMT.Compiler.scriptsForWithAssertions
        kind fuel declarations assertions term ∧
      Moist.SMT.Compiler.outputAccepted
          declarations scripts.satisfiability = true ∧
      Moist.SMT.Compiler.outputAccepted declarations scripts.target = true := by
  by_cases hInput : Moist.SMT.Compiler.inputWithAssertionsAccepted
      declarations assertions term = true
  · let canonical := Moist.SMT.Compiler.scriptsForWithAssertions
      kind fuel declarations assertions term
    by_cases hOutput : Moist.SMT.Compiler.assertionQueriesOutputAccepted
        declarations canonical = true
    · have hScripts : scripts = canonical := by
        simpa [Moist.SMT.Compiler.compileAssertionQueries?,
          Moist.SMT.Compiler.compileAssertionQueriesInputChecked?, hInput,
          Moist.SMT.Compiler.assertionQueriesOutputChecked?, hOutput,
          canonical] using h.symm
      have hOutputs :
          Moist.SMT.Compiler.outputAccepted
              declarations canonical.satisfiability = true ∧
            Moist.SMT.Compiler.outputAccepted
              declarations canonical.target = true := by
        simpa [Moist.SMT.Compiler.assertionQueriesOutputAccepted]
          using hOutput
      subst scripts
      exact ⟨hInput, rfl, hOutputs⟩
    · simp [Moist.SMT.Compiler.compileAssertionQueries?,
        Moist.SMT.Compiler.compileAssertionQueriesInputChecked?, hInput,
        Moist.SMT.Compiler.assertionQueriesOutputChecked?, hOutput,
        canonical] at h
  · simp [Moist.SMT.Compiler.compileAssertionQueries?,
      Moist.SMT.Compiler.compileAssertionQueriesInputChecked?, hInput] at h

/-- A successful bundled compilation is exactly the two successful legacy
checked compilations, never a proof-side reconstruction. -/
theorem compileAssertionQueries_some_separate
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {term : Term} {scripts : Moist.SMT.Compiler.AssertionQueryScripts}
    (h : Moist.SMT.Compiler.compileAssertionQueries?
      kind fuel declarations assertions term = some scripts) :
    Moist.SMT.Compiler.compileAssertionsSatisfiable?
        declarations assertions = some scripts.satisfiability ∧
      Moist.SMT.Compiler.compileWithAssertions?
        kind fuel declarations assertions term = some scripts.target := by
  have components := compileAssertionQueries_some h
  have hAssertionInput := inputWithAssertionsAccepted_assertionSet
    declarations assertions term components.1
  have hScripts := components.2.1
  have hSatOutput := components.2.2.1
  have hTargetOutput := components.2.2.2
  subst scripts
  have hSatOutput' : Moist.SMT.Compiler.outputAccepted declarations
      (scriptForAssertionsSatisfiable declarations assertions) = true := by
    simpa using hSatOutput
  have hTargetOutput' : Moist.SMT.Compiler.outputAccepted declarations
      (Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations assertions term) = true := by
    simpa using hTargetOutput
  constructor
  · simp [Moist.SMT.Compiler.compileAssertionsSatisfiable?,
      Moist.SMT.Compiler.compileAssertionsSatisfiableInputChecked?,
      hAssertionInput, Moist.SMT.Compiler.outputChecked?, hSatOutput']
  · simp [Moist.SMT.Compiler.compileWithAssertions?,
      Moist.SMT.Compiler.compileWithAssertionsInputChecked?, components.1,
      Moist.SMT.Compiler.outputChecked?, hTargetOutput']

end CheckedCompiler

/-- Kernel evidence attached to the exact proof-free target script compiled
under UPLC assertions. -/
structure CertifiedAssertedCompilation
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) where
  script : Moist.SMT.Script
  script_eq : script = Moist.SMT.Compiler.scriptForWithAssertions
    kind fuel declarations assertions term
  declarationsNoOpaque :
    symEnvNoOpaqueForSoundness (envOf declarations) = true
  declarationsRendererSafe : declarationsRendererSafe declarations = true
  declarationsSortSafe : declarationsSortSafe declarations = true
  declarationsInputSafe : declarationsInputSafe declarations = true
  declarationNamesDistinct : declarationNamesDistinct declarations = true
  termNoOpaque : termUsesOpaqueBuiltinForSoundness term = false
  assertionsNoOpaque : ∀ assertion, assertion ∈ assertions →
    termUsesOpaqueBuiltinForSoundness assertion.term = false
  output : GeneratedOutputContract declarations script

namespace CertifiedAssertedCompilation

private def certifySome
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {term : Term} {script : Moist.SMT.Script}
    (hResult : Moist.SMT.Compiler.compileWithAssertions?
      kind fuel declarations assertions term = some script) :
    CertifiedAssertedCompilation kind fuel declarations assertions term :=
  have hResultComponents :=
    CheckedCompiler.compileWithAssertions_some hResult
  have hInput := CheckedCompiler.inputWithAssertionsAccepted_components
    declarations assertions term hResultComponents.1
  { script
    script_eq := hResultComponents.2.1
    declarationsNoOpaque := hInput.1
    declarationsRendererSafe := hInput.2.1
    declarationsSortSafe := hInput.2.2.1
    declarationsInputSafe := hInput.2.2.2.1
    declarationNamesDistinct := hInput.2.2.2.2.1
    termNoOpaque := hInput.2.2.2.2.2.1
    assertionsNoOpaque := hInput.2.2.2.2.2.2
    output := GeneratedOutputContract.ofOutputAccepted hResultComponents.2.2 }

/-- Certify the exact proof-free asserted-query result without recompiling. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) :
    Option (CertifiedAssertedCompilation
      kind fuel declarations assertions term) :=
  match hResult : Moist.SMT.Compiler.compileWithAssertions?
      kind fuel declarations assertions term with
  | none => none
  | some _script => some (certifySome hResult)

@[simp] theorem compile_map_script (kind : Moist.SMT.Compiler.QueryKind)
    (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    (compile? kind fuel declarations assertions term).map (·.script) =
      Moist.SMT.Compiler.compileWithAssertions?
        kind fuel declarations assertions term := by
  unfold compile?
  split <;> simp_all [certifySome]

end CertifiedAssertedCompilation

/-- Kernel evidence for the exact assertion-only non-vacuity script. -/
structure CertifiedAssertionSetCompilation
    (declarations : List SymDecl) (assertions : List UplcAssertion) where
  script : Moist.SMT.Script
  script_eq : script = scriptForAssertionsSatisfiable declarations assertions
  declarationsNoOpaque :
    symEnvNoOpaqueForSoundness (envOf declarations) = true
  declarationsRendererSafe : declarationsRendererSafe declarations = true
  declarationsSortSafe : declarationsSortSafe declarations = true
  declarationsInputSafe : declarationsInputSafe declarations = true
  declarationNamesDistinct : declarationNamesDistinct declarations = true
  assertionsNoOpaque : ∀ assertion, assertion ∈ assertions →
    termUsesOpaqueBuiltinForSoundness assertion.term = false
  output : GeneratedOutputContract declarations script

namespace CertifiedAssertionSetCompilation

private def certifySome
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {script : Moist.SMT.Script}
    (hResult : Moist.SMT.Compiler.compileAssertionsSatisfiable?
      declarations assertions = some script) :
    CertifiedAssertionSetCompilation declarations assertions :=
  have hResultComponents :=
    CheckedCompiler.compileAssertionsSatisfiable_some hResult
  have hInput := CheckedCompiler.assertionSetInputAccepted_components
    declarations assertions hResultComponents.1
  { script
    script_eq := hResultComponents.2.1
    declarationsNoOpaque := hInput.1
    declarationsRendererSafe := hInput.2.1
    declarationsSortSafe := hInput.2.2.1
    declarationsInputSafe := hInput.2.2.2.1
    declarationNamesDistinct := hInput.2.2.2.2.1
    assertionsNoOpaque := hInput.2.2.2.2.2
    output := GeneratedOutputContract.ofOutputAccepted hResultComponents.2.2 }

def compile? (declarations : List SymDecl)
    (assertions : List UplcAssertion) :
    Option (CertifiedAssertionSetCompilation declarations assertions) :=
  match hResult : Moist.SMT.Compiler.compileAssertionsSatisfiable?
      declarations assertions with
  | none => none
  | some _script => some (certifySome hResult)

@[simp] theorem compile_map_script (declarations : List SymDecl)
    (assertions : List UplcAssertion) :
    (compile? declarations assertions).map (·.script) =
      Moist.SMT.Compiler.compileAssertionsSatisfiable?
        declarations assertions := by
  unfold compile?
  split <;> simp_all [certifySome]

end CertifiedAssertionSetCompilation

/-- Kernel evidence for the exact pair returned by the shared assertion
compiler.  Both scripts are tied to the same source declarations and UPLC
assertion list. -/
structure CertifiedAssertionQueriesCompilation
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) where
  scripts : Moist.SMT.Compiler.AssertionQueryScripts
  satisfiability_eq : scripts.satisfiability =
    scriptForAssertionsSatisfiable declarations assertions
  target_eq : scripts.target =
    Moist.SMT.Compiler.scriptForWithAssertions
      kind fuel declarations assertions term
  declarationsNoOpaque :
    symEnvNoOpaqueForSoundness (envOf declarations) = true
  declarationsRendererSafe : declarationsRendererSafe declarations = true
  declarationsSortSafe : declarationsSortSafe declarations = true
  declarationsInputSafe : declarationsInputSafe declarations = true
  declarationNamesDistinct : declarationNamesDistinct declarations = true
  termNoOpaque : termUsesOpaqueBuiltinForSoundness term = false
  assertionsNoOpaque : ∀ assertion, assertion ∈ assertions →
    termUsesOpaqueBuiltinForSoundness assertion.term = false
  satisfiabilityOutput :
    GeneratedOutputContract declarations scripts.satisfiability
  targetOutput : GeneratedOutputContract declarations scripts.target

namespace CertifiedAssertionQueriesCompilation

private def certifySome
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {assertions : List UplcAssertion}
    {term : Term}
    {scripts : Moist.SMT.Compiler.AssertionQueryScripts}
    (hResult : Moist.SMT.Compiler.compileAssertionQueries?
      kind fuel declarations assertions term = some scripts) :
    CertifiedAssertionQueriesCompilation
      kind fuel declarations assertions term :=
  have hResultComponents :=
    CheckedCompiler.compileAssertionQueries_some hResult
  have hInput := CheckedCompiler.inputWithAssertionsAccepted_components
    declarations assertions term hResultComponents.1
  have hSatisfiability : scripts.satisfiability =
      scriptForAssertionsSatisfiable declarations assertions := by
    calc
      scripts.satisfiability =
          (Moist.SMT.Compiler.scriptsForWithAssertions
            kind fuel declarations assertions term).satisfiability :=
        congrArg (·.satisfiability) hResultComponents.2.1
      _ = _ := scriptsForWithAssertions_satisfiability _ _ _ _ _
  have hTarget : scripts.target =
      Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations assertions term := by
    calc
      scripts.target =
          (Moist.SMT.Compiler.scriptsForWithAssertions
            kind fuel declarations assertions term).target :=
        congrArg (·.target) hResultComponents.2.1
      _ = _ := scriptsForWithAssertions_target _ _ _ _ _
  { scripts
    satisfiability_eq := hSatisfiability
    target_eq := hTarget
    declarationsNoOpaque := hInput.1
    declarationsRendererSafe := hInput.2.1
    declarationsSortSafe := hInput.2.2.1
    declarationsInputSafe := hInput.2.2.2.1
    declarationNamesDistinct := hInput.2.2.2.2.1
    termNoOpaque := hInput.2.2.2.2.2.1
    assertionsNoOpaque := hInput.2.2.2.2.2.2
    satisfiabilityOutput :=
      GeneratedOutputContract.ofOutputAccepted hResultComponents.2.2.1
    targetOutput :=
      GeneratedOutputContract.ofOutputAccepted hResultComponents.2.2.2 }

/-- Certify the exact proof-free pair without reconstructing either script. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) :
    Option (CertifiedAssertionQueriesCompilation
      kind fuel declarations assertions term) :=
  match hResult : Moist.SMT.Compiler.compileAssertionQueries?
      kind fuel declarations assertions term with
  | none => none
  | some _scripts => some (certifySome hResult)

@[simp] theorem compile_map_scripts (kind : Moist.SMT.Compiler.QueryKind)
    (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    (compile? kind fuel declarations assertions term).map (·.scripts) =
      Moist.SMT.Compiler.compileAssertionQueries?
        kind fuel declarations assertions term := by
  unfold compile?
  split <;> simp_all [certifySome]

/-- Zero-recompilation projection to the existing asserted target
certificate. -/
def toAsserted
    (compilation : CertifiedAssertionQueriesCompilation
      kind fuel declarations assertions term) :
    CertifiedAssertedCompilation
      kind fuel declarations assertions term :=
  { script := compilation.scripts.target
    script_eq := compilation.target_eq
    declarationsNoOpaque := compilation.declarationsNoOpaque
    declarationsRendererSafe := compilation.declarationsRendererSafe
    declarationsSortSafe := compilation.declarationsSortSafe
    declarationsInputSafe := compilation.declarationsInputSafe
    declarationNamesDistinct := compilation.declarationNamesDistinct
    termNoOpaque := compilation.termNoOpaque
    assertionsNoOpaque := compilation.assertionsNoOpaque
    output := compilation.targetOutput }

/-- Zero-recompilation projection to the existing non-vacuity certificate. -/
def toAssertionSet
    (compilation : CertifiedAssertionQueriesCompilation
      kind fuel declarations assertions term) :
    CertifiedAssertionSetCompilation declarations assertions :=
  { script := compilation.scripts.satisfiability
    script_eq := compilation.satisfiability_eq
    declarationsNoOpaque := compilation.declarationsNoOpaque
    declarationsRendererSafe := compilation.declarationsRendererSafe
    declarationsSortSafe := compilation.declarationsSortSafe
    declarationsInputSafe := compilation.declarationsInputSafe
    declarationNamesDistinct := compilation.declarationNamesDistinct
    assertionsNoOpaque := compilation.assertionsNoOpaque
    output := compilation.satisfiabilityOutput }

end CertifiedAssertionQueriesCompilation

end Moist.SMT.UPLC.Soundness
