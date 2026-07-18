import Moist.SMT.Soundness.SolverInput
import Moist.SMT.Render

/-!
# Solver/model boundary

The CEK soundness theorems consume the executable semantics in
`Moist.SMT.Semantics`; an untrusted string containing the word `sat` is not a
proof of their premises.  This module makes the one external boundary
explicit: a solver integration must decode its model and certify every
generated assertion under that executable semantics.

The low-level script theorems below establish the demand-selected prelude
syntactically.
The proof-carrying query API rejects terms and declaration environments that
contain opaque builtins before it emits a production query.  The one remaining
trusted step is the user-accepted
rendering/SMT-LIB/Z3 bridge: submit exactly the reference rendering, or the
operational DAG rendering; decode the actual Z3 model; and transfer every
assertion into `Semantics.eval`.  The pointer-based DAG renderer is `unsafe`,
so its equivalence to the reference renderer deliberately remains in that
external boundary rather than being disguised as a kernel theorem.  Once the
semantic certificate is available, all three supported compiler queries
compose directly with the CEK theorems below, without a caller-supplied
fragment premise.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekEnv)

/-- Kernel-checkable equality for integrations using the transparent
reference renderer.  `Script.renderDag` is intentionally absent: it uses
pointer identity and therefore belongs to the explicit external boundary. -/
def IsReferenceRendering (script : Moist.SMT.Script) (text : String) : Prop :=
  text = script.render

/-- A script contains the exact demand-selected compiler prelude for its own
assertions, in order.  Tying selection to `script.assertions` prevents an
unrelated witness from weakening this syntactic boundary invariant. -/
def hasCompilerPrelude (script : Moist.SMT.Script) : Prop :=
  ∃ suffix,
    script.commands = preludeForAssertions script.assertions ++ suffix

/--
A decoded solver model at the trusted SMT-LIB boundary.

`assertionsTrue` is the exact semantic-transfer premise: all assertions,
including declaration validity assumptions, are true in the same executable
model used by the CEK simulation.  Neither a `sat` token nor syntactic prelude
membership can construct this field.
-/
structure CertifiedZ3Model (inputs : SupportedDeclarations)
    (script : Moist.SMT.Script) where
  model : SmtSem.Model
  /-- The external model bridge is limited to the values and sorts of symbols
  actually declared by the checked input.  Total composite-expression typing
  and evaluation, plus direct `Val` decoding, are proved internally; the
  latter also uses the exact `val_valid` assertion from `assertionsTrue`. -/
  inputSemantics : SolverInputModel inputs.declarations model
  assertionsTrue : ∀ e, e ∈ script.assertions →
    SmtSem.evalBoolIs model e true = true

/-- Semantic satisfiability exposed to solver integrations.  Raw Z3 `sat`
must be accompanied by a `CertifiedZ3Model` carrying the exact model bridge
and assertion semantics; no theorem treats the status token alone as
evidence. -/
def Z3Sat (inputs : SupportedDeclarations)
    (script : Moist.SMT.Script) : Prop :=
  Nonempty (CertifiedZ3Model inputs script)

namespace CertifiedZ3Model

/-- Declaration assertions in the certified script, together with the
checked input grammar, determine one exact CEK environment.  Environment
decoding is a theorem, not a field supplied by the solver integration. -/
theorem environmentDecodes {inputs : SupportedDeclarations}
    {script : Moist.SMT.Script} (z3 : CertifiedZ3Model inputs script)
    (declarationAssertionsIncluded : ∀ expression,
      expression ∈ inputs.declarations.flatMap SymDecl.assumptions →
        expression ∈ script.assertions) :
    ∃ environment, symEnvToCek? z3.model (envOf inputs.declarations) =
      some environment := by
  apply declarationsInputSafe_decodes z3.inputSemantics
    inputs.inputSafe inputs.sortSafe
  intro declaration hdeclaration expression hexpression
  apply z3.assertionsTrue
  apply declarationAssertionsIncluded
  simp only [List.mem_flatMap]
  exact ⟨declaration, hdeclaration, hexpression⟩

end CertifiedZ3Model

theorem scriptWith_hasCompilerPrelude (decls : List SymDecl)
    (assertions : List SExpr) :
    hasCompilerPrelude (scriptWith decls assertions) := by
  refine ⟨declCommands decls ++ assumptionCommands decls ++
    groupedAssertionCommands assertions ++
      [.checkSatUsing z3QueryTactic, .getModel], ?_⟩
  rw [scriptWith_assertions]
  simp [scriptWith, scriptWithTactic, List.append_assoc]

theorem scriptForBoolTrue_hasCompilerPrelude (fuel : Nat)
    (decls : List SymDecl) (t : Term) :
    hasCompilerPrelude (scriptForBoolTrue fuel decls t) := by
  exact scriptWith_hasCompilerPrelude _ _

theorem scriptForIntEq_hasCompilerPrelude (fuel : Nat)
    (decls : List SymDecl) (t : Term) (rhs : SExpr) :
    hasCompilerPrelude (scriptForIntEq fuel decls t rhs) := by
  exact scriptWith_hasCompilerPrelude _ _

theorem scriptForError_hasCompilerPrelude (fuel : Nat)
    (decls : List SymDecl) (t : Term) :
    hasCompilerPrelude (scriptForError fuel decls t) := by
  exact scriptWith_hasCompilerPrelude _ _

/-- A checked Boolean-success production query. -/
structure BoolTrueQuery where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm

namespace BoolTrueQuery

def script (query : BoolTrueQuery) : Moist.SMT.Script :=
  scriptForBoolTrue query.fuel query.inputs.declarations query.program.term

/-- Check both the term and its symbolic declaration environment. -/
def compile? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option BoolTrueQuery := do
  let inputs ← SupportedDeclarations.check declarations
  let program ← SupportedTerm.check term
  pure ⟨fuel, inputs, program⟩

@[simp] theorem compile_isSome (fuel : Nat) (declarations : List SymDecl)
    (term : Term) :
    (compile? fuel declarations term).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations &&
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hsort : declarationsSortSafe declarations = sortOk
  generalize hsafeInput : declarationsInputSafe declarations = inputOk
  generalize hdistinct : declarationNamesDistinct declarations = distinctOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases sortOk <;>
    cases inputOk <;> cases distinctOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hsort, hsafeInput, hdistinct, hterm]

theorem hasCompilerPrelude (query : BoolTrueQuery) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  exact scriptForBoolTrue_hasCompilerPrelude _ _ _

private theorem declarationAssertionsIncluded (query : BoolTrueQuery) :
    ∀ expression,
      expression ∈ query.inputs.declarations.flatMap SymDecl.assumptions →
        expression ∈ query.script.assertions := by
  intro expression hmember
  rw [script, scriptForBoolTrue_assertions]
  exact List.mem_append_left _ hmember

theorem environmentDecodes (query : BoolTrueQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∃ environment,
      symEnvToCek? z3.model (envOf query.inputs.declarations) =
        some environment :=
  z3.environmentDecodes (declarationAssertionsIncluded query)

/-- The CEK environment is derived from the checked solver input and the
model's certified declaration assertions. -/
noncomputable def cekEnv (query : BoolTrueQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) : CekEnv :=
  (environmentDecodes query z3).choose

theorem cekEnv_decodes (query : BoolTrueQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    symEnvToCek? z3.model (envOf query.inputs.declarations) =
      some (cekEnv query z3) :=
  (environmentDecodes query z3).choose_spec

/-- A certified model of a checked Boolean query yields the actual CEK
result.  Fragment membership is carried by `query`; callers cannot forget it. -/
theorem sound (query : BoolTrueQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekHaltsBoolTrue (cekEnv query z3) query.program.term := by
  apply evalSym_okBoolTrueCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    (cekEnv_decodes query z3) query.inputs.noOpaque query.program.noOpaque
  apply z3.assertionsTrue
  rw [script, scriptForBoolTrue_assertions]
  exact List.mem_append_right _ (by simp)

end BoolTrueQuery

/-- A checked query for one concrete integer result.  Restricting the public
query to a literal expected integer removes a second avoidable semantic
premise about an arbitrary right-hand SMT expression. -/
structure IntEqQuery where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm
  expected : Int

namespace IntEqQuery

def script (query : IntEqQuery) : Moist.SMT.Script :=
  scriptForIntEq query.fuel query.inputs.declarations query.program.term
    (.int query.expected)

/-- Check both the term and its symbolic declaration environment. -/
def compile? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) : Option IntEqQuery := do
  let inputs ← SupportedDeclarations.check declarations
  let program ← SupportedTerm.check term
  pure ⟨fuel, inputs, program, expected⟩

@[simp] theorem compile_isSome (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) :
    (compile? fuel declarations term expected).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations &&
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hsort : declarationsSortSafe declarations = sortOk
  generalize hsafeInput : declarationsInputSafe declarations = inputOk
  generalize hdistinct : declarationNamesDistinct declarations = distinctOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases sortOk <;>
    cases inputOk <;> cases distinctOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hsort, hsafeInput, hdistinct, hterm]

theorem hasCompilerPrelude (query : IntEqQuery) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  exact scriptForIntEq_hasCompilerPrelude _ _ _ _

private theorem declarationAssertionsIncluded (query : IntEqQuery) :
    ∀ expression,
      expression ∈ query.inputs.declarations.flatMap SymDecl.assumptions →
        expression ∈ query.script.assertions := by
  intro expression hmember
  rw [script, scriptForIntEq_assertions]
  exact List.mem_append_left _ hmember

theorem environmentDecodes (query : IntEqQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∃ environment,
      symEnvToCek? z3.model (envOf query.inputs.declarations) =
        some environment :=
  z3.environmentDecodes (declarationAssertionsIncluded query)

noncomputable def cekEnv (query : IntEqQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) : CekEnv :=
  (environmentDecodes query z3).choose

theorem cekEnv_decodes (query : IntEqQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    symEnvToCek? z3.model (envOf query.inputs.declarations) =
      some (cekEnv query z3) :=
  (environmentDecodes query z3).choose_spec

/-- A certified model of a checked integer query yields exactly the requested
CEK integer. -/
theorem sound (query : IntEqQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekHaltsInteger (cekEnv query z3) query.program.term query.expected := by
  apply evalSym_okIntEqCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    (rhs := .int query.expected) (expected := query.expected)
    (cekEnv_decodes query z3) query.inputs.noOpaque query.program.noOpaque
  · simp [Moist.SMT.Semantics.eval]
  · apply z3.assertionsTrue
    rw [script, scriptForIntEq_assertions]
    exact List.mem_append_right _ (by simp)

end IntEqQuery

/-- A checked runtime-error production query. -/
structure ErrorQuery where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm

namespace ErrorQuery

def script (query : ErrorQuery) : Moist.SMT.Script :=
  scriptForError query.fuel query.inputs.declarations query.program.term

/-- Check both the term and its symbolic declaration environment. -/
def compile? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option ErrorQuery := do
  let inputs ← SupportedDeclarations.check declarations
  let program ← SupportedTerm.check term
  pure ⟨fuel, inputs, program⟩

@[simp] theorem compile_isSome (fuel : Nat) (declarations : List SymDecl)
    (term : Term) :
    (compile? fuel declarations term).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations &&
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hsort : declarationsSortSafe declarations = sortOk
  generalize hsafeInput : declarationsInputSafe declarations = inputOk
  generalize hdistinct : declarationNamesDistinct declarations = distinctOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases sortOk <;>
    cases inputOk <;> cases distinctOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hsort, hsafeInput, hdistinct, hterm]

theorem hasCompilerPrelude (query : ErrorQuery) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  exact scriptForError_hasCompilerPrelude _ _ _

private theorem declarationAssertionsIncluded (query : ErrorQuery) :
    ∀ expression,
      expression ∈ query.inputs.declarations.flatMap SymDecl.assumptions →
        expression ∈ query.script.assertions := by
  intro expression hmember
  rw [script, scriptForError_assertions]
  exact List.mem_append_left _ hmember

theorem environmentDecodes (query : ErrorQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∃ environment,
      symEnvToCek? z3.model (envOf query.inputs.declarations) =
        some environment :=
  z3.environmentDecodes (declarationAssertionsIncluded query)

noncomputable def cekEnv (query : ErrorQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) : CekEnv :=
  (environmentDecodes query z3).choose

theorem cekEnv_decodes (query : ErrorQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    symEnvToCek? z3.model (envOf query.inputs.declarations) =
      some (cekEnv query z3) :=
  (environmentDecodes query z3).choose_spec

/-- A certified model of a checked error query reaches the actual CEK
runtime-error state in finitely many transitions. -/
theorem sound (query : ErrorQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekHaltsError (cekEnv query z3) query.program.term := by
  apply evalSym_errorCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    (cekEnv_decodes query z3) query.inputs.noOpaque query.program.noOpaque
  apply z3.assertionsTrue
  rw [script, scriptForError_assertions]
  exact List.mem_append_right _ (by simp)

end ErrorQuery

end Moist.SMT.UPLC.Soundness
