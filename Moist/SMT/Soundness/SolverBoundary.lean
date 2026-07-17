import Moist.SMT.Soundness.SolverInput

/-!
# Solver/model boundary

The CEK soundness theorems consume the executable semantics in
`Moist.SMT.Semantics`; an untrusted string containing the word `sat` is not a
proof of their premises.  This module makes the one external boundary
explicit: a solver integration must decode its model and certify every
generated assertion under that executable semantics.

The low-level script theorems below establish the fixed prelude syntactically.
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

/-- A script contains the compiler's complete fixed prelude, in order. -/
def hasCompilerPrelude (script : Moist.SMT.Script) : Prop :=
  ∃ suffix, script.commands = prelude ++ suffix

/--
A decoded solver model at the trusted SMT-LIB boundary.

`assertionsTrue` is the exact semantic-transfer premise: all assertions,
including declaration validity assumptions, are true in the same executable
model used by the CEK simulation.  Neither a `sat` token nor syntactic prelude
membership can construct this field.
-/
structure CertifiedZ3Model (decls : List SymDecl)
    (script : Moist.SMT.Script) where
  model : SmtSem.Model
  /-- The typed CEK environment decoded from exactly the symbolic
  declarations used to build the production script. -/
  cekEnv : CekEnv
  env_decodes : symEnvToCek? model (envOf decls) = some cekEnv
  assertionsTrue : ∀ e, e ∈ script.assertions →
    SmtSem.evalBoolIs model e true = true

/-- Semantic satisfiability exposed to solver integrations.  Raw Z3 `sat`
must be accompanied by a decoded `CertifiedZ3Model`; no theorem treats the
status token alone as evidence. -/
def Z3Sat (decls : List SymDecl) (script : Moist.SMT.Script) : Prop :=
  Nonempty (CertifiedZ3Model decls script)

theorem scriptWith_hasCompilerPrelude (decls : List SymDecl)
    (assertions : List SExpr) :
    hasCompilerPrelude (scriptWith decls assertions) := by
  refine ⟨declCommands decls ++ assumptionCommands decls ++
    assertions.map Moist.SMT.Command.assert ++
      [.checkSatUsing z3QueryTactic, .getModel], ?_⟩
  rfl

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

/-- A certified model of a checked Boolean query yields the actual CEK
result.  Fragment membership is carried by `query`; callers cannot forget it. -/
theorem sound (query : BoolTrueQuery)
    (z3 : CertifiedZ3Model query.inputs.declarations query.script) :
    CekHaltsBoolTrue z3.cekEnv query.program.term := by
  apply evalSym_okBoolTrueCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    z3.env_decodes query.inputs.noOpaque query.program.noOpaque
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

/-- A certified model of a checked integer query yields exactly the requested
CEK integer. -/
theorem sound (query : IntEqQuery)
    (z3 : CertifiedZ3Model query.inputs.declarations query.script) :
    CekHaltsInteger z3.cekEnv query.program.term query.expected := by
  apply evalSym_okIntEqCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    (rhs := .int query.expected) (expected := query.expected)
    z3.env_decodes query.inputs.noOpaque query.program.noOpaque
  · exact Moist.SMT.Semantics.eval.eq_7 _ _
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

/-- A certified model of a checked error query reaches the actual CEK
runtime-error state in finitely many transitions. -/
theorem sound (query : ErrorQuery)
    (z3 : CertifiedZ3Model query.inputs.declarations query.script) :
    CekHaltsError z3.cekEnv query.program.term := by
  apply evalSym_errorCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    z3.env_decodes query.inputs.noOpaque query.program.noOpaque
  apply z3.assertionsTrue
  rw [script, scriptForError_assertions]
  exact List.mem_append_right _ (by simp)

end ErrorQuery

end Moist.SMT.UPLC.Soundness
