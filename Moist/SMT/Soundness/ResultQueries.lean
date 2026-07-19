import Moist.SMT.Soundness.Assertions

/-!
# General proof-carrying result queries

This module is the exact CEK-sound wrapper for the base production
`Compiler.compile?` API.  Unlike the assertion-oriented wrapper, its erasure
is definitionally tied to the no-assertion compiler entry point, including the
general success and Boolean-false cases.
-/

namespace Moist.SMT.UPLC.Soundness

set_option maxHeartbeats 1000000

open Moist.Plutus.Term
open Moist.CEK (CekEnv)

/-- Empty source assertions produce the exact canonical base query script. -/
theorem scriptForWithAssertions_empty
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations [] term =
      Moist.SMT.Compiler.scriptFor kind fuel declarations term := by
  cases kind <;> rfl

/-- A fully checked, proof-carrying wrapper around the exact script returned
by the general base production compiler. -/
structure ResultQuery (kind : Moist.SMT.Compiler.QueryKind) where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm
  script : Moist.SMT.Script
  script_eq : script = Moist.SMT.Compiler.scriptFor
    kind fuel inputs.declarations program.term
  output : GeneratedOutputContract inputs.declarations script

namespace ResultQuery

/-- Compile once through `Compiler.compile?`, then attach erased kernel
evidence to that exact stored script. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    Option (ResultQuery kind) := do
  let compilation ← CertifiedCompilation.compile?
    kind fuel declarations term
  let inputs : SupportedDeclarations :=
    { declarations
      noOpaque := compilation.declarationsNoOpaque
      rendererSafe := compilation.declarationsRendererSafe
      sortSafe := compilation.declarationsSortSafe
      inputSafe := compilation.declarationsInputSafe
      namesDistinct := compilation.declarationNamesDistinct }
  let program : SupportedTerm :=
    { term, noOpaque := compilation.termNoOpaque }
  pure
    { fuel, inputs, program
      script := compilation.script
      script_eq := compilation.script_eq
      output := compilation.output }

def compileSucceeds? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option (ResultQuery .succeeds) :=
  compile? .succeeds fuel declarations term

def compileBoolTrue? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option (ResultQuery .boolTrue) :=
  compile? .boolTrue fuel declarations term

def compileBoolEq? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Bool) :
    Option (ResultQuery (.boolEq expected)) :=
  compile? (.boolEq expected) fuel declarations term

def compileIntEq? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) :
    Option (ResultQuery (.intEq expected)) :=
  compile? (.intEq expected) fuel declarations term

def compileError? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option (ResultQuery .error) :=
  compile? .error fuel declarations term

/-- Certify the exact call-by-value verification program
`.Apply consumer term`. The consumer expression is evaluated first, as in CEK. -/
def compileResultProgram?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (term consumer : Term) :
    Option (ResultQuery expectation) :=
  compile? expectation fuel declarations (.Apply consumer term)

/-- Boolean-true result-predicate specialization. -/
def compileResultSatisfies? (fuel : Nat)
    (declarations : List SymDecl) (term predicate : Term) :
    Option (ResultQuery (.boolEq true)) :=
  compileResultProgram? (.boolEq true) fuel declarations term predicate

/-- Erasing certification yields exactly the base production compiler
result, for every generalized expectation. -/
@[simp] theorem compile_map_script
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) :
    (compile? kind fuel declarations term).map (·.script) =
      Moist.SMT.Compiler.compile? kind fuel declarations term := by
  calc
    (compile? kind fuel declarations term).map (·.script) =
        (CertifiedCompilation.compile?
          kind fuel declarations term).map (·.script) := by
      unfold compile?
      generalize hCompilation : CertifiedCompilation.compile?
        kind fuel declarations term = result
      cases result <;> rfl
    _ = _ := CertifiedCompilation.compile_map_script
      kind fuel declarations term

@[simp] theorem compileResultProgram_map_script
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (term consumer : Term) :
    (compileResultProgram?
        expectation fuel declarations term consumer).map (·.script) =
      Moist.SMT.Compiler.compileResultProgram?
        expectation fuel declarations term consumer := by
  exact compile_map_script expectation fuel declarations
    (.Apply consumer term)

@[simp] theorem compileResultSatisfies_map_script (fuel : Nat)
    (declarations : List SymDecl) (term predicate : Term) :
    (compileResultSatisfies?
        fuel declarations term predicate).map (·.script) =
      Moist.SMT.Compiler.compileResultSatisfies?
        fuel declarations term predicate := by
  exact compile_map_script (.boolEq true) fuel declarations
    (.Apply predicate term)

/-- Successful base-facade compilation preserves the caller's exact fuel,
declarations, and UPLC program. -/
theorem compile_some_fields
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {term : Term}
    {compiled : ResultQuery kind}
    (hcompile : compile? kind fuel declarations term = some compiled) :
    compiled.fuel = fuel ∧
      compiled.inputs.declarations = declarations ∧
      compiled.program.term = term := by
  unfold compile? at hcompile
  generalize hCompilation : CertifiedCompilation.compile?
    kind fuel declarations term = result at hcompile
  cases result with
  | none => simp at hcompile
  | some compilation =>
      simp at hcompile
      subst compiled
      exact ⟨rfl, rfl, rfl⟩

/-- Reuse the already-audited asserted-query theorem with an empty assertion
set.  The script conversion is proved above by exhaustive cases on the shared
result expectation. -/
def asAssertedQuery (query : ResultQuery kind) : AssertedQuery kind :=
  { fuel := query.fuel
    inputs := query.inputs
    assertions := []
    assertionsNoOpaque := by simp
    program := query.program
    script := query.script
    script_eq := query.script_eq.trans
      (scriptForWithAssertions_empty kind query.fuel
        query.inputs.declarations query.program.term).symm
    output := query.output }

noncomputable def cekEnv (query : ResultQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) : CekEnv :=
  AssertedQuery.cekEnv (asAssertedQuery query) z3

/-- A certified model of the exact base compiler script proves the selected
result of the actual CEK transition system. -/
theorem sound (query : ResultQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekQueryResult kind (cekEnv query z3) query.program.term := by
  exact AssertedQuery.target_sound (asAssertedQuery query) z3

/-- Source-facing soundness for the exact result returned by the base
production compiler. -/
theorem compile_sound {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {term : Term}
    {compiled : ResultQuery kind}
    (hcompile : compile? kind fuel declarations term = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.script) :
    CekExpectationHolds kind (cekEnv compiled z3) term := by
  obtain ⟨_hFuel, _hDeclarations, hTerm⟩ :=
    compile_some_fields hcompile
  simpa [CekQueryResult, hTerm] using sound compiled z3

/-- Source-facing soundness for an arbitrary ordinary UPLC result consumer. -/
theorem compileResultProgram_sound
    {expectation : UplcAssertionExpectation} {fuel : Nat}
    {declarations : List SymDecl} {term consumer : Term}
    {compiled : ResultQuery expectation}
    (hcompile : compileResultProgram?
      expectation fuel declarations term consumer = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.script) :
    CekExpectationHolds expectation (cekEnv compiled z3)
      (.Apply consumer term) := by
  exact compile_sound hcompile z3

end ResultQuery

end Moist.SMT.UPLC.Soundness
