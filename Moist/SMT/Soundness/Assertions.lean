import Moist.SMT.Soundness.SolverBoundary
import Moist.SMT.Soundness.AssertionConditions
import Moist.SMT.Soundness.AssertionErasure

/-!
# CEK-sound UPLC assertions

This module is the proof-carrying boundary for parameter predicates and other
caller-inserted assertions.  An assertion is ordinary UPLC, compiled by the
same symbolic evaluator and against the exact same declaration environment as
the target.  The production compiler never accepts raw SMT predicates here.

A certified satisfying model proves both the requested target result and the
selected result expectation for every asserted UPLC term in one identical
decoded CEK environment.  Target and assertion expectations can require any
successful value, either exact Boolean, an exact integer, or an actual runtime
error; fuel exhaustion is never treated as a CEK result.  Refinement clients should prefer
`AssertionQueryBundle`, which couples the non-vacuity and target scripts
compiled from one source assertion set.  The standalone
`AssertionSatisfiabilityQuery` remains available when a client already manages
that coupling: an unsatisfiable target obligation alone does not rule out
contradictory preconditions.
-/

namespace Moist.SMT.UPLC.Soundness

set_option maxHeartbeats 1000000

open Moist.Plutus.Term
open Moist.CEK (CekEnv)

/-- Exact CEK meaning shared by target and assertion expectations. -/
def CekExpectationHolds (expectation : UplcAssertionExpectation)
    (environment : CekEnv) (term : Term) : Prop :=
  match expectation with
  | .succeeds =>
      ∃ value, CekHaltsValue environment term value
  | .boolEq expected =>
      CekHaltsValue environment term (.VCon (.Bool expected))
  | .intEq expected =>
      CekHaltsInteger environment term expected
  | .error =>
      CekHaltsError environment term

/-- Exact CEK meaning of one source UPLC assertion. -/
def CekAssertionHolds (environment : CekEnv)
    (assertion : UplcAssertion) : Prop :=
  CekExpectationHolds assertion.expectation environment assertion.term

/-- Every original assertion holds in the same CEK environment. -/
def CekAssertionsHold (environment : CekEnv)
    (assertions : List UplcAssertion) : Prop :=
  ∀ assertion, assertion ∈ assertions →
    CekAssertionHolds environment assertion

/-- CEK proposition selected by the proof-free compiler query kind. -/
def CekQueryResult (kind : Moist.SMT.Compiler.QueryKind)
    (environment : CekEnv) (term : Term) : Prop :=
  CekExpectationHolds kind environment term

/-- One shared result condition entails precisely its finite actual CEK
reachability proposition. Target queries and source assertions both specialize
this theorem. -/
theorem resultExpectation_condition_sound {model : SmtSem.Model}
    {fuel : Nat} {ρ : List SymVal} {environment : CekEnv} {term : Term}
    (expectation : UplcAssertionExpectation)
    (henv : symEnvToCek? model ρ = some environment)
    (hdeclarations : symEnvNoOpaqueForSoundness ρ = true)
    (hterm : termNoOpaqueBuiltinsForSoundness term)
    (hcondition : SmtSem.evalBoolIs model
      (expectation.condition (evalSym fuel ρ term)) true = true) :
    CekExpectationHolds expectation environment term := by
  cases expectation with
  | succeeds =>
      exact evalSym_okCond_sound henv hdeclarations hterm
        hcondition
  | boolEq expected =>
      exact evalSym_okBoolEqCond_sound expected henv hdeclarations hterm
        hcondition
  | intEq expected =>
      apply evalSym_okIntEqCond_sound
        (rhs := .int expected) (expected := expected)
        henv hdeclarations hterm
      · simp [Moist.SMT.Semantics.eval]
      · exact hcondition
  | error =>
      exact evalSym_errorCond_sound henv hdeclarations hterm
        hcondition

/-- One compiled assertion condition entails precisely the CEK proposition
selected by its source-level expectation. -/
theorem uplcAssertion_condition_sound {model : SmtSem.Model}
    {declarations : List SymDecl} {environment : CekEnv}
    (assertion : UplcAssertion)
    (henv : symEnvToCek? model (envOf declarations) = some environment)
    (hdeclarations :
      symEnvNoOpaqueForSoundness (envOf declarations) = true)
    (hterm : termNoOpaqueBuiltinsForSoundness assertion.term)
    (hcondition : SmtSem.evalBoolIs model
      (assertion.condition declarations) true = true) :
    CekAssertionHolds environment assertion := by
  apply resultExpectation_condition_sound assertion.expectation
    henv hdeclarations hterm
  simpa [UplcAssertion.condition] using hcondition

theorem scriptForWithAssertions_hasCompilerPrelude
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) :
    hasCompilerPrelude
      (Moist.SMT.Compiler.scriptForWithAssertions
        kind fuel declarations assertions term) := by
  exact scriptWith_hasCompilerPrelude _ _

theorem scriptForAssertionsSatisfiable_hasCompilerPrelude
    (declarations : List SymDecl) (assertions : List UplcAssertion) :
    hasCompilerPrelude
      (scriptForAssertionsSatisfiable declarations assertions) := by
  exact scriptWith_hasCompilerPrelude _ _

/-- A fully checked target query restricted by ordinary UPLC assertions. -/
structure AssertedQuery (kind : Moist.SMT.Compiler.QueryKind) where
  fuel : Nat
  inputs : SupportedDeclarations
  assertions : List UplcAssertion
  assertionsNoOpaque : ∀ assertion, assertion ∈ assertions →
    termUsesOpaqueBuiltinForSoundness assertion.term = false
  program : SupportedTerm
  script : Moist.SMT.Script
  script_eq : script = Moist.SMT.Compiler.scriptForWithAssertions
    kind fuel inputs.declarations assertions program.term
  output : GeneratedOutputContract inputs.declarations script

namespace AssertedQuery

/-- Compile once through the proof-free production compiler, then attach only
erased evidence to that exact stored script. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option (AssertedQuery kind) := do
  let compilation ← CertifiedAssertedCompilation.compile?
    kind fuel declarations assertions term
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
    { fuel, inputs, assertions
      assertionsNoOpaque := compilation.assertionsNoOpaque
      program
      script := compilation.script
      script_eq := compilation.script_eq
      output := compilation.output }

def compileSucceeds? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    Option (AssertedQuery .succeeds) :=
  compile? .succeeds fuel declarations assertions term

def compileBoolTrue? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    Option (AssertedQuery .boolTrue) :=
  compile? .boolTrue fuel declarations assertions term

def compileBoolEq? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) (expected : Bool) :
    Option (AssertedQuery (.boolEq expected)) :=
  compile? (.boolEq expected) fuel declarations assertions term

def compileIntEq? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) (expected : Int) :
    Option (AssertedQuery (.intEq expected)) :=
  compile? (.intEq expected) fuel declarations assertions term

def compileError? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    Option (AssertedQuery .error) :=
  compile? .error fuel declarations assertions term

/-- Certify a source-attached UPLC query template. The dependent result records
the query's exact expectation, so `sound` returns precisely the corresponding
actual CEK proposition. -/
def compileUplcQuery? (fuel : Nat) (declarations : List SymDecl)
    (query : UplcQuery) : Option (AssertedQuery query.expectation) :=
  compile? query.expectation fuel declarations
    query.source.assertions query.target

/-- Certify a host-side assertion wrapper without changing its ordinary UPLC
target term. -/
def compileAssertedTerm? (kind : Moist.SMT.Compiler.QueryKind)
    (fuel : Nat) (declarations : List SymDecl) (source : AssertedTerm) :
    Option (AssertedQuery kind) :=
  compile? kind fuel declarations source.assertions source.term

/-- Certify arbitrary result matching through ordinary UPLC application. -/
def compileResultProgram?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm)
    (consumer : Term) : Option (AssertedQuery expectation) :=
  compileUplcQuery? fuel declarations
    (source.resultSatisfiesWith expectation consumer)

/-- Erasing proof-carrying compilation yields exactly the proof-free asserted
compiler result. -/
@[simp] theorem compile_map_script (kind : Moist.SMT.Compiler.QueryKind)
    (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    (compile? kind fuel declarations assertions term).map (·.script) =
      Moist.SMT.Compiler.compileWithAssertions?
        kind fuel declarations assertions term := by
  calc
    (compile? kind fuel declarations assertions term).map (·.script) =
        (CertifiedAssertedCompilation.compile?
          kind fuel declarations assertions term).map (·.script) := by
      unfold compile?
      generalize hCompilation : CertifiedAssertedCompilation.compile?
        kind fuel declarations assertions term = result
      cases result <;> rfl
    _ = _ := CertifiedAssertedCompilation.compile_map_script
      kind fuel declarations assertions term

/-- Proof erasure for the source-attached query facade is exactly the corresponding
production compiler call. -/
@[simp] theorem compileUplcQuery_map_script (fuel : Nat)
    (declarations : List SymDecl) (query : UplcQuery) :
    (compileUplcQuery? fuel declarations query).map (·.script) =
      Moist.SMT.Compiler.compileUplcQuery? fuel declarations query := by
  exact compile_map_script query.expectation fuel declarations
    query.source.assertions query.target

/-- Proof erasure for the source-attached wrapper is exactly the corresponding
production compiler call. -/
@[simp] theorem compileAssertedTerm_map_script
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    (compileAssertedTerm? kind fuel declarations source).map (·.script) =
      Moist.SMT.Compiler.compileAssertedTerm?
        kind fuel declarations source := by
  exact compile_map_script kind fuel declarations
    source.assertions source.term

/-- Proof erasure for arbitrary result consumers is exactly the corresponding
production result-program compiler call. -/
@[simp] theorem compileResultProgram_map_script
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm)
    (consumer : Term) :
    (compileResultProgram? expectation fuel declarations source consumer).map
        (·.script) =
      Moist.SMT.Compiler.compileResultProgramWithAssertions?
        expectation fuel declarations source.assertions source.term
          consumer := by
  exact compile_map_script expectation fuel declarations source.assertions
    (.Apply consumer source.term)

/-- Successful facade compilation preserves every source-controlled field.
This theorem makes the source/verification-target split explicit at the
proof boundary rather than relying on record projections in client code. -/
theorem compileUplcQuery_some_fields
    {fuel : Nat} {declarations : List SymDecl} {query : UplcQuery}
    {compiled : AssertedQuery query.expectation}
    (hcompile :
      compileUplcQuery? fuel declarations query = some compiled) :
    compiled.fuel = fuel ∧
      compiled.inputs.declarations = declarations ∧
      compiled.assertions = query.source.assertions ∧
      compiled.program.term = query.target := by
  unfold compileUplcQuery? at hcompile
  unfold compile? at hcompile
  generalize hCompilation : CertifiedAssertedCompilation.compile?
    query.expectation fuel declarations query.source.assertions query.target =
      result at hcompile
  cases result with
  | none => simp at hcompile
  | some compilation =>
      simp at hcompile
      subst compiled
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- Successful source-attached compilation certifies the deployable source as
well as the materialized target. This follows structurally because every
`UplcQueryTarget` retains its source leaf; a safe consumer cannot hide an
unsupported builtin in `query.erase`. -/
theorem compileUplcQuery_source_noOpaque
    {fuel : Nat} {declarations : List SymDecl} {query : UplcQuery}
    {compiled : AssertedQuery query.expectation}
    (hcompile :
      compileUplcQuery? fuel declarations query = some compiled) :
    termUsesOpaqueBuiltinForSoundness query.source.term = false := by
  obtain ⟨_hFuel, _hDeclarations, _hAssertions, hTarget⟩ :=
    compileUplcQuery_some_fields hcompile
  have hTargetNoOpaque :
      termUsesOpaqueBuiltinForSoundness query.target = false := by
    simpa [hTarget] using compiled.program.noOpaque
  cases hSource :
      termUsesOpaqueBuiltinForSoundness query.source.term with
  | false => rfl
  | true =>
      have hTargetOpaque :=
        UplcQueryTarget.resolve_usesOpaque_of_source
          query.targetPlan query.source.term hSource
      have : termUsesOpaqueBuiltinForSoundness query.target = true := by
        simpa [UplcQuery.target] using hTargetOpaque
      simp_all

theorem hasCompilerPrelude (query : AssertedQuery kind) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  rw [query.script_eq]
  exact scriptForWithAssertions_hasCompilerPrelude _ _ _ _ _

private theorem declarationAssertionsIncluded (query : AssertedQuery kind) :
    ∀ expression,
      expression ∈ query.inputs.declarations.flatMap SymDecl.assumptions →
        expression ∈ query.script.assertions := by
  intro expression hMember
  rw [query.script_eq,
    scriptForWithAssertions_assertions]
  exact List.mem_append_left _ hMember

theorem environmentDecodes (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∃ environment,
      symEnvToCek? z3.model (envOf query.inputs.declarations) =
        some environment :=
  z3.environmentDecodes (declarationAssertionsIncluded query)

/-- The one CEK environment shared by every assertion and the target. -/
noncomputable def cekEnv (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) : CekEnv :=
  (environmentDecodes query z3).choose

theorem cekEnv_decodes (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    symEnvToCek? z3.model (envOf query.inputs.declarations) =
      some (cekEnv query z3) :=
  (environmentDecodes query z3).choose_spec

/-- Recover every ungrouped compiler-owned condition from the exact grouped
assertion command certified by the model. -/
private theorem compiledConditionsTrue (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∀ expression, expression ∈
        (uplcAssertionConditions query.inputs.declarations query.assertions ++
          [Moist.SMT.Compiler.queryCondition kind
            (evalSym query.fuel (envOf query.inputs.declarations)
              query.program.term)]) →
      SmtSem.evalBoolIs z3.model expression true = true := by
  apply (groupedAssertions_true_iff z3.model _).mp
  intro expression hMember
  apply z3.assertionsTrue
  rw [query.script_eq,
    scriptForWithAssertions_assertions]
  exact List.mem_append_right _ hMember

/-- Every asserted UPLC program reaches its requested actual CEK result, in
the same decoded environment later used for the target conclusion. -/
theorem assertions_sound (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekAssertionsHold (cekEnv query z3) query.assertions := by
  intro assertion hMember
  apply uplcAssertion_condition_sound assertion
    (cekEnv_decodes query z3)
    query.inputs.noOpaque
    (query.assertionsNoOpaque assertion hMember)
  apply compiledConditionsTrue query z3
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨assertion, hMember, rfl⟩

/-- The target proposition selected by `kind` reaches the actual CEK result. -/
theorem target_sound (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekQueryResult kind (cekEnv query z3) query.program.term := by
  have hTarget : SmtSem.evalBoolIs z3.model
      (Moist.SMT.Compiler.queryCondition kind
        (evalSym query.fuel (envOf query.inputs.declarations)
          query.program.term)) true = true := by
    apply compiledConditionsTrue query z3
    exact List.mem_append_right _ (by simp)
  apply resultExpectation_condition_sound kind
    (cekEnv_decodes query z3)
    query.inputs.noOpaque query.program.noOpaque
  simpa [Moist.SMT.Compiler.queryCondition] using hTarget

/-- Strong public endpoint: a certified model proves every assertion and the
target against the identical actual CEK environment. -/
theorem sound (query : AssertedQuery kind)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekAssertionsHold (cekEnv query z3) query.assertions ∧
      CekQueryResult kind (cekEnv query z3) query.program.term :=
  ⟨assertions_sound query z3, target_sound query z3⟩

/-- Source-facing soundness for the source-attached query facade. A model of the
exact script returned for `query` proves its original attached assertions and
the actual CEK result of its verification target. -/
theorem compileUplcQuery_sound {fuel : Nat}
    {declarations : List SymDecl} {query : UplcQuery}
    {compiled : AssertedQuery query.expectation}
    (hcompile :
      compileUplcQuery? fuel declarations query = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.script) :
    CekAssertionsHold (cekEnv compiled z3) query.source.assertions ∧
      CekExpectationHolds query.expectation
        (cekEnv compiled z3) query.target := by
  obtain ⟨_hFuel, _hDeclarations, hAssertions, hTarget⟩ :=
    compileUplcQuery_some_fields hcompile
  simpa [CekQueryResult, hAssertions, hTarget] using sound compiled z3

/-- Source-facing specialization for attached assertions on an unchanged
deployable term. -/
theorem compileAssertedTerm_sound {kind : Moist.SMT.Compiler.QueryKind}
    {fuel : Nat} {declarations : List SymDecl} {source : AssertedTerm}
    {compiled : AssertedQuery kind}
    (hcompile :
      compileAssertedTerm? kind fuel declarations source = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.script) :
    CekAssertionsHold (cekEnv compiled z3) source.assertions ∧
      CekExpectationHolds kind (cekEnv compiled z3) source.term := by
  exact compileUplcQuery_sound
    (query := source.expecting kind) hcompile z3

/-- Source-facing specialization for arbitrary result consumers.  The CEK
conclusion mentions the exact call-by-value UPLC application compiled into
SMT, while `source.erase` remains the deployable term. -/
theorem compileResultProgram_sound
    {expectation : UplcAssertionExpectation} {fuel : Nat}
    {declarations : List SymDecl} {source : AssertedTerm} {consumer : Term}
    {compiled : AssertedQuery expectation}
    (hcompile : compileResultProgram?
      expectation fuel declarations source consumer = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.script) :
    CekAssertionsHold (cekEnv compiled z3) source.assertions ∧
      CekExpectationHolds expectation (cekEnv compiled z3)
        (.Apply consumer source.erase) := by
  exact compileUplcQuery_sound
    (query := source.resultSatisfiesWith expectation consumer) hcompile z3

end AssertedQuery

/-- A fully checked assertion-only query used to establish that a refinement
precondition has a real CEK witness. -/
structure AssertionSatisfiabilityQuery where
  inputs : SupportedDeclarations
  assertions : List UplcAssertion
  assertionsNoOpaque : ∀ assertion, assertion ∈ assertions →
    termUsesOpaqueBuiltinForSoundness assertion.term = false
  script : Moist.SMT.Script
  script_eq : script =
    scriptForAssertionsSatisfiable inputs.declarations assertions
  output : GeneratedOutputContract inputs.declarations script

namespace AssertionSatisfiabilityQuery

def compile? (declarations : List SymDecl)
    (assertions : List UplcAssertion) :
    Option AssertionSatisfiabilityQuery := do
  let compilation ←
    CertifiedAssertionSetCompilation.compile? declarations assertions
  let inputs : SupportedDeclarations :=
    { declarations
      noOpaque := compilation.declarationsNoOpaque
      rendererSafe := compilation.declarationsRendererSafe
      sortSafe := compilation.declarationsSortSafe
      inputSafe := compilation.declarationsInputSafe
      namesDistinct := compilation.declarationNamesDistinct }
  pure
    { inputs, assertions
      assertionsNoOpaque := compilation.assertionsNoOpaque
      script := compilation.script
      script_eq := compilation.script_eq
      output := compilation.output }

@[simp] theorem compile_map_script (declarations : List SymDecl)
    (assertions : List UplcAssertion) :
    (compile? declarations assertions).map (·.script) =
      Moist.SMT.Compiler.compileAssertionsSatisfiable?
        declarations assertions := by
  calc
    (compile? declarations assertions).map (·.script) =
        (CertifiedAssertionSetCompilation.compile?
          declarations assertions).map (·.script) := by
      unfold compile?
      generalize hCompilation : CertifiedAssertionSetCompilation.compile?
        declarations assertions = result
      cases result <;> rfl
    _ = _ := CertifiedAssertionSetCompilation.compile_map_script
      declarations assertions

private theorem declarationAssertionsIncluded
    (query : AssertionSatisfiabilityQuery) :
    ∀ expression,
      expression ∈ query.inputs.declarations.flatMap SymDecl.assumptions →
        expression ∈ query.script.assertions := by
  intro expression hMember
  rw [query.script_eq,
    scriptForAssertionsSatisfiable_assertions]
  exact List.mem_append_left _ hMember

theorem environmentDecodes (query : AssertionSatisfiabilityQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∃ environment,
      symEnvToCek? z3.model (envOf query.inputs.declarations) =
        some environment :=
  z3.environmentDecodes (declarationAssertionsIncluded query)

noncomputable def cekEnv (query : AssertionSatisfiabilityQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) : CekEnv :=
  (environmentDecodes query z3).choose

theorem cekEnv_decodes (query : AssertionSatisfiabilityQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    symEnvToCek? z3.model (envOf query.inputs.declarations) =
      some (cekEnv query z3) :=
  (environmentDecodes query z3).choose_spec

private theorem compiledConditionsTrue
    (query : AssertionSatisfiabilityQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    ∀ expression,
      expression ∈ uplcAssertionConditions
        query.inputs.declarations query.assertions →
      SmtSem.evalBoolIs z3.model expression true = true := by
  apply (groupedAssertions_true_iff z3.model _).mp
  intro expression hMember
  apply z3.assertionsTrue
  rw [query.script_eq,
    scriptForAssertionsSatisfiable_assertions]
  exact List.mem_append_right _ hMember

/-- A certified satisfying model of the non-vacuity query is a genuine CEK
witness for every requested assertion result. -/
theorem sound (query : AssertionSatisfiabilityQuery)
    (z3 : CertifiedZ3Model query.inputs query.script) :
    CekAssertionsHold (cekEnv query z3) query.assertions := by
  intro assertion hMember
  apply uplcAssertion_condition_sound assertion
    (cekEnv_decodes query z3)
    query.inputs.noOpaque
    (query.assertionsNoOpaque assertion hMember)
  apply compiledConditionsTrue query z3
  exact List.mem_map.mpr ⟨assertion, hMember, rfl⟩

end AssertionSatisfiabilityQuery

/-! ## Coupled non-vacuity and target workflow -/

/-- Proof-carrying pair for refinement clients.  Its private constructor and
single shared source record prevent a satisfiability script from being paired
with a target compiled from different declarations or assertions. -/
structure AssertionQueryBundle (kind : Moist.SMT.Compiler.QueryKind) where
  private mk ::
  fuel : Nat
  inputs : SupportedDeclarations
  assertions : List UplcAssertion
  assertionsNoOpaque : ∀ assertion, assertion ∈ assertions →
    termUsesOpaqueBuiltinForSoundness assertion.term = false
  program : SupportedTerm
  scripts : Moist.SMT.Compiler.AssertionQueryScripts
  satisfiability_eq : scripts.satisfiability =
    scriptForAssertionsSatisfiable inputs.declarations assertions
  target_eq : scripts.target =
    Moist.SMT.Compiler.scriptForWithAssertions
      kind fuel inputs.declarations assertions program.term
  satisfiabilityOutput : GeneratedOutputContract
    inputs.declarations scripts.satisfiability
  targetOutput : GeneratedOutputContract inputs.declarations scripts.target

namespace AssertionQueryBundle

/-- Compile the two exact scripts together.  The proof wrapper consumes the
stored proof-free result and never repeats symbolic evaluation. -/
def compile? (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option (AssertionQueryBundle kind) := do
  let compilation ← CertifiedAssertionQueriesCompilation.compile?
    kind fuel declarations assertions term
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
    { fuel, inputs, assertions
      assertionsNoOpaque := compilation.assertionsNoOpaque
      program
      scripts := compilation.scripts
      satisfiability_eq := compilation.satisfiability_eq
      target_eq := compilation.target_eq
      satisfiabilityOutput := compilation.satisfiabilityOutput
      targetOutput := compilation.targetOutput }

def compileSucceeds? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    Option (AssertionQueryBundle .succeeds) :=
  compile? .succeeds fuel declarations assertions term

def compileBoolTrue? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    Option (AssertionQueryBundle .boolTrue) :=
  compile? .boolTrue fuel declarations assertions term

def compileBoolEq? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) (expected : Bool) :
    Option (AssertionQueryBundle (.boolEq expected)) :=
  compile? (.boolEq expected) fuel declarations assertions term

def compileIntEq? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) (expected : Int) :
    Option (AssertionQueryBundle (.intEq expected)) :=
  compile? (.intEq expected) fuel declarations assertions term

def compileError? (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    Option (AssertionQueryBundle .error) :=
  compile? .error fuel declarations assertions term

/-- Certify the coupled non-vacuity/target workflow for one complete
source-level UPLC query. -/
def compileUplcQuery? (fuel : Nat) (declarations : List SymDecl)
    (query : UplcQuery) : Option (AssertionQueryBundle query.expectation) :=
  compile? query.expectation fuel declarations
    query.source.assertions query.target

/-- Certify a source-attached term as a coupled query. -/
def compileAssertedTerm? (kind : Moist.SMT.Compiler.QueryKind)
    (fuel : Nat) (declarations : List SymDecl) (source : AssertedTerm) :
    Option (AssertionQueryBundle kind) :=
  compile? kind fuel declarations source.assertions source.term

/-- Certify a result consumer/matcher together with the source assertion
non-vacuity query. -/
def compileResultProgram?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm)
    (consumer : Term) : Option (AssertionQueryBundle expectation) :=
  compileUplcQuery? fuel declarations
    (source.resultSatisfiesWith expectation consumer)

/-- Erasure is exactly the shared proof-free compiler result. -/
@[simp] theorem compile_map_scripts (kind : Moist.SMT.Compiler.QueryKind)
    (fuel : Nat) (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) :
    (compile? kind fuel declarations assertions term).map (·.scripts) =
      Moist.SMT.Compiler.compileAssertionQueries?
        kind fuel declarations assertions term := by
  calc
    (compile? kind fuel declarations assertions term).map (·.scripts) =
        (CertifiedAssertionQueriesCompilation.compile?
          kind fuel declarations assertions term).map (·.scripts) := by
      unfold compile?
      generalize hCompilation :
        CertifiedAssertionQueriesCompilation.compile?
          kind fuel declarations assertions term = result
      cases result <;> rfl
    _ = _ := CertifiedAssertionQueriesCompilation.compile_map_scripts
      kind fuel declarations assertions term

@[simp] theorem compileUplcQuery_map_scripts (fuel : Nat)
    (declarations : List SymDecl) (query : UplcQuery) :
    (compileUplcQuery? fuel declarations query).map (·.scripts) =
      Moist.SMT.Compiler.compileUplcQueryQueries?
        fuel declarations query := by
  exact compile_map_scripts query.expectation fuel declarations
    query.source.assertions query.target

@[simp] theorem compileAssertedTerm_map_scripts
    (kind : Moist.SMT.Compiler.QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    (compileAssertedTerm? kind fuel declarations source).map (·.scripts) =
      Moist.SMT.Compiler.compileAssertedTermQueries?
        kind fuel declarations source := by
  exact compile_map_scripts kind fuel declarations
    source.assertions source.term

@[simp] theorem compileResultProgram_map_scripts
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm)
    (consumer : Term) :
    (compileResultProgram? expectation fuel declarations source consumer).map
        (·.scripts) =
      Moist.SMT.Compiler.compileResultProgramAssertionQueries?
        expectation fuel declarations source.assertions source.term
          consumer := by
  exact compile_map_scripts expectation fuel declarations source.assertions
    (.Apply consumer source.term)

theorem compileUplcQuery_some_fields
    {fuel : Nat} {declarations : List SymDecl} {query : UplcQuery}
    {compiled : AssertionQueryBundle query.expectation}
    (hcompile :
      compileUplcQuery? fuel declarations query = some compiled) :
    compiled.fuel = fuel ∧
      compiled.inputs.declarations = declarations ∧
      compiled.assertions = query.source.assertions ∧
      compiled.program.term = query.target := by
  unfold compileUplcQuery? at hcompile
  unfold compile? at hcompile
  generalize hCompilation : CertifiedAssertionQueriesCompilation.compile?
    query.expectation fuel declarations query.source.assertions query.target =
      result at hcompile
  cases result with
  | none => simp at hcompile
  | some compilation =>
      simp at hcompile
      subst compiled
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- View the target projection through the already proved asserted-query
endpoint, without recompilation. -/
def targetQuery (bundle : AssertionQueryBundle kind) : AssertedQuery kind :=
  { fuel := bundle.fuel
    inputs := bundle.inputs
    assertions := bundle.assertions
    assertionsNoOpaque := bundle.assertionsNoOpaque
    program := bundle.program
    script := bundle.scripts.target
    script_eq := bundle.target_eq
    output := bundle.targetOutput }

/-- View the non-vacuity projection through its existing sound endpoint,
without recompilation. -/
def satisfiabilityQuery (bundle : AssertionQueryBundle kind) :
    AssertionSatisfiabilityQuery :=
  { inputs := bundle.inputs
    assertions := bundle.assertions
    assertionsNoOpaque := bundle.assertionsNoOpaque
    script := bundle.scripts.satisfiability
    script_eq := bundle.satisfiability_eq
    output := bundle.satisfiabilityOutput }

/-- The CEK witness environment supplied by a model of the standalone
assertion-satisfiability script. -/
noncomputable def satisfiabilityCekEnv (bundle : AssertionQueryBundle kind)
    (z3 : CertifiedZ3Model bundle.inputs bundle.scripts.satisfiability) :
    CekEnv :=
  AssertionSatisfiabilityQuery.cekEnv (satisfiabilityQuery bundle) z3

/-- The independently decoded CEK environment supplied by a model of the
target script.  It is intentionally not identified with the satisfiability
witness environment. -/
noncomputable def targetCekEnv (bundle : AssertionQueryBundle kind)
    (z3 : CertifiedZ3Model bundle.inputs bundle.scripts.target) : CekEnv :=
  AssertedQuery.cekEnv (targetQuery bundle) z3

theorem satisfiability_sound (bundle : AssertionQueryBundle kind)
    (z3 : CertifiedZ3Model bundle.inputs bundle.scripts.satisfiability) :
    CekAssertionsHold (satisfiabilityCekEnv bundle z3)
      bundle.assertions := by
  exact AssertionSatisfiabilityQuery.sound
    (satisfiabilityQuery bundle) z3

theorem target_sound (bundle : AssertionQueryBundle kind)
    (z3 : CertifiedZ3Model bundle.inputs bundle.scripts.target) :
    CekAssertionsHold (targetCekEnv bundle z3) bundle.assertions ∧
      CekQueryResult kind (targetCekEnv bundle z3)
        bundle.program.term := by
  exact AssertedQuery.sound (targetQuery bundle) z3

/-- Source-facing target soundness for a coupled source-attached UPLC query. -/
theorem compileUplcQuery_target_sound {fuel : Nat}
    {declarations : List SymDecl} {query : UplcQuery}
    {compiled : AssertionQueryBundle query.expectation}
    (hcompile :
      compileUplcQuery? fuel declarations query = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.scripts.target) :
    CekAssertionsHold (targetCekEnv compiled z3) query.source.assertions ∧
      CekExpectationHolds query.expectation
        (targetCekEnv compiled z3) query.target := by
  obtain ⟨_hFuel, _hDeclarations, hAssertions, hTarget⟩ :=
    compileUplcQuery_some_fields hcompile
  simpa [CekQueryResult, hAssertions, hTarget] using
    target_sound compiled z3

theorem compileAssertedTerm_target_sound
    {kind : Moist.SMT.Compiler.QueryKind} {fuel : Nat}
    {declarations : List SymDecl} {source : AssertedTerm}
    {compiled : AssertionQueryBundle kind}
    (hcompile :
      compileAssertedTerm? kind fuel declarations source = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.scripts.target) :
    CekAssertionsHold (targetCekEnv compiled z3) source.assertions ∧
      CekExpectationHolds kind (targetCekEnv compiled z3) source.term := by
  exact compileUplcQuery_target_sound
    (query := source.expecting kind) hcompile z3

theorem compileResultProgram_target_sound
    {expectation : UplcAssertionExpectation} {fuel : Nat}
    {declarations : List SymDecl} {source : AssertedTerm} {consumer : Term}
    {compiled : AssertionQueryBundle expectation}
    (hcompile : compileResultProgram?
      expectation fuel declarations source consumer = some compiled)
    (z3 : CertifiedZ3Model compiled.inputs compiled.scripts.target) :
    CekAssertionsHold (targetCekEnv compiled z3) source.assertions ∧
      CekExpectationHolds expectation (targetCekEnv compiled z3)
        (.Apply consumer source.erase) := by
  exact compileUplcQuery_target_sound
    (query := source.resultSatisfiesWith expectation consumer) hcompile z3

/-- Combined endpoint.  Each solver model yields its own genuine CEK
environment; the target model still aligns every assertion and the target in
one identical environment. -/
theorem sound (bundle : AssertionQueryBundle kind)
    (satisfiabilityModel :
      CertifiedZ3Model bundle.inputs bundle.scripts.satisfiability)
    (targetModel : CertifiedZ3Model bundle.inputs bundle.scripts.target) :
    CekAssertionsHold
        (satisfiabilityCekEnv bundle satisfiabilityModel) bundle.assertions ∧
      (CekAssertionsHold (targetCekEnv bundle targetModel) bundle.assertions ∧
        CekQueryResult kind (targetCekEnv bundle targetModel)
          bundle.program.term) :=
  ⟨satisfiability_sound bundle satisfiabilityModel,
    target_sound bundle targetModel⟩

end AssertionQueryBundle

end Moist.SMT.UPLC.Soundness
