import Moist.SMT.Compiler.Validation

/-!
# Proof-free input-checked SMT compiler primitive

This module contains the first stage of the portable compiler.  It checks
caller-controlled data and returns only the typed SMT script AST; no semantic
theorem or proof-carrying wrapper is imported.

The unchecked `scriptFor*` functions remain useful low-level primitives.  The
functions below additionally reject unsupported UPLC builtins, malformed or
ambiguous declarations, and renderer-unsafe caller input.

Generated assertions are compiler-owned rather than caller-controlled and are
deliberately not checked by this low-level stage.  Use `Compiler.compile?` from
`Moist.SMT.Compiler.Checked` for the production boundary: it applies the
sharing-aware generated-output analysis to this exact returned script.
-/

namespace Moist.SMT.Compiler

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Moist.SMT.Compiler.Validation

/-- Target queries and source assertions use the same observable CEK result
expectation. Integer equality intentionally carries a literal integer rather
than an arbitrary SMT expression. -/
abbrev QueryKind := UplcAssertionExpectation

namespace QueryKind

/-- Source-compatible spelling for the original strict Boolean query. -/
def boolTrue : QueryKind := .boolEq true

end QueryKind

/-- The coupled scripts used by a refinement-style workflow.  The first
checks that the UPLC assertions have a witness; the second checks the selected
target under those exact same assertions. -/
structure AssertionQueryScripts where
  satisfiability : Moist.SMT.Script
  target : Moist.SMT.Script
deriving Repr

/-- Validate all caller-controlled input before symbolic evaluation.

This is the single executable input gate.  Mandatory decoding assumptions
belong to the computational `declarationsInputSafe` check; `SymDecl` itself is
a proof-free record.  A foreign-language port must preserve this validation. -/
def inputAccepted (declarations : List SymDecl) (term : Term) : Bool :=
  symEnvNoOpaqueForSoundness (envOf declarations) &&
    declarationsRendererSafe declarations &&
    declarationsSortSafe declarations &&
    declarationsInputSafe declarations &&
    declarationNamesDistinct declarations &&
    !termUsesOpaqueBuiltinForSoundness term

/-- Every caller-supplied UPLC assertion must belong to the same supported
builtin fragment as the target program. -/
def assertionsAccepted (assertions : List UplcAssertion) : Bool :=
  assertions.all fun assertion =>
    !termUsesOpaqueBuiltinForSoundness assertion.term

/-- Input gate for a target query restricted by UPLC assertions. -/
def inputWithAssertionsAccepted (declarations : List SymDecl)
    (assertions : List UplcAssertion) (term : Term) : Bool :=
  inputAccepted declarations term && assertionsAccepted assertions

/-- Input gate for the standalone non-vacuity query. -/
def assertionSetInputAccepted (declarations : List SymDecl)
    (assertions : List UplcAssertion) : Bool :=
  symEnvNoOpaqueForSoundness (envOf declarations) &&
    declarationsRendererSafe declarations &&
    declarationsSortSafe declarations &&
    declarationsInputSafe declarations &&
    declarationNamesDistinct declarations &&
    assertionsAccepted assertions

/-- Construct the one canonical script for a checked query kind. -/
def scriptFor (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Moist.SMT.Script :=
  match kind with
  | .succeeds => scriptForSucceeds fuel declarations term
  | .boolEq expected =>
      scriptForBoolEq fuel declarations term expected
  | .intEq expected =>
      scriptForIntEq fuel declarations term (.int expected)
  | .error => scriptForError fuel declarations term

/-- Compile the requested target proposition from one symbolic outcome list.
Keeping this separate from script assembly makes the asserted-query proof and
foreign-language ports share one explicit observable-result boundary. -/
def queryCondition (kind : QueryKind) (outcomes : List Outcome) : SExpr :=
  kind.condition outcomes

/-- Construct the canonical query for a target under ordinary UPLC
assertions.  Every assertion and the target are symbolically evaluated once. -/
def scriptForWithAssertions (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Moist.SMT.Script :=
  let outcomes := evalSym fuel (envOf declarations) term
  scriptWith declarations
    (uplcAssertionConditions declarations assertions ++
      [queryCondition kind outcomes])

/-- Construct the non-vacuity and target scripts together.  The expensive
symbolic assertion conditions are computed once and shared by both scripts;
the target is also evaluated exactly once. -/
def scriptsForWithAssertions (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : AssertionQueryScripts :=
  let assertionConditions :=
    uplcAssertionConditions declarations assertions
  let targetOutcomes := evalSym fuel (envOf declarations) term
  { satisfiability := scriptWith declarations assertionConditions
    target := scriptWith declarations
      (assertionConditions ++ [queryCondition kind targetOutcomes]) }

/-- Compile after fail-closed validation of all caller-controlled input.

The canonical script is constructed once.  This function intentionally does
not run generated-output validation.  The fully checked compiler consumes
this exact stored result without invoking `evalSym` a second time.  Script
construction retains the bounded prelude-dependency scan needed to select
declarations.

The name is deliberately explicit: success certifies the input boundary, not
the compiler-owned output AST.  Use `Compiler.compile?` for complete
proof-free validation, or the proof-carrying query constructors when a CEK
soundness endpoint is required. -/
def compileInputChecked? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Option Moist.SMT.Script :=
  if inputAccepted declarations term then
    some (scriptFor kind fuel declarations term)
  else
    none

def compileSucceedsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Option Moist.SMT.Script :=
  compileInputChecked? .succeeds fuel declarations term

def compileBoolTrueInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compileInputChecked? .boolTrue fuel declarations term

def compileBoolEqInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Bool) : Option Moist.SMT.Script :=
  compileInputChecked? (.boolEq expected) fuel declarations term

def compileIntEqInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) : Option Moist.SMT.Script :=
  compileInputChecked? (.intEq expected) fuel declarations term

def compileErrorInputChecked? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compileInputChecked? .error fuel declarations term

/-- Compile a target query after validating both the target and every UPLC
assertion. -/
def compileWithAssertionsInputChecked? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  if inputWithAssertionsAccepted declarations assertions term then
    some (scriptForWithAssertions kind fuel declarations assertions term)
  else
    none

def compileSucceedsWithAssertionsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked?
    .succeeds fuel declarations assertions term

def compileBoolTrueWithAssertionsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked? .boolTrue fuel declarations assertions term

def compileBoolEqWithAssertionsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) (expected : Bool) : Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked?
    (.boolEq expected) fuel declarations assertions term

def compileIntEqWithAssertionsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) (expected : Int) : Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked?
    (.intEq expected) fuel declarations assertions term

def compileErrorWithAssertionsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked? .error fuel declarations assertions term

/-- Compile the standalone assertion-satisfiability query after the same
fail-closed declaration and UPLC-fragment checks. -/
def compileAssertionsSatisfiableInputChecked? (declarations : List SymDecl)
    (assertions : List UplcAssertion) : Option Moist.SMT.Script :=
  if assertionSetInputAccepted declarations assertions then
    some (scriptForAssertionsSatisfiable declarations assertions)
  else
    none

/-- Compile a coupled refinement query after one shared input check and one
symbolic pass over each assertion.  Returning both scripts from the same value
prevents callers from accidentally pairing different predicate sets. -/
def compileAssertionQueriesInputChecked? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option AssertionQueryScripts :=
  if inputWithAssertionsAccepted declarations assertions term then
    some (scriptsForWithAssertions kind fuel declarations assertions term)
  else
    none

/-! ## Source-attached UPLC assertion wrappers -/

/-- Compile a source-attached UPLC query template. This is the most general
proof-free input-checked entry point: it supports all result expectations,
source-attached assertions, and result consumers constructed through
`AssertedTerm.resultSatisfiesWith`. -/
def compileUplcQueryInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (query : UplcQuery) :
    Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked?
    query.expectation fuel declarations query.source.assertions query.target

/-- Compile the coupled assertion-satisfiability and target scripts for one
source-attached UPLC query template. -/
def compileUplcQueryQueriesInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (query : UplcQuery) :
    Option AssertionQueryScripts :=
  compileAssertionQueriesInputChecked?
    query.expectation fuel declarations query.source.assertions query.target

/-- Compile an ordinary UPLC term together with its host-side assertion
metadata. -/
def compileAssertedTermInputChecked? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked?
    kind fuel declarations source.assertions source.term

/-- Compile the coupled assertion-satisfiability and target scripts from one
source-attached term. -/
def compileAssertedTermQueriesInputChecked? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    Option AssertionQueryScripts :=
  compileAssertionQueriesInputChecked?
    kind fuel declarations source.assertions source.term

/-- Compile the exact call-by-value application `.Apply predicate term` and
require it to return `Bool true`. The predicate expression is evaluated before
the term argument, exactly as in CEK. -/
def compileResultSatisfiesInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (term predicate : Term) :
    Option Moist.SMT.Script :=
  compileBoolTrueInputChecked?
    fuel declarations (.Apply predicate term)

/-- Discharge `term` into an ordinary UPLC consumer and select any supported
observable result of that consumer. This is the general result-matching
primitive behind `compileResultSatisfiesInputChecked?`. -/
def compileResultProgramInputChecked?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (term consumer : Term) :
    Option Moist.SMT.Script :=
  compileInputChecked?
    expectation fuel declarations (.Apply consumer term)

def compileResultSatisfiesWithAssertionsInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term predicate : Term) : Option Moist.SMT.Script :=
  compileBoolTrueWithAssertionsInputChecked?
    fuel declarations assertions (.Apply predicate term)

def compileResultProgramWithAssertionsInputChecked?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term consumer : Term) : Option Moist.SMT.Script :=
  compileWithAssertionsInputChecked?
    expectation fuel declarations assertions (.Apply consumer term)

def compileResultSatisfiesAssertionQueriesInputChecked? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term predicate : Term) : Option AssertionQueryScripts :=
  compileAssertionQueriesInputChecked?
    .boolTrue fuel declarations assertions (.Apply predicate term)

def compileResultProgramAssertionQueriesInputChecked?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term consumer : Term) : Option AssertionQueryScripts :=
  compileAssertionQueriesInputChecked?
    expectation fuel declarations assertions (.Apply consumer term)

end Moist.SMT.Compiler
