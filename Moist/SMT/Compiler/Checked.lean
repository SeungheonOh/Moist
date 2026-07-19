import Moist.SMT.Compiler.InputChecked
import Moist.SMT.Compiler.OutputAnalysis

/-!
# Fully checked proof-free SMT compiler

This is the production compilation boundary for callers that need a plain
`Option Script`, without importing any soundness proof.  It validates both
caller-controlled input and the exact generated script:

* command forms and fixed raw prelude text;
* the single, fixed solver-control suffix;
* renderer safety for every generated assertion; and
* Boolean sorting for every generated assertion.

The final two checks share one memoized traversal through
`Compiler.OutputAnalysis`.  Cache reuse is guarded by exact structural
identity, so it cannot change acceptance.  The proof module
`Moist.SMT.Soundness.CheckedCompiler` establishes equivalence to the four
transparent output predicates and attaches the CEK soundness certificate to
the exact script returned here.
-/

namespace Moist.SMT.Compiler

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Moist.SMT.Compiler.Validation
open Moist.SMT.Compiler.OutputAnalysis

/-- Validate every compiler-owned part of an already generated script.

The sharing-aware assertion check is proved equivalent to the independent
transparent renderer and sort checks.  Keeping this definition proof-free
makes it directly portable to another implementation language. -/
def outputAccepted (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Bool :=
  generatedCommandsSafe declarations script &&
    generatedSolverControlSafe script &&
    generatedAssertionsOutputSafe declarations script

/-- Return the same script exactly when all generated-output checks pass. -/
def outputChecked? (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Option Moist.SMT.Script :=
  if outputAccepted declarations script then some script else none

/-- Compile one canonical script, after validating both its input and output.

`compileInputChecked?` constructs the script once.  `outputChecked?` consumes
that stored value; symbolic evaluation is never invoked a second time. -/
def compile? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (term : Term) : Option Moist.SMT.Script := do
  let script ← compileInputChecked? kind fuel declarations term
  outputChecked? declarations script

def compileSucceeds? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compile? .succeeds fuel declarations term

def compileBoolTrue? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compile? .boolTrue fuel declarations term

def compileBoolEq? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Bool) : Option Moist.SMT.Script :=
  compile? (.boolEq expected) fuel declarations term

def compileIntEq? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) : Option Moist.SMT.Script :=
  compile? (.intEq expected) fuel declarations term

def compileError? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option Moist.SMT.Script :=
  compile? .error fuel declarations term

/-! ## Queries restricted by ordinary UPLC assertions -/

/-- Compile one target query under ordinary UPLC assertions, validating the
exact generated script once after the input-checked compiler constructs it.

Every assertion is evaluated under the same declaration environment as the
target.  This function does not reconstruct the script or invoke symbolic
evaluation during output checking. -/
def compileWithAssertions? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script := do
  let script ← compileWithAssertionsInputChecked?
    kind fuel declarations assertions term
  outputChecked? declarations script

def compileSucceedsWithAssertions? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  compileWithAssertions? .succeeds fuel declarations assertions term

def compileBoolTrueWithAssertions? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  compileWithAssertions? .boolTrue fuel declarations assertions term

def compileBoolEqWithAssertions? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) (expected : Bool) : Option Moist.SMT.Script :=
  compileWithAssertions?
    (.boolEq expected) fuel declarations assertions term

def compileIntEqWithAssertions? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) (expected : Int) : Option Moist.SMT.Script :=
  compileWithAssertions?
    (.intEq expected) fuel declarations assertions term

def compileErrorWithAssertions? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option Moist.SMT.Script :=
  compileWithAssertions? .error fuel declarations assertions term

/-- Compile the assertion-only satisfiability query.  Refinement clients use
this alongside an obligation query so contradictory predicates cannot prove
an obligation vacuously. -/
def compileAssertionsSatisfiable? (declarations : List SymDecl)
    (assertions : List UplcAssertion) : Option Moist.SMT.Script := do
  let script ←
    compileAssertionsSatisfiableInputChecked? declarations assertions
  outputChecked? declarations script

/-! ## Coupled refinement queries -/

/-- Sharing-aware output validation for both exact scripts in a coupled
assertion query. -/
def assertionQueriesOutputAccepted (declarations : List SymDecl)
    (scripts : AssertionQueryScripts) : Bool :=
  outputAccepted declarations scripts.satisfiability &&
    outputAccepted declarations scripts.target

def assertionQueriesOutputChecked? (declarations : List SymDecl)
    (scripts : AssertionQueryScripts) : Option AssertionQueryScripts :=
  if assertionQueriesOutputAccepted declarations scripts then
    some scripts
  else
    none

/-- Compile the assertion-satisfiability and target scripts as one coupled
result.  Assertion symbolic evaluation is shared, both exact generated scripts
are output-checked, and their source declarations/assertions cannot diverge. -/
def compileAssertionQueries? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option AssertionQueryScripts := do
  let scripts ← compileAssertionQueriesInputChecked?
    kind fuel declarations assertions term
  assertionQueriesOutputChecked? declarations scripts

def compileSucceedsAssertionQueries? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option AssertionQueryScripts :=
  compileAssertionQueries? .succeeds fuel declarations assertions term

def compileBoolTrueAssertionQueries? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option AssertionQueryScripts :=
  compileAssertionQueries? .boolTrue fuel declarations assertions term

def compileBoolEqAssertionQueries? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) (expected : Bool) : Option AssertionQueryScripts :=
  compileAssertionQueries?
    (.boolEq expected) fuel declarations assertions term

def compileIntEqAssertionQueries? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) (expected : Int) : Option AssertionQueryScripts :=
  compileAssertionQueries? (.intEq expected)
    fuel declarations assertions term

def compileErrorAssertionQueries? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term : Term) : Option AssertionQueryScripts :=
  compileAssertionQueries? .error fuel declarations assertions term

/-! ## Source-attached assertions and result predicates -/

/-- Compile one source-attached UPLC query template through the production
input and generated-output checks. -/
def compileUplcQuery? (fuel : Nat) (declarations : List SymDecl)
    (query : UplcQuery) : Option Moist.SMT.Script :=
  compileWithAssertions?
    query.expectation fuel declarations query.source.assertions query.target

/-- Compile the coupled non-vacuity and target scripts for one source-attached
UPLC query template. -/
def compileUplcQueryQueries? (fuel : Nat) (declarations : List SymDecl)
    (query : UplcQuery) : Option AssertionQueryScripts :=
  compileAssertionQueries?
    query.expectation fuel declarations query.source.assertions query.target

def compileAssertedTerm? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    Option Moist.SMT.Script :=
  compileWithAssertions?
    kind fuel declarations source.assertions source.term

def compileAssertedTermQueries? (kind : QueryKind) (fuel : Nat)
    (declarations : List SymDecl) (source : AssertedTerm) :
    Option AssertionQueryScripts :=
  compileAssertionQueries?
    kind fuel declarations source.assertions source.term

def compileResultSatisfies? (fuel : Nat)
    (declarations : List SymDecl) (term predicate : Term) :
    Option Moist.SMT.Script :=
  compileBoolTrue? fuel declarations (.Apply predicate term)

/-- Discharge `term` into an ordinary UPLC consumer and query any supported
observable result of that consumer. -/
def compileResultProgram? (expectation : UplcAssertionExpectation)
    (fuel : Nat) (declarations : List SymDecl) (term consumer : Term) :
    Option Moist.SMT.Script :=
  compile? expectation fuel declarations (.Apply consumer term)

def compileResultSatisfiesWithAssertions? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term predicate : Term) : Option Moist.SMT.Script :=
  compileBoolTrueWithAssertions?
    fuel declarations assertions (.Apply predicate term)

def compileResultProgramWithAssertions?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term consumer : Term) : Option Moist.SMT.Script :=
  compileWithAssertions?
    expectation fuel declarations assertions (.Apply consumer term)

def compileResultSatisfiesAssertionQueries? (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term predicate : Term) : Option AssertionQueryScripts :=
  compileBoolTrueAssertionQueries?
    fuel declarations assertions (.Apply predicate term)

def compileResultProgramAssertionQueries?
    (expectation : UplcAssertionExpectation) (fuel : Nat)
    (declarations : List SymDecl) (assertions : List UplcAssertion)
    (term consumer : Term) : Option AssertionQueryScripts :=
  compileAssertionQueries?
    expectation fuel declarations assertions (.Apply consumer term)

end Moist.SMT.Compiler
