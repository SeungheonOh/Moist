import Moist.SMT.Compiler.UPLC.Prelude
import Moist.SMT.Compiler.UPLC.Evaluation
import Moist.SMT.Compiler.UPLC.Declarations

/-!
# UPLC compiler query assembly

Logical result conditions and canonical SMT script constructors.  This is the
top executable UPLC compiler layer.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term

/-! ## Assertion grouping

Refinement contexts commonly contribute hundreds of assertions which share
large subexpressions.  Keeping each assertion in a separate SMT command hides
that sharing from the per-command DAG renderer.  Group caller assertions into
one conjunction while leaving declaration assumptions separate (the latter
are used individually to decode the solver environment).

The singleton case is definitionally unchanged, so every production CEK
query still exposes its exact generated condition. -/

def assertionConjunction : List SExpr → SExpr
  | [] => SExpr.trueE
  | expression :: expressions =>
      SExpr.and expression (assertionConjunction expressions)

def groupedAssertions : List SExpr → List SExpr
  | [] => []
  | [expression] => [expression]
  | expression :: next :: expressions =>
      [assertionConjunction (expression :: next :: expressions)]

def groupedAssertionCommands (assertions : List SExpr) :
    List Moist.SMT.Command :=
  (groupedAssertions assertions).map Moist.SMT.Command.assert

def okBoolTrueCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .ok pc v =>
        let b := asBool v
        some (SExpr.all [pc, b.guard, b.val])
    | _ => none

/-- At least one successful symbolic outcome is active, regardless of the
returned value.  Errors and fuel timeouts never satisfy this condition. -/
def okCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .ok pc _ => some pc
    | _ => none

/-- At least one active successful outcome is the requested Boolean.  The
`true` branch deliberately reuses the established production condition
exactly; the `false` branch checks the same guarded Boolean projection. -/
def okBoolEqCond (outs : List Outcome) (expected : Bool) : SExpr :=
  if expected then
    okBoolTrueCond outs
  else
    SExpr.any <| outs.filterMap fun
      | .ok pc v =>
          let b := asBool v
          some (SExpr.all [pc, b.guard, SExpr.not b.val])
      | _ => none

def okIntEqCond (outs : List Outcome) (rhs : SExpr) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .ok pc v =>
        let i := asInt v
        some (SExpr.all [pc, i.guard, SExpr.eq i.val rhs])
    | _ => none

def errorCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .error pc => some pc
    | _ => none

def timeoutCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .timeout pc => some pc
    | _ => none

/-! ## UPLC assertions

An assertion is an ordinary UPLC program evaluated in the same symbolic
environment as the target program.  Its result expectation can require any
successful value, an exact Boolean or integer, or an actual runtime error.
Fuel timeout never satisfies an assertion because it is not a CEK result.

Keeping assertions as source UPLC terms, rather than accepting raw SMT
expressions, lets the public soundness boundary recover the actual CEK result
for every asserted predicate. -/

/-- The observable result required from an asserted UPLC evaluation.

`succeeds` exposes the general `∃ value, CEK reaches value` proposition.  The
typed cases additionally pin common first-order results.  Runtime error is
kept distinct from fuel exhaustion all the way to the CEK theorem. -/
inductive UplcAssertionExpectation where
  | succeeds
  | boolEq (expected : Bool)
  | intEq (expected : Int)
  | error
deriving Repr, BEq

namespace UplcAssertionExpectation

/-- Lower one observable evaluation expectation to its SMT condition.

This single dispatcher is shared by standalone targets and source UPLC
assertions, preventing the two public APIs from drifting apart. -/
def condition (expectation : UplcAssertionExpectation)
    (outcomes : List Outcome) : SExpr :=
  match expectation with
  | .succeeds => okCond outcomes
  | .boolEq expected => okBoolEqCond outcomes expected
  | .intEq expected => okIntEqCond outcomes (.int expected)
  | .error => errorCond outcomes

end UplcAssertionExpectation

/-- One independently fueled UPLC assertion over the query declarations.

`Var 1` refers to the first declaration, `Var 2` to the second, and so on,
exactly as it does for the target program. -/
structure UplcAssertion where
  fuel : Nat
  term : Term
  /-- Defaults to the original parameter-predicate interpretation. -/
  expectation : UplcAssertionExpectation := .boolEq true
deriving Repr

namespace UplcAssertion

/-- Check a one-based external parameter index against the declaration
environment that will be supplied to compilation. -/
def parameterIndexAccepted (declarations : List SymDecl)
    (parameterIndex : Nat) : Bool :=
  parameterIndex != 0 && parameterIndex <= declarations.length

/-- Check every one-based external parameter index before constructing a
parameter assertion. -/
def parameterIndicesAccepted (declarations : List SymDecl)
    (parameterIndices : List Nat) : Bool :=
  parameterIndices.all (parameterIndexAccepted declarations)

/-- Build an assertion with an explicit result expectation. -/
def expecting (fuel : Nat) (expectation : UplcAssertionExpectation)
    (term : Term) : UplcAssertion :=
  { fuel, term, expectation }

/-- Require evaluation to halt successfully with some CEK value. -/
def succeeds (fuel : Nat) (term : Term) : UplcAssertion :=
  expecting fuel .succeeds term

/-- Require evaluation to return the exact Boolean. -/
def returnsBool (fuel : Nat) (expected : Bool)
    (term : Term) : UplcAssertion :=
  expecting fuel (.boolEq expected) term

/-- Require evaluation to return the exact integer. -/
def returnsInt (fuel : Nat) (expected : Int)
    (term : Term) : UplcAssertion :=
  expecting fuel (.intEq expected) term

/-- Require evaluation to reach an actual CEK runtime error. -/
def errors (fuel : Nat) (term : Term) : UplcAssertion :=
  expecting fuel .error term

/-- Apply an arbitrary UPLC program to explicit argument terms and require the
selected result. -/
def appliedWith (fuel : Nat) (expectation : UplcAssertionExpectation)
    (predicate : Term) (arguments : List Term) : UplcAssertion :=
  expecting fuel expectation <|
    arguments.foldl (fun function argument => .Apply function argument)
      predicate

/-- Apply a Boolean predicate, preserving the original `Bool true` default. -/
def applied (fuel : Nat) (predicate : Term)
    (arguments : List Term) : UplcAssertion :=
  appliedWith fuel (.boolEq true) predicate arguments

/-- Build the exact UPLC application `.Apply predicate term` and require it to
return `Bool true`. CEK evaluates the predicate expression first and, once it
produces a callable value, evaluates `term` and passes that value to it. This
is the general value-refinement constructor: the predicate can inspect
structured values using ordinary UPLC builtins and `Case`, without exposing
raw SMT. -/
def resultSatisfies (fuel : Nat) (term predicate : Term) : UplcAssertion :=
  applied fuel predicate [term]

/-- As `resultSatisfies`, but select an explicit expectation for the result of
the UPLC predicate/program. -/
def resultSatisfiesWith (fuel : Nat)
    (expectation : UplcAssertionExpectation) (term predicate : Term) :
    UplcAssertion :=
  appliedWith fuel expectation predicate [term]

/-- Convenience constructor for a unary predicate over one symbolic
parameter.  Parameter indices are one-based, matching UPLC variables and
`envOf`. -/
def onParameter (fuel : Nat) (predicate : Term)
    (parameterIndex : Nat) : UplcAssertion :=
  applied fuel predicate [.Var parameterIndex]

/-- Apply a unary UPLC program to one symbolic parameter and require an
explicit result. -/
def onParameterWith (fuel : Nat) (expectation : UplcAssertionExpectation)
    (predicate : Term) (parameterIndex : Nat) : UplcAssertion :=
  appliedWith fuel expectation predicate [.Var parameterIndex]

/-- Declaration-aware unary parameter constructor. Unlike `onParameter`, this
rejects index zero and indices outside the supplied symbolic environment. -/
def onParameterWithChecked? (declarations : List SymDecl) (fuel : Nat)
    (expectation : UplcAssertionExpectation) (predicate : Term)
    (parameterIndex : Nat) : Option UplcAssertion :=
  if parameterIndexAccepted declarations parameterIndex then
    some (onParameterWith fuel expectation predicate parameterIndex)
  else
    none

/-- Boolean-true specialization of `onParameterWithChecked?`. -/
def onParameterChecked? (declarations : List SymDecl) (fuel : Nat)
    (predicate : Term) (parameterIndex : Nat) : Option UplcAssertion :=
  onParameterWithChecked? declarations fuel (.boolEq true)
    predicate parameterIndex

/-- Apply a predicate to several one-based symbolic parameters in source
order. -/
def onParameters (fuel : Nat) (predicate : Term)
    (parameterIndices : List Nat) : UplcAssertion :=
  applied fuel predicate (parameterIndices.map Term.Var)

/-- Multi-parameter assertion with an explicit result expectation. -/
def onParametersWith (fuel : Nat)
    (expectation : UplcAssertionExpectation) (predicate : Term)
    (parameterIndices : List Nat) : UplcAssertion :=
  appliedWith fuel expectation predicate (parameterIndices.map Term.Var)

/-- Declaration-aware multi-parameter constructor. -/
def onParametersWithChecked? (declarations : List SymDecl) (fuel : Nat)
    (expectation : UplcAssertionExpectation) (predicate : Term)
    (parameterIndices : List Nat) : Option UplcAssertion :=
  if parameterIndicesAccepted declarations parameterIndices then
    some (onParametersWith fuel expectation predicate parameterIndices)
  else
    none

/-- Boolean-true specialization of `onParametersWithChecked?`. -/
def onParametersChecked? (declarations : List SymDecl) (fuel : Nat)
    (predicate : Term) (parameterIndices : List Nat) :
    Option UplcAssertion :=
  onParametersWithChecked? declarations fuel (.boolEq true)
    predicate parameterIndices

/-- Apply a UPLC predicate first to a result-producing term and then to
selected symbolic parameters. This models return refinements that relate the
result to the original inputs, with ordinary CEK application order. -/
def resultAndParametersSatisfy (fuel : Nat) (term predicate : Term)
    (parameterIndices : List Nat) : UplcAssertion :=
  applied fuel predicate
    (term :: parameterIndices.map Term.Var)

/-- Result-and-input refinement with an explicit predicate/program result
expectation. -/
def resultAndParametersSatisfyWith (fuel : Nat)
    (expectation : UplcAssertionExpectation) (term predicate : Term)
    (parameterIndices : List Nat) : UplcAssertion :=
  appliedWith fuel expectation predicate
    (term :: parameterIndices.map Term.Var)

/-- Compile the assertion through the ordinary symbolic UPLC evaluator. -/
def condition (declarations : List SymDecl) (assertion : UplcAssertion) : SExpr :=
  let outcomes :=
    evalSym assertion.fuel (envOf declarations) assertion.term
  assertion.expectation.condition outcomes

end UplcAssertion

/-! ## UPLC term with source-attached verification assertions -/

/-- Host-side verification metadata attached to an ordinary UPLC term.

The wrapper is intentionally not a `Term` constructor. SMT compilation uses
both fields; CEK execution and Flat serialization use `erase`, which is
exactly the original ordinary UPLC term. -/
structure AssertedTerm where
  term : Term
  assertions : List UplcAssertion := []
deriving Repr

/-- A verification-target derivation rooted at the deployable source term.

The plan cannot represent an unrelated target: every constructor retains the
`source` leaf.  Besides preventing accidental source/target mismatches, the
recursive form lets callers compose function application and result consumers
without exposing raw SMT expressions. -/
inductive UplcQueryTarget where
  | source
  | applied (target : UplcQueryTarget) (arguments : List Term)
  | consumed (consumer : Term) (target : UplcQueryTarget)
deriving Repr

namespace UplcQueryTarget

/-- Materialize the ordinary UPLC term selected by a source-rooted target
plan. -/
def resolve (sourceTerm : Term) : UplcQueryTarget → Term
  | .source => sourceTerm
  | .applied target arguments =>
      arguments.foldl
        (fun function argument => .Apply function argument)
        (target.resolve sourceTerm)
  | .consumed consumer target =>
      .Apply consumer (target.resolve sourceTerm)

end UplcQueryTarget

/-- A source-attached verification-query template.

`source` retains the exact deployable UPLC program and its host-side
verification metadata. `targetPlan` records a source-rooted transformation;
`UplcQuery.target` materializes the ordinary UPLC program evaluated by CEK for
the verification obligation. `expectation` selects its observable CEK result.

For arbitrary result matching, construct the query through
`AssertedTerm.resultSatisfiesWith` or compose another `consumed` target. These
operations apply an ordinary UPLC consumer/predicate to the selected result;
they do not invent a generic SMT equality for higher-order CEK values. -/
structure UplcQuery where
  source : AssertedTerm
  targetPlan : UplcQueryTarget := .source
  expectation : UplcAssertionExpectation := .succeeds
deriving Repr

namespace UplcQuery

/-- The exact ordinary UPLC target materialized from the deployable source. -/
def target (query : UplcQuery) : Term :=
  query.targetPlan.resolve query.source.term

end UplcQuery

namespace AssertedTerm

/-- The positional UPLC variables denoted by a declaration schema. This is the
canonical argument list for binding source-attached parameter assertions to a
symbolic function call. -/
def declarationArguments (declarations : List SymDecl) : List Term :=
  (List.range declarations.length).map fun index => .Var (index + 1)

def ofTerm (term : Term) : AssertedTerm :=
  { term }

/-- Recover the exact deployable/executable UPLC term. -/
def erase (source : AssertedTerm) : Term :=
  source.term

/-- Append one source assertion without changing the UPLC term. -/
def asserting (source : AssertedTerm)
    (assertion : UplcAssertion) : AssertedTerm :=
  { source with assertions := source.assertions ++ [assertion] }

/-- Append assertions in source order. -/
def assertingAll (source : AssertedTerm)
    (assertions : List UplcAssertion) : AssertedTerm :=
  { source with assertions := source.assertions ++ assertions }

def requiringParameter (source : AssertedTerm) (fuel : Nat)
    (predicate : Term) (parameterIndex : Nat) : AssertedTerm :=
  source.asserting <|
    UplcAssertion.onParameter fuel predicate parameterIndex

def requiringParameters (source : AssertedTerm) (fuel : Nat)
    (predicate : Term) (parameterIndices : List Nat) : AssertedTerm :=
  source.asserting <|
    UplcAssertion.onParameters fuel predicate parameterIndices

/-- Attach a unary external-parameter assertion only when its one-based index
belongs to the supplied declaration schema. -/
def requiringParameterChecked? (source : AssertedTerm)
    (declarations : List SymDecl) (fuel : Nat) (predicate : Term)
    (parameterIndex : Nat) : Option AssertedTerm := do
  let assertion ← UplcAssertion.onParameterChecked?
    declarations fuel predicate parameterIndex
  pure (source.asserting assertion)

/-- Checked multi-parameter attachment. -/
def requiringParametersChecked? (source : AssertedTerm)
    (declarations : List SymDecl) (fuel : Nat) (predicate : Term)
    (parameterIndices : List Nat) : Option AssertedTerm := do
  let assertion ← UplcAssertion.onParametersChecked?
    declarations fuel predicate parameterIndices
  pure (source.asserting assertion)

/-- Query the source term using any supported observable CEK expectation. -/
def expecting (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) : UplcQuery :=
  { source
    expectation }

/-- Require the source term to finish with any CEK value. -/
def succeeds (source : AssertedTerm) : UplcQuery :=
  source.expecting .succeeds

/-- Require the source term to return the exact Boolean. -/
def returnsBool (source : AssertedTerm) (expected : Bool) : UplcQuery :=
  source.expecting (.boolEq expected)

/-- Require the source term to return the exact integer. -/
def returnsInt (source : AssertedTerm) (expected : Int) : UplcQuery :=
  source.expecting (.intEq expected)

/-- Require the source term to reach an actual CEK runtime error. -/
def errors (source : AssertedTerm) : UplcQuery :=
  source.expecting .error

/-- Apply the deployable source program to explicit UPLC arguments and query
the actual CEK result of that call. Attached parameter assertions still refer
to external symbolic declarations, while the supplied argument terms determine
the call being verified. A parameter contract applies to the call only when
the call uses the corresponding symbolic declaration term as its argument. -/
def appliedWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation)
    (arguments : List Term) : UplcQuery :=
  { source
    targetPlan := .applied .source arguments
    expectation }

/-- Apply the source program and require any successful CEK result. -/
def applied (source : AssertedTerm) (arguments : List Term) : UplcQuery :=
  source.appliedWith .succeeds arguments

/-- Apply the source function to exactly the symbolic declaration variables.
This is the safe positional function-contract bridge: an assertion on
external `Var i` and the corresponding call argument necessarily denote the
same CEK environment entry. -/
def appliedToDeclarationsWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation)
    (declarations : List SymDecl) : UplcQuery :=
  source.appliedWith expectation (declarationArguments declarations)

/-- Require any successful result from applying the source to all symbolic
declaration variables. -/
def appliedToDeclarations (source : AssertedTerm)
    (declarations : List SymDecl) : UplcQuery :=
  source.appliedToDeclarationsWith .succeeds declarations

/-- Build `.Apply predicate source.term` and query its exact CEK result using
an arbitrary supported expectation. CEK evaluates `predicate` before the
source argument. When the predicate expression successfully produces a
callable value, the source is evaluated and its CEK value is passed to it.

For `.error`, remember that the error can arise while evaluating either the
consumer, the source argument, or the call itself. Use a syntactic lambda as
the consumer when the obligation specifically requires source evaluation
before the consumer body.

The returned value is a verification query, not another `AssertedTerm`.
Consequently `source.erase` remains the exact deployable source program. -/
def resultSatisfiesWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) (predicate : Term) : UplcQuery :=
  { source
    targetPlan := .consumed predicate .source
    expectation }

/-- Compile `.Apply predicate source.term` and require exactly `Bool true`. -/
def resultSatisfies (source : AssertedTerm)
    (predicate : Term) : UplcQuery :=
  source.resultSatisfiesWith (.boolEq true) predicate

/-- Apply a source function to arguments, then use that call as the argument of
an ordinary UPLC consumer/predicate application and query the exact result. -/
def appliedResultSatisfiesWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) (arguments : List Term)
    (predicate : Term) : UplcQuery :=
  { source
    targetPlan := .consumed predicate (.applied .source arguments)
    expectation }

/-- Boolean-true specialization of `appliedResultSatisfiesWith`. -/
def appliedResultSatisfies (source : AssertedTerm)
    (arguments : List Term) (predicate : Term) : UplcQuery :=
  source.appliedResultSatisfiesWith (.boolEq true) arguments predicate

/-- Apply the source to exactly the symbolic declaration variables, then pass
that call to a result consumer. -/
def declarationResultSatisfiesWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation)
    (declarations : List SymDecl) (predicate : Term) : UplcQuery :=
  source.appliedResultSatisfiesWith expectation
    (declarationArguments declarations) predicate

/-- Boolean-true specialization of `declarationResultSatisfiesWith`. -/
def declarationResultSatisfies (source : AssertedTerm)
    (declarations : List SymDecl) (predicate : Term) : UplcQuery :=
  source.declarationResultSatisfiesWith (.boolEq true)
    declarations predicate

end AssertedTerm

namespace UplcQuery

/-- Construct a query directly from an ordinary UPLC term. -/
def ofTerm (term : Term)
    (expectation : UplcAssertionExpectation := .succeeds) : UplcQuery :=
  (AssertedTerm.ofTerm term).expecting expectation

/-- Recover the original deployable UPLC term, never the verification-only
target. -/
def erase (query : UplcQuery) : Term :=
  query.source.erase

/-- Select a different observable CEK result without changing the source or
verification target. -/
def withExpectation (query : UplcQuery)
    (expectation : UplcAssertionExpectation) : UplcQuery :=
  { query with expectation }

/-- Apply the current source-rooted target to more UPLC arguments.  This can
be chained with `consumeResult` while `erase` continues to return the original
deployable source. -/
def applyArguments (query : UplcQuery)
    (arguments : List Term) : UplcQuery :=
  { query with targetPlan := .applied query.targetPlan arguments }

/-- Pass the current source-rooted target to an ordinary call-by-value UPLC
consumer.  The materialized target is exactly `.Apply consumer query.target`.
As in CEK, the consumer expression is evaluated before its argument. -/
def consumeResult (query : UplcQuery) (consumer : Term) : UplcQuery :=
  { query with targetPlan := .consumed consumer query.targetPlan }

/-- Append one source assertion without changing the target program or its
result expectation. -/
def asserting (query : UplcQuery)
    (assertion : UplcAssertion) : UplcQuery :=
  { query with source := query.source.asserting assertion }

/-- Append source assertions in order. -/
def assertingAll (query : UplcQuery)
    (assertions : List UplcAssertion) : UplcQuery :=
  { query with source := query.source.assertingAll assertions }

end UplcQuery

end Moist.SMT.UPLC

namespace Moist.Plutus.Term.Term

open Moist.SMT.UPLC

/-- Attach verification assertions to an ordinary UPLC term without changing
its runtime or serialized representation. -/
def withAssertions (term : Term)
    (assertions : List UplcAssertion) : AssertedTerm :=
  { term, assertions }

def withAssertion (term : Term)
    (assertion : UplcAssertion) : AssertedTerm :=
  { term, assertions := [assertion] }

def withParameterAssertion (term : Term) (fuel : Nat)
    (predicate : Term) (parameterIndex : Nat) : AssertedTerm :=
  term.withAssertion <|
    UplcAssertion.onParameter fuel predicate parameterIndex

def withParameterAssertions (term : Term) (fuel : Nat)
    (predicate : Term) (parameterIndices : List Nat) : AssertedTerm :=
  term.withAssertion <|
    UplcAssertion.onParameters fuel predicate parameterIndices

/-- Declaration-aware parameter assertion attachment. -/
def withParameterAssertionChecked? (term : Term)
    (declarations : List SymDecl) (fuel : Nat) (predicate : Term)
    (parameterIndex : Nat) : Option AssertedTerm :=
  (AssertedTerm.ofTerm term).requiringParameterChecked?
    declarations fuel predicate parameterIndex

/-- Declaration-aware multi-parameter assertion attachment. -/
def withParameterAssertionsChecked? (term : Term)
    (declarations : List SymDecl) (fuel : Nat) (predicate : Term)
    (parameterIndices : List Nat) : Option AssertedTerm :=
  (AssertedTerm.ofTerm term).requiringParametersChecked?
    declarations fuel predicate parameterIndices

/-- Build a source-attached query template over an ordinary UPLC term. -/
def querying (term : Term)
    (expectation : UplcAssertionExpectation := .succeeds) : UplcQuery :=
  (AssertedTerm.ofTerm term).expecting expectation

/-- Query whether an ordinary UPLC term finishes with any CEK value. -/
def queryingSuccess (term : Term) : UplcQuery :=
  term.querying .succeeds

/-- Discharge the term's result into an ordinary UPLC predicate and require
the predicate to return exactly `Bool true`. -/
def queryingResult (term : Term) (predicate : Term) : UplcQuery :=
  (AssertedTerm.ofTerm term).resultSatisfies predicate

/-- Pass the term to an ordinary UPLC consumer and select any supported
observable result of the resulting call-by-value application. -/
def queryingResultWith (term : Term)
    (expectation : UplcAssertionExpectation) (consumer : Term) : UplcQuery :=
  (AssertedTerm.ofTerm term).resultSatisfiesWith expectation consumer

/-- Apply an ordinary UPLC function term to arguments and select any
supported observable result of that call. -/
def queryingAppliedWith (term : Term)
    (expectation : UplcAssertionExpectation)
    (arguments : List Term) : UplcQuery :=
  (AssertedTerm.ofTerm term).appliedWith expectation arguments

end Moist.Plutus.Term.Term

namespace Moist.SMT.UPLC

open Moist.Plutus.Term

/-- Compile every UPLC assertion once, in source order. -/
def uplcAssertionConditions (declarations : List SymDecl)
    (assertions : List UplcAssertion) : List SExpr :=
  assertions.map (UplcAssertion.condition declarations)

/-- Try a propagation-heavy refinement pass for at most one second, then fall
back to the former two-way portfolio of context-aware and direct SMT search.
The bounded fast path solves common arithmetic/control-flow obligations with
roughly half the solver memory, while the fallback retains the more robust
behavior needed by hard datatype equalities.

This changes only solver strategy.  `scriptWithTactic_assertions` in
`Moist.SMT.Soundness.Compiler` proves that the tactic string cannot add,
remove, or rewrite a logical assertion, and the production CEK endpoints
consume exactly that assertion list. -/
def z3QueryTactic : String :=
  "(or-else (try-for (then simplify propagate-values smt) 1000) " ++
    "(par-or (then simplify ctx-solver-simplify smt) smt))"

/-- Construct the typed command sequence with a caller-supplied solver tactic.
The production compiler uses only the fixed, reviewed `z3QueryTactic`; callers of
this benchmarking helper remain responsible for supplying well-formed Z3
tactic syntax at the external rendering boundary. -/
def scriptWithTactic (tactic : String) (decls : List SymDecl)
    (assertions : List SExpr) : Moist.SMT.Script :=
  let logicalAssertions :=
    decls.flatMap SymDecl.assumptions ++ groupedAssertions assertions
  ⟨preludeForAssertions logicalAssertions ++
    declCommands decls ++ assumptionCommands decls ++
    groupedAssertionCommands assertions ++
      [.checkSatUsing tactic, .getModel]⟩

def scriptWith (decls : List SymDecl) (assertions : List SExpr) : Moist.SMT.Script :=
  scriptWithTactic z3QueryTactic decls assertions

/-- Unoptimized reference used to state and benchmark prelude slicing. -/
def scriptWithFullPrelude (decls : List SymDecl)
    (assertions : List SExpr) : Moist.SMT.Script :=
  ⟨prelude ++ declCommands decls ++ assumptionCommands decls ++
    assertions.map Moist.SMT.Command.assert ++
      [.checkSatUsing z3QueryTactic, .getModel]⟩

/-- Opt-in final normalization for callers supplying arbitrary hand-written
assertions.  Compiler-generated queries already use the verified smart
constructors throughout; traversing their potentially shared decision DAG a
second time is both redundant and prohibitively expensive for symbolic list
programs. -/
def scriptWithSimplified (decls : List SymDecl)
    (assertions : List SExpr) : Moist.SMT.Script :=
  scriptWith decls (assertions.map Expr.simplifyBool)

/-- Check that a collection of UPLC parameter predicates has at least one
model.  Refinement-style callers should establish this query as satisfiable
before accepting an unsatisfiable obligation under the same assertions; that
separate check prevents contradictory preconditions from proving a result
vacuously. -/
def scriptForAssertionsSatisfiable (decls : List SymDecl)
    (assertions : List UplcAssertion) : Moist.SMT.Script :=
  scriptWith decls (uplcAssertionConditions decls assertions)

def scriptForSucceedsWithAssertions (fuel : Nat) (decls : List SymDecl)
    (assertions : List UplcAssertion) (t : Term) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls
    (uplcAssertionConditions decls assertions ++ [okCond outs])

def scriptForBoolTrueWithAssertions (fuel : Nat) (decls : List SymDecl)
    (assertions : List UplcAssertion) (t : Term) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls
    (uplcAssertionConditions decls assertions ++ [okBoolTrueCond outs])

def scriptForBoolEqWithAssertions (fuel : Nat) (decls : List SymDecl)
    (assertions : List UplcAssertion) (t : Term)
    (expected : Bool) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls
    (uplcAssertionConditions decls assertions ++
      [okBoolEqCond outs expected])

def scriptForIntEqWithAssertions (fuel : Nat) (decls : List SymDecl)
    (assertions : List UplcAssertion) (t : Term)
    (rhs : SExpr) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls
    (uplcAssertionConditions decls assertions ++ [okIntEqCond outs rhs])

def scriptForErrorWithAssertions (fuel : Nat) (decls : List SymDecl)
    (assertions : List UplcAssertion) (t : Term) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls
    (uplcAssertionConditions decls assertions ++ [errorCond outs])

def scriptForSucceeds (fuel : Nat) (decls : List SymDecl)
    (t : Term) : Moist.SMT.Script :=
  scriptForSucceedsWithAssertions fuel decls [] t

def scriptForBoolTrue (fuel : Nat) (decls : List SymDecl) (t : Term) : Moist.SMT.Script :=
  scriptForBoolTrueWithAssertions fuel decls [] t

def scriptForBoolEq (fuel : Nat) (decls : List SymDecl)
    (t : Term) (expected : Bool) : Moist.SMT.Script :=
  scriptForBoolEqWithAssertions fuel decls [] t expected

def scriptForIntEq (fuel : Nat) (decls : List SymDecl) (t : Term) (rhs : SExpr) : Moist.SMT.Script :=
  scriptForIntEqWithAssertions fuel decls [] t rhs

def scriptForError (fuel : Nat) (decls : List SymDecl) (t : Term) : Moist.SMT.Script :=
  scriptForErrorWithAssertions fuel decls [] t

end Moist.SMT.UPLC
