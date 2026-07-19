import Moist.SMT.Compiler.Validation

/-!
# Erasure laws for source-attached UPLC assertions

These small kernel theorems keep the deployable ordinary UPLC term separate
from verification-only targets.  No executable compiler module imports this
proof file.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term

namespace UplcQueryTarget

@[simp] theorem resolve_source (source : Term) :
    UplcQueryTarget.source.resolve source = source := rfl

@[simp] theorem resolve_applied (source : Term) (target : UplcQueryTarget)
    (arguments : List Term) :
    (UplcQueryTarget.applied target arguments).resolve source =
      arguments.foldl (fun function argument => .Apply function argument)
        (target.resolve source) := rfl

@[simp] theorem resolve_consumed (source consumer : Term)
    (target : UplcQueryTarget) :
    (UplcQueryTarget.consumed consumer target).resolve source =
      .Apply consumer (target.resolve source) := rfl

private theorem foldApply_usesOpaque_of_initial
    (arguments : List Term) (initial : Term)
    (hInitial :
      Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness initial =
        true) :
    Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness
      (arguments.foldl
        (fun function argument => .Apply function argument) initial) = true := by
  induction arguments generalizing initial with
  | nil => exact hInitial
  | cons argument arguments ih =>
      apply ih
      simp [Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness,
        hInitial]

/-- Every materialized query target syntactically retains its deployable
source. In particular, the supported-builtin scan cannot accept a target while
hiding an unsupported builtin in `UplcQuery.erase`. -/
theorem resolve_usesOpaque_of_source
    (target : UplcQueryTarget) (source : Term)
    (hSource :
      Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness source =
        true) :
    Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness
      (target.resolve source) = true := by
  induction target with
  | source => exact hSource
  | applied target arguments ih =>
      exact foldApply_usesOpaque_of_initial arguments _ ih
  | consumed consumer target ih =>
      simp [UplcQueryTarget.resolve,
        Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness,
        ih]

/-- Contrapositive form used by checked source-attached compiler endpoints. -/
theorem source_noOpaque_of_resolve_noOpaque
    (target : UplcQueryTarget) (source : Term)
    (hTarget :
      Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness
        (target.resolve source) = false) :
    Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness source =
      false := by
  cases hSource :
      Moist.SMT.Compiler.Validation.termUsesOpaqueBuiltinForSoundness source with
  | false => rfl
  | true =>
      have := resolve_usesOpaque_of_source target source hSource
      simp_all

end UplcQueryTarget

namespace AssertedTerm

@[simp] theorem erase_ofTerm (term : Term) :
    (ofTerm term).erase = term := rfl

@[simp] theorem erase_asserting (source : AssertedTerm)
    (assertion : UplcAssertion) :
    (source.asserting assertion).erase = source.erase := rfl

@[simp] theorem erase_assertingAll (source : AssertedTerm)
    (assertions : List UplcAssertion) :
    (source.assertingAll assertions).erase = source.erase := rfl

@[simp] theorem erase_requiringParameter (source : AssertedTerm)
    (fuel : Nat) (predicate : Term) (parameterIndex : Nat) :
    (source.requiringParameter fuel predicate parameterIndex).erase =
      source.erase := rfl

@[simp] theorem erase_requiringParameters (source : AssertedTerm)
    (fuel : Nat) (predicate : Term) (parameterIndices : List Nat) :
    (source.requiringParameters fuel predicate parameterIndices).erase =
      source.erase := rfl

theorem erase_requiringParameterChecked?_of_some
    {source result : AssertedTerm} {declarations : List SymDecl}
    {fuel : Nat} {predicate : Term} {parameterIndex : Nat}
    (h : source.requiringParameterChecked? declarations fuel predicate
      parameterIndex = some result) :
    result.erase = source.erase := by
  by_cases hAccepted :
      UplcAssertion.parameterIndexAccepted declarations parameterIndex = true
  · simp [requiringParameterChecked?, UplcAssertion.onParameterChecked?,
      UplcAssertion.onParameterWithChecked?, hAccepted] at h
    subst result
    rfl
  · simp [requiringParameterChecked?, UplcAssertion.onParameterChecked?,
      UplcAssertion.onParameterWithChecked?, hAccepted] at h

theorem erase_requiringParametersChecked?_of_some
    {source result : AssertedTerm} {declarations : List SymDecl}
    {fuel : Nat} {predicate : Term} {parameterIndices : List Nat}
    (h : source.requiringParametersChecked? declarations fuel predicate
      parameterIndices = some result) :
    result.erase = source.erase := by
  by_cases hAccepted :
      UplcAssertion.parameterIndicesAccepted
        declarations parameterIndices = true
  · simp [requiringParametersChecked?, UplcAssertion.onParametersChecked?,
      UplcAssertion.onParametersWithChecked?, hAccepted] at h
    subst result
    rfl
  · simp [requiringParametersChecked?, UplcAssertion.onParametersChecked?,
      UplcAssertion.onParametersWithChecked?, hAccepted] at h

end AssertedTerm

namespace UplcQuery

@[simp] theorem erase_ofTerm (term : Term)
    (expectation : UplcAssertionExpectation) :
    (ofTerm term expectation).erase = term := rfl

@[simp] theorem erase_asserting (query : UplcQuery)
    (assertion : UplcAssertion) :
    (query.asserting assertion).erase = query.erase := rfl

@[simp] theorem erase_assertingAll (query : UplcQuery)
    (assertions : List UplcAssertion) :
    (query.assertingAll assertions).erase = query.erase := rfl

@[simp] theorem erase_withExpectation (query : UplcQuery)
    (expectation : UplcAssertionExpectation) :
    (query.withExpectation expectation).erase = query.erase := rfl

@[simp] theorem erase_applyArguments (query : UplcQuery)
    (arguments : List Term) :
    (query.applyArguments arguments).erase = query.erase := rfl

@[simp] theorem erase_consumeResult (query : UplcQuery)
    (consumer : Term) :
    (query.consumeResult consumer).erase = query.erase := rfl

end UplcQuery

namespace AssertedTerm

@[simp] theorem erase_expecting (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) :
    (source.expecting expectation).erase = source.erase := rfl

@[simp] theorem erase_succeeds (source : AssertedTerm) :
    source.succeeds.erase = source.erase := rfl

@[simp] theorem erase_returnsBool (source : AssertedTerm)
    (expected : Bool) :
    (source.returnsBool expected).erase = source.erase := rfl

@[simp] theorem erase_returnsInt (source : AssertedTerm)
    (expected : Int) :
    (source.returnsInt expected).erase = source.erase := rfl

@[simp] theorem erase_errors (source : AssertedTerm) :
    source.errors.erase = source.erase := rfl

@[simp] theorem erase_appliedWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) (arguments : List Term) :
    (source.appliedWith expectation arguments).erase = source.erase := rfl

@[simp] theorem erase_applied (source : AssertedTerm)
    (arguments : List Term) :
    (source.applied arguments).erase = source.erase := rfl

@[simp] theorem erase_appliedToDeclarationsWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation)
    (declarations : List SymDecl) :
    (source.appliedToDeclarationsWith expectation declarations).erase =
      source.erase := rfl

@[simp] theorem erase_appliedToDeclarations (source : AssertedTerm)
    (declarations : List SymDecl) :
    (source.appliedToDeclarations declarations).erase = source.erase := rfl

@[simp] theorem erase_resultSatisfiesWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) (predicate : Term) :
    (source.resultSatisfiesWith expectation predicate).erase =
      source.erase := rfl

@[simp] theorem erase_resultSatisfies (source : AssertedTerm)
    (predicate : Term) :
    (source.resultSatisfies predicate).erase = source.erase := rfl

@[simp] theorem erase_appliedResultSatisfiesWith (source : AssertedTerm)
    (expectation : UplcAssertionExpectation) (arguments : List Term)
    (predicate : Term) :
    (source.appliedResultSatisfiesWith
      expectation arguments predicate).erase = source.erase := rfl

@[simp] theorem erase_appliedResultSatisfies (source : AssertedTerm)
    (arguments : List Term) (predicate : Term) :
    (source.appliedResultSatisfies arguments predicate).erase =
      source.erase := rfl

@[simp] theorem erase_declarationResultSatisfiesWith
    (source : AssertedTerm) (expectation : UplcAssertionExpectation)
    (declarations : List SymDecl) (predicate : Term) :
    (source.declarationResultSatisfiesWith
      expectation declarations predicate).erase = source.erase := rfl

@[simp] theorem erase_declarationResultSatisfies
    (source : AssertedTerm) (declarations : List SymDecl)
    (predicate : Term) :
    (source.declarationResultSatisfies declarations predicate).erase =
      source.erase := rfl

end AssertedTerm

end Moist.SMT.UPLC

namespace Moist.Plutus.Term.Term

open Moist.SMT.UPLC

@[simp] theorem erase_withAssertions (term : Term)
    (assertions : List UplcAssertion) :
    (term.withAssertions assertions).erase = term := rfl

@[simp] theorem erase_withAssertion (term : Term)
    (assertion : UplcAssertion) :
    (term.withAssertion assertion).erase = term := rfl

@[simp] theorem erase_withParameterAssertion (term : Term) (fuel : Nat)
    (predicate : Term) (parameterIndex : Nat) :
    (term.withParameterAssertion fuel predicate parameterIndex).erase =
      term := rfl

@[simp] theorem erase_withParameterAssertions (term : Term) (fuel : Nat)
    (predicate : Term) (parameterIndices : List Nat) :
    (term.withParameterAssertions fuel predicate parameterIndices).erase =
      term := rfl

@[simp] theorem erase_querying (term : Term)
    (expectation : UplcAssertionExpectation) :
    (term.querying expectation).erase = term := rfl

@[simp] theorem erase_queryingSuccess (term : Term) :
    term.queryingSuccess.erase = term := rfl

@[simp] theorem erase_queryingResult (term predicate : Term) :
    (term.queryingResult predicate).erase = term := rfl

@[simp] theorem erase_queryingResultWith (term : Term)
    (expectation : UplcAssertionExpectation) (consumer : Term) :
    (term.queryingResultWith expectation consumer).erase = term := rfl

@[simp] theorem erase_queryingAppliedWith (term : Term)
    (expectation : UplcAssertionExpectation) (arguments : List Term) :
    (term.queryingAppliedWith expectation arguments).erase = term := rfl

end Moist.Plutus.Term.Term
