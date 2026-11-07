import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Cardano.V3

namespace Test.Comparison.Cross.Constitution

open Moist.Plutus (Data)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! Port of `Constitution.Contracts.ConstitutionSortedPlinth`: guardrail checks for
parameter-change proposals, as a sorted merge-join between the configuration and the
changed parameters. -/

@[plutus_data]
inductive PredKey where
  | minValue : PredKey
  | maxValue : PredKey
  | notEqual : PredKey

/-- `(PredKey, [Integer])`. -/
@[plutus_data]
structure IntegerPredicate where
  key : PredKey
  expected : List Data

/-- `(Integer, Integer)`. -/
@[plutus_data]
structure Fraction where
  numerator : Int
  denominator : Int

/-- `(PredKey, [(Integer, Integer)])`. -/
@[plutus_data]
structure RationalPredicate where
  key : PredKey
  expected : List Fraction

@[plutus_data]
inductive ParamValue where
  | paramInteger : List IntegerPredicate → ParamValue
  | paramRational : List RationalPredicate → ParamValue
  | paramList : List ParamValue → ParamValue
  | paramAny : ParamValue

/-- `(Integer, ParamValue)`; the value stays undecoded until a changed parameter needs it. -/
@[plutus_data]
structure ConfigEntry where
  paramId : Int
  value : Data

@[onchain] def allAtLeast (actual : Int) : List Data → Bool
  | [] => true
  | bound :: rest => if lessThanEqInteger (unIData bound) actual then allAtLeast actual rest else false

@[onchain] def allAtMost (actual : Int) : List Data → Bool
  | [] => true
  | bound :: rest => if lessThanEqInteger actual (unIData bound) then allAtMost actual rest else false

@[onchain] def allDifferent (actual : Int) : List Data → Bool
  | [] => true
  | bound :: rest => if equalsInteger (unIData bound) actual then false else allDifferent actual rest

@[onchain] def integerPredicates (actual : Int) : List IntegerPredicate → Bool
  | [] => true
  | predicate :: rest =>
    let holds := match predicate.key with
      | .minValue => allAtLeast actual predicate.expected
      | .maxValue => allAtMost actual predicate.expected
      | .notEqual => allDifferent actual predicate.expected
    if holds then integerPredicates actual rest else false

@[onchain] def fractionsAtLeast (numerator denominator : Int) : List Fraction → Bool
  | [] => true
  | bound :: rest =>
    if lessThanEqInteger (multiplyInteger bound.numerator denominator)
        (multiplyInteger numerator bound.denominator)
    then fractionsAtLeast numerator denominator rest else false

@[onchain] def fractionsAtMost (numerator denominator : Int) : List Fraction → Bool
  | [] => true
  | bound :: rest =>
    if lessThanEqInteger (multiplyInteger numerator bound.denominator)
        (multiplyInteger bound.numerator denominator)
    then fractionsAtMost numerator denominator rest else false

@[onchain] def fractionsDifferent (numerator denominator : Int) : List Fraction → Bool
  | [] => true
  | bound :: rest =>
    if equalsInteger (multiplyInteger bound.numerator denominator)
        (multiplyInteger numerator bound.denominator)
    then false else fractionsDifferent numerator denominator rest

@[onchain] def rationalPredicates (numerator denominator : Int) : List RationalPredicate → Bool
  | [] => true
  | predicate :: rest =>
    let holds := match predicate.key with
      | .minValue => fractionsAtLeast numerator denominator predicate.expected
      | .maxValue => fractionsAtMost numerator denominator predicate.expected
      | .notEqual => fractionsDifferent numerator denominator predicate.expected
    if holds then rationalPredicates numerator denominator rest else false

/-- The changed value of a rational parameter is the list `[numerator, denominator]`. -/
@[onchain] def rationalValue (predicates : List RationalPredicate) (actual : Data) : Bool :=
  let components := unListData actual
  let numerator := unIData (headList components)
  let denominator := unIData (headList (tailList components))
  rationalPredicates numerator denominator predicates

/-- A list parameter must supply exactly one value per configured sub-parameter. -/
@[onchain] def validateValues : List ParamValue → List Data → Bool
  | [], actuals => nullList actuals
  | _ :: _, [] => false
  | value :: values, actual :: actuals =>
    match value with
    | .paramInteger predicates =>
      if integerPredicates (unIData actual) predicates then validateValues values actuals else false
    | .paramRational predicates =>
      if rationalValue predicates actual then validateValues values actuals else false
    | .paramList inner =>
      if validateValues inner (unListData actual) then validateValues values actuals else false
    | .paramAny => validateValues values actuals
termination_by values => sizeOf values

@[onchain] def validateParamValue (value : ParamValue) (actual : Data) : Bool :=
  validateValues [value] [actual]

/-- Sorted merge-join: `paramId`/`actual` is the current changed parameter and `rest` the
changed parameters after it. Configuration entries below `paramId` are skipped. -/
@[onchain] def mergeRules (paramId : Int) (actual : Data) (rest : List (Data × Data)) :
    List ConfigEntry → Bool
  | [] => false
  | entry :: config =>
    if equalsInteger paramId entry.paramId then
      if validateParamValue (Moist.Onchain.PlutusData.unsafeFromData entry.value) actual then
        match rest with
        | [] => true
        | changed :: rest => mergeRules (unIData changed.1) changed.2 rest config
      else false
    else if lessThanInteger entry.paramId paramId then mergeRules paramId actual rest config
    else false

@[onchain] def runRules (config : List ConfigEntry) : List (Data × Data) → Bool
  | [] => true
  | changed :: rest => mergeRules (unIData changed.1) changed.2 rest config

@[onchain] noncomputable def constitution (configData : Data) (context : ScriptContext) : Unit :=
  let config : List ConfigEntry := Moist.Onchain.PlutusData.unsafeFromData configData
  match context.scriptInfo with
  | .proposingScript _ proposal =>
    match proposal.governanceAction with
    | .parameterChange _ changed _ => if runRules config (unMapData changed) then () else pError
    | .treasuryWithdrawals _ _ => ()
    | _ => pError
  | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! constitution

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def scriptSize := compile! constitution

end Test.Comparison.Cross.Constitution
