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

/-! The configuration is user-supplied, so it is decoded exactly as Plinth decodes it:
`unknown` stands for any constructor index the Plinth type does not have, and is rejected
instead of being read as the last constructor. Tuples are `makeIsDataIndexed` products,
which require index 0 and decode both components. -/

@[plutus_data]
inductive PredKey where
  | minValue : PredKey
  | maxValue : PredKey
  | notEqual : PredKey
  | unknown : PredKey

/-- `(PredKey, [Integer])`. -/
@[plutus_data]
inductive IntegerPredicate where
  | mk : PredKey → List Data → IntegerPredicate
  | unknown : IntegerPredicate

/-- `(Integer, Integer)`. -/
@[plutus_data]
inductive Fraction where
  | mk : Int → Int → Fraction
  | unknown : Fraction

/-- `(PredKey, [(Integer, Integer)])`. -/
@[plutus_data]
inductive RationalPredicate where
  | mk : PredKey → List Fraction → RationalPredicate
  | unknown : RationalPredicate

@[plutus_data]
inductive ParamValue where
  | paramInteger : List IntegerPredicate → ParamValue
  | paramRational : List RationalPredicate → ParamValue
  | paramList : List ParamValue → ParamValue
  | paramAny : ParamValue
  | unknown : ParamValue

/-- `(Integer, ParamValue)`; the value stays undecoded until a changed parameter needs it. -/
@[plutus_data]
inductive ConfigEntry where
  | mk : Int → Data → ConfigEntry
  | unknown : ConfigEntry

@[onchain] def allAtLeast (actual : Int) : List Data → Bool
  | [] => true
  | bound :: rest => if lessThanEqInteger (unIData bound) actual then allAtLeast actual rest else false

@[onchain] def allAtMost (actual : Int) : List Data → Bool
  | [] => true
  | bound :: rest => if lessThanEqInteger actual (unIData bound) then allAtMost actual rest else false

@[onchain] def allDifferent (actual : Int) : List Data → Bool
  | [] => true
  | bound :: rest => if equalsInteger (unIData bound) actual then false else allDifferent actual rest

@[onchain] noncomputable def integerPredicates (actual : Int) : List IntegerPredicate → Bool
  | [] => true
  | .unknown :: _ => pError
  | .mk key expected :: rest =>
    let holds := match key with
      | .minValue => allAtLeast actual expected
      | .maxValue => allAtMost actual expected
      | .notEqual => allDifferent actual expected
      | .unknown => pError
    if holds then integerPredicates actual rest else false

@[onchain] noncomputable def fractionsAtLeast (numerator denominator : Int) : List Fraction → Bool
  | [] => true
  | .unknown :: _ => pError
  | .mk boundNumerator boundDenominator :: rest =>
    if lessThanEqInteger (multiplyInteger boundNumerator denominator)
        (multiplyInteger numerator boundDenominator)
    then fractionsAtLeast numerator denominator rest else false

@[onchain] noncomputable def fractionsAtMost (numerator denominator : Int) : List Fraction → Bool
  | [] => true
  | .unknown :: _ => pError
  | .mk boundNumerator boundDenominator :: rest =>
    if lessThanEqInteger (multiplyInteger numerator boundDenominator)
        (multiplyInteger boundNumerator denominator)
    then fractionsAtMost numerator denominator rest else false

@[onchain] noncomputable def fractionsDifferent (numerator denominator : Int) : List Fraction → Bool
  | [] => true
  | .unknown :: _ => pError
  | .mk boundNumerator boundDenominator :: rest =>
    if equalsInteger (multiplyInteger boundNumerator denominator)
        (multiplyInteger numerator boundDenominator)
    then false else fractionsDifferent numerator denominator rest

@[onchain] noncomputable def rationalPredicates (numerator denominator : Int) :
    List RationalPredicate → Bool
  | [] => true
  | .unknown :: _ => pError
  | .mk key expected :: rest =>
    let holds := match key with
      | .minValue => fractionsAtLeast numerator denominator expected
      | .maxValue => fractionsAtMost numerator denominator expected
      | .notEqual => fractionsDifferent numerator denominator expected
      | .unknown => pError
    if holds then rationalPredicates numerator denominator rest else false

/-- The changed value of a rational parameter is the list `[numerator, denominator]`. -/
@[onchain] noncomputable def rationalValue (predicates : List RationalPredicate) (actual : Data) : Bool :=
  let components := unListData actual
  let numerator := unIData (headList components)
  let denominator := unIData (headList (tailList components))
  rationalPredicates numerator denominator predicates

/-- A list parameter must supply exactly one value per configured sub-parameter. -/
@[onchain] noncomputable def validateValues : List ParamValue → List Data → Bool
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
    | .unknown => pError
termination_by values => sizeOf values

@[onchain] noncomputable def validateParamValue (value : ParamValue) (actual : Data) : Bool :=
  validateValues [value] [actual]

/-- Sorted merge-join: `paramId`/`actual` is the current changed parameter and `rest` the
changed parameters after it. Configuration entries below `paramId` are skipped. -/
@[onchain] noncomputable def mergeRules (paramId : Int) (actual : Data) (rest : List (Data × Data)) :
    List ConfigEntry → Bool
  | [] => false
  | .unknown :: _ => pError
  | .mk entryId value :: config =>
    if equalsInteger paramId entryId then
      if validateParamValue (Moist.Onchain.PlutusData.unsafeFromData value) actual then
        match rest with
        | [] => true
        | changed :: rest => mergeRules (unIData changed.1) changed.2 rest config
      else false
    else if lessThanInteger entryId paramId then mergeRules paramId actual rest config
    else false

@[onchain] noncomputable def runRules (config : List ConfigEntry) : List (Data × Data) → Bool
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
