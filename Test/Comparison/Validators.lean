import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Cardano.V3

namespace Test.Comparison.Validators

open Moist.Plutus (Data ByteString)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! Ports of Voting, Certifying and Vesting at comparison repository commit
e21532661107f5d4feb380f9b1dcdf3ddb3b023f. Inputs retain the V3 Data ABI.
These deliberately preserve the source contracts' rules, not hardened replacements. -/

@[onchain] def fields (value : Data) : List Data := sndPair (unConstrData value)
@[onchain] def first (value : Data) : Data := headList (fields value)
@[onchain] def second (value : Data) : Data := headList (tailList (fields value))
@[onchain] def third (value : Data) : Data := headList (tailList (tailList (fields value)))
@[onchain] def fourth (value : Data) : Data :=
  headList (tailList (tailList (tailList (fields value))))

@[onchain] def findToken (token : Data) : List (Data × Data) → Bool
  | [] => false
  | entry :: rest =>
    if equalsData entry.1 token then equalsInteger (unIData entry.2) 1
    else findToken token rest

@[onchain] def findCurrency (currency token : Data) : List (Data × Data) → Bool
  | [] => false
  | entry :: rest =>
    if equalsData entry.1 currency then findToken token (unMapData entry.2)
    else findCurrency currency token rest

@[onchain] def anyInputHasNFT (currency token : Data) : List Data → Bool
  | [] => false
  | input :: rest =>
    if findCurrency currency token (unMapData (second (second input))) then true
    else anyInputHasNFT currency token rest

@[onchain] noncomputable def voting (currency token context : Data) : Unit :=
  if equalsInteger (fstPair (unConstrData (third context))) 4 then
    if anyInputHasNFT currency token (unListData (first (first context)))
      then () else pError
  else pError

@[onchain] def entirelyAfter (range : POSIXTimeRange) (expiration : Int) : Bool :=
  match range.lowerBound.bound with
  | .negInf => false
  | .posInf => true
  | .finite timestamp =>
    match range.lowerBound.closure with
    | .inclusive => lessThanInteger expiration timestamp
    | .exclusive => lessThanEqInteger expiration timestamp

@[onchain] def delegateToAbstain (delegatee : Delegatee) : Bool :=
  match delegatee with
  | .delegVote .dRepAlwaysAbstain => true
  | _ => false

@[onchain] noncomputable def certifying (expiration : Data) (context : ScriptContext) : Unit :=
  let expirationTime := unIData expiration
  match context.scriptInfo with
  | .certifyingScript _ certificate =>
    let valid := match certificate with
      | .txCertRegStaking _ _ => true
      | .txCertUnRegStaking _ _ => entirelyAfter context.txInfo.validRange expirationTime
      | .txCertDelegStaking _ delegatee => delegateToAbstain delegatee
      | .txCertRegDeleg _ delegatee _ => delegateToAbstain delegatee
      | _ => false
    if valid then () else pError
  | _ => pError

@[onchain] noncomputable def lovelace (value : Data) : Int :=
  match unMapData value with
  | [] => pError
  | outer :: _ =>
    match unMapData outer.2 with
    | [] => pError
    | inner :: _ => unIData inner.2

@[onchain] def addressIsPkh (address : Data) (beneficiary : ByteString) : Bool :=
  let credential := unConstrData (first address)
  if equalsInteger credential.1 0 then
    equalsByteString (unBData (headList credential.2)) beneficiary
  else false

@[onchain] noncomputable def sumOutputs (beneficiary : ByteString) (accumulator : Int) : List Data → Int
  | [] => accumulator
  | output :: rest =>
    let amount := if addressIsPkh (first output) beneficiary then lovelace (second output) else 0
    sumOutputs beneficiary (addInteger accumulator amount) rest

@[onchain] noncomputable def sumInputs (beneficiary : ByteString) (accumulator : Int) : List Data → Int
  | [] => accumulator
  | input :: rest =>
    let output := second input
    let amount := if addressIsPkh (first output) beneficiary then lovelace (second output) else 0
    sumInputs beneficiary (addInteger accumulator amount) rest

@[onchain] def signedBy (beneficiary : ByteString) : List Data → Bool
  | [] => false
  | signer :: rest =>
    if equalsByteString (unBData signer) beneficiary then true else signedBy beneficiary rest

@[onchain] noncomputable def ownInput (reference : Data) : List Data → Data
  | [] => pError
  | input :: rest =>
    if equalsData (first input) reference then second input else ownInput reference rest

@[onchain] def outputsAt (address : Data) : List Data → List Data
  | [] => []
  | output :: rest =>
    if equalsData (first output) address then output :: outputsAt address rest
    else outputsAt address rest

@[onchain] def earliestTime (range : Data) : Int :=
  let extended := first (first range)
  if equalsInteger (fstPair (unConstrData extended)) 1 then unIData (first extended) else 0

@[onchain] def linearVesting (start duration allocation timestamp : Int) : Int :=
  if lessThanInteger timestamp start then 0
  else if lessThanInteger (addInteger start duration) timestamp then allocation
  else divideInteger (multiplyInteger allocation (subtractInteger timestamp start)) duration

@[onchain] noncomputable def continuationMatches (address datum : Data) (outputs : List Data) : Bool :=
  match outputsAt address outputs with
  | [output] =>
    let outputDatum := third output
    if equalsInteger (fstPair (unConstrData outputDatum)) 2 then equalsData (first outputDatum) datum
    else pError
  | _ => false

@[onchain] noncomputable def vesting (context : Data) : Unit :=
  let scriptInfo := third context
  if equalsInteger (fstPair (unConstrData scriptInfo)) 1 then
    let maybeDatum := second scriptInfo
    if equalsInteger (fstPair (unConstrData maybeDatum)) 0 then
      let datum := first maybeDatum
      let beneficiary := unBData (first datum)
      let infoFields := fields (first context)
      let afterWithdrawals := tailList (tailList (tailList (tailList (tailList (tailList (tailList infoFields))))))
      if signedBy beneficiary (unListData (headList (tailList afterWithdrawals))) then
        let inputs := unListData (headList infoFields)
        let outputs := unListData (headList (tailList (tailList infoFields)))
        let resolved := ownInput (first scriptInfo) inputs
        let contractAmount := lovelace (second resolved)
        let declaredAmount := unIData (first (second context))
        let allocation := unIData (fourth datum)
        let released := subtractInteger allocation contractAmount
        let releaseAmount := subtractInteger
          (linearVesting (unIData (second datum)) (unIData (third datum)) allocation
            (earliestTime (headList afterWithdrawals))) released
        if equalsInteger declaredAmount releaseAmount then
          let fee := unIData (headList (tailList (tailList (tailList infoFields))))
          if equalsInteger (sumOutputs beneficiary 0 outputs)
              (subtractInteger (addInteger declaredAmount (sumInputs beneficiary 0 inputs)) fee) then
            if equalsInteger declaredAmount contractAmount then ()
            else if continuationMatches (first resolved) datum outputs then () else pError
          else pError
        else pError
      else pError
    else pError
  else pError

set_option maxRecDepth 10000 in
def votingScript := compile! voting

set_option maxRecDepth 10000 in
def certifyingScript := compile! certifying

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingScript := compile! vesting

open Lean Elab Term in
elab "comparisonRaw! " target:ident : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let expression ← Moist.Onchain.translateDefByName name body
  match Moist.MIR.lowerExpr expression with
  | .error message => throwError message
  | .ok script => return Moist.Onchain.ToExprInstances.uplcTermToExpr script

set_option maxRecDepth 10000 in
def votingRaw := comparisonRaw! voting
set_option maxRecDepth 10000 in
def certifyingRaw := comparisonRaw! certifying
set_option maxRecDepth 10000 in
def vestingRaw := comparisonRaw! vesting

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def votingSize := compile! voting
set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def certifyingSize := compile! certifying
set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingSize := compile! vesting

end Test.Comparison.Validators
