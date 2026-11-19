import Test.Cape.Ledger

namespace Test.Cape.LinearVesting

open Moist.Cardano.V3
open Moist.Onchain (PlutusData dataBeq)
open Moist.Onchain.Prelude

@[plutus_data] structure Asset where
  policy : CurrencySymbol
  token : TokenName

@[plutus_data] structure Schedule where
  beneficiary : Address
  asset : Asset
  total : Int
  startTime : Int
  endTime : Int
  firstUnlock : Int
  installments : Int

@[onchain] def ceilDiv (amount divisor : Int) :=
  addInteger 1 (divideInteger (subtractInteger amount 1) divisor)

@[onchain] noncomputable def continuingOutput (address : Address) : List TxOut → TxOut
  | [] => pError
  | output :: rest =>
    if dataBeq output.address address then output else continuingOutput address rest

@[onchain] noncomputable def partialUnlock (schedule : Schedule) (time : Int)
    (reference : TxOutRef) (inputs : List TxInInfo) (outputs : List TxOut) : Bool :=
  let previous := match uniqueOwnOutput reference inputs with
    | some output => output
    | none => pError
  let continuing := continuingOutput previous.address outputs
  let asset := schedule.asset
  let remaining := quantity continuing.value asset.policy asset.token
  let interval := ceilDiv (subtractInteger schedule.endTime schedule.startTime) schedule.installments
  let future := ceilDiv (subtractInteger schedule.endTime time) interval
  lessThanInteger schedule.firstUnlock time &&
    dataBeq previous.datum continuing.datum &&
    lessThanInteger 0 remaining &&
    lessThanInteger remaining (quantity previous.value asset.policy asset.token) &&
    equalsInteger remaining (ceilDiv (multiplyInteger future schedule.total) schedule.installments)

@[onchain] noncomputable def validate (context : ScriptContext) : Unit :=
  match context.scriptInfo with
  | .spendingScript reference (.justData raw) =>
    let schedule : Schedule := PlutusData.unsafeFromData raw
    let ⟨inputs, _, outputs, _, _, _, _, range, signers, _, _, _, _, _, _, _⟩ := context.txInfo
    let time := earliest range.lowerBound
    if signedByAddress schedule.beneficiary signers &&
      (if equalsData context.redeemer (constrData 0 []) then partialUnlock schedule time reference inputs outputs
       else equalsData context.redeemer (constrData 1 []) && lessThanInteger schedule.endTime time)
    then () else pError
  | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
def script := compile! validate

end Test.Cape.LinearVesting
