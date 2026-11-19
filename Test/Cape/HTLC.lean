import Test.Cape.Ledger

namespace Test.Cape.HTLC

open Moist.Cardano.V3
open Moist.Onchain (PlutusData)
open Moist.Onchain.Prelude
open Moist.Plutus (ByteString)

@[plutus_data] structure Terms where
  payer : Address
  recipient : Address
  secretHash : ByteString
  timeout : Int

@[onchain] noncomputable def validate (context : ScriptContext) : Unit :=
  match context.scriptInfo with
  | .spendingScript reference (.justData raw) =>
    let terms : Terms := PlutusData.unsafeFromData raw
    let info := context.txInfo
    let action := unConstrData context.redeemer
    let authorized :=
      if equalsInteger action.1 0 then
        match action.2 with
        | [preimage] =>
          equalsByteString (sha2_256 (unBData preimage)) terms.secretHash &&
          signedByAddress terms.recipient info.signatories &&
          lessThanInteger (latest info.validRange.upperBound) terms.timeout
        | _ => false
      else equalsData context.redeemer (constrData 1 []) &&
        signedByAddress terms.payer info.signatories &&
        lessThanInteger terms.timeout (earliest info.validRange.lowerBound)
    if authorized &&
      equalsInteger (countInputs (ownOutput reference info.inputs).address.credential info.inputs) 1
    then () else pError
  | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! validate

end Test.Cape.HTLC
