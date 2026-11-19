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
    let ⟨inputs, _, _, _, _, _, _, range, signers, _, _, _, _, _, _, _⟩ := context.txInfo
    let action := unConstrData context.redeemer
    let authorized := match action.2 with
      | [] => equalsInteger action.1 1 &&
        signedByAddress terms.payer signers &&
        lessThanInteger terms.timeout (earliest range.lowerBound)
      | [preimage] => equalsInteger action.1 0 &&
        equalsByteString (sha2_256 (unBData preimage)) terms.secretHash &&
        signedByAddress terms.recipient signers &&
        lessThanInteger (latest range.upperBound) terms.timeout
      | _ => false
    let single := match inputs with
      | [input] => Moist.Onchain.dataBeq input.outRef reference
      | _ => (uniqueOwnOutput reference inputs).isSome
    if authorized && single
    then () else pError
  | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
def script := compile! validate

end Test.Cape.HTLC
