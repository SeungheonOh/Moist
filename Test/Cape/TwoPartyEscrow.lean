import Test.Cape.Ledger

namespace Test.Cape.TwoPartyEscrow

open Moist.Cardano.V3
open Moist.Onchain (PlutusData dataBeq)
open Moist.Onchain.Prelude
open Moist.Plutus (Data)

@[onchain] def buyer : PubKeyHash := ⟨Array.replicate 28 0xaa⟩

@[onchain] def seller : PubKeyHash := ⟨Array.replicate 28 0xbb⟩

@[onchain] def token : TokenName := ⟨#[0x65, 0x73, 0x63, 0x72, 0x6f, 0x77]⟩
@[onchain] def ada : CurrencySymbol := ⟨#[]⟩

@[onchain] def exactMint (info : TxInfo) (policy : CurrencySymbol) (amount : Int) : Bool :=
  match Moist.Onchain.AssocMap.lookup policy info.mint with
  | none => false
  | some tokens => dataBeq tokens (Moist.Onchain.AssocMap.singleton token amount)

@[onchain] def outputsAt (credential : Credential) : List TxOut → List TxOut
  | [] => []
  | output :: rest =>
    let others := outputsAt credential rest
    if dataBeq output.address.credential credential then output :: others else others

@[onchain] def paidTo (key : PubKeyHash) : List TxOut → Int
  | [] => 0
  | output :: rest =>
    let total := paidTo key rest
    if dataBeq output.address.credential (.pubKeyCredential key)
    then addInteger total (quantity output.value ada ada) else total

@[onchain] noncomputable def deposit (info : TxInfo) (policy : CurrencySymbol) : Bool :=
  match outputsAt (.scriptCredential policy) info.outputs with
  | [output] =>
    let depositTime := subtractInteger (finiteTime info.validRange.upperBound.bound) 1
    match output.datum with
    | .outputDatum datum =>
      signedBy buyer info.signatories && exactMint info policy 1 &&
        equalsInteger (quantity output.value ada ada) 75000000 &&
        equalsInteger (quantity output.value policy token) 1 &&
        equalsData datum (constrData 0 [iData depositTime])
    | _ => false
  | _ => false

@[onchain] noncomputable def pastDeadline (info : TxInfo) (datum : MaybeData Data) : Bool :=
  match datum with
  | .justData raw =>
    let fields := unConstrData raw
    match fields.2 with
    | [time] => equalsInteger fields.1 0 &&
        lessThanInteger (addInteger (unIData time) 1800000) (finiteTime info.validRange.lowerBound.bound)
    | _ => false
  | _ => false

@[onchain] noncomputable def spend (info : TxInfo) (reference : TxOutRef)
    (datum : MaybeData Data) (action : Int) : Bool :=
  let credential := (ownOutput reference info.inputs).address.credential
  match credential with
  | .scriptCredential policy =>
    equalsInteger (countInputs credential info.inputs) 1 &&
      equalsInteger (quantity info.mint policy token) (-1) &&
      (if equalsInteger action 1 then
         signedBy seller info.signatories && lessThanEqInteger 75000000 (paidTo seller info.outputs)
       else equalsInteger action 2 && signedBy buyer info.signatories && pastDeadline info datum &&
         lessThanEqInteger 75000000 (paidTo buyer info.outputs))
  | _ => false

@[onchain] noncomputable def validate (context : ScriptContext) : Unit :=
  let action := unIData context.redeemer
  let info := context.txInfo
  let valid := match context.scriptInfo with
    | .mintingScript policy =>
      if equalsInteger action 0 then deposit info policy
      else (equalsInteger action 1 || equalsInteger action 2) && exactMint info policy (-1)
    | .spendingScript reference datum => spend info reference datum action
    | _ => false
  if valid then () else pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! validate

end Test.Cape.TwoPartyEscrow
