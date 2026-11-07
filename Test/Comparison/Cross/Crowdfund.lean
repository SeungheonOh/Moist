import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Cardano.V3

namespace Test.Comparison.Cross.Crowdfund

open Moist.Plutus (Data ByteString AssocMap)
open Moist.Onchain (PlutusData dataBeq)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! Port of `Crowdfund.Contracts.CrowdfundPlinth`: a crowdfunding spending validator with
donate, withdraw and reclaim actions. -/

@[plutus_data]
structure CrowdfundDatum where
  recipient : PubKeyHash
  goal : Int
  deadline : Int
  wallets : AssocMap PubKeyHash Int

@[plutus_data]
inductive CrowdfundRedeemer where
  | donate : Int → PubKeyHash → CrowdfundRedeemer
  | withdraw : CrowdfundRedeemer
  | reclaim : CrowdfundRedeemer

/-- The quantity of the first token of the first currency (Ada in a ledger-ordered value). -/
@[onchain] noncomputable def lovelace (value : Value) : Int :=
  Moist.Onchain.AssocMap.withHead (fun _ => pError)
    (fun _ tokens _ => Moist.Onchain.AssocMap.withHead (fun _ => pError)
      (fun _ quantity _ => quantity) tokens) value

@[onchain] noncomputable def ownAddress (reference : TxOutRef) : List TxInInfo → Address
  | [] => pError
  | input :: rest =>
    if dataBeq input.outRef reference then input.resolved.address else ownAddress reference rest

/-- Total Ada held by the inputs at `address`. -/
@[onchain] noncomputable def adaAt (address : Address) (accumulator : Int) : List TxInInfo → Int
  | [] => accumulator
  | input :: rest =>
    let output := input.resolved
    if dataBeq output.address address then
      adaAt address (addInteger accumulator (lovelace output.value)) rest
    else adaAt address accumulator rest

@[onchain] def outputsAt (address : Address) : List TxOut → List TxOut
  | [] => []
  | output :: rest =>
    if dataBeq output.address address then output :: outputsAt address rest else outputsAt address rest

@[onchain] def signedBy (signer : PubKeyHash) : List PubKeyHash → Bool
  | [] => false
  | candidate :: rest => if equalsByteString candidate signer then true else signedBy signer rest

/-- The validity range starts at a finite time strictly before `deadline`. -/
@[onchain] def startsBefore (range : POSIXTimeRange) (deadline : Int) : Bool :=
  match range.lowerBound.bound with
  | .finite time => lessThanInteger time deadline
  | _ => false

@[onchain] noncomputable def inlineDatum (output : TxOut) : CrowdfundDatum :=
  match output.datum with
  | .outputDatum datum => PlutusData.unsafeFromData datum
  | _ => pError

@[onchain] noncomputable def checkDonate (datum : CrowdfundDatum) (range : POSIXTimeRange)
    (signatories : List PubKeyHash) (outputs : List TxOut) (contractAmount amount : Int)
    (donor : PubKeyHash) : Bool :=
  match outputs with
  | [output] =>
    if startsBefore range datum.deadline then
      if signedBy donor signatories then
        if equalsInteger (lovelace output.value) (addInteger contractAmount amount) then
          match inlineDatum output with
          | ⟨outRecipient, outGoal, outDeadline, outWallets⟩ =>
            if equalsByteString outRecipient datum.recipient then
              if equalsInteger outGoal datum.goal then
                if equalsInteger outDeadline datum.deadline then
                  if dataBeq (Moist.Onchain.AssocMap.delete donor datum.wallets)
                      (Moist.Onchain.AssocMap.delete donor outWallets) then
                    match Moist.Onchain.AssocMap.lookup donor outWallets with
                    | none => false
                    | some outAmount =>
                      match Moist.Onchain.AssocMap.lookup donor datum.wallets with
                      | none => equalsInteger amount outAmount
                      | some previous => equalsInteger outAmount (addInteger previous amount)
                  else false
                else false
              else false
            else false
        else false
      else false
    else false
  | _ => false

@[onchain] noncomputable def checkReclaim (datum : CrowdfundDatum) (range : POSIXTimeRange)
    (signatories : List PubKeyHash) (outputs : List TxOut) (inputAmount : Int) : Bool :=
  let signer := match signatories with
    | [] => pError
    | signer :: _ => signer
  match Moist.Onchain.AssocMap.lookup signer datum.wallets with
  | none => false
  | some withdrawn =>
    if startsBefore range datum.deadline then false
    else if Moist.Onchain.AssocMap.hasMultiple datum.wallets then
      match outputs with
      | [output] =>
        if equalsInteger (lovelace output.value) (subtractInteger inputAmount withdrawn) then
          match inlineDatum output with
          | ⟨outRecipient, outGoal, outDeadline, outWallets⟩ =>
            if equalsByteString outRecipient datum.recipient then
              if equalsInteger outGoal datum.goal then
                if equalsInteger outDeadline datum.deadline then
                  dataBeq outWallets (Moist.Onchain.AssocMap.delete signer datum.wallets)
                else false
              else false
            else false
        else false
      | _ => false
    else match outputs with
      | [] => true
      | _ => false

@[onchain] noncomputable def crowdfundValidator (datum : CrowdfundDatum)
    (redeemer : CrowdfundRedeemer) (ownRef : TxOutRef) (info : TxInfo) : Bool :=
  match info with
  | ⟨inputs, _, outputs, _, _, _, _, range, signatories, _, _, _, _, _, _, _⟩ =>
    let address := ownAddress ownRef inputs
    let contractAmount :=
      Moist.Onchain.AssocMap.foldl (fun total _ amount => addInteger total amount) 0 datum.wallets
    let inputAmount := adaAt address 0 inputs
    if equalsInteger contractAmount inputAmount then
      match redeemer with
      | .donate amount donor =>
        checkDonate datum range signatories (outputsAt address outputs) contractAmount amount donor
      | .withdraw =>
        if signedBy datum.recipient signatories then
          if startsBefore range datum.deadline then false
          else lessThanEqInteger datum.goal contractAmount
        else false
      | .reclaim => checkReclaim datum range signatories (outputsAt address outputs) inputAmount
    else false

@[onchain] noncomputable def crowdfund (context : ScriptContext) : Unit :=
  match context with
  | ⟨info, redeemer, scriptInfo⟩ =>
    match scriptInfo with
    | .spendingScript ownRef (.justData datum) =>
      if crowdfundValidator (PlutusData.unsafeFromData datum) (PlutusData.unsafeFromData redeemer)
          ownRef info
      then () else pError
    | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! crowdfund

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def scriptSize := compile! crowdfund

end Test.Comparison.Cross.Crowdfund
