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

/-- `wallets` is a `Map PubKeyHash Integer`, kept as raw entries: like Plinth's data-backed
map, the port compares keys as `Data` and never decodes them. -/
@[plutus_data]
structure CrowdfundDatum where
  recipient : PubKeyHash
  goal : Int
  deadline : Int
  wallets : Data

/-- `unknown` stands for any other constructor index, which Plinth rejects. -/
@[plutus_data]
inductive CrowdfundRedeemer where
  | donate : Int → PubKeyHash → CrowdfundRedeemer
  | withdraw : CrowdfundRedeemer
  | reclaim : CrowdfundRedeemer
  | unknown : CrowdfundRedeemer

/-! ## Wallets (`DMap` operations on the raw entries) -/

@[onchain] def walletTotal (accumulator : Int) : List (Data × Data) → Int
  | [] => accumulator
  | entry :: rest => walletTotal (addInteger accumulator (unIData entry.2)) rest

@[onchain] def walletOf (owner : Data) : List (Data × Data) → Option Int
  | [] => none
  | entry :: rest => if equalsData owner entry.1 then some (unIData entry.2) else walletOf owner rest

@[onchain] def withoutWallet (owner : Data) : List (Data × Data) → List (Data × Data)
  | [] => []
  | entry :: rest => if equalsData owner entry.1 then rest else entry :: withoutWallet owner rest

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

/-- The datum fields every action reads, decoded up front as Plinth does. -/
@[plutus_sop]
structure Campaign where
  recipient : PubKeyHash
  goal : Int
  deadline : Int
  wallets : List (Data × Data)

@[onchain] noncomputable def checkDonate (campaign : Campaign) (range : POSIXTimeRange)
    (signatories : List PubKeyHash) (outputs : List TxOut) (contractAmount amount : Int)
    (donor : PubKeyHash) : Bool :=
  match outputs with
  | [output] =>
    if startsBefore range campaign.deadline then
      if signedBy donor signatories then
        if equalsInteger (lovelace output.value) (addInteger contractAmount amount) then
          match inlineDatum output with
          | ⟨outRecipient, outGoal, outDeadline, outWallets⟩ =>
            if equalsByteString outRecipient campaign.recipient then
              if equalsInteger outGoal campaign.goal then
                if equalsInteger outDeadline campaign.deadline then
                  let donorKey := bData donor
                  let outEntries := unMapData outWallets
                  if equalsData (mapData (withoutWallet donorKey campaign.wallets))
                      (mapData (withoutWallet donorKey outEntries)) then
                    match walletOf donorKey outEntries with
                    | none => false
                    | some outAmount =>
                      match walletOf donorKey campaign.wallets with
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

@[onchain] noncomputable def checkReclaim (campaign : Campaign) (range : POSIXTimeRange)
    (signatories : List PubKeyHash) (outputs : List TxOut) (inputAmount : Int) : Bool :=
  let signer := match signatories with
    | [] => pError
    | signer :: _ => bData signer
  match walletOf signer campaign.wallets with
  | none => false
  | some withdrawn =>
    if startsBefore range campaign.deadline then false
    else match campaign.wallets with
      | _ :: _ :: _ =>
        match outputs with
        | [output] =>
          if equalsInteger (lovelace output.value) (subtractInteger inputAmount withdrawn) then
            match inlineDatum output with
            | ⟨outRecipient, outGoal, outDeadline, outWallets⟩ =>
              if equalsByteString outRecipient campaign.recipient then
                if equalsInteger outGoal campaign.goal then
                  if equalsInteger outDeadline campaign.deadline then
                    equalsData outWallets (mapData (withoutWallet signer campaign.wallets))
                  else false
                else false
              else false
          else false
        | _ => false
      | _ =>
        match outputs with
        | [] => true
        | _ => false

@[onchain] noncomputable def crowdfundValidator (campaign : Campaign)
    (redeemer : CrowdfundRedeemer) (ownRef : TxOutRef) (info : TxInfo) : Bool :=
  match info with
  | ⟨inputs, _, outputs, _, _, _, _, range, signatories, _, _, _, _, _, _, _⟩ =>
    let address := ownAddress ownRef inputs
    let contractAmount := walletTotal 0 campaign.wallets
    let inputAmount := adaAt address 0 inputs
    if equalsInteger contractAmount inputAmount then
      match redeemer with
      | .donate amount donor =>
        checkDonate campaign range signatories (outputsAt address outputs) contractAmount amount donor
      | .withdraw =>
        if signedBy campaign.recipient signatories then
          if startsBefore range campaign.deadline then false
          else lessThanEqInteger campaign.goal contractAmount
        else false
      | .reclaim => checkReclaim campaign range signatories (outputsAt address outputs) inputAmount
      | .unknown => pError
    else false

@[onchain] noncomputable def crowdfund (context : ScriptContext) : Unit :=
  match context with
  | ⟨info, redeemer, scriptInfo⟩ =>
    match scriptInfo with
    | .spendingScript ownRef (.justData datum) =>
      match (PlutusData.unsafeFromData datum : CrowdfundDatum) with
      | ⟨recipient, goal, deadline, wallets⟩ =>
        let campaign : Campaign := ⟨recipient, goal, deadline, unMapData wallets⟩
        if crowdfundValidator campaign (PlutusData.unsafeFromData redeemer) ownRef info
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
