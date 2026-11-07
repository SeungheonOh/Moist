import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Cardano.V3

noncomputable section

namespace Test.Comparison.Cross.Hydra

open Moist.Plutus (Data ByteString)
open Moist.Onchain
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! Port of the Hydra head validator (`src/Hydra/Contracts/HeadPlinth.hs`).
The script takes the V3 `ScriptContext` as its only argument. Ledger and head
state types are read through Data-backed views; fields that are only compared,
serialised or iterated stay as `Data`. -/

/-! ## Ledger views -/

@[plutus_data] inductive TxOutDatum where
  | noOutputDatum : TxOutDatum
  | outputDatumHash : Data → TxOutDatum
  | outputDatum : Data → TxOutDatum

@[plutus_data] structure HeadTxOut where
  address : Data
  value : Data
  datum : TxOutDatum
  referenceScript : Data

@[plutus_data] structure HeadTxInInfo where
  outRef : Data
  resolved : HeadTxOut

@[plutus_data] structure HeadTxInfo where
  inputs : List HeadTxInInfo
  referenceInputs : Data
  outputs : List HeadTxOut
  fee : Data
  mint : Data
  txCerts : Data
  wdrl : Data
  validRange : POSIXTimeRange
  signatories : List Data
  redeemers : Data
  datumWitnesses : Data
  id : Data
  votes : Data
  proposalProcedures : Data
  currentTreasuryAmount : Data
  treasuryDonation : Data

/-! ## Head state and redeemers (`Hydra.Types.HeadState`) -/

@[plutus_data] structure OpenDatum where
  headSeed : Data
  headId : Data
  parties : Data
  contestationPeriod : Int
  version : Int
  utxoHash : ByteString

@[plutus_data] structure ClosedDatum where
  headId : Data
  parties : Data
  contestationPeriod : Int
  version : Int
  snapshotNumber : Int
  utxoHash : ByteString
  alphaUTxOHash : ByteString
  omegaUTxOHash : ByteString
  contesters : Data
  contestationDeadline : Int

@[plutus_data] inductive State where
  | openState : OpenDatum → State
  | closedState : ClosedDatum → State
  | finalState : State

@[plutus_data] inductive CloseRedeemer where
  | closeInitial : CloseRedeemer
  | closeAny : Data → CloseRedeemer
  | closeUnusedDec : Data → CloseRedeemer
  | closeUsedDec : Data → ByteString → CloseRedeemer
  | closeUnusedInc : Data → ByteString → CloseRedeemer
  | closeUsedInc : Data → ByteString → CloseRedeemer

@[plutus_data] inductive ContestRedeemer where
  | contestCurrent : Data → ContestRedeemer
  | contestUsedDec : Data → ByteString → ContestRedeemer
  | contestUnusedDec : Data → ContestRedeemer
  | contestUnusedInc : Data → ByteString → ContestRedeemer
  | contestUsedInc : Data → ContestRedeemer

@[plutus_data] structure IncrementRedeemer where
  signatures : Data
  snapshotNumber : Int
  depositRef : Data

@[plutus_data] structure DecrementRedeemer where
  signatures : Data
  snapshotNumber : Int
  numberOfDecommitOutputs : Int

@[plutus_data] inductive Input where
  | collectCom : Input
  | increment : IncrementRedeemer → Input
  | decrement : DecrementRedeemer → Input
  | close : CloseRedeemer → Input
  | contest : ContestRedeemer → Input
  | abort : Input
  | fanout : Int → Int → Int → Input

@[plutus_data] inductive HeadScriptInfo where
  | mintingScript : Data → HeadScriptInfo
  | spendingScript : Data → MaybeData State → HeadScriptInfo
  | rewardingScript : Data → HeadScriptInfo
  | certifyingScript : Data → Data → HeadScriptInfo
  | votingScript : Data → HeadScriptInfo
  | proposingScript : Data → Data → HeadScriptInfo

@[plutus_data] structure HeadContext where
  txInfo : HeadTxInfo
  redeemer : Input
  scriptInfo : HeadScriptInfo

/-! ## Constants -/

def hydraHeadV2 : ByteString := "HydraHeadV2".toUTF8

/-- `sha2_256 ""`, the hash of an empty list of outputs. -/
def emptyHash : ByteString := ByteArray.mk #[
  0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
  0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55]

/-! ## Lists -/

@[onchain] def listLength : List Data → Int
  | [] => 0
  | _ :: rest => addInteger 1 (listLength rest)

@[onchain] def notElem (wanted : Data) : List Data → Bool
  | [] => true
  | entry :: rest => if equalsData entry wanted then false else notElem wanted rest

/-! ## Values

Values are read as plain Data maps. Comparisons follow `PlutusLedgerApi.V1.Value`:
amounts are compared pointwise over the union of keys, with missing entries read as 0. -/

/-- Token map of `currency` (first match), or empty. -/
@[onchain] def tokensOf (currency : Data) : List (Data × Data) → List (Data × Data)
  | [] => []
  | entry :: rest => if equalsData entry.1 currency then unMapData entry.2 else tokensOf currency rest

@[onchain] def quantityOf (token : Data) : List (Data × Data) → Int
  | [] => 0
  | entry :: rest => if equalsData entry.1 token then unIData entry.2 else quantityOf token rest

@[onchain] def sumQuantities : List (Data × Data) → Int
  | [] => 0
  | entry :: rest => addInteger (unIData entry.2) (sumQuantities rest)

/-- `atLeast`: `left ≥ right`; otherwise `left = right`. -/
@[onchain] def quantitiesRelate (atLeast : Bool) (left right : Int) : Bool :=
  if atLeast then lessThanEqInteger right left else equalsInteger left right

/-- Each token of one currency relates to its quantity in `others`, the same currency's tokens
on the other side. `mineOnLeft` says which side `tokens` is on. -/
@[onchain] def tokensRelate (atLeast mineOnLeft : Bool) (others : List (Data × Data)) :
    List (Data × Data) → Bool
  | [] => true
  | entry :: rest =>
    let mine := unIData entry.2
    let theirs := quantityOf entry.1 others
    let holds := if mineOnLeft then quantitiesRelate atLeast mine theirs
      else quantitiesRelate atLeast theirs mine
    if holds then tokensRelate atLeast mineOnLeft others rest else false

@[onchain] def currenciesRelate (atLeast mineOnLeft : Bool) (other : List (Data × Data)) :
    List (Data × Data) → Bool
  | [] => true
  | entry :: rest =>
    if tokensRelate atLeast mineOnLeft (tokensOf entry.1 other) (unMapData entry.2) then
      currenciesRelate atLeast mineOnLeft other rest
    else false

/-- Pointwise relation between two values over every asset of either. -/
@[onchain] def valueRelate (atLeast : Bool) (left right : List (Data × Data)) : Bool :=
  if currenciesRelate atLeast true right left then currenciesRelate atLeast false left right else false

/-! Value addition (`unionWith (+)`). -/

@[onchain] def addQuantity (token : Data) (quantity : Int) : List (Data × Data) → List (Data × Data)
  | [] => [(token, iData quantity)]
  | entry :: rest =>
    if equalsData entry.1 token then (token, iData (addInteger (unIData entry.2) quantity)) :: rest
    else entry :: addQuantity token quantity rest

@[onchain] def addTokens (into : List (Data × Data)) : List (Data × Data) → List (Data × Data)
  | [] => into
  | entry :: rest => addTokens (addQuantity entry.1 (unIData entry.2) into) rest

@[onchain] def addCurrency (currency : Data) (tokens : List (Data × Data)) :
    List (Data × Data) → List (Data × Data)
  | [] => [(currency, mapData tokens)]
  | entry :: rest =>
    if equalsData entry.1 currency then (currency, mapData (addTokens (unMapData entry.2) tokens)) :: rest
    else entry :: addCurrency currency tokens rest

@[onchain] def addValue (into : List (Data × Data)) : List (Data × Data) → List (Data × Data)
  | [] => into
  | entry :: rest => addValue (addCurrency entry.1 (unMapData entry.2) into) rest

@[onchain] def addOutputValues (into : List (Data × Data)) : List HeadTxOut → List (Data × Data)
  | [] => into
  | output :: rest => addOutputValues (addValue into (unMapData output.value)) rest

@[onchain] def mapIsEmpty (map : Data) : Bool :=
  match unMapData map with
  | [] => true
  | _ => false

@[onchain] def hasST (headId : Data) (value : Data) : Bool :=
  equalsInteger (quantityOf (bData hydraHeadV2) (tokensOf headId (unMapData value))) 1

/-! ## Outputs and hashing -/

@[onchain] def serialiseTake (count : Int) (outputs : List HeadTxOut) : ByteString :=
  if lessThanEqInteger count 0 then ByteArray.empty
  else match outputs with
    | [] => ByteArray.empty
    | output :: rest =>
      appendByteString (serialiseData (PlutusData.toData output)) (serialiseTake (subtractInteger count 1) rest)

/-- `hashTxOuts (take count outputs)`. -/
@[onchain] def hashTake (count : Int) (outputs : List HeadTxOut) : ByteString :=
  sha2_256 (serialiseTake count outputs)

@[onchain] def takeOutputs (count : Int) (outputs : List HeadTxOut) : List HeadTxOut :=
  if lessThanEqInteger count 0 then []
  else match outputs with
    | [] => []
    | output :: rest => output :: takeOutputs (subtractInteger count 1) rest

@[onchain] def dropOutputs (count : Int) (outputs : List HeadTxOut) : List HeadTxOut :=
  if lessThanEqInteger count 0 then outputs
  else match outputs with
    | [] => []
    | _ :: rest => dropOutputs (subtractInteger count 1) rest

/-! ## Deposit datum

`fromBuiltinData @(CurrencySymbol, POSIXTime, [Commit])`: a malformed datum yields no commits. -/

@[onchain] def isConstr (value : Data) : Bool := chooseData value true false false false false
@[onchain] def isList (value : Data) : Bool := chooseData value false false true false false
@[onchain] def isInteger (value : Data) : Bool := chooseData value false false false true false
@[onchain] def isBytes (value : Data) : Bool := chooseData value false false false false true

/-- Fields of a `Constr 0` value, or `none`. -/
@[onchain] def constrZeroFields (value : Data) : Option (List Data) :=
  if isConstr value then
    let parts := unConstrData value
    if equalsInteger (fstPair parts) 0 then some (sndPair parts) else none
  else none

@[onchain] def isTxOutRef (value : Data) : Bool :=
  match constrZeroFields value with
  | some (id :: index :: _) => if isBytes id then isInteger index else false
  | _ => false

@[onchain] def isCommit (value : Data) : Bool :=
  match constrZeroFields value with
  | some (input :: output :: _) => if isTxOutRef input then isBytes output else false
  | _ => false

@[onchain] def allCommits : List Data → Bool
  | [] => true
  | commit :: rest => if isCommit commit then allCommits rest else false

@[onchain] def depositCommits (datum : TxOutDatum) : List Data :=
  match datum with
  | .outputDatum value =>
    match constrZeroFields value with
    | some (headId :: deadline :: commits :: _) =>
      if isBytes headId then
        if isInteger deadline then
          if isList commits then
            let entries := unListData commits
            if allCommits entries then entries else []
          else []
        else []
      else []
    | _ => []
  | _ => []

/-- `compareRef (commitInput a) (commitInput b) /= GT` for validated commits. -/
@[onchain] def commitNotAfter (left right : Data) : Bool :=
  let leftRef := sndPair (unConstrData (headList (sndPair (unConstrData left))))
  let rightRef := sndPair (unConstrData (headList (sndPair (unConstrData right))))
  let leftId := unBData (headList leftRef)
  let rightId := unBData (headList rightRef)
  if lessThanByteString leftId rightId then true
  else if equalsByteString leftId rightId then
    lessThanEqInteger (unIData (headList (tailList leftRef))) (unIData (headList (tailList rightRef)))
  else false

@[onchain] def insertCommit (commit : Data) : List Data → List Data
  | [] => [commit]
  | entry :: rest =>
    if commitNotAfter commit entry then commit :: entry :: rest else entry :: insertCommit commit rest

@[onchain] def sortCommits : List Data → List Data
  | [] => []
  | commit :: rest => insertCommit commit (sortCommits rest)

@[onchain] def concatPreSerialized : List Data → ByteString
  | [] => ByteArray.empty
  | commit :: rest =>
    appendByteString (unBData (headList (tailList (sndPair (unConstrData commit))))) (concatPreSerialized rest)

@[onchain] def hashPreSerializedCommits (commits : List Data) : ByteString :=
  sha2_256 (concatPreSerialized (sortCommits commits))

/-! ## Snapshot signatures -/

@[onchain] def snapshotMessage (headId : Data) (version snapshotNumber : Int)
    (utxoHash commitHash decommitHash : ByteString) : ByteString :=
  appendByteString (serialiseData headId)
    (appendByteString (serialiseData (iData version))
      (appendByteString (serialiseData (iData snapshotNumber))
        (appendByteString (serialiseData (bData utxoHash))
          (appendByteString (serialiseData (bData commitHash)) (serialiseData (bData decommitHash))))))

/-- Every party signed `message`, with exactly one signature per party. -/
@[onchain] def verifyAll (message : ByteString) (signatures : List Data) : List Data → Bool
  | [] => nullList signatures
  | party :: parties =>
    match signatures with
    | [] => false
    | signature :: rest =>
      if verifyEd25519Signature (unBData party) message (unBData signature) then verifyAll message rest parties
      else false

@[onchain] def verifySnapshotSignature (parties : Data) (headId : Data) (version snapshotNumber : Int)
    (utxoHash commitHash decommitHash : ByteString) (signatures : Data) : Bool :=
  verifyAll (snapshotMessage headId version snapshotNumber utxoHash commitHash decommitHash)
    (unListData signatures) (unListData parties)

/-! ## Head validator helpers -/

@[onchain] def ownInput (reference : Data) : List HeadTxInInfo → HeadTxOut
  | [] => pError
  | input :: rest => if equalsData input.outRef reference then input.resolved else ownInput reference rest

@[onchain] def inputWithST (headId : Data) : List HeadTxInInfo → Data
  | [] => pError
  | input :: rest => if hasST headId input.resolved.value then input.resolved.value else inputWithST headId rest

/-- State in the inline datum of the first output, which must sit at the head address. -/
@[onchain] def headOutputState (headAddress : Data) (outputs : List HeadTxOut) : State :=
  match outputs with
  | [] => pError
  | output :: _ =>
    if equalsData output.address headAddress then
      match output.datum with
      | .outputDatum datum => PlutusData.unsafeFromData datum
      | _ => pError
    else pError

@[onchain] def firstValue (outputs : List HeadTxOut) : Data :=
  match outputs with
  | [] => pError
  | output :: _ => output.value

@[onchain] def hasParticipationToken (signer : Data) : List (Data × Data) → Bool
  | [] => false
  | entry :: rest =>
    if equalsData entry.1 signer then
      if equalsInteger (unIData entry.2) 1 then true else hasParticipationToken signer rest
    else hasParticipationToken signer rest

@[onchain] def anyInputHoldsToken (headId signer : Data) : List HeadTxInInfo → Bool
  | [] => false
  | input :: rest =>
    if hasParticipationToken signer (tokensOf headId (unMapData input.resolved.value)) then true
    else anyInputHoldsToken headId signer rest

/-- The only signatory holds a participation token (quantity 1, not the state token) of the head. -/
@[onchain] def mustBeSignedByParticipant (headId : Data) (info : HeadTxInfo) : Bool :=
  match info.signatories with
  | [signer] =>
    if equalsData signer (bData hydraHeadV2) then false
    else anyInputHoldsToken headId signer info.inputs
  | _ => pError

@[onchain] def upperTime (range : POSIXTimeRange) : Int :=
  match range.upperBound.bound with
  | .finite time => time
  | _ => pError

@[onchain] def lowerTime (range : POSIXTimeRange) : Int :=
  match range.lowerBound.bound with
  | .finite time => time
  | _ => pError

@[onchain] def mustNotChangeParameters (parties parties' : Data) (period period' : Int)
    (headId headId' : Data) : Bool :=
  if equalsData parties parties' then
    if equalsInteger period period' then equalsData headId headId' else false
  else false

/-! ## Transitions

Every open/closed transition other than fanout needs the same four checks: its own state
rules, a participant signature, a value relation between the head input and the outputs,
and a multi-signed snapshot. Each transition describes these, and `headTransition` checks
them in one place. All checks are side-effect free, so their order does not affect which
transactions are accepted. -/

/-- The snapshot a transition must be signed over. -/
@[plutus_sop] inductive Snapshot where
  | invalid : Snapshot
  | unsigned : Snapshot
  | signed (parties headId : Data) (version snapshotNumber : Int)
      (utxoHash commitHash decommitHash : ByteString) (signatures : Data) : Snapshot

@[plutus_sop] structure Transition where
  rulesHold : Bool
  headId : Data
  /-- `true`: `lhs ≥ rhs`; `false`: `lhs = rhs`, pointwise. -/
  atLeast : Bool
  lhs : List (Data × Data)
  rhs : List (Data × Data)
  snapshot : Snapshot

@[onchain] def snapshotSigned (snapshot : Snapshot) : Bool :=
  match snapshot with
  | .invalid => false
  | .unsigned => true
  | .signed parties headId version snapshotNumber utxoHash commitHash decommitHash signatures =>
    verifySnapshotSignature parties headId version snapshotNumber utxoHash commitHash decommitHash signatures

@[onchain] def snapshotRejected (snapshot : Snapshot) : Bool :=
  match snapshot with
  | .invalid => true
  | _ => false

@[onchain] def headTransition (info : HeadTxInfo) (transition : Transition) : Bool :=
  if transition.rulesHold then
    if snapshotRejected transition.snapshot then false
    else if mustBeSignedByParticipant transition.headId info then
      if valueRelate transition.atLeast transition.lhs transition.rhs then snapshotSigned transition.snapshot
      else false
    else false
  else false

@[onchain] def increment (info : HeadTxInfo) (head : HeadTxOut) (before : OpenDatum)
    (redeemer : IncrementRedeemer) : Transition :=
  let next : OpenDatum := match headOutputState head.address info.outputs with
    | .openState datum => datum
    | _ => pError
  -- Finding the deposit input also establishes that the claimed deposit is spent.
  let deposit := ownInput redeemer.depositRef info.inputs
  { rulesHold :=
      if mustNotChangeParameters before.parties next.parties before.contestationPeriod
          next.contestationPeriod before.headId next.headId then
        equalsInteger next.version (addInteger before.version 1)
      else false
    headId := before.headId
    atLeast := false
    lhs := addValue (unMapData (inputWithST before.headId info.inputs)) (unMapData deposit.value)
    rhs := unMapData (firstValue info.outputs)
    snapshot := .signed next.parties next.headId before.version redeemer.snapshotNumber next.utxoHash
      (hashPreSerializedCommits (depositCommits deposit.datum)) emptyHash redeemer.signatures }

@[onchain] def decrement (info : HeadTxInfo) (head : HeadTxOut) (before : OpenDatum)
    (redeemer : DecrementRedeemer) : Transition :=
  let next : OpenDatum := match headOutputState head.address info.outputs with
    | .openState datum => datum
    | _ => pError
  let decommitOutputs := match info.outputs with
    | [] => pError
    | _ :: rest => takeOutputs redeemer.numberOfDecommitOutputs rest
  { rulesHold :=
      if mustNotChangeParameters before.parties next.parties before.contestationPeriod
          next.contestationPeriod before.headId next.headId then
        equalsInteger next.version (addInteger before.version 1)
      else false
    headId := before.headId
    atLeast := false
    lhs := unMapData head.value
    rhs := addOutputValues (unMapData (firstValue info.outputs)) decommitOutputs
    snapshot := .signed next.parties next.headId before.version redeemer.snapshotNumber next.utxoHash
      emptyHash (hashTake redeemer.numberOfDecommitOutputs decommitOutputs) redeemer.signatures }

@[onchain] def closeSnapshot (before : OpenDatum) (closed : ClosedDatum) (redeemer : CloseRedeemer) :
    Snapshot :=
  let alphaEmpty := equalsByteString closed.alphaUTxOHash emptyHash
  let omegaEmpty := equalsByteString closed.omegaUTxOHash emptyHash
  let snapshot := fun (version : Int) (snapshotNumber : Int) (utxoHash commitHash decommitHash : ByteString)
      (signatures : Data) =>
    Snapshot.signed before.parties before.headId version snapshotNumber utxoHash commitHash decommitHash
      signatures
  match redeemer with
  | .closeInitial =>
    if equalsInteger before.version 0 then
      if equalsInteger closed.snapshotNumber 0 then
        if equalsByteString closed.utxoHash before.utxoHash then .unsigned else .invalid
      else .invalid
    else .invalid
  | .closeAny signatures =>
    if lessThanInteger 0 closed.snapshotNumber then
      if alphaEmpty then
        if omegaEmpty then
          snapshot before.version closed.snapshotNumber closed.utxoHash emptyHash emptyHash signatures
        else .invalid
      else .invalid
    else .invalid
  | .closeUnusedDec signatures =>
    if alphaEmpty then
      if omegaEmpty then .invalid
      else snapshot before.version closed.snapshotNumber closed.utxoHash emptyHash closed.omegaUTxOHash
        signatures
    else .invalid
  | .closeUsedDec signatures alreadyDecommitted =>
    if alphaEmpty then
      if omegaEmpty then
        snapshot (subtractInteger before.version 1) closed.snapshotNumber closed.utxoHash emptyHash
          alreadyDecommitted signatures
      else .invalid
    else .invalid
  | .closeUnusedInc signatures alreadyCommitted =>
    if alphaEmpty then
      if omegaEmpty then
        snapshot before.version closed.snapshotNumber closed.utxoHash alreadyCommitted emptyHash signatures
      else .invalid
    else .invalid
  | .closeUsedInc signatures alreadyCommitted =>
    if equalsByteString closed.alphaUTxOHash alreadyCommitted then
      if omegaEmpty then
        snapshot (subtractInteger before.version 1) closed.snapshotNumber closed.utxoHash alreadyCommitted
          emptyHash signatures
      else .invalid
    else .invalid

@[onchain] def close (info : HeadTxInfo) (head : HeadTxOut) (before : OpenDatum)
    (redeemer : CloseRedeemer) : Transition :=
  let closed : ClosedDatum := match headOutputState head.address info.outputs with
    | .closedState datum => datum
    | _ => pError
  let upper := upperTime info.validRange
  let period := before.contestationPeriod
  { rulesHold :=
      if mapIsEmpty info.mint then
        if lessThanEqInteger (subtractInteger upper (lowerTime info.validRange)) period then
          if equalsInteger closed.contestationDeadline (addInteger upper period) then
            if equalsInteger closed.version before.version then
              if nullList (unListData closed.contesters) then
                mustNotChangeParameters closed.parties before.parties closed.contestationPeriod period
                  closed.headId before.headId
              else false
            else false
          else false
        else false
      else false
    headId := before.headId
    atLeast := true
    lhs := unMapData (firstValue info.outputs)
    rhs := unMapData head.value
    snapshot := closeSnapshot before closed redeemer }

@[onchain] def contestSnapshot (before closed : ClosedDatum) (redeemer : ContestRedeemer) : Snapshot :=
  let alphaEmpty := equalsByteString closed.alphaUTxOHash emptyHash
  let omegaEmpty := equalsByteString closed.omegaUTxOHash emptyHash
  let snapshot := fun (version : Int) (snapshotNumber : Int) (utxoHash commitHash decommitHash : ByteString)
      (signatures : Data) =>
    Snapshot.signed before.parties before.headId version snapshotNumber utxoHash commitHash decommitHash
      signatures
  match redeemer with
  | .contestCurrent signatures =>
    if alphaEmpty then
      if omegaEmpty then
        snapshot before.version closed.snapshotNumber closed.utxoHash emptyHash emptyHash signatures
      else .invalid
    else .invalid
  | .contestUsedDec signatures alreadyDecommitted =>
    if alphaEmpty then
      if omegaEmpty then
        snapshot (subtractInteger before.version 1) closed.snapshotNumber closed.utxoHash emptyHash
          alreadyDecommitted signatures
      else .invalid
    else .invalid
  | .contestUnusedDec signatures =>
    if alphaEmpty then
      snapshot before.version closed.snapshotNumber closed.utxoHash emptyHash closed.omegaUTxOHash signatures
    else .invalid
  | .contestUnusedInc signatures alreadyCommitted =>
    if omegaEmpty then
      snapshot (subtractInteger before.version 1) closed.snapshotNumber closed.utxoHash alreadyCommitted
        emptyHash signatures
    else .invalid
  | .contestUsedInc signatures =>
    if omegaEmpty then
      snapshot before.version closed.snapshotNumber closed.utxoHash closed.alphaUTxOHash emptyHash signatures
    else .invalid

@[onchain] def contest (info : HeadTxInfo) (head : HeadTxOut) (before : ClosedDatum)
    (redeemer : ContestRedeemer) : Transition :=
  let closed : ClosedDatum := match headOutputState head.address info.outputs with
    | .closedState datum => datum
    | _ => pError
  let contester : Data := match info.signatories with
    | [signer] => signer
    | _ => pError
  let contesters := unListData before.contesters
  let deadline := before.contestationDeadline
  { rulesHold :=
      if mapIsEmpty info.mint then
        if equalsInteger closed.version before.version then
          if lessThanInteger before.snapshotNumber closed.snapshotNumber then
            if notElem contester contesters then
              if lessThanEqInteger (upperTime info.validRange) deadline then
                if equalsData closed.contesters (listData (mkCons contester contesters)) then
                  let pushed :=
                    if equalsInteger (listLength (unListData closed.contesters))
                        (listLength (unListData before.parties)) then deadline
                    else addInteger deadline before.contestationPeriod
                  if equalsInteger closed.contestationDeadline pushed then
                    mustNotChangeParameters closed.parties before.parties closed.contestationPeriod
                      before.contestationPeriod closed.headId before.headId
                  else false
                else false
              else false
            else false
          else false
        else false
      else false
    headId := before.headId
    atLeast := true
    lhs := unMapData (firstValue info.outputs)
    rhs := unMapData head.value
    snapshot := contestSnapshot before closed redeemer }

@[onchain] def fanout (info : HeadTxInfo) (closed : ClosedDatum)
    (fanoutCount commitCount decommitCount : Int) : Bool :=
  let burnt := subtractInteger 0 (sumQuantities (tokensOf closed.headId (unMapData info.mint)))
  if equalsInteger burnt (addInteger (listLength (unListData closed.parties)) 1) then
    if equalsByteString (hashTake fanoutCount info.outputs) closed.utxoHash then
      let rest := dropOutputs fanoutCount info.outputs
      if equalsByteString closed.alphaUTxOHash (hashTake commitCount rest) then
        if equalsByteString closed.omegaUTxOHash (hashTake decommitCount rest) then
          lessThanInteger closed.contestationDeadline (lowerTime info.validRange)
        else false
      else false
    else false
  else false

/-! ## Entry point -/

@[onchain] def hydraHead (context : HeadContext) : Unit :=
  match context.scriptInfo with
  | .spendingScript ownRef (.justData state) =>
    let info := context.txInfo
    let head := fun (_ : Unit) => ownInput ownRef info.inputs
    let valid := match state with
      | .openState before =>
        match context.redeemer with
        | .increment redeemer => headTransition info (increment info (head ()) before redeemer)
        | .decrement redeemer => headTransition info (decrement info (head ()) before redeemer)
        | .close redeemer => headTransition info (close info (head ()) before redeemer)
        | _ => pError
      | .closedState before =>
        match context.redeemer with
        | .contest redeemer => headTransition info (contest info (head ()) before redeemer)
        | .fanout fanoutCount commitCount decommitCount =>
          fanout info before fanoutCount commitCount decommitCount
        | _ => pError
      | .finalState => pError
    if valid then () else pError
  | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! hydraHead

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def scriptSize := compile! hydraHead

end Test.Comparison.Cross.Hydra

end
