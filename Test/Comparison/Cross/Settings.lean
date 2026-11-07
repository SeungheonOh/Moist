import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Cardano.V3

namespace Test.Comparison.Cross.Settings

open Moist.Plutus (Data ByteString AssocMap)
open Moist.Onchain (PlutusData dataBeq)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! Port of `Settings.Contracts.SettingsPlinth`: the settings UTxO spending validator
(settings-admin and treasury-admin updates) and the one-shot settings NFT minting policy. -/

@[plutus_data]
inductive MultisigScript where
  | signature : PubKeyHash → MultisigScript
  | allOf : List MultisigScript → MultisigScript
  | anyOf : List MultisigScript → MultisigScript
  | atLeast : Int → List MultisigScript → MultisigScript
  | before : Int → MultisigScript
  | after : Int → MultisigScript
  | scriptWit : PubKeyHash → MultisigScript

/-- Every field is compared or decoded on demand, so all of them stay as raw `Data`. -/
@[plutus_data]
structure SettingsDatum where
  settingsAdmin : Data
  metadataAdmin : Data
  treasuryAdmin : Data
  treasuryAddress : Data
  treasuryAllowance : Data
  authorizedScoopers : Data
  authorizedStakingKeys : Data
  baseFee : Data
  simpleFee : Data
  strategyFee : Data
  poolCreationFee : Data
  extensions : Data

@[plutus_data]
inductive SettingsRedeemer where
  | settingsAdminUpdate : SettingsRedeemer
  | treasuryAdminUpdate : SettingsRedeemer

/-- The transaction facts a multisig script is checked against. -/
@[plutus_sop]
structure Witnesses where
  signatories : List PubKeyHash
  range : POSIXTimeRange
  withdrawals : AssocMap Credential Lovelace

@[onchain] def signedBy (signer : PubKeyHash) : List PubKeyHash → Bool
  | [] => false
  | candidate :: rest => if equalsByteString candidate signer then true else signedBy signer rest

@[onchain] def withdraws (credential : Credential) (withdrawals : AssocMap Credential Lovelace) : Bool :=
  Moist.Onchain.AssocMap.foldrLazy
    (fun key _ _ next => if dataBeq key credential then true else next ()) false withdrawals

@[onchain] def endsBy (range : POSIXTimeRange) (time : Int) : Bool :=
  match range.upperBound with
  | ⟨.finite high, .inclusive⟩ => lessThanEqInteger high time
  | ⟨.finite high, .exclusive⟩ => lessThanInteger high time
  | _ => false

@[onchain] def startsAfter (range : POSIXTimeRange) (time : Int) : Bool :=
  match range.lowerBound with
  | ⟨.finite low, .inclusive⟩ => lessThanEqInteger time low
  | ⟨.finite low, .exclusive⟩ => lessThanInteger time low
  | _ => false

/-- Folds one member's verdict into a combination of `scripts` (see `combine`). -/
@[onchain] def step (mode : Int) (satisfied : Bool) (others : Unit → Int) : Int :=
  if equalsInteger mode 0 then
    if satisfied then others () else 0
  else if equalsInteger mode 1 then
    if satisfied then 1 else others ()
  else
    let count := others ()
    if satisfied then addInteger count 1 else count

/-- How `scripts` combines its members: `0` all (short-circuits), `1` any (short-circuits),
`2` the number satisfied (checks every member). All and any answer `1` or `0`. -/
@[onchain] def combine (witnesses : Witnesses) (mode : Int) : List MultisigScript → Int
  | [] => if equalsInteger mode 0 then 1 else 0
  | script :: scripts =>
    step mode
      (match script with
        | .signature key => signedBy key witnesses.signatories
        | .allOf members => equalsInteger (combine witnesses 0 members) 1
        | .anyOf members => equalsInteger (combine witnesses 1 members) 1
        | .atLeast required members => lessThanEqInteger required (combine witnesses 2 members)
        | .before time => endsBy witnesses.range time
        | .after time => startsAfter witnesses.range time
        | .scriptWit hash => withdraws (.scriptCredential hash) witnesses.withdrawals)
      (fun _ => combine witnesses mode scripts)
termination_by scripts => sizeOf scripts

@[onchain] def multisigSatisfied (witnesses : Witnesses) (script : MultisigScript) : Bool :=
  equalsInteger (combine witnesses 0 [script]) 1

/-! ## Value equality

`PlutusLedgerApi.V1.Data.Value.eq`: order-insensitive, and entries whose quantities are all
zero count as absent (plutus-ledger-api's `unordEqWith`). -/

@[onchain] def allZero (isZero : Data → Bool) : List (Data × Data) → Bool
  | [] => true
  | entry :: rest => if isZero entry.2 then allZero isZero rest else false

@[onchain] def revAppend : List (Data × Data) → List (Data × Data) → List (Data × Data)
  | [], accumulator => accumulator
  | entry :: rest, accumulator => revAppend rest (entry :: accumulator)

/-- Finds the first non-zero entry for `key` and checks its value against `value`; on a match,
answers the other entries (zero entries passed over are dropped). -/
@[onchain] def removeMatching (isZero : Data → Bool) (equal : Data → Data → Bool) (key value : Data)
    (scanned : List (Data × Data)) : List (Data × Data) → Option (List (Data × Data))
  | [] => none
  | entry :: rest =>
    if isZero entry.2 then removeMatching isZero equal key value scanned rest
    else if equalsData entry.1 key then
      if equal value entry.2 then some (revAppend scanned rest) else none
    else removeMatching isZero equal key value (entry :: scanned) rest

@[onchain] def unorderedEqual (isZero : Data → Bool) (equal : Data → Data → Bool)
    (left right : List (Data × Data)) : Bool :=
  match left with
  | [] => allZero isZero right
  | first :: lefts =>
    match right with
    | [] => allZero isZero left
    | second :: rights =>
      if equalsData first.1 second.1 then
        if equal first.2 second.2 then unorderedEqual isZero equal lefts rights else false
      else if isZero first.2 then unorderedEqual isZero equal lefts right
      else
        let scanned := if isZero second.2 then [] else [second]
        match removeMatching isZero equal first.1 first.2 scanned rights with
        | none => false
        | some remaining => unorderedEqual isZero equal lefts remaining

@[onchain] def quantityIsZero (quantity : Data) : Bool := equalsInteger (unIData quantity) 0

@[onchain] def quantitiesEqual (left right : Data) : Bool :=
  equalsInteger (unIData left) (unIData right)

@[onchain] def tokensAreZero (tokens : Data) : Bool := allZero quantityIsZero (unMapData tokens)

@[onchain] def tokensEqual (left right : Data) : Bool :=
  unorderedEqual quantityIsZero quantitiesEqual (unMapData left) (unMapData right)

@[onchain] def valueEqual (left right : List (Data × Data)) : Bool :=
  unorderedEqual tokensAreZero tokensEqual left right

/-- `DMap.delete (CurrencySymbol "")`: drops the first Ada entry. -/
@[onchain] def withoutAda : List (Data × Data) → List (Data × Data)
  | [] => []
  | entry :: rest =>
    if equalsData entry.1 (bData ByteArray.empty) then rest else entry :: withoutAda rest

/-! ## Spending -/

@[onchain] noncomputable def ownOutput (reference : TxOutRef) : List TxInInfo → TxOut
  | [] => pError
  | input :: rest => if dataBeq input.outRef reference then input.resolved else ownOutput reference rest

@[onchain] noncomputable def inlineDatum (output : TxOut) : SettingsDatum :=
  match output.datum with
  | .outputDatum datum => PlutusData.unsafeFromData datum
  | _ => pError

@[onchain] def entries (value : Value) : List (Data × Data) := unMapData (PlutusData.toData value)

/-- A settings-admin update keeps the treasury address, allowance and staking keys. -/
@[onchain] def settingsAdminKeeps (input output : SettingsDatum) : Bool :=
  if equalsData input.authorizedStakingKeys output.authorizedStakingKeys then
    if equalsData input.treasuryAddress output.treasuryAddress then
      equalsData input.treasuryAllowance output.treasuryAllowance
    else false
  else false

/-- A treasury-admin update keeps everything but the treasury address, allowance and
staking keys. -/
@[onchain] def treasuryAdminKeeps (input output : SettingsDatum) : Bool :=
  match input, output with
  | ⟨settingsAdmin, metadataAdmin, treasuryAdmin, _, _, scoopers, _, baseFee, simpleFee,
      strategyFee, poolCreationFee, extensions⟩,
    ⟨settingsAdmin', metadataAdmin', treasuryAdmin', _, _, scoopers', _, baseFee', simpleFee',
      strategyFee', poolCreationFee', extensions'⟩ =>
    if equalsData settingsAdmin settingsAdmin' then
    if equalsData metadataAdmin metadataAdmin' then
    if equalsData treasuryAdmin treasuryAdmin' then
    if equalsData scoopers scoopers' then
    if equalsData baseFee baseFee' then
    if equalsData simpleFee simpleFee' then
    if equalsData strategyFee strategyFee' then
    if equalsData poolCreationFee poolCreationFee' then
      equalsData extensions extensions'
    else false else false else false else false else false else false else false else false

@[onchain] noncomputable def settingsValidator (input : SettingsDatum) (redeemer : SettingsRedeemer)
    (ownRef : TxOutRef) (info : TxInfo) : Bool :=
  match info with
  | ⟨inputs, _, outputs, _, mint, _, withdrawals, range, signatories, _, _, _, _, _, _, _⟩ =>
    let spent := ownOutput ownRef inputs
    match outputs with
    | [] => pError
    | output :: _ =>
      let outputDatum := inlineDatum output
      if dataBeq output.address spent.address then
        if valueEqual (withoutAda (entries output.value)) (withoutAda (entries spent.value)) then
          match entries mint with
          | [] =>
            let admin := match redeemer with
              | .settingsAdminUpdate => input.settingsAdmin
              | .treasuryAdminUpdate => input.treasuryAdmin
            let witnesses : Witnesses := ⟨signatories, range, withdrawals⟩
            if multisigSatisfied witnesses (PlutusData.unsafeFromData admin) then
              match redeemer with
              | .settingsAdminUpdate => settingsAdminKeeps input outputDatum
              | .treasuryAdminUpdate => treasuryAdminKeeps input outputDatum
            else false
          | _ => false
        else false
      else false

/-! ## Minting -/

@[onchain] def settingsToken : ByteString := "settings".toUTF8

@[onchain] def mintsExactlyOneToken (policy : ByteString) (mint : MintValue) : Bool :=
  match entries mint with
  | [currency] =>
    if equalsByteString (unBData currency.1) policy then
      match unMapData currency.2 with
      | [token] =>
        if equalsByteString (unBData token.1) settingsToken then equalsInteger (unIData token.2) 1
        else false
      | _ => false
    else false
  | _ => false

@[onchain] def spendsReference (reference : TxOutRef) : List TxInInfo → Bool
  | [] => false
  | input :: rest => if dataBeq input.outRef reference then true else spendsReference reference rest

@[onchain] def paysToPolicyScript (policy : ByteString) : List TxOut → Bool
  | [] => false
  | output :: rest =>
    let paid := match output.address.credential with
      | .scriptCredential hash =>
        if equalsByteString hash policy then
          match output.datum with
          | .outputDatum _ => true
          | _ => false
        else false
      | _ => false
    if paid then true else paysToPolicyScript policy rest

@[onchain] def settingsMintValidator (bootReference : TxOutRef) (policy : ByteString)
    (info : TxInfo) : Bool :=
  match info with
  | ⟨inputs, _, outputs, _, mint, _, _, _, _, _, _, _, _, _, _, _⟩ =>
    if mintsExactlyOneToken policy mint then
      if spendsReference bootReference inputs then paysToPolicyScript policy outputs else false
    else false

@[onchain] noncomputable def settings (bootReference : TxOutRef) (context : ScriptContext) : Unit :=
  match context with
  | ⟨info, redeemer, scriptInfo⟩ =>
    match scriptInfo with
    | .spendingScript ownRef (.justData datum) =>
      if settingsValidator (PlutusData.unsafeFromData datum) (PlutusData.unsafeFromData redeemer)
          ownRef info
      then () else pError
    | .mintingScript policy =>
      if settingsMintValidator bootReference policy info then () else pError
    | _ => pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! settings

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def scriptSize := compile! settings

end Test.Comparison.Cross.Settings
