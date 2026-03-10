import Moist.Onchain.Attribute
import Moist.Onchain.Prelude
import Moist.Plutus.Types

namespace Moist.Onchain.ScriptContext

open Moist.Plutus (Data ByteString)

/-! # Plutus V3 ScriptContext Types

On-chain types for validator scripts. All are marked @[plutus_data]
so they use Data encoding (ConstrData/UnConstrData) when compiled.

These mirror the Plutus V3 ledger API types.
-/

/-! ## Credentials and Addresses -/

@[plutus_data]
inductive Credential where
  | pubKeyCredential : ByteString → Credential
  | scriptCredential : ByteString → Credential

@[plutus_data]
inductive StakingCredential where
  | stakingHash : Credential → StakingCredential
  | stakingPtr : Int → Int → Int → StakingCredential

@[plutus_data]
inductive MaybeData (α : Type) where
  | nothingData : MaybeData α
  | justData : α → MaybeData α

@[plutus_data]
inductive Address where
  | address : Credential → MaybeData StakingCredential → Address

/-! ## Value and CurrencySymbol -/

/-- CurrencySymbol is a ByteString (policy hash). -/
abbrev CurrencySymbol := ByteString

/-- TokenName is a ByteString. -/
abbrev TokenName := ByteString

/-- Value is represented as a map of maps on-chain:
    Map CurrencySymbol (Map TokenName Integer) -/
abbrev Value := Data

/-! ## Transaction Components -/

@[plutus_data]
inductive TxId where
  | txId : ByteString → TxId

@[plutus_data]
inductive TxOutRef where
  | txOutRef : TxId → Int → TxOutRef

@[plutus_data]
inductive OutputDatum where
  | noOutputDatum : OutputDatum
  | outputDatumHash : ByteString → OutputDatum
  | outputDatum : Data → OutputDatum

@[plutus_data]
inductive TxOut where
  | txOut : Address → Value → OutputDatum → MaybeData ByteString → TxOut

@[plutus_data]
inductive TxInInfo where
  | txInInfo : TxOutRef → TxOut → TxInInfo

/-! ## Script Purpose -/

@[plutus_data]
inductive ScriptPurpose where
  | minting : ByteString → ScriptPurpose
  | spending : TxOutRef → ScriptPurpose
  | rewarding : Credential → ScriptPurpose
  | certifying : Data → ScriptPurpose
  | voting : Data → ScriptPurpose
  | proposing : Data → ScriptPurpose

/-! ## TxInfo and ScriptContext -/

/-- Simplified TxInfo — fields are accessed via Data operations.
    The full TxInfo has many fields; we represent it as opaque Data
    and provide accessor functions. -/
abbrev TxInfo := Data

@[plutus_data]
inductive ScriptContext where
  | scriptContext : TxInfo → Data → ScriptPurpose → ScriptContext

end Moist.Onchain.ScriptContext
