import Moist.Onchain.Attribute
import Moist.Plutus.Types

namespace Moist.Cardano.V3

open Moist.Plutus (Data ByteString)

/-! # Plutus V3 Ledger API Types

Complete on-chain types for Plutus V3 (Conway era) validator scripts.

Encoding rules:
- Sum types and multi-field product types use @[plutus_data] (Constr encoding).
- Single-field newtypes are transparent (abbrev) — no Constr wrapper.
  e.g. PubKeyHash is raw `B bytes`, Lovelace is raw `I n`.
-/

/-! ## Utility Types -/

@[plutus_data]
inductive MaybeData (α : Type) where
  | justData : α → MaybeData α
  | nothingData : MaybeData α

@[plutus_data]
inductive RationalData where
  | rationalData : Int → Int → RationalData

/-! ## Crypto -/

abbrev PubKeyHash := ByteString
abbrev ScriptHash := ByteString
abbrev DatumHash := ByteString

/-! ## Scripts -/

abbrev Datum := Data
abbrev Redeemer := Data

/-! ## Value -/

abbrev CurrencySymbol := ByteString
abbrev TokenName := ByteString
abbrev Lovelace := Int

/-- Value: Map CurrencySymbol (Map TokenName Integer) -/
abbrev Value := Data

/-- MintValue: same on-chain representation as Value -/
abbrev MintValue := Data

/-! ## Credentials and Addresses -/

@[plutus_data]
inductive Credential where
  | pubKeyCredential : PubKeyHash → Credential
  | scriptCredential : ScriptHash → Credential

@[plutus_data]
inductive StakingCredential where
  | stakingHash : Credential → StakingCredential
  | stakingPtr : Int → Int → Int → StakingCredential

@[plutus_data]
inductive Address where
  | address : Credential → MaybeData StakingCredential → Address

/-! ## Time and Intervals -/

abbrev POSIXTime := Int

@[plutus_data]
inductive Extended where
  | negInf : Extended
  | finite : POSIXTime → Extended
  | posInf : Extended

@[plutus_data]
inductive LowerBound where
  | lowerBound : Extended → Bool → LowerBound

@[plutus_data]
inductive UpperBound where
  | upperBound : Extended → Bool → UpperBound

@[plutus_data]
inductive Interval where
  | interval : LowerBound → UpperBound → Interval

abbrev POSIXTimeRange := Interval

/-! ## Transaction Types -/

abbrev TxId := ByteString

@[plutus_data]
inductive TxOutRef where
  | txOutRef : TxId → Int → TxOutRef

@[plutus_data]
inductive OutputDatum where
  | noOutputDatum : OutputDatum
  | outputDatumHash : DatumHash → OutputDatum
  | outputDatum : Datum → OutputDatum

@[plutus_data]
inductive TxOut where
  | txOut : Address → Value → OutputDatum → MaybeData ScriptHash → TxOut

@[plutus_data]
inductive TxInInfo where
  | txInInfo : TxOutRef → TxOut → TxInInfo

/-! ## CIP-1694 Governance Types -/

abbrev ColdCommitteeCredential := Credential
abbrev HotCommitteeCredential := Credential
abbrev DRepCredential := Credential

@[plutus_data]
inductive DRep where
  | dRep : DRepCredential → DRep
  | dRepAlwaysAbstain : DRep
  | dRepAlwaysNoConfidence : DRep

@[plutus_data]
inductive Delegatee where
  | delegStake : PubKeyHash → Delegatee
  | delegVote : DRep → Delegatee
  | delegStakeVote : PubKeyHash → DRep → Delegatee

@[plutus_data]
inductive TxCert where
  | txCertRegStaking : Credential → MaybeData Lovelace → TxCert
  | txCertUnRegStaking : Credential → MaybeData Lovelace → TxCert
  | txCertDelegStaking : Credential → Delegatee → TxCert
  | txCertRegDeleg : Credential → Delegatee → Lovelace → TxCert
  | txCertRegDRep : DRepCredential → Lovelace → TxCert
  | txCertUpdateDRep : DRepCredential → TxCert
  | txCertUnRegDRep : DRepCredential → Lovelace → TxCert
  | txCertPoolRegister : PubKeyHash → PubKeyHash → TxCert
  | txCertPoolRetire : PubKeyHash → Int → TxCert
  | txCertAuthHotCommittee : ColdCommitteeCredential → HotCommitteeCredential → TxCert
  | txCertResignColdCommittee : ColdCommitteeCredential → TxCert

@[plutus_data]
inductive Voter where
  | committeeVoter : HotCommitteeCredential → Voter
  | dRepVoter : DRepCredential → Voter
  | stakePoolVoter : PubKeyHash → Voter

@[plutus_data]
inductive Vote where
  | voteYes : Vote
  | voteNo : Vote
  | abstain : Vote

@[plutus_data]
inductive GovernanceActionId where
  | governanceActionId : TxId → Int → GovernanceActionId

abbrev ChangedParameters := Data

@[plutus_data]
inductive ProtocolVersion where
  | protocolVersion : Int → Int → ProtocolVersion

abbrev Constitution := MaybeData ScriptHash

@[plutus_data]
inductive Committee where
  | committee : Data → RationalData → Committee
  -- first field: Map ColdCommitteeCredential Integer

@[plutus_data]
inductive GovernanceAction where
  | parameterChange : MaybeData GovernanceActionId → ChangedParameters → MaybeData ScriptHash → GovernanceAction
  | hardForkInitiation : MaybeData GovernanceActionId → ProtocolVersion → GovernanceAction
  | treasuryWithdrawals : Data → MaybeData ScriptHash → GovernanceAction
  -- first field: Map Credential Lovelace
  | noConfidence : MaybeData GovernanceActionId → GovernanceAction
  | updateCommittee :
      MaybeData GovernanceActionId →
      List ColdCommitteeCredential →
      Data →             -- Map ColdCommitteeCredential Integer
      RationalData →
      GovernanceAction
  | newConstitution : MaybeData GovernanceActionId → Constitution → GovernanceAction
  | infoAction : GovernanceAction

@[plutus_data]
inductive ProposalProcedure where
  | proposalProcedure : Lovelace → Credential → GovernanceAction → ProposalProcedure

/-! ## Script Purpose and Script Info -/

@[plutus_data]
inductive ScriptPurpose where
  | minting : CurrencySymbol → ScriptPurpose
  | spending : TxOutRef → ScriptPurpose
  | rewarding : Credential → ScriptPurpose
  | certifying : Int → TxCert → ScriptPurpose
  | voting : Voter → ScriptPurpose
  | proposing : Int → ProposalProcedure → ScriptPurpose

@[plutus_data]
inductive ScriptInfo where
  | mintingScript : CurrencySymbol → ScriptInfo
  | spendingScript : TxOutRef → MaybeData Datum → ScriptInfo
  | rewardingScript : Credential → ScriptInfo
  | certifyingScript : Int → TxCert → ScriptInfo
  | votingScript : Voter → ScriptInfo
  | proposingScript : Int → ProposalProcedure → ScriptInfo

/-! ## Transaction Info -/

@[plutus_data]
structure TxInfo where
  inputs : List TxInInfo
  referenceInputs : List TxInInfo
  outputs : List TxOut
  fee : Lovelace
  mint : MintValue
  txCerts : List TxCert
  wdrl : Data                       -- Map Credential Lovelace
  validRange : POSIXTimeRange
  signatories : List PubKeyHash
  redeemers : Data                   -- Map ScriptPurpose Redeemer
  datumWitnesses : Data              -- Map DatumHash Datum
  id : TxId
  votes : Data                       -- Map Voter (Map GovernanceActionId Vote)
  proposalProcedures : List ProposalProcedure
  currentTreasuryAmount : MaybeData Lovelace
  treasuryDonation : MaybeData Lovelace

/-! ## Script Context -/

@[plutus_data]
inductive ScriptContext where
  | scriptContext : TxInfo → Redeemer → ScriptInfo → ScriptContext

end Moist.Cardano.V3
