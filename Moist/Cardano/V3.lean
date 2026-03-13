import Moist.Onchain.Repr
import Moist.Plutus.Types

namespace Moist.Cardano.V3

open Moist.Plutus (Data ByteString AssocMap)

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
structure RationalData where
  numerator : Int
  denominator : Int

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
abbrev Value := AssocMap CurrencySymbol (AssocMap TokenName Int)

/-- MintValue: same on-chain representation as Value -/
abbrev MintValue := AssocMap CurrencySymbol (AssocMap TokenName Int)

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
structure Address where
  credential : Credential
  stakingCredential : MaybeData StakingCredential

/-! ## Time and Intervals -/

abbrev POSIXTime := Int

@[plutus_data]
inductive Extended where
  | negInf : Extended
  | finite : POSIXTime → Extended
  | posInf : Extended

@[plutus_data]
inductive Closure where
  | exclusive : Closure   -- ConstrData 0 [] (= Plutus False)
  | inclusive : Closure    -- ConstrData 1 [] (= Plutus True)

@[plutus_data]
structure LowerBound where
  bound : Extended
  closure : Closure

@[plutus_data]
structure UpperBound where
  bound : Extended
  closure : Closure

@[plutus_data]
structure Interval where
  lowerBound : LowerBound
  upperBound : UpperBound

abbrev POSIXTimeRange := Interval

/-! ## Transaction Types -/

abbrev TxId := ByteString

@[plutus_data]
structure TxOutRef where
  id : TxId
  idx : Int

@[plutus_data]
inductive OutputDatum where
  | noOutputDatum : OutputDatum
  | outputDatumHash : DatumHash → OutputDatum
  | outputDatum : Datum → OutputDatum

@[plutus_data]
structure TxOut where
  address : Address
  value : Value
  datum : OutputDatum
  referenceScript : MaybeData ScriptHash

@[plutus_data]
structure TxInInfo where
  outRef : TxOutRef
  resolved : TxOut

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
  | voteNo : Vote      -- ConstrData 0 []
  | voteYes : Vote     -- ConstrData 1 []
  | abstain : Vote     -- ConstrData 2 []

@[plutus_data]
structure GovernanceActionId where
  txId : TxId
  govActionIx : Int

abbrev ChangedParameters := Data

@[plutus_data]
structure ProtocolVersion where
  major : Int
  minor : Int

abbrev Constitution := MaybeData ScriptHash

@[plutus_data]
structure Committee where
  members : AssocMap ColdCommitteeCredential Int
  quorum : RationalData

@[plutus_data]
inductive GovernanceAction where
  | parameterChange : MaybeData GovernanceActionId → ChangedParameters → MaybeData ScriptHash → GovernanceAction
  | hardForkInitiation : MaybeData GovernanceActionId → ProtocolVersion → GovernanceAction
  | treasuryWithdrawals : AssocMap Credential Lovelace → MaybeData ScriptHash → GovernanceAction
  | noConfidence : MaybeData GovernanceActionId → GovernanceAction
  | updateCommittee :
      MaybeData GovernanceActionId →
      List ColdCommitteeCredential →
      AssocMap ColdCommitteeCredential Int →
      RationalData →
      GovernanceAction
  | newConstitution : MaybeData GovernanceActionId → Constitution → GovernanceAction
  | infoAction : GovernanceAction

@[plutus_data]
structure ProposalProcedure where
  deposit : Lovelace
  returnAddr : Credential
  governanceAction : GovernanceAction

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
  wdrl : AssocMap Credential Lovelace
  validRange : POSIXTimeRange
  signatories : List PubKeyHash
  redeemers : AssocMap ScriptPurpose Redeemer
  datumWitnesses : AssocMap DatumHash Datum
  id : TxId
  votes : AssocMap Voter (AssocMap GovernanceActionId Vote)
  proposalProcedures : List ProposalProcedure
  currentTreasuryAmount : MaybeData Lovelace
  treasuryDonation : MaybeData Lovelace

/-! ## Script Context -/

@[plutus_data]
structure ScriptContext where
  txInfo : TxInfo
  redeemer : Redeemer
  scriptInfo : ScriptInfo

end Moist.Cardano.V3
