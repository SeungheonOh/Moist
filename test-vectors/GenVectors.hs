{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}

module GenVectors where

import PlutusLedgerApi.V3
import PlutusLedgerApi.V3.MintValue (MintValue(..))
import PlutusLedgerApi.V1.Value (Value(..), CurrencySymbol(..), TokenName(..), singleton, lovelaceValue)
import PlutusTx (toData, Data(..), dataToBuiltinData)
import PlutusTx.AssocMap qualified as AssocMap

import Codec.Serialise (serialise)
import Data.ByteString.Lazy (toStrict)
import "base16-bytestring" Data.ByteString.Base16 qualified as B16
import Data.ByteString.Char8 qualified as BS8

hex :: Data -> String
hex d = BS8.unpack (B16.encode (toStrict (serialise d)))

-- | ENCODE|name|cbor_hex
enc :: String -> Data -> IO ()
enc name d = putStrLn $ "ENCODE|" ++ name ++ "|" ++ hex d

-- | DECODE|name|field_cbor_hex|outer_cbor_hex
dec :: String -> Data -> Data -> IO ()
dec name fieldD outerD = putStrLn $ "DECODE|" ++ name ++ "|" ++ hex fieldD ++ "|" ++ hex outerD

main :: IO ()
main = do
  -- === Shared values ===
  let cred1 = PubKeyCredential "deadbeef"
  let cred2 = ScriptCredential "cafebabe"
  let stakeCred = StakingHash cred1
  let drepCred = DRepCredential (PubKeyCredential "dddddddd")
  let hotCred = HotCommitteeCredential (PubKeyCredential "cccccccc")
  let txOutRef = TxOutRef "aabbccdd" 42
  let val = lovelaceValue 2_000_000 <> singleton (CurrencySymbol "aabb") (TokenName "tok1") 50
  let addr = Address cred1 (Just stakeCred)
  let txOut = TxOut addr val (OutputDatumHash "11223344") Nothing
  let txInInfo = TxInInfo txOutRef txOut
  let lb = LowerBound (Finite 1000) True
  let ub = UpperBound (PosInf :: Extended POSIXTime) False
  let ivl = Interval lb ub
  let govActId = GovernanceActionId "ffff0000" 7
  let emptyMint = UnsafeMintValue (AssocMap.unsafeFromList [])

  -- =========================================================
  -- ENCODING VECTORS
  -- =========================================================

  -- Credential
  enc "Credential.PubKeyCredential" (toData cred1)
  enc "Credential.ScriptCredential" (toData cred2)

  -- StakingCredential
  enc "StakingCredential.StakingHash" (toData stakeCred)
  enc "StakingCredential.StakingPtr" (toData (StakingPtr 1 2 3))

  -- Address
  enc "Address" (toData addr)
  enc "Address.NoStake" (toData (Address cred2 Nothing))

  -- TxOutRef
  enc "TxOutRef" (toData txOutRef)

  -- OutputDatum
  enc "OutputDatum.NoOutputDatum" (toData NoOutputDatum)
  enc "OutputDatum.OutputDatumHash" (toData (OutputDatumHash "11223344"))
  enc "OutputDatum.OutputDatum" (toData (OutputDatum (Datum (dataToBuiltinData (I 999)))))

  -- Value
  enc "Value" (toData val)

  -- TxOut
  enc "TxOut" (toData txOut)

  -- TxInInfo
  enc "TxInInfo" (toData txInInfo)

  -- Extended
  enc "Extended.NegInf" (toData (NegInf :: Extended POSIXTime))
  enc "Extended.Finite" (toData (Finite (1000 :: POSIXTime)))
  enc "Extended.PosInf" (toData (PosInf :: Extended POSIXTime))

  -- Closure (Bool)
  enc "Closure.False" (toData False)
  enc "Closure.True" (toData True)

  -- LowerBound / UpperBound / Interval
  enc "LowerBound" (toData lb)
  enc "UpperBound" (toData ub)
  enc "Interval" (toData ivl)

  -- MaybeData
  enc "MaybeData.Just" (toData (Just (42 :: Integer)))
  enc "MaybeData.Nothing" (toData (Nothing :: Maybe Integer))

  -- DRep
  enc "DRep.DRep" (toData (DRep drepCred))
  enc "DRep.DRepAlwaysAbstain" (toData DRepAlwaysAbstain)
  enc "DRep.DRepAlwaysNoConfidence" (toData DRepAlwaysNoConfidence)

  -- Delegatee
  enc "Delegatee.DelegStake" (toData (DelegStake "eeeeeeee"))
  enc "Delegatee.DelegVote" (toData (DelegVote (DRep drepCred)))
  enc "Delegatee.DelegStakeVote" (toData (DelegStakeVote "eeeeeeee" (DRep drepCred)))

  -- TxCert
  enc "TxCert.TxCertRegStaking" (toData (TxCertRegStaking cred1 (Just 2_000_000)))
  enc "TxCert.TxCertUnRegStaking" (toData (TxCertUnRegStaking cred1 Nothing))
  enc "TxCert.TxCertDelegStaking" (toData (TxCertDelegStaking cred1 (DelegStake "eeeeeeee")))
  enc "TxCert.TxCertRegDeleg" (toData (TxCertRegDeleg cred1 (DelegStake "eeeeeeee") 2_000_000))
  enc "TxCert.TxCertRegDRep" (toData (TxCertRegDRep drepCred 2_000_000))
  enc "TxCert.TxCertUpdateDRep" (toData (TxCertUpdateDRep drepCred))
  enc "TxCert.TxCertUnRegDRep" (toData (TxCertUnRegDRep drepCred 2_000_000))
  enc "TxCert.TxCertPoolRegister" (toData (TxCertPoolRegister "aaaaaaaa" "bbbbbbbb"))
  enc "TxCert.TxCertPoolRetire" (toData (TxCertPoolRetire "aaaaaaaa" 10))
  enc "TxCert.TxCertAuthHotCommittee" (toData (TxCertAuthHotCommittee (ColdCommitteeCredential cred1) hotCred))
  enc "TxCert.TxCertResignColdCommittee" (toData (TxCertResignColdCommittee (ColdCommitteeCredential cred1)))

  -- Voter
  enc "Voter.CommitteeVoter" (toData (CommitteeVoter hotCred))
  enc "Voter.DRepVoter" (toData (DRepVoter drepCred))
  enc "Voter.StakePoolVoter" (toData (StakePoolVoter "eeeeeeee"))

  -- Vote
  enc "Vote.VoteNo" (toData VoteNo)
  enc "Vote.VoteYes" (toData VoteYes)
  enc "Vote.Abstain" (toData Abstain)

  -- GovernanceActionId
  enc "GovernanceActionId" (toData govActId)

  -- ScriptPurpose (all 6)
  enc "ScriptPurpose.Minting" (toData (Minting (CurrencySymbol "aabb")))
  enc "ScriptPurpose.Spending" (toData (Spending txOutRef))
  enc "ScriptPurpose.Rewarding" (toData (Rewarding cred1))
  enc "ScriptPurpose.Certifying" (toData (Certifying 0 (TxCertRegStaking cred1 (Just 2_000_000))))
  enc "ScriptPurpose.Voting" (toData (Voting (DRepVoter drepCred)))
  enc "ScriptPurpose.Proposing" (toData (Proposing 0 (ProposalProcedure 1_000_000 cred1 InfoAction)))

  -- ScriptInfo (all 6)
  enc "ScriptInfo.MintingScript" (toData (MintingScript (CurrencySymbol "aabb")))
  enc "ScriptInfo.SpendingScript" (toData (SpendingScript txOutRef (Just (Datum (dataToBuiltinData (I 42))))))
  enc "ScriptInfo.RewardingScript" (toData (RewardingScript cred1))
  enc "ScriptInfo.CertifyingScript" (toData (CertifyingScript 0 (TxCertRegStaking cred1 (Just 2_000_000))))
  enc "ScriptInfo.VotingScript" (toData (VotingScript (DRepVoter drepCred)))
  enc "ScriptInfo.ProposingScript" (toData (ProposingScript 0 (ProposalProcedure 1_000_000 cred1 InfoAction)))

  -- ProposalProcedure
  enc "ProposalProcedure" (toData (ProposalProcedure 1_000_000 cred1 InfoAction))

  -- GovernanceAction (all 7)
  enc "GovernanceAction.ParameterChange" (toData (ParameterChange (Just govActId) (ChangedParameters (dataToBuiltinData (I 0))) Nothing))
  enc "GovernanceAction.HardForkInitiation" (toData (HardForkInitiation Nothing (ProtocolVersion 10 0)))
  enc "GovernanceAction.TreasuryWithdrawals" (toData (TreasuryWithdrawals (AssocMap.unsafeFromList [(cred1, 5_000_000)]) Nothing))
  enc "GovernanceAction.NoConfidence" (toData (NoConfidence (Just govActId)))
  enc "GovernanceAction.UpdateCommittee" (toData (UpdateCommittee Nothing [] (AssocMap.unsafeFromList []) (unsafeRatio 2 3)))
  enc "GovernanceAction.NewConstitution" (toData (NewConstitution Nothing (Constitution Nothing)))
  enc "GovernanceAction.InfoAction" (toData InfoAction)

  -- ProtocolVersion
  enc "ProtocolVersion" (toData (ProtocolVersion 9 0))

  -- =========================================================
  -- DECODING VECTORS (field extraction)
  -- format: DECODE|Type.field|field_cbor_hex|outer_cbor_hex
  -- =========================================================

  -- Credential fields
  let d1 = toData cred1
  dec "Credential.PubKeyCredential.hash" (toData ("deadbeef" :: PubKeyHash)) d1
  let d2 = toData cred2
  dec "Credential.ScriptCredential.hash" (toData ("cafebabe" :: ScriptHash)) d2

  -- StakingCredential.StakingHash → credential
  let dSH = toData stakeCred
  dec "StakingCredential.StakingHash.cred" (toData cred1) dSH

  -- StakingCredential.StakingPtr → fields
  let dSP = toData (StakingPtr 1 2 3)
  dec "StakingCredential.StakingPtr.a" (I 1) dSP
  dec "StakingCredential.StakingPtr.b" (I 2) dSP
  dec "StakingCredential.StakingPtr.c" (I 3) dSP

  -- Address fields
  let dAddr = toData addr
  dec "Address.credential" (toData cred1) dAddr
  dec "Address.stakingCredential" (toData (Just stakeCred)) dAddr

  let dAddrNoStake = toData (Address cred2 Nothing)
  dec "Address.NoStake.credential" (toData cred2) dAddrNoStake
  dec "Address.NoStake.stakingCredential" (toData (Nothing :: Maybe StakingCredential)) dAddrNoStake

  -- TxOutRef fields
  let dTxOutRef = toData txOutRef
  dec "TxOutRef.txId" (toData ("aabbccdd" :: TxId)) dTxOutRef
  dec "TxOutRef.idx" (I 42) dTxOutRef

  -- OutputDatum fields
  dec "OutputDatum.OutputDatumHash.hash" (toData ("11223344" :: DatumHash)) (toData (OutputDatumHash "11223344"))
  dec "OutputDatum.OutputDatum.datum" (I 999) (toData (OutputDatum (Datum (dataToBuiltinData (I 999)))))

  -- TxOut fields (nested)
  let dTxOut = toData txOut
  dec "TxOut.address" (toData addr) dTxOut
  dec "TxOut.value" (toData val) dTxOut
  dec "TxOut.datum" (toData (OutputDatumHash "11223344")) dTxOut
  dec "TxOut.referenceScript" (toData (Nothing :: Maybe ScriptHash)) dTxOut

  -- TxInInfo fields (nested)
  let dTxInInfo = toData txInInfo
  dec "TxInInfo.txOutRef" (toData txOutRef) dTxInInfo
  dec "TxInInfo.txOut" (toData txOut) dTxInInfo

  -- LowerBound fields
  let dLB = toData lb
  dec "LowerBound.extended" (toData (Finite (1000 :: POSIXTime))) dLB
  dec "LowerBound.closure" (toData True) dLB

  -- UpperBound fields
  let dUB = toData ub
  dec "UpperBound.extended" (toData (PosInf :: Extended POSIXTime)) dUB
  dec "UpperBound.closure" (toData False) dUB

  -- Interval fields
  let dIvl = toData ivl
  dec "Interval.lowerBound" (toData lb) dIvl
  dec "Interval.upperBound" (toData ub) dIvl

  -- DRep fields
  dec "DRep.DRep.cred" (toData (PubKeyCredential "dddddddd")) (toData (DRep drepCred))

  -- Delegatee fields
  dec "Delegatee.DelegStake.pkh" (toData ("eeeeeeee" :: PubKeyHash)) (toData (DelegStake "eeeeeeee"))
  dec "Delegatee.DelegVote.drep" (toData (DRep drepCred)) (toData (DelegVote (DRep drepCred)))
  dec "Delegatee.DelegStakeVote.pkh" (toData ("eeeeeeee" :: PubKeyHash)) (toData (DelegStakeVote "eeeeeeee" (DRep drepCred)))
  dec "Delegatee.DelegStakeVote.drep" (toData (DRep drepCred)) (toData (DelegStakeVote "eeeeeeee" (DRep drepCred)))

  -- TxCert fields (representative)
  dec "TxCert.TxCertRegStaking.cred" (toData cred1) (toData (TxCertRegStaking cred1 (Just 2_000_000)))
  dec "TxCert.TxCertRegStaking.deposit" (toData (Just (2_000_000 :: Lovelace))) (toData (TxCertRegStaking cred1 (Just 2_000_000)))
  dec "TxCert.TxCertPoolRegister.pkh1" (toData ("aaaaaaaa" :: PubKeyHash)) (toData (TxCertPoolRegister "aaaaaaaa" "bbbbbbbb"))
  dec "TxCert.TxCertPoolRegister.pkh2" (toData ("bbbbbbbb" :: PubKeyHash)) (toData (TxCertPoolRegister "aaaaaaaa" "bbbbbbbb"))
  dec "TxCert.TxCertPoolRetire.pkh" (toData ("aaaaaaaa" :: PubKeyHash)) (toData (TxCertPoolRetire "aaaaaaaa" 10))
  dec "TxCert.TxCertPoolRetire.epoch" (I 10) (toData (TxCertPoolRetire "aaaaaaaa" 10))

  -- Voter fields
  dec "Voter.CommitteeVoter.cred" (toData (PubKeyCredential "cccccccc")) (toData (CommitteeVoter hotCred))
  dec "Voter.DRepVoter.cred" (toData (PubKeyCredential "dddddddd")) (toData (DRepVoter drepCred))

  -- GovernanceActionId fields
  dec "GovernanceActionId.txId" (toData ("ffff0000" :: TxId)) (toData govActId)
  dec "GovernanceActionId.idx" (I 7) (toData govActId)

  -- ScriptPurpose fields
  dec "ScriptPurpose.Minting.cs" (toData (CurrencySymbol "aabb")) (toData (Minting (CurrencySymbol "aabb")))
  dec "ScriptPurpose.Spending.txOutRef" (toData txOutRef) (toData (Spending txOutRef))
  dec "ScriptPurpose.Rewarding.cred" (toData cred1) (toData (Rewarding cred1))

  -- ScriptInfo fields
  dec "ScriptInfo.MintingScript.cs" (toData (CurrencySymbol "aabb")) (toData (MintingScript (CurrencySymbol "aabb")))
  let siSpend = SpendingScript txOutRef (Just (Datum (dataToBuiltinData (I 42))))
  dec "ScriptInfo.SpendingScript.txOutRef" (toData txOutRef) (toData siSpend)
  dec "ScriptInfo.SpendingScript.datum" (toData (Just (Datum (dataToBuiltinData (I 42))))) (toData siSpend)
  dec "ScriptInfo.RewardingScript.cred" (toData cred1) (toData (RewardingScript cred1))

  -- ProposalProcedure fields
  let pp = ProposalProcedure 1_000_000 cred1 InfoAction
  dec "ProposalProcedure.deposit" (I 1_000_000) (toData pp)
  dec "ProposalProcedure.credential" (toData cred1) (toData pp)
  dec "ProposalProcedure.action" (toData InfoAction) (toData pp)

  -- ScriptContext fields
  let testTxInfo = TxInfo
        { txInfoInputs = [txInInfo]
        , txInfoReferenceInputs = []
        , txInfoOutputs = [txOut]
        , txInfoFee = 200_000
        , txInfoMint = emptyMint
        , txInfoTxCerts = []
        , txInfoWdrl = AssocMap.unsafeFromList []
        , txInfoValidRange = ivl
        , txInfoSignatories = ["deadbeef"]
        , txInfoRedeemers = AssocMap.unsafeFromList []
        , txInfoData = AssocMap.unsafeFromList []
        , txInfoId = "aabbccdd"
        , txInfoVotes = AssocMap.unsafeFromList []
        , txInfoProposalProcedures = []
        , txInfoCurrentTreasuryAmount = Nothing
        , txInfoTreasuryDonation = Nothing
        }
  let testRedeemer = Redeemer (dataToBuiltinData (I 0))
  let testScriptInfo = SpendingScript txOutRef (Just (Datum (dataToBuiltinData (I 42))))
  let testCtx = ScriptContext testTxInfo testRedeemer testScriptInfo
  let dCtx = toData testCtx

  dec "ScriptContext.txInfo" (toData testTxInfo) dCtx
  dec "ScriptContext.redeemer" (toData testRedeemer) dCtx
  dec "ScriptContext.scriptInfo" (toData testScriptInfo) dCtx

  -- TxInfo fields (from standalone TxInfo)
  let dTI = toData testTxInfo
  dec "TxInfo.inputs" (toData [txInInfo]) dTI
  dec "TxInfo.referenceInputs" (toData ([] :: [TxInInfo])) dTI
  dec "TxInfo.outputs" (toData [txOut]) dTI
  dec "TxInfo.fee" (I 200_000) dTI
  dec "TxInfo.mint" (toData emptyMint) dTI
  dec "TxInfo.txCerts" (toData ([] :: [TxCert])) dTI
  dec "TxInfo.wdrl" (toData (AssocMap.unsafeFromList [] :: AssocMap.Map Credential Lovelace)) dTI
  dec "TxInfo.validRange" (toData ivl) dTI
  dec "TxInfo.signatories" (toData [("deadbeef" :: PubKeyHash)]) dTI
  dec "TxInfo.redeemers" (toData (AssocMap.unsafeFromList [] :: AssocMap.Map ScriptPurpose Redeemer)) dTI
  dec "TxInfo.datumWitnesses" (toData (AssocMap.unsafeFromList [] :: AssocMap.Map DatumHash Datum)) dTI
  dec "TxInfo.id" (toData ("aabbccdd" :: TxId)) dTI
  dec "TxInfo.votes" (toData (AssocMap.unsafeFromList [] :: AssocMap.Map Voter (AssocMap.Map GovernanceActionId Vote))) dTI
  dec "TxInfo.proposalProcedures" (toData ([] :: [ProposalProcedure])) dTI
  dec "TxInfo.currentTreasuryAmount" (toData (Nothing :: Maybe Lovelace)) dTI
  dec "TxInfo.treasuryDonation" (toData (Nothing :: Maybe Lovelace)) dTI

  -- Nested: ScriptContext → TxInfo → fee
  dec "ScriptContext.txInfo.fee" (I 200_000) dCtx
  -- Nested: ScriptContext → ScriptInfo → TxOutRef
  dec "ScriptContext.scriptInfo.txOutRef" (toData txOutRef) dCtx
  -- Nested: TxInInfo → TxOut → Address → Credential
  dec "TxInInfo.txOut.address.credential" (toData cred1) dTxInInfo
