import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Plutus.Eval
import Moist.Plutus.CBOR
import Moist.Cardano.V3

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)
open Moist.Onchain.Prelude
open Moist.Plutus.Eval
open Moist.Cardano.V3

namespace Test.LedgerEncoding

/-! ## Helpers -/

def dataTerm (d : Moist.Plutus.Data) : Term :=
  Term.Constant (Const.Data d, BuiltinType.AtomicType AtomicType.TypeData)

def bsTerm (bs : ByteString) : Term :=
  Term.Constant (Const.ByteString bs, BuiltinType.AtomicType AtomicType.TypeByteString)

def intTerm (n : Int) : Term :=
  Term.Constant (Const.Integer n, BuiltinType.AtomicType AtomicType.TypeInteger)

def fromHex! (hex : String) : Moist.Plutus.Data :=
  match Moist.Plutus.CBOR.dataFromCBORHex hex with
  | some d => d
  | none => .I 999999

def checkResult (name : String) (result : Except (CEKError × ExBudget × String) EvalResult)
    (expected : Moist.Plutus.Data) : IO Unit := do
  match result with
  | .ok r =>
    match r.term with
    | .Constant (Const.Data d, _) =>
      if d == expected then IO.println s!"  ✓ {name}"
      else do
        IO.println s!"  ✗ {name}"
        IO.println s!"    expected: {expected}"
        IO.println s!"    got:      {d}"
    | .Constant (Const.Integer i, _) =>
      match expected with
      | .I n =>
        if i == n then IO.println s!"  ✓ {name}"
        else IO.println s!"  ✗ {name}: expected I {n}, got I {i}"
      | _ => IO.println s!"  ✗ {name}: got Integer but expected {expected}"
    | .Constant (Const.ByteString bs, _) =>
      match expected with
      | .B b =>
        if bs == b then IO.println s!"  ✓ {name}"
        else IO.println s!"  ✗ {name}: ByteString mismatch"
      | _ => IO.println s!"  ✗ {name}: got ByteString but expected {expected}"
    | other => IO.println s!"  ✗ {name}: unexpected result: {repr other}"
  | .error (err, _, msg) =>
    IO.println s!"  ✗ {name}: eval error {err} - {msg}"

def evalCheck (name : String) (t : Term) (expectedHex : String) : IO Unit := do
  let r ← evalTerm t
  checkResult name r (fromHex! expectedHex)

def evalCheckData (name : String) (t : Term) (expected : Moist.Plutus.Data) : IO Unit := do
  let r ← evalTerm t
  checkResult name r expected

/-! ## Encoding constructors -/

@[onchain] noncomputable def mkPubKeyCred (h : ByteString) : Credential := .pubKeyCredential h
@[onchain] noncomputable def mkScriptCred (h : ByteString) : Credential := .scriptCredential h
@[onchain] noncomputable def mkStakingHash (c : Credential) : StakingCredential := .stakingHash c
@[onchain] noncomputable def mkStakingPtr (a b c : Int) : StakingCredential := .stakingPtr a b c
@[onchain] noncomputable def mkAddress (c : Credential) (s : MaybeData StakingCredential) : Address := .mk c s
@[onchain] noncomputable def mkTxOutRef (txId : ByteString) (idx : Int) : TxOutRef := .mk txId idx
@[onchain] noncomputable def mkNoOutputDatum : OutputDatum := .noOutputDatum
@[onchain] noncomputable def mkOutputDatumHash (h : ByteString) : OutputDatum := .outputDatumHash h
@[onchain] noncomputable def mkOutputDatumI (n : Int) : OutputDatum := .outputDatum (iData n)
@[onchain] noncomputable def mkNegInf : Extended := .negInf
@[onchain] noncomputable def mkFinite (t : Int) : Extended := .finite t
@[onchain] noncomputable def mkPosInf : Extended := .posInf
@[onchain] noncomputable def mkExclusive : Closure := .exclusive
@[onchain] noncomputable def mkInclusive : Closure := .inclusive
@[onchain] noncomputable def mkLowerBound (ext : Extended) (cl : Closure) : LowerBound := .mk ext cl
@[onchain] noncomputable def mkUpperBound (ext : Extended) (cl : Closure) : UpperBound := .mk ext cl
@[onchain] noncomputable def mkInterval (lb : LowerBound) (ub : UpperBound) : Interval := .mk lb ub
@[onchain] noncomputable def mkJustInt (n : Int) : MaybeData Int := .justData n
@[onchain] noncomputable def mkNothingInt : MaybeData Int := .nothingData
@[onchain] noncomputable def mkDRep (c : Credential) : DRep := .dRep c
@[onchain] noncomputable def mkDRepAlwaysAbstain : DRep := .dRepAlwaysAbstain
@[onchain] noncomputable def mkDRepAlwaysNoConfidence : DRep := .dRepAlwaysNoConfidence
@[onchain] noncomputable def mkDelegStake (pkh : ByteString) : Delegatee := .delegStake pkh
@[onchain] noncomputable def mkDelegVote (d : DRep) : Delegatee := .delegVote d
@[onchain] noncomputable def mkDelegStakeVote (pkh : ByteString) (d : DRep) : Delegatee := .delegStakeVote pkh d
@[onchain] noncomputable def mkTxCertRegStaking (c : Credential) (d : MaybeData Int) : TxCert := .txCertRegStaking c d
@[onchain] noncomputable def mkTxCertUnRegStaking (c : Credential) (d : MaybeData Int) : TxCert := .txCertUnRegStaking c d
@[onchain] noncomputable def mkTxCertDelegStaking (c : Credential) (d : Delegatee) : TxCert := .txCertDelegStaking c d
@[onchain] noncomputable def mkTxCertRegDeleg (c : Credential) (d : Delegatee) (l : Int) : TxCert := .txCertRegDeleg c d l
@[onchain] noncomputable def mkTxCertRegDRep (c : Credential) (l : Int) : TxCert := .txCertRegDRep c l
@[onchain] noncomputable def mkTxCertUpdateDRep (c : Credential) : TxCert := .txCertUpdateDRep c
@[onchain] noncomputable def mkTxCertUnRegDRep (c : Credential) (l : Int) : TxCert := .txCertUnRegDRep c l
@[onchain] noncomputable def mkTxCertPoolRegister (a b : ByteString) : TxCert := .txCertPoolRegister a b
@[onchain] noncomputable def mkTxCertPoolRetire (a : ByteString) (n : Int) : TxCert := .txCertPoolRetire a n
@[onchain] noncomputable def mkTxCertAuthHotCommittee (cold hot : Credential) : TxCert := .txCertAuthHotCommittee cold hot
@[onchain] noncomputable def mkTxCertResignColdCommittee (cold : Credential) : TxCert := .txCertResignColdCommittee cold
@[onchain] noncomputable def mkCommitteeVoter (c : Credential) : Voter := .committeeVoter c
@[onchain] noncomputable def mkDRepVoter (c : Credential) : Voter := .dRepVoter c
@[onchain] noncomputable def mkStakePoolVoter (pkh : ByteString) : Voter := .stakePoolVoter pkh
@[onchain] noncomputable def mkVoteNo : Vote := .voteNo
@[onchain] noncomputable def mkVoteYes : Vote := .voteYes
@[onchain] noncomputable def mkAbstain : Vote := .abstain
@[onchain] noncomputable def mkGovActId (txId : ByteString) (idx : Int) : GovernanceActionId := .mk txId idx
@[onchain] noncomputable def mkMinting (cs : ByteString) : ScriptPurpose := .minting cs
@[onchain] noncomputable def mkSpending (r : TxOutRef) : ScriptPurpose := .spending r
@[onchain] noncomputable def mkRewarding (c : Credential) : ScriptPurpose := .rewarding c
@[onchain] noncomputable def mkCertifying (n : Int) (tc : TxCert) : ScriptPurpose := .certifying n tc
@[onchain] noncomputable def mkVotingSP (v : Voter) : ScriptPurpose := .voting v
@[onchain] noncomputable def mkProposing (n : Int) (pp : ProposalProcedure) : ScriptPurpose := .proposing n pp
@[onchain] noncomputable def mkMintingScript (cs : ByteString) : ScriptInfo := .mintingScript cs
@[onchain] noncomputable def mkSpendingScript (r : TxOutRef) (d : MaybeData Moist.Plutus.Data) : ScriptInfo := .spendingScript r d
@[onchain] noncomputable def mkRewardingScript (c : Credential) : ScriptInfo := .rewardingScript c
@[onchain] noncomputable def mkCertifyingScript (n : Int) (tc : TxCert) : ScriptInfo := .certifyingScript n tc
@[onchain] noncomputable def mkVotingScript (v : Voter) : ScriptInfo := .votingScript v
@[onchain] noncomputable def mkProposingScript (n : Int) (pp : ProposalProcedure) : ScriptInfo := .proposingScript n pp
@[onchain] noncomputable def mkProposalProcedure (l : Int) (c : Credential) (a : GovernanceAction) : ProposalProcedure := .mk l c a
@[onchain] noncomputable def mkInfoAction : GovernanceAction := .infoAction
@[onchain] noncomputable def mkNoConfidence (g : MaybeData GovernanceActionId) : GovernanceAction := .noConfidence g
@[onchain] noncomputable def mkProtocolVersion (major minor : Int) : ProtocolVersion := .mk major minor

/-! ## Decoding extractors

Only extractors that the @[onchain] compiler can handle:
- Single-constructor types (all fields extractable)
- Multi-constructor types where ALL branches return same type without constructing values
-/

-- Credential: both branches return ByteString — works
@[onchain] noncomputable def credHash (c : Credential) : ByteString :=
  match c with | .pubKeyCredential h => h | .scriptCredential h => h

-- Address (structure)
@[onchain] noncomputable def addressCred (a : Address) : Credential := a.credential
@[onchain] noncomputable def addressStaking (a : Address) : MaybeData StakingCredential := a.stakingCredential

-- TxOutRef (structure)
@[onchain] noncomputable def txOutRefTxId (r : TxOutRef) : ByteString := r.id
@[onchain] noncomputable def txOutRefIdx (r : TxOutRef) : Int := r.idx

-- TxOut (structure)
@[onchain] noncomputable def txOutAddr (t : TxOut) : Address := t.address
@[onchain] noncomputable def txOutDatum (t : TxOut) : OutputDatum := t.datum
@[onchain] noncomputable def txOutRefScript (t : TxOut) : MaybeData ByteString := t.referenceScript

-- TxInInfo (structure)
@[onchain] noncomputable def txInInfoRef (t : TxInInfo) : TxOutRef := t.outRef
@[onchain] noncomputable def txInInfoOut (t : TxInInfo) : TxOut := t.resolved

-- LowerBound (structure)
@[onchain] noncomputable def lowerBoundExt (lb : LowerBound) : Extended := lb.bound
@[onchain] noncomputable def lowerBoundCl (lb : LowerBound) : Closure := lb.closure

-- UpperBound (structure)
@[onchain] noncomputable def upperBoundExt (ub : UpperBound) : Extended := ub.bound
@[onchain] noncomputable def upperBoundCl (ub : UpperBound) : Closure := ub.closure

-- Interval (structure)
@[onchain] noncomputable def intervalLB (i : Interval) : LowerBound := i.lowerBound
@[onchain] noncomputable def intervalUB (i : Interval) : UpperBound := i.upperBound

-- GovernanceActionId (structure)
@[onchain] noncomputable def govActTxId (g : GovernanceActionId) : ByteString := g.txId
@[onchain] noncomputable def govActIdx (g : GovernanceActionId) : Int := g.govActionIx

-- ProposalProcedure (structure)
@[onchain] noncomputable def ppDeposit (p : ProposalProcedure) : Int := p.deposit
@[onchain] noncomputable def ppCred (p : ProposalProcedure) : Credential := p.returnAddr
@[onchain] noncomputable def ppAction (p : ProposalProcedure) : GovernanceAction := p.governanceAction

-- ScriptContext (structure)
@[onchain] noncomputable def ctxRedeemer (ctx : ScriptContext) : Moist.Plutus.Data := ctx.redeemer
@[onchain] noncomputable def ctxScriptInfo (ctx : ScriptContext) : ScriptInfo := ctx.scriptInfo

-- Multi-constructor: use tag-returning approach to avoid constructing values in fallback
-- Extended: all branches return Int
@[onchain] noncomputable def extendedVal (e : Extended) : Int :=
  match e with | .negInf => -1 | .finite t => t | .posInf => -2

-- StakingCredential: stakingPtr returns fields as Int, stakingHash returns -1
@[onchain] noncomputable def stakingPtrA (s : StakingCredential) : Int :=
  match s with | .stakingHash _ => -1 | .stakingPtr a _ _ => a
@[onchain] noncomputable def stakingPtrB (s : StakingCredential) : Int :=
  match s with | .stakingHash _ => -1 | .stakingPtr _ b _ => b
@[onchain] noncomputable def stakingPtrC (s : StakingCredential) : Int :=
  match s with | .stakingHash _ => -1 | .stakingPtr _ _ c => c

-- OutputDatum: tag
@[onchain] noncomputable def outputDatumTag (od : OutputDatum) : Int :=
  match od with | .noOutputDatum => 0 | .outputDatumHash _ => 1 | .outputDatum _ => 2

-- Vote: tag
@[onchain] noncomputable def voteTag (v : Vote) : Int :=
  match v with | .voteNo => 0 | .voteYes => 1 | .abstain => 2

-- Nested: ScriptContext → ScriptInfo → tag
@[onchain] noncomputable def ctxScriptInfoTag (ctx : ScriptContext) : Int :=
  match ctx.scriptInfo with
  | .mintingScript _ => 0 | .spendingScript _ _ => 1 | .rewardingScript _ => 2
  | .certifyingScript _ _ => 3 | .votingScript _ => 4 | .proposingScript _ _ => 5

-- Nested: TxInInfo → TxOut → Address → Credential
@[onchain] noncomputable def txInInfoAddrCred (t : TxInInfo) : Credential :=
  t.resolved.address.credential

/-! ## Run Tests -/

def deadbeef : ByteString := ⟨#[0xde, 0xad, 0xbe, 0xef]⟩
def cafebabe : ByteString := ⟨#[0xca, 0xfe, 0xba, 0xbe]⟩
def aabbccdd : ByteString := ⟨#[0xaa, 0xbb, 0xcc, 0xdd]⟩
def bs11223344 : ByteString := ⟨#[0x11, 0x22, 0x33, 0x44]⟩
def dddddddd : ByteString := ⟨#[0xdd, 0xdd, 0xdd, 0xdd]⟩
def cccccccc : ByteString := ⟨#[0xcc, 0xcc, 0xcc, 0xcc]⟩
def eeeeeeee : ByteString := ⟨#[0xee, 0xee, 0xee, 0xee]⟩
def aaaaaaaa : ByteString := ⟨#[0xaa, 0xaa, 0xaa, 0xaa]⟩
def bbbbbbbb : ByteString := ⟨#[0xbb, 0xbb, 0xbb, 0xbb]⟩
def ffff0000 : ByteString := ⟨#[0xff, 0xff, 0x00, 0x00]⟩
def aabb : ByteString := ⟨#[0x61, 0x61, 0x62, 0x62]⟩

def ap1 (f : Term) (a : Term) := f.Apply a
def ap2 (f : Term) (a b : Term) := f.Apply a |>.Apply b
def ap3 (f : Term) (a b c : Term) := f.Apply a |>.Apply b |>.Apply c
def dt (hex : String) : Term := dataTerm (fromHex! hex)
def bs (b : ByteString) : Term := bsTerm b
def ii (n : Int) : Term := intTerm n

-- Pre-compile all terms
section CompiledTerms
  def cPubKeyCred := compile! mkPubKeyCred
  def cScriptCred := compile! mkScriptCred
  def cStakingHash := compile! mkStakingHash
  def cStakingPtr := compile! mkStakingPtr
  def cTxOutRef := compile! mkTxOutRef
  def cNoOutputDatum := compile! mkNoOutputDatum
  def cOutputDatumHash := compile! mkOutputDatumHash
  def cOutputDatumI := compile! mkOutputDatumI
  def cNegInf := compile! mkNegInf
  def cFinite := compile! mkFinite
  def cPosInf := compile! mkPosInf
  def cExclusive := compile! mkExclusive
  def cInclusive := compile! mkInclusive
  def cLowerBound := compile! mkLowerBound
  def cUpperBound := compile! mkUpperBound
  def cInterval := compile! mkInterval
  def cJustInt := compile! mkJustInt
  def cNothingInt := compile! mkNothingInt
  def cDRep := compile! mkDRep
  def cDRepAlwaysAbstain := compile! mkDRepAlwaysAbstain
  def cDRepAlwaysNoConfidence := compile! mkDRepAlwaysNoConfidence
  def cDelegStake := compile! mkDelegStake
  def cDelegVote := compile! mkDelegVote
  def cDelegStakeVote := compile! mkDelegStakeVote
  def cTxCertRegStaking := compile! mkTxCertRegStaking
  def cTxCertUnRegStaking := compile! mkTxCertUnRegStaking
  def cTxCertDelegStaking := compile! mkTxCertDelegStaking
  def cTxCertRegDeleg := compile! mkTxCertRegDeleg
  def cTxCertRegDRep := compile! mkTxCertRegDRep
  def cTxCertUpdateDRep := compile! mkTxCertUpdateDRep
  def cTxCertUnRegDRep := compile! mkTxCertUnRegDRep
  def cTxCertPoolRegister := compile! mkTxCertPoolRegister
  def cTxCertPoolRetire := compile! mkTxCertPoolRetire
  def cTxCertAuthHotCommittee := compile! mkTxCertAuthHotCommittee
  def cTxCertResignColdCommittee := compile! mkTxCertResignColdCommittee
  def cCommitteeVoter := compile! mkCommitteeVoter
  def cDRepVoter := compile! mkDRepVoter
  def cStakePoolVoter := compile! mkStakePoolVoter
  def cVoteNo := compile! mkVoteNo
  def cVoteYes := compile! mkVoteYes
  def cAbstain := compile! mkAbstain
  def cGovActId := compile! mkGovActId
  def cMinting := compile! mkMinting
  def cSpending := compile! mkSpending
  def cRewarding := compile! mkRewarding
  def cCertifying := compile! mkCertifying
  def cVotingSP := compile! mkVotingSP
  def cProposing := compile! mkProposing
  def cMintingScript := compile! mkMintingScript
  def cSpendingScript := compile! mkSpendingScript
  def cRewardingScript := compile! mkRewardingScript
  def cCertifyingScript := compile! mkCertifyingScript
  def cVotingScript := compile! mkVotingScript
  def cProposingScript := compile! mkProposingScript
  def cProposalProcedure := compile! mkProposalProcedure
  def cInfoAction := compile! mkInfoAction
  def cNoConfidence := compile! mkNoConfidence
  def cProtocolVersion := compile! mkProtocolVersion
  -- Decoders
  def cCredHash := compile! credHash
  def cAddressCred := compile! addressCred
  def cAddressStaking := compile! addressStaking
  def cTxOutRefTxId := compile! txOutRefTxId
  def cTxOutRefIdx := compile! txOutRefIdx
  def cTxOutAddr := compile! txOutAddr
  def cTxOutDatum := compile! txOutDatum
  def cTxOutRefScript := compile! txOutRefScript
  def cTxInInfoRef := compile! txInInfoRef
  def cTxInInfoOut := compile! txInInfoOut
  def cLowerBoundExt := compile! lowerBoundExt
  def cLowerBoundCl := compile! lowerBoundCl
  def cUpperBoundExt := compile! upperBoundExt
  def cUpperBoundCl := compile! upperBoundCl
  def cIntervalLB := compile! intervalLB
  def cIntervalUB := compile! intervalUB
  def cGovActTxId := compile! govActTxId
  def cGovActIdx := compile! govActIdx
  def cPpDeposit := compile! ppDeposit
  def cPpCred := compile! ppCred
  def cPpAction := compile! ppAction
  def cCtxRedeemer := compile! ctxRedeemer
  def cCtxScriptInfo := compile! ctxScriptInfo
  def cExtendedVal := compile! extendedVal
  def cStakingPtrA := compile! stakingPtrA
  def cStakingPtrB := compile! stakingPtrB
  def cStakingPtrC := compile! stakingPtrC
  def cOutputDatumTag := compile! outputDatumTag
  def cVoteTag := compile! voteTag
  def cCtxScriptInfoTag := compile! ctxScriptInfoTag
  def cTxInInfoAddrCred := compile! txInInfoAddrCred
end CompiledTerms

#eval do
  IO.println "=== ENCODING TESTS ==="

  -- Credential
  evalCheck "Credential.PubKeyCredential" (ap1 cPubKeyCred (bs deadbeef)) "d8799f44deadbeefff"
  evalCheck "Credential.ScriptCredential" (ap1 cScriptCred (bs cafebabe)) "d87a9f44cafebabeff"

  -- StakingCredential
  evalCheck "StakingCredential.StakingHash" (ap1 cStakingHash (ap1 cPubKeyCred (bs deadbeef))) "d8799fd8799f44deadbeefffff"
  evalCheck "StakingCredential.StakingPtr" (ap3 cStakingPtr (ii 1) (ii 2) (ii 3)) "d87a9f010203ff"

  -- TxOutRef
  evalCheck "TxOutRef" (ap2 cTxOutRef (bs aabbccdd) (ii 42)) "d8799f44aabbccdd182aff"

  -- OutputDatum
  evalCheck "OutputDatum.NoOutputDatum" cNoOutputDatum "d87980"
  evalCheck "OutputDatum.OutputDatumHash" (ap1 cOutputDatumHash (bs bs11223344)) "d87a9f4411223344ff"
  evalCheck "OutputDatum.OutputDatum" (ap1 cOutputDatumI (ii 999)) "d87b9f1903e7ff"

  -- Extended
  evalCheck "Extended.NegInf" cNegInf "d87980"
  evalCheck "Extended.Finite" (ap1 cFinite (ii 1000)) "d87a9f1903e8ff"
  evalCheck "Extended.PosInf" cPosInf "d87b80"

  -- Closure
  evalCheck "Closure.exclusive" cExclusive "d87980"
  evalCheck "Closure.inclusive" cInclusive "d87a80"

  -- LowerBound / UpperBound / Interval
  let lbT := ap2 cLowerBound (ap1 cFinite (ii 1000)) cInclusive
  let ubT := ap2 cUpperBound cPosInf cExclusive
  evalCheck "LowerBound" lbT "d8799fd87a9f1903e8ffd87a80ff"
  evalCheck "UpperBound" ubT "d8799fd87b80d87980ff"
  evalCheck "Interval" (ap2 cInterval lbT ubT) "d8799fd8799fd87a9f1903e8ffd87a80ffd8799fd87b80d87980ffff"

  -- MaybeData
  evalCheck "MaybeData.Just" (ap1 cJustInt (ii 42)) "d8799f182aff"
  evalCheck "MaybeData.Nothing" cNothingInt "d87a80"

  -- DRep
  let drepT := ap1 cDRep (ap1 cPubKeyCred (bs dddddddd))
  evalCheck "DRep.DRep" drepT "d8799fd8799f44ddddddddffff"
  evalCheck "DRep.DRepAlwaysAbstain" cDRepAlwaysAbstain "d87a80"
  evalCheck "DRep.DRepAlwaysNoConfidence" cDRepAlwaysNoConfidence "d87b80"

  -- Delegatee
  evalCheck "Delegatee.DelegStake" (ap1 cDelegStake (bs eeeeeeee)) "d8799f44eeeeeeeeff"
  evalCheck "Delegatee.DelegVote" (ap1 cDelegVote drepT) "d87a9fd8799fd8799f44ddddddddffffff"
  evalCheck "Delegatee.DelegStakeVote" (ap2 cDelegStakeVote (bs eeeeeeee) drepT) "d87b9f44eeeeeeeed8799fd8799f44ddddddddffffff"

  -- TxCert (all 11 — including high-tag constructors 7-10)
  let credT := ap1 cPubKeyCred (bs deadbeef)
  let just2m := ap1 cJustInt (ii 2000000)
  evalCheck "TxCert.TxCertRegStaking" (ap2 cTxCertRegStaking credT just2m) "d8799fd8799f44deadbeefffd8799f1a001e8480ffff"
  evalCheck "TxCert.TxCertUnRegStaking" (ap2 cTxCertUnRegStaking credT cNothingInt) "d87a9fd8799f44deadbeefffd87a80ff"
  evalCheck "TxCert.TxCertDelegStaking" (ap2 cTxCertDelegStaking credT (ap1 cDelegStake (bs eeeeeeee))) "d87b9fd8799f44deadbeefffd8799f44eeeeeeeeffff"
  evalCheck "TxCert.TxCertRegDeleg" (ap3 cTxCertRegDeleg credT (ap1 cDelegStake (bs eeeeeeee)) (ii 2000000)) "d87c9fd8799f44deadbeefffd8799f44eeeeeeeeff1a001e8480ff"
  let drepCredT := ap1 cPubKeyCred (bs dddddddd)
  evalCheck "TxCert.TxCertRegDRep" (ap2 cTxCertRegDRep drepCredT (ii 2000000)) "d87d9fd8799f44ddddddddff1a001e8480ff"
  evalCheck "TxCert.TxCertUpdateDRep" (ap1 cTxCertUpdateDRep drepCredT) "d87e9fd8799f44ddddddddffff"
  evalCheck "TxCert.TxCertUnRegDRep" (ap2 cTxCertUnRegDRep drepCredT (ii 2000000)) "d87f9fd8799f44ddddddddff1a001e8480ff"
  evalCheck "TxCert.TxCertPoolRegister" (ap2 cTxCertPoolRegister (bs aaaaaaaa) (bs bbbbbbbb)) "d905009f44aaaaaaaa44bbbbbbbbff"
  evalCheck "TxCert.TxCertPoolRetire" (ap2 cTxCertPoolRetire (bs aaaaaaaa) (ii 10)) "d905019f44aaaaaaaa0aff"
  evalCheck "TxCert.TxCertAuthHotCommittee" (ap2 cTxCertAuthHotCommittee credT (ap1 cPubKeyCred (bs cccccccc))) "d905029fd8799f44deadbeefffd8799f44ccccccccffff"
  evalCheck "TxCert.TxCertResignColdCommittee" (ap1 cTxCertResignColdCommittee credT) "d905039fd8799f44deadbeefffff"

  -- Voter
  evalCheck "Voter.CommitteeVoter" (ap1 cCommitteeVoter (ap1 cPubKeyCred (bs cccccccc))) "d8799fd8799f44ccccccccffff"
  evalCheck "Voter.DRepVoter" (ap1 cDRepVoter drepCredT) "d87a9fd8799f44ddddddddffff"
  evalCheck "Voter.StakePoolVoter" (ap1 cStakePoolVoter (bs eeeeeeee)) "d87b9f44eeeeeeeeff"

  -- Vote
  evalCheck "Vote.VoteNo" cVoteNo "d87980"
  evalCheck "Vote.VoteYes" cVoteYes "d87a80"
  evalCheck "Vote.Abstain" cAbstain "d87b80"

  -- GovernanceActionId
  evalCheck "GovernanceActionId" (ap2 cGovActId (bs ffff0000) (ii 7)) "d8799f44ffff000007ff"

  -- ScriptPurpose (all 6)
  let txOutRefT := ap2 cTxOutRef (bs aabbccdd) (ii 42)
  evalCheck "ScriptPurpose.Minting" (ap1 cMinting (bs aabb)) "d8799f4461616262ff"
  evalCheck "ScriptPurpose.Spending" (ap1 cSpending txOutRefT) "d87a9fd8799f44aabbccdd182affff"
  evalCheck "ScriptPurpose.Rewarding" (ap1 cRewarding credT) "d87b9fd8799f44deadbeefffff"
  evalCheck "ScriptPurpose.Certifying" (ap2 cCertifying (ii 0) (ap2 cTxCertRegStaking credT just2m)) "d87c9f00d8799fd8799f44deadbeefffd8799f1a001e8480ffffff"
  evalCheck "ScriptPurpose.Voting" (ap1 cVotingSP (ap1 cDRepVoter drepCredT)) "d87d9fd87a9fd8799f44ddddddddffffff"
  let ppT := ap3 cProposalProcedure (ii 1000000) credT cInfoAction
  evalCheck "ScriptPurpose.Proposing" (ap2 cProposing (ii 0) ppT) "d87e9f00d8799f1a000f4240d8799f44deadbeefffd87f80ffff"

  -- ScriptInfo (all 6)
  evalCheck "ScriptInfo.MintingScript" (ap1 cMintingScript (bs aabb)) "d8799f4461616262ff"
  evalCheck "ScriptInfo.SpendingScript" (ap2 cSpendingScript txOutRefT (ap1 cJustInt (ii 42))) "d87a9fd8799f44aabbccdd182affd8799f182affff"
  evalCheck "ScriptInfo.RewardingScript" (ap1 cRewardingScript credT) "d87b9fd8799f44deadbeefffff"
  evalCheck "ScriptInfo.CertifyingScript" (ap2 cCertifyingScript (ii 0) (ap2 cTxCertRegStaking credT just2m)) "d87c9f00d8799fd8799f44deadbeefffd8799f1a001e8480ffffff"
  evalCheck "ScriptInfo.VotingScript" (ap1 cVotingScript (ap1 cDRepVoter drepCredT)) "d87d9fd87a9fd8799f44ddddddddffffff"
  evalCheck "ScriptInfo.ProposingScript" (ap2 cProposingScript (ii 0) ppT) "d87e9f00d8799f1a000f4240d8799f44deadbeefffd87f80ffff"

  -- ProposalProcedure
  evalCheck "ProposalProcedure" ppT "d8799f1a000f4240d8799f44deadbeefffd87f80ff"

  -- GovernanceAction
  evalCheck "GovernanceAction.InfoAction" cInfoAction "d87f80"

  -- ProtocolVersion
  evalCheck "ProtocolVersion" (ap2 cProtocolVersion (ii 9) (ii 0)) "d8799f0900ff"

  IO.println ""
  IO.println "=== DECODING TESTS ==="

  -- Credential
  evalCheck "D:Credential.PubKey.hash" (ap1 cCredHash (dt "d8799f44deadbeefff")) "44deadbeef"
  evalCheck "D:Credential.Script.hash" (ap1 cCredHash (dt "d87a9f44cafebabeff")) "44cafebabe"

  -- StakingCredential.StakingPtr fields
  evalCheckData "D:StakingPtr.a" (ap1 cStakingPtrA (dt "d87a9f010203ff")) (.I 1)
  evalCheckData "D:StakingPtr.b" (ap1 cStakingPtrB (dt "d87a9f010203ff")) (.I 2)
  evalCheckData "D:StakingPtr.c" (ap1 cStakingPtrC (dt "d87a9f010203ff")) (.I 3)

  -- Address
  evalCheck "D:Address.cred" (ap1 cAddressCred (dt "d8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffff")) "d8799f44deadbeefff"
  evalCheck "D:Address.staking" (ap1 cAddressStaking (dt "d8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffff")) "d8799fd8799fd8799f44deadbeefffffff"
  evalCheck "D:Address.NoStake.cred" (ap1 cAddressCred (dt "d8799fd87a9f44cafebabeffd87a80ff")) "d87a9f44cafebabeff"
  evalCheck "D:Address.NoStake.staking" (ap1 cAddressStaking (dt "d8799fd87a9f44cafebabeffd87a80ff")) "d87a80"

  -- TxOutRef
  evalCheck "D:TxOutRef.txId" (ap1 cTxOutRefTxId (dt "d8799f44aabbccdd182aff")) "44aabbccdd"
  evalCheckData "D:TxOutRef.idx" (ap1 cTxOutRefIdx (dt "d8799f44aabbccdd182aff")) (.I 42)

  -- OutputDatum
  evalCheckData "D:OutputDatum.tag0" (ap1 cOutputDatumTag (dt "d87980")) (.I 0)
  evalCheckData "D:OutputDatum.tag1" (ap1 cOutputDatumTag (dt "d87a9f4411223344ff")) (.I 1)
  evalCheckData "D:OutputDatum.tag2" (ap1 cOutputDatumTag (dt "d87b9f1903e7ff")) (.I 2)

  -- TxOut (nested)
  let txOutHex := "d8799fd8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffffa240a1401a001e84804461616262a144746f6b311832d87a9f4411223344ffd87a80ff"
  evalCheck "D:TxOut.address" (ap1 cTxOutAddr (dt txOutHex)) "d8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffff"
  evalCheck "D:TxOut.datum" (ap1 cTxOutDatum (dt txOutHex)) "d87a9f4411223344ff"
  evalCheck "D:TxOut.refScript" (ap1 cTxOutRefScript (dt txOutHex)) "d87a80"

  -- TxInInfo (nested)
  let txInInfoHex := "d8799fd8799f44aabbccdd182affd8799fd8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffffa240a1401a001e84804461616262a144746f6b311832d87a9f4411223344ffd87a80ffff"
  evalCheck "D:TxInInfo.txOutRef" (ap1 cTxInInfoRef (dt txInInfoHex)) "d8799f44aabbccdd182aff"
  evalCheck "D:TxInInfo.txOut" (ap1 cTxInInfoOut (dt txInInfoHex)) txOutHex

  -- LowerBound
  let lbHex := "d8799fd87a9f1903e8ffd87a80ff"
  evalCheck "D:LowerBound.ext" (ap1 cLowerBoundExt (dt lbHex)) "d87a9f1903e8ff"
  evalCheck "D:LowerBound.cl" (ap1 cLowerBoundCl (dt lbHex)) "d87a80"

  -- UpperBound
  let ubHex := "d8799fd87b80d87980ff"
  evalCheck "D:UpperBound.ext" (ap1 cUpperBoundExt (dt ubHex)) "d87b80"
  evalCheck "D:UpperBound.cl" (ap1 cUpperBoundCl (dt ubHex)) "d87980"

  -- Interval
  let ivlHex := "d8799fd8799fd87a9f1903e8ffd87a80ffd8799fd87b80d87980ffff"
  evalCheck "D:Interval.lb" (ap1 cIntervalLB (dt ivlHex)) lbHex
  evalCheck "D:Interval.ub" (ap1 cIntervalUB (dt ivlHex)) ubHex

  -- Extended values
  evalCheckData "D:Extended.NegInf" (ap1 cExtendedVal (dt "d87980")) (.I (-1))
  evalCheckData "D:Extended.Finite" (ap1 cExtendedVal (dt "d87a9f1903e8ff")) (.I 1000)
  evalCheckData "D:Extended.PosInf" (ap1 cExtendedVal (dt "d87b80")) (.I (-2))

  -- Vote
  evalCheckData "D:Vote.No" (ap1 cVoteTag (dt "d87980")) (.I 0)
  evalCheckData "D:Vote.Yes" (ap1 cVoteTag (dt "d87a80")) (.I 1)
  evalCheckData "D:Vote.Abstain" (ap1 cVoteTag (dt "d87b80")) (.I 2)

  -- GovernanceActionId
  evalCheck "D:GovActId.txId" (ap1 cGovActTxId (dt "d8799f44ffff000007ff")) "44ffff0000"
  evalCheckData "D:GovActId.idx" (ap1 cGovActIdx (dt "d8799f44ffff000007ff")) (.I 7)

  -- ProposalProcedure
  let ppHex := "d8799f1a000f4240d8799f44deadbeefffd87f80ff"
  evalCheckData "D:PP.deposit" (ap1 cPpDeposit (dt ppHex)) (.I 1000000)
  evalCheck "D:PP.cred" (ap1 cPpCred (dt ppHex)) "d8799f44deadbeefff"
  evalCheck "D:PP.action" (ap1 cPpAction (dt ppHex)) "d87f80"

  -- ScriptContext
  let ctxHex := "d8799fd8799f9fd8799fd8799f44aabbccdd182affd8799fd8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffffa240a1401a001e84804461616262a144746f6b311832d87a9f4411223344ffd87a80ffffff809fd8799fd8799fd8799f44deadbeefffd8799fd8799fd8799f44deadbeefffffffffa240a1401a001e84804461616262a144746f6b311832d87a9f4411223344ffd87a80ffff1a00030d40a080a0d8799fd8799fd87a9f1903e8ffd87a80ffd8799fd87b80d87980ffff9f44deadbeefffa0a044aabbccdda080d87a80d87a80ff00d87a9fd8799f44aabbccdd182affd8799f182affffff"
  evalCheckData "D:ScriptContext.redeemer" (ap1 cCtxRedeemer (dt ctxHex)) (.I 0)
  evalCheck "D:ScriptContext.scriptInfo" (ap1 cCtxScriptInfo (dt ctxHex)) "d87a9fd8799f44aabbccdd182affd8799f182affff"
  evalCheckData "D:ScriptContext.scriptInfoTag" (ap1 cCtxScriptInfoTag (dt ctxHex)) (.I 1)

  -- Nested 3-deep: TxInInfo → TxOut → Address → Credential
  evalCheck "D:TxInInfo→TxOut→Addr→Cred" (ap1 cTxInInfoAddrCred (dt txInInfoHex)) "d8799f44deadbeefff"

  IO.println ""
  IO.println "=== ALL TESTS COMPLETE ==="

end Test.LedgerEncoding
