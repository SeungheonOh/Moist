import Test.MIR.Helpers
import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Cardano.V3
import Moist.Plutus.Types

namespace Test.MIR.Eval.Policy

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)
open Moist.Onchain.Prelude
open Moist.Cardano.V3
open Test.MIR
open Test.Framework

/-! # Minting Policy Golden Tests

End-to-end: @[onchain] policy → compile! → apply to Data-encoded
ScriptContext → CEK eval → record result + budget.

ScriptContext arguments are built as plain Lean `Data` values and passed
as UPLC Data constants (same encoding the ledger provides on-chain).
-/

/-! ## UPLC constant helpers -/

private def intTerm (n : Int) : Term :=
  .Constant (.Integer n, .AtomicType .TypeInteger)

private def bsTerm (b : ByteString) : Term :=
  .Constant (.ByteString b, .AtomicType .TypeByteString)

private def dataTerm (d : Data) : Term :=
  .Constant (.Data d, .AtomicType .TypeData)

/-! ## Test constants -/

private def testTxId : ByteString := ⟨#[0xAA, 0xBB, 0xCC, 0xDD]⟩
private def testCs   : ByteString := ⟨#[0xDE, 0xAD]⟩
private def otherCs  : ByteString := ⟨#[0xCA, 0xFE]⟩

/-! ## ScriptContext Data construction (plain Lean, not @[onchain])

Build Data values matching the @[plutus_data] ConstrData encoding
of Plutus V3 ScriptContext.
-/

private def validRangeData : Data :=
  -- Interval (LowerBound(NegInf, Inclusive), UpperBound(PosInf, Inclusive))
  .Constr 0
    [.Constr 0 [.Constr 0 [], .Constr 1 []]   -- LowerBound: NegInf, Inclusive
    ,.Constr 0 [.Constr 2 [], .Constr 1 []]]   -- UpperBound: PosInf, Inclusive

/-- Minimal TxInfo with all empty collections. -/
private def emptyTxInfoData (txId : ByteString) : Data :=
  .Constr 0
    [.List []       -- inputs
    ,.List []       -- referenceInputs
    ,.List []       -- outputs
    ,.I 0           -- fee
    ,.Map []        -- mint
    ,.List []       -- txCerts
    ,.Map []        -- wdrl
    ,validRangeData -- validRange
    ,.List []       -- signatories
    ,.Map []        -- redeemers
    ,.Map []        -- datumWitnesses
    ,.B txId        -- id
    ,.Map []        -- votes
    ,.List []       -- proposalProcedures
    ,.Constr 1 []   -- currentTreasuryAmount = Nothing
    ,.Constr 1 []   -- treasuryDonation = Nothing
    ]

/-- ScriptContext for a MintingScript purpose. -/
private def mintCtxData (cs : ByteString) (txId : ByteString) (redeemer : Data) : Data :=
  .Constr 0
    [emptyTxInfoData txId
    ,redeemer
    ,.Constr 0 [.B cs]   -- ScriptInfo.mintingScript cs
    ]

/-- ScriptContext for a SpendingScript purpose. -/
private def spendCtxData (txId : ByteString) (idx : Int) (redeemer : Data) : Data :=
  .Constr 0
    [emptyTxInfoData txId
    ,redeemer
    ,.Constr 1             -- ScriptInfo.spendingScript
      [.Constr 0 [.B txId, .I idx]   -- TxOutRef
      ,.Constr 1 []                   -- MaybeData Datum = Nothing
      ]
    ]

/-! ## Concrete test contexts as UPLC terms -/

-- Mint, redeemer = I 42 (for redeemerGatePolicy)
private def ctxMintRdm42 := dataTerm (mintCtxData testCs testTxId (.I 42))
-- Mint, redeemer = I 0 (wrong value)
private def ctxMintRdm0  := dataTerm (mintCtxData testCs testTxId (.I 0))
-- Mint, redeemer = List [B testTxId, I 0] (for nftMintPolicy)
private def ctxMintNftOk := dataTerm (mintCtxData testCs testTxId (.List [.B testTxId, .I 0]))
-- Mint, redeemer = I 99 (non-list, causes nftMintPolicy to fail)
private def ctxMintNftBad := dataTerm (mintCtxData testCs testTxId (.I 99))
-- Spend, redeemer = I 42 (for testing non-minting rejection)
private def ctxSpend := dataTerm (spendCtxData testTxId 0 (.I 42))

/-! ## Policy definitions -/

/-- Always-succeed minting policy. -/
@[onchain]
noncomputable def alwaysMintPolicy (ctx : ScriptContext) : Bool :=
  match ctx.scriptInfo with
  | _ => true

/-- Redeemer-gated: mints only when redeemer == iData 42.
    Exercises: ScriptContext field access, ScriptInfo match, unIData. -/
@[onchain]
noncomputable def redeemerGatePolicy (ctx : ScriptContext) : Bool :=
  match ctx.scriptInfo with
  | .mintingScript _ => equalsInteger (unIData ctx.redeemer) 42
  | _ => false

/-- Currency-symbol check: mints only when own cs matches expected.
    Exercises: parameterised policy, ByteString comparison. -/
@[onchain]
noncomputable def csCheckPolicy (expectedCs : CurrencySymbol)
    (ctx : ScriptContext) : Bool :=
  match ctx.scriptInfo with
  | .mintingScript cs => equalsByteString cs expectedCs
  | _ => false

/-- NFT minting policy (simplified, no input traversal).
    Checks:
    1. ScriptInfo is MintingScript
    2. Redeemer is List [bData txId, iData idx]
    3. Decoded redeemer fields match expected UTxO ref

    Exercises: nested Data deconstruction (unListData, headList, tailList,
    unBData, unIData) inside a ScriptInfo match. -/
@[onchain]
noncomputable def nftMintPolicy (expectedTxId : ByteString) (expectedIdx : Int)
    (ctx : ScriptContext) : Bool :=
  match ctx.scriptInfo with
  | .mintingScript _ =>
    let rdList := unListData ctx.redeemer
    let rdTxId := unBData (headList rdList)
    let rdIdx  := unIData (headList (tailList rdList))
    ifThenElse (equalsByteString rdTxId expectedTxId)
      (equalsInteger rdIdx expectedIdx)
      false
  | _ => false

/-! ## Compile policies -/

section Compiled
  def cAlwaysMint   := compile! alwaysMintPolicy
  def cRedeemerGate := compile! redeemerGatePolicy
  def cCsCheck      := compile! csCheckPolicy
  def cNftMint      := compile! nftMintPolicy
end Compiled

/-! ## Golden test tree -/

def policyTree : TestTree := suite "policy" do

  -- Verify context Data evaluates cleanly
  group "ctx" do
    mkTermEvalGolden "mint_ctx" ctxMintRdm42
    mkTermEvalGolden "spend_ctx" ctxSpend

  group "always" do
    -- alwaysMintPolicy(mintCtx) → true
    mkTermApplyEvalGolden "always_mint_ok" cAlwaysMint [ctxMintRdm42]
    -- alwaysMintPolicy(spendCtx) → true (ignores scriptInfo)
    mkTermApplyEvalGolden "always_mint_spend" cAlwaysMint [ctxSpend]

  group "redeemer_gate" do
    -- redeemer=42 on mint → true
    mkTermApplyEvalGolden "rdm_gate_ok" cRedeemerGate [ctxMintRdm42]
    -- redeemer=0 on mint → false
    mkTermApplyEvalGolden "rdm_gate_wrong" cRedeemerGate [ctxMintRdm0]
    -- spend context → false (not minting)
    mkTermApplyEvalGolden "rdm_gate_spend" cRedeemerGate [ctxSpend]

  group "cs_check" do
    -- matching currency symbol → true
    mkTermApplyEvalGolden "cs_match" cCsCheck [bsTerm testCs, ctxMintRdm42]
    -- wrong currency symbol → false
    mkTermApplyEvalGolden "cs_mismatch" cCsCheck [bsTerm otherCs, ctxMintRdm42]
    -- spend context → false
    mkTermApplyEvalGolden "cs_spend" cCsCheck [bsTerm testCs, ctxSpend]

  group "nft" do
    -- valid redeemer [txId, idx] → true
    mkTermApplyEvalGolden "nft_ok" cNftMint [bsTerm testTxId, intTerm 0, ctxMintNftOk]
    -- non-list redeemer → error (unListData on non-list)
    mkTermApplyEvalGolden "nft_bad_redeemer" cNftMint [bsTerm testTxId, intTerm 0, ctxMintNftBad]
    -- spend context → false
    mkTermApplyEvalGolden "nft_spend" cNftMint [bsTerm testTxId, intTerm 0, ctxSpend]
    -- wrong idx → false
    mkTermApplyEvalGolden "nft_wrong_idx" cNftMint [bsTerm testTxId, intTerm 1, ctxMintNftOk]

end Test.MIR.Eval.Policy
