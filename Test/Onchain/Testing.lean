import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude
import Moist.Plutus.Eval
import Moist.Plutus.Convert

open PlutusCore.UPLC.Term
open Moist.Plutus (Data ByteString)
open Moist.Plutus.Convert (convertData)
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude
open Moist.Plutus.Eval
open Moist.Cardano.V3
open Moist.Onchain.PlutusData
open Moist.Onchain (PlutusData)

@[plutus_sop]
inductive Maybe (α : Type) where
  | none : Maybe α
  | some : α → Maybe α

@[onchain]
def findInputByOutRef (inputs : List TxInInfo) (ref : TxOutRef) : Maybe TxInInfo :=
  match inputs with
  | [] => .none
  | x :: xs =>
    if x.outRef == ref
    then .some x
    else findInputByOutRef xs ref

@[onchain]
def nft (seed : TxOutRef) (ctx : ScriptContext) : Unit :=
  match ctx.scriptInfo with
  | .mintingScript _myCS =>
    match findInputByOutRef ctx.txInfo.inputs seed with
    | .none => panic "not minting the correct NFT"
    | .some _ => () -- success case, do nothing
  | _ => panic "not minting"

#show_optimized_mir nft

/-! ## Compile -/

def cNft := compile! nft

/-! ## Helpers -/

private def dataTerm (d : Data) : Term :=
  .Const (.Data (convertData d))

/-! ## Mock ledger values -/

private def seed : TxOutRef := ⟨⟨#[0xAA, 0xBB, 0xCC, 0xDD]⟩, 0⟩

private def dummyTxOut : TxOut :=
  { address := ⟨.pubKeyCredential ⟨#[0x01]⟩, .nothingData⟩
  , value := ⟨[]⟩
  , datum := .noOutputDatum
  , referenceScript := .nothingData }

private def emptyRange : Interval :=
  { lowerBound := ⟨.negInf, .inclusive⟩
  , upperBound := ⟨.posInf, .inclusive⟩ }

private def mkTxInfo (inputs : List TxInInfo) : TxInfo :=
  { inputs         := inputs
  , referenceInputs := []
  , outputs        := []
  , fee            := 0
  , mint           := ⟨[]⟩
  , txCerts        := []
  , wdrl           := ⟨[]⟩
  , validRange     := emptyRange
  , signatories    := []
  , redeemers      := ⟨[]⟩
  , datumWitnesses := ⟨[]⟩
  , id             := ⟨#[0xAA, 0xBB, 0xCC, 0xDD]⟩
  , votes          := ⟨[]⟩
  , proposalProcedures := []
  , currentTreasuryAmount := .nothingData
  , treasuryDonation      := .nothingData }

private def mkMintCtx (inputs : List TxInInfo) : ScriptContext :=
  { txInfo     := mkTxInfo inputs
  , redeemer   := .I 0
  , scriptInfo := .mintingScript ⟨#[0xDE, 0xAD]⟩ }

private def spendCtx : ScriptContext :=
  { txInfo     := mkTxInfo []
  , redeemer   := .I 0
  , scriptInfo := .spendingScript seed .nothingData }

/-! ## Concrete test cases -/

-- 1. Mint + seed is in inputs → should succeed (Unit)
private def ctxMintWithSeed :=
  dataTerm <| PlutusData.toData <| mkMintCtx [⟨seed, dummyTxOut⟩]

-- 2. Mint + seed NOT in inputs → should fail ("not minting the correct NFT")
private def ctxMintNoSeed :=
  dataTerm <| PlutusData.toData <| mkMintCtx []

-- 3. Mint + different utxo in inputs → should fail
private def ctxMintWrongInput :=
  let other : TxOutRef := ⟨⟨#[0xFF]⟩, 99⟩
  dataTerm <| PlutusData.toData <| mkMintCtx [⟨other, dummyTxOut⟩]

-- 4. Spending context → should fail ("not minting")
private def ctxSpend :=
  dataTerm <| PlutusData.toData spendCtx

/-! ## Run tests -/

private def seedTerm := dataTerm (PlutusData.toData seed)

def main : IO Unit := do
  IO.println "=== NFT policy tests ==="

  IO.println "\n--- 1. Mint with seed in inputs (expect: success / Unit) ---"
  (Term.Apply (Term.Apply cNft seedTerm) ctxMintWithSeed).evaluatePretty

  IO.println "\n--- 2. Mint with empty inputs (expect: trace 'not minting the correct NFT' + error) ---"
  (Term.Apply (Term.Apply cNft seedTerm) ctxMintNoSeed).evaluatePretty

  IO.println "\n--- 3. Mint with wrong input (expect: trace 'not minting the correct NFT' + error) ---"
  (Term.Apply (Term.Apply cNft seedTerm) ctxMintWrongInput).evaluatePretty

  IO.println "\n--- 4. Spend context (expect: trace 'not minting' + error) ---"
  (Term.Apply (Term.Apply cNft seedTerm) ctxSpend).evaluatePretty

#eval main
