import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Cross.ProgrammableLogicGlobal

open Moist.Plutus (Data ByteString)
open Moist.Onchain.Prelude

/-! CIP-143 programmable-token global logic (`ProgrammableLogicGlobal`), ported from
`SmartTokens.Contracts.ProgrammableLogicBasePlinth.plinthProgrammableLogicGlobalScript`.

Arguments: the protocol-parameters currency symbol and the V3 `ScriptContext`, both as `Data`.
Values are handled as their sorted Data association lists; credentials, addresses and
currency symbols are compared as Data. -/

abbrev Pairs := List (Data × Data)

/-- A merge of two sorted association lists. The recursive merges are bound once in the
validator and passed to the helpers that use them, so each appears once in the script. -/
abbrev Merge := Pairs → Pairs → Pairs

/-! ## Data access -/

@[onchain] def fields (value : Data) : List Data := sndPair (unConstrData value)
@[onchain] def constrTag (value : Data) : Int := fstPair (unConstrData value)
@[onchain] def first (value : Data) : Data := headList (fields value)
@[onchain] def second (value : Data) : Data := headList (tailList (fields value))

/-- Inline datum of a `TxOut`; any other datum form is rejected. -/
@[onchain] noncomputable def inlineDatum (txOut : Data) : Data :=
  let datum := unConstrData (headList (tailList (tailList (fields txOut))))
  if equalsInteger datum.1 2 then headList datum.2 else pError

/-- `BuiltinList.drop`. -/
@[onchain] def dropData (count : Int) (list : List Data) : List Data :=
  if lessThanEqInteger count 0 then list
  else match list with
    | [] => []
    | _ :: rest => dropData (subtractInteger count 1) rest

@[onchain] def dropPairs (count : Int) (list : Pairs) : Pairs :=
  if lessThanEqInteger count 0 then list
  else match list with
    | [] => []
    | _ :: rest => dropPairs (subtractInteger count 1) rest

/-- `BuiltinList.!!`. -/
@[onchain] noncomputable def elementAt (index : Int) (list : List Data) : Data :=
  if lessThanInteger index 0 then pError else headList (dropData index list)

@[onchain] def lengthData (count : Int) : List Data → Int
  | [] => count
  | _ :: rest => lengthData (addInteger count 1) rest

@[onchain] def containsData (wanted : Data) : List Data → Bool
  | [] => false
  | entry :: rest => if equalsData entry wanted then true else containsData wanted rest

/-- `AssocMap.member` over Data keys (withdrawal credentials). -/
@[onchain] def isInvoked (credential : Data) : Pairs → Bool
  | [] => false
  | entry :: rest => if equalsData entry.1 credential then true else isInvoked credential rest

/-- `AssocMap.lookup` over Data keys, returning the token map of a policy or the empty map. -/
@[onchain] def tokensOf (currency : Data) : Pairs → Pairs
  | [] => []
  | entry :: rest => if equalsData entry.1 currency then unMapData entry.2 else tokensOf currency rest

@[onchain] def quantityOf (token : Data) : Pairs → Int
  | [] => 0
  | entry :: rest => if equalsData entry.1 token then unIData entry.2 else quantityOf token rest

/-- `valueOf`. -/
@[onchain] def assetQuantity (currency token : Data) : Pairs → Int
  | [] => 0
  | entry :: rest =>
    if equalsData entry.1 currency then quantityOf token (unMapData entry.2)
    else assetQuantity currency token rest

/-- The first non-Ada policy of a value is `currency`. -/
@[onchain] def hasCsFirstNonAda (currency : ByteString) (value : Data) : Bool :=
  match unMapData value with
  | [] => false
  | _ :: rest =>
    match rest with
    | [] => false
    | entry :: _ => equalsByteString (unBData entry.1) currency

@[onchain] def stripAda (value : Data) : Pairs :=
  match unMapData value with
  | [] => []
  | _ :: rest => rest

@[onchain] def reversePairs (accumulator : Pairs) : Pairs → Pairs
  | [] => accumulator
  | entry :: rest => reversePairs (entry :: accumulator) rest

/-! ## Value arithmetic on sorted association lists -/

@[onchain] def tokenUnion (xs ys : Pairs) : Pairs :=
  match (generalizing := false) hx : xs with
  | [] => ys
  | x :: xr =>
    match (generalizing := false) hy : ys with
    | [] => xs
    | y :: yr =>
      let xb := unBData x.1
      let yb := unBData y.1
      if equalsByteString xb yb then
        (x.1, iData (addInteger (unIData x.2) (unIData y.2))) :: tokenUnion xr yr
      else if lessThanByteString xb yb then x :: tokenUnion xr ys
      else y :: tokenUnion xs yr
termination_by xs.length + ys.length
decreasing_by all_goals (subst_vars; simp <;> omega)

@[onchain] def currencyUnion (tokens : Merge) (xs ys : Pairs) : Pairs :=
  match (generalizing := false) hx : xs with
  | [] => ys
  | x :: xr =>
    match (generalizing := false) hy : ys with
    | [] => xs
    | y :: yr =>
      let xb := unBData x.1
      let yb := unBData y.1
      if equalsByteString xb yb then
        (x.1, mapData (tokens (unMapData x.2) (unMapData y.2))) :: currencyUnion tokens xr yr
      else if lessThanByteString xb yb then x :: currencyUnion tokens xr ys
      else y :: currencyUnion tokens xs yr
termination_by xs.length + ys.length
decreasing_by all_goals (subst_vars; simp <;> omega)

@[onchain] def negateTokens : Pairs → Pairs
  | [] => []
  | entry :: rest => (entry.1, iData (subtractInteger 0 (unIData entry.2))) :: negateTokens rest

/-- Signed token delta `ins - outs`, dropping zero entries. -/
@[onchain] def subtractTokens (ins outs : Pairs) : Pairs :=
  match (generalizing := false) hi : ins with
  | [] => negateTokens outs
  | inEntry :: inRest =>
    match (generalizing := false) ho : outs with
    | [] => ins
    | outEntry :: outRest =>
      let inName := unBData inEntry.1
      let outName := unBData outEntry.1
      if lessThanByteString inName outName then inEntry :: subtractTokens inRest outs
      else if equalsByteString inName outName then
        let difference := subtractInteger (unIData inEntry.2) (unIData outEntry.2)
        if equalsInteger difference 0 then subtractTokens inRest outRest
        else (inEntry.1, iData difference) :: subtractTokens inRest outRest
      else (outEntry.1, iData (subtractInteger 0 (unIData outEntry.2))) :: subtractTokens ins outRest
termination_by ins.length + outs.length
decreasing_by all_goals (subst_vars; simp <;> omega)

/-- Every required token quantity is covered by `actual` (missing tokens count as zero). -/
@[onchain] def tokenPairsContain (actual required : Pairs) : Bool :=
  match (generalizing := false) hr : required with
  | [] => true
  | requiredEntry :: requiredRest =>
    let requiredQuantity := unIData requiredEntry.2
    match (generalizing := false) ha : actual with
    | [] => if lessThanEqInteger requiredQuantity 0 then tokenPairsContain [] requiredRest else false
    | actualEntry :: actualRest =>
      let actualName := unBData actualEntry.1
      let requiredName := unBData requiredEntry.1
      if equalsByteString actualName requiredName then
        if lessThanEqInteger requiredQuantity (unIData actualEntry.2) then
          tokenPairsContain actualRest requiredRest
        else false
      else if lessThanByteString actualName requiredName then tokenPairsContain actualRest required
      else if lessThanEqInteger requiredQuantity 0 then tokenPairsContain actual requiredRest
      else false
termination_by actual.length + required.length
decreasing_by all_goals (subst_vars; simp <;> omega)

/-! ## Value aggregation -/

/-- Non-Ada value of all inputs paid to `credential`; each such input's owner must authorize. -/
@[onchain] noncomputable def valueFromCred (union : Merge) (credential : Data) (signatories : List Data)
    (withdrawals : Pairs) (accumulator : Pairs) : List Data → Pairs
  | [] => accumulator
  | input :: rest =>
    let resolved := fields (second input)
    let address := fields (headList resolved)
    if equalsData (headList address) credential then
      let staking := unConstrData (headList (tailList address))
      if equalsInteger staking.1 0 then
        let stakingCredential := unConstrData (headList staking.2)
        if equalsInteger stakingCredential.1 0 then
          let owner := headList stakingCredential.2
          let ownerCredential := unConstrData owner
          let authorized :=
            if equalsInteger ownerCredential.1 0 then containsData (headList ownerCredential.2) signatories
            else isInvoked owner withdrawals
          if authorized then
            valueFromCred union credential signatories withdrawals
              (union accumulator (stripAda (headList (tailList resolved)))) rest
          else pError
        else pError
      else pError
    else valueFromCred union credential signatories withdrawals accumulator rest

/-- Non-Ada value of all outputs paid to `credential`. -/
@[onchain] def valueToCred (union : Merge) (credential : Data) (accumulator : Pairs) : List Data → Pairs
  | [] => accumulator
  | output :: rest =>
    let outputFields := fields output
    if equalsData (first (headList outputFields)) credential then
      valueToCred union credential (union accumulator (stripAda (headList (tailList outputFields)))) rest
    else valueToCred union credential accumulator rest

/-! ## Output containment -/

@[onchain] def hasAtLeastAsset (credential currency token : Data) (required current : Int)
    (outputs : List Data) : Bool :=
  if lessThanEqInteger required current then true
  else match outputs with
    | [] => false
    | output :: rest =>
      let outputFields := fields output
      if equalsData (first (headList outputFields)) credential then
        hasAtLeastAsset credential currency token required
          (addInteger current (assetQuantity currency token (unMapData (headList (tailList outputFields))))) rest
      else hasAtLeastAsset credential currency token required current rest

@[onchain] def tokensAtLeast (actual : Pairs) (currency : Data) : Pairs → Bool
  | [] => true
  | entry :: rest =>
    if lessThanEqInteger (unIData entry.2) (assetQuantity currency entry.1 actual) then
      tokensAtLeast actual currency rest
    else false

@[onchain] def currenciesAtLeast (actual : Pairs) : Pairs → Bool
  | [] => true
  | entry :: rest =>
    if tokensAtLeast actual entry.1 (unMapData entry.2) then currenciesAtLeast actual rest else false

/-- Single-asset expectations scan the outputs directly; otherwise the whole value at the
credential is aggregated and compared. -/
@[onchain] def outputsContainExpectedValueAtCred (union : Merge) (credential : Data) (outputs : List Data)
    (expected : Pairs) : Bool :=
  match (generalizing := false) expected with
  | [] => true
  | firstCurrency :: restCurrencies =>
    let tokens : Pairs := match restCurrencies with
      | [] => unMapData firstCurrency.2
      | _ :: _ => []
    let singleAsset : Bool := match tokens with
      | [] => false
      | _ :: restTokens => match restTokens with
        | [] => true
        | _ :: _ => false
    if singleAsset then
      match tokens with
      | [] => true
      | firstToken :: _ =>
        hasAtLeastAsset credential firstCurrency.1 firstToken.1 (unIData firstToken.2) 0 outputs
    else currenciesAtLeast (valueToCred union credential [] outputs) expected

/-! ## Directory and protocol parameters

Directory-node datums are read like Plinth's `DirectorySetNodeD` matcher: no constructor tag
check, extra fields ignored, and the key, next and global-state currency symbols are always
decoded as bytestrings. -/

@[plutus_sop] structure DirectoryNode where
  key : ByteString
  next : ByteString
  transferLogicScript : Data
  issuerLogicScript : Data

@[onchain] noncomputable def directoryNode (nodeOutput : Data) : DirectoryNode :=
  let node := fields (inlineDatum nodeOutput)
  let key := unBData (headList node)
  let afterKey := tailList node
  let next := unBData (headList afterKey)
  let afterNext := tailList afterKey
  let afterTransfer := tailList afterNext
  let _globalStateCs := unBData (headList (tailList afterTransfer))
  ⟨key, next, headList afterNext, headList afterTransfer⟩

@[onchain] noncomputable def findParams (currency : ByteString) : List Data → Data
  | [] => pError
  | input :: rest =>
    let resolved := second input
    if hasCsFirstNonAda currency (second resolved) then inlineDatum resolved
    else findParams currency rest

/-- Programmable value of the inputs: every policy needs a directory proof; policies present in
the directory are kept, policies proven absent are dropped. Result is in reverse order. -/
@[onchain] noncomputable def checkTransferLogic (directoryCs : ByteString) (referenceInputs : List Data)
    (withdrawals : Pairs) (proofs : List Data) (cachedTransferScript : Data) (accumulator : Pairs) :
    Pairs → Pairs
  | [] => accumulator
  | entry :: rest =>
    match proofs with
    | [] => pError
    | proof :: proofsRest =>
      let currency := unBData entry.1
      let nodeOutput := second (elementAt (unIData proof) referenceInputs)
      let node := directoryNode nodeOutput
      let nodeKey := node.key
      let nodeNext := node.next
      let transferLogic := node.transferLogicScript
      if lessThanByteString nodeKey currency then
        if lessThanByteString currency nodeNext then
          if hasCsFirstNonAda directoryCs (second nodeOutput) then
            checkTransferLogic directoryCs referenceInputs withdrawals proofsRest cachedTransferScript
              accumulator rest
          else pError
        else pError
      else
        let transferOk :=
          if equalsData transferLogic cachedTransferScript then true else isInvoked transferLogic withdrawals
        if transferOk then
          if equalsByteString nodeKey currency then
            if hasCsFirstNonAda directoryCs (second nodeOutput) then
              checkTransferLogic directoryCs referenceInputs withdrawals proofsRest transferLogic
                (entry :: accumulator) rest
            else pError
          else pError
        else pError

/-- Programmable part of the mint: one directory proof per minted policy, none left over.
Result is in reverse order. -/
@[onchain] noncomputable def checkMintLogic (directoryCs : ByteString) (referenceInputs : List Data)
    (withdrawals : Pairs) (proofs : List Data) (accumulator : Pairs) : Pairs → Pairs
  | [] =>
    match proofs with
    | [] => accumulator
    | _ :: _ => pError
  | entry :: rest =>
    match proofs with
    | [] => pError
    | proof :: proofsRest =>
      let currency := unBData entry.1
      let nodeOutput := second (elementAt (unIData proof) referenceInputs)
      let node := directoryNode nodeOutput
      let nodeKey := node.key
      let nodeNext := node.next
      let transferLogic := node.transferLogicScript
      if equalsByteString nodeKey currency then
        if isInvoked transferLogic withdrawals then
          if hasCsFirstNonAda directoryCs (second nodeOutput) then
            checkMintLogic directoryCs referenceInputs withdrawals proofsRest (entry :: accumulator) rest
          else pError
        else pError
      else if lessThanByteString nodeKey currency then
        if lessThanByteString currency nodeNext then
          if hasCsFirstNonAda directoryCs (second nodeOutput) then
            checkMintLogic directoryCs referenceInputs withdrawals proofsRest accumulator rest
          else pError
        else pError
      else pError

/-! ## Seize -/

/-- Input and output values must agree on every policy except `programmableCs`, whose signed
token delta is returned. -/
@[onchain] noncomputable def valueEqualsDeltaCurrencySymbol (programmableCs : Data) : Pairs → Pairs → Pairs
  | [], _ => []
  | _ :: _, [] => []
  | inEntry :: inRest, outEntry :: outRest =>
    if equalsData inEntry.1 outEntry.1 then
      if equalsData inEntry.1 programmableCs then
        if equalsData (mapData inRest) (mapData outRest) then
          subtractTokens (unMapData inEntry.2) (unMapData outEntry.2)
        else pError
      else if equalsData inEntry.2 outEntry.2 then valueEqualsDeltaCurrencySymbol programmableCs inRest outRest
      else pError
    else if equalsData inEntry.2 outEntry.2 then []
    else pError

@[onchain] def accumulateProgOutputTokens (tokens : Merge) (programmableCs credential : Data) :
    List Data → Pairs
  | [] => []
  | output :: rest =>
    let outputFields := fields output
    if equalsData (first (headList outputFields)) credential then
      tokens (tokensOf programmableCs (unMapData (headList (tailList outputFields))))
        (accumulateProgOutputTokens tokens programmableCs credential rest)
    else accumulateProgOutputTokens tokens programmableCs credential rest

/-- Walk the (relative) seized input indices, pairing each programmable input with the next
programmable output, then check the outputs hold the accumulated delta plus the mint. -/
@[onchain] noncomputable def processThirdPartyTransfer (tokens : Merge) (programmableCs credential : Data)
    (mintedTokens : Pairs) (inputs outputs : List Data) (delta : Pairs) : List Data → Bool
  | [] =>
    if tokenPairsContain (accumulateProgOutputTokens tokens programmableCs credential outputs)
        (tokens delta mintedTokens) then true
    else pError
  | relativeIndex :: restIndices =>
    match dropData (unIData relativeIndex) inputs with
    | [] => pError
    | input :: afterInput =>
      let inputFields := fields (second input)
      let inputAddress := headList inputFields
      let inputCredential := first inputAddress
      if equalsData inputCredential credential then
        match outputs with
        | [] => pError
        | output :: outputsRest =>
          let outputFields := fields output
          if equalsData inputAddress (headList outputFields) then
            let inputRest := tailList inputFields
            let outputRest := tailList outputFields
            let inputMetadata := tailList inputRest
            let outputMetadata := tailList outputRest
            if equalsData (headList inputMetadata) (headList outputMetadata) then
              if equalsData (headList (tailList inputMetadata)) (headList (tailList outputMetadata)) then
                let entryDelta := valueEqualsDeltaCurrencySymbol programmableCs
                  (unMapData (headList inputRest)) (unMapData (headList outputRest))
                processThirdPartyTransfer tokens programmableCs credential mintedTokens afterInput
                  outputsRest (tokens entryDelta delta) restIndices
              else pError
            else pError
          else pError
      else if equalsInteger (constrTag inputCredential) 1 then
        processThirdPartyTransfer tokens programmableCs credential mintedTokens afterInput outputs delta
          restIndices
      else pError

/-- The `count`-th redeemer is the last spending one. -/
@[onchain] def enforceNSpendRedeemers (count : Int) (redeemers : Pairs) : Bool :=
  match dropPairs (subtractInteger count 1) redeemers with
  | [] => false
  | entry :: rest =>
    if equalsInteger (constrTag entry.1) 1 then
      match rest with
      | [] => true
      | next :: _ => if equalsInteger (constrTag next.1) 1 then false else true
    else false

/-! ## Validator -/

@[onchain] noncomputable def programmableLogicGlobal (protocolParamsCs context : Data) : Unit :=
  let parametersCs := unBData protocolParamsCs
  let contextFields := fields context
  let info := fields (headList contextFields)
  let afterInfo := tailList contextFields
  let inputs := unListData (headList info)
  let afterInputs := tailList info
  let referenceInputs := unListData (headList afterInputs)
  let afterReferenceInputs := tailList afterInputs
  let outputs := unListData (headList afterReferenceInputs)
  let atMint := tailList (tailList afterReferenceInputs)
  let mint := unMapData (headList atMint)
  let atWithdrawals := tailList (tailList atMint)
  let withdrawals := unMapData (headList atWithdrawals)
  let atSignatories := tailList (tailList atWithdrawals)
  let parameters := fields (findParams parametersCs referenceInputs)
  let directoryCs := unBData (headList parameters)
  let progLogicCred := headList (tailList parameters)
  let redeemer := unConstrData (headList afterInfo)
  let redeemerFields := redeemer.2
  if equalsInteger redeemer.1 0 then
    -- TransferAct transferProofs mintProofs
    let cachedTransferScript := match withdrawals with
      | [] => pError
      | entry :: _ => entry.1
    let union := currencyUnion tokenUnion
    let inputValue :=
      valueFromCred union progLogicCred (unListData (headList atSignatories)) withdrawals [] inputs
    let programmableValue := reversePairs []
      (checkTransferLogic directoryCs referenceInputs withdrawals (unListData (headList redeemerFields))
        cachedTransferScript [] inputValue)
    let expected := match mint with
      | [] => programmableValue
      | _ :: _ =>
        union programmableValue (reversePairs []
          (checkMintLogic directoryCs referenceInputs withdrawals
            (unListData (headList (tailList redeemerFields))) [] mint))
    if equalsInteger (constrTag (headList (tailList afterInfo))) 2 then
      if outputsContainExpectedValueAtCred union progLogicCred outputs expected then () else pError
    else pError
  else if equalsInteger redeemer.1 1 then
    -- SeizeAct directoryNodeIdx inputIdxs outputsStartIdx lengthInputIdxs
    let afterNodeIndex := tailList redeemerFields
    let inputIndices := unListData (headList afterNodeIndex)
    let afterInputIndices := tailList afterNodeIndex
    let indexCount := unIData (headList (tailList afterInputIndices))
    let remainingOutputs := dropData (unIData (headList afterInputIndices)) outputs
    let nodeOutput := second (elementAt (unIData (headList redeemerFields)) referenceInputs)
    let node := directoryNode nodeOutput
    let programmableCs := bData node.key
    let issuerLogic := node.issuerLogicScript
    let mintedTokens := tokensOf programmableCs mint
    if processThirdPartyTransfer tokenUnion programmableCs progLogicCred mintedTokens inputs remainingOutputs []
        inputIndices then
      if isInvoked issuerLogic withdrawals then
        if hasCsFirstNonAda directoryCs (second nodeOutput) then
          if enforceNSpendRedeemers indexCount (unMapData (headList (tailList atSignatories))) then
            if equalsInteger (lengthData 0 inputIndices) indexCount then () else pError
          else pError
        else pError
      else pError
    else pError
  else pError

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def script := compile! programmableLogicGlobal

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def scriptSize := compile! programmableLogicGlobal

end Test.Comparison.Cross.ProgrammableLogicGlobal
