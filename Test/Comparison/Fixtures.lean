import Moist.Plutus.Types

namespace Test.Comparison.Fixtures

open Moist.Plutus (Data ByteString)

structure Scenario where
  validator : String
  name : String
  arguments : List Data
  accepts : Bool := true
  reference : Option (Nat × Nat × Nat × Nat) := none

def nothingData : Data := .Constr 1 []
def unitData : Data := .Constr 0 []
def bytes (value : String) : Data := .B value.toUTF8
def repeated (value : UInt8) : Data := .B ⟨Array.replicate 28 value⟩
def reference (identifier : Data) : Data := .Constr 0 [identifier, .I 0]
def credential (script : Bool) (hash : Data) : Data := .Constr (if script then 1 else 0) [hash]
def address (script : Bool) (hash : Data) : Data := .Constr 0 [credential script hash, nothingData]
def ada (amount : Int) : Data := .Map [(bytes "", .Map [(bytes "", .I amount)])]
def output (addr value : Data) (datum : Data := .Constr 0 []) : Data :=
  .Constr 0 [addr, value, datum, nothingData]
def input (ref resolved : Data) : Data := .Constr 0 [ref, resolved]
def bound (extended : Data) (inclusive : Bool := true) : Data :=
  .Constr 0 [extended, .Constr (if inclusive then 1 else 0) []]
def alwaysRange : Data := .Constr 0 [bound (.Constr 0 []), bound (.Constr 2 [])]
def atTime (timestamp : Int) (inclusive : Bool := true) : Data :=
  .Constr 0 [bound (.Constr 1 [.I timestamp]) inclusive, bound (.Constr 1 [.I (timestamp + 100)])]

def context (scriptInfo : Data) (inputs outputs : List Data := [])
    (range : Data := alwaysRange) (signers : List Data := []) (fee : Int := 0)
    (redeemer : Data := unitData) (certificates : List Data := [])
    (redeemers : List (Data × Data) := []) : Data :=
  .Constr 0 [.Constr 0 [.List inputs, .List [], .List outputs, .I fee, .Map [],
    .List certificates, .Map [], range, .List signers, .Map redeemers, .Map [],
    .B ⟨#[0xde, 0xad, 0xbe, 0xef]⟩, .Map [], .List [], nothingData, nothingData],
    redeemer, scriptInfo]

def nftCurrency := bytes "aabbccddaabbccddaabbccddaabbccddaabbccddaabbccddaabbccdd"
def nftToken := bytes "HotNFT"
def otherCurrency := bytes "11223344112233441122334411223344112233441122334411223344"
def otherToken := bytes "OtherNFT"
def voter : Data := .Constr 0 [credential true nftCurrency]
def voterPkh := bytes "1122334411223344112233441122334411223344112233441122334455667788"

def tokenValue (currency token : Data) (quantity : Int := 1) (amount : Int := 5000000) : Data :=
  .Map [(bytes "", .Map [(bytes "", .I amount)]), (currency, .Map [(token, .I quantity)])]

def votingContext (entries : List (Bool × Data × UInt8)) (voting : Bool := true) : Data :=
  let info := if voting then .Constr 4 [voter] else .Constr 0 [nftCurrency]
  let inputs := entries.map fun (script, value, identifier) =>
    input (reference (.B ⟨#[identifier, 0]⟩)) (output (address script (if script then nftCurrency else voterPkh)) value)
  let spending := entries.filterMap fun (script, _, identifier) =>
    if script then some (.Constr 1 [reference (.B ⟨#[identifier, 0]⟩)], unitData) else none
  context info inputs [] (redeemers := (.Constr 4 [voter], unitData) :: spending)

def votingScenarios : List Scenario :=
  let nft := tokenValue nftCurrency nftToken
  let base := ada 10000000
  let make := fun name entries accepts reference =>
    Scenario.mk "Voting" name [nftCurrency, nftToken, votingContext entries] accepts reference
  [make "nft in script input" [(true, nft, 0xaa)] true (some (12244560,30755,11461062,27727)),
   make "nft in pubkey input" [(false, nft, 0xaa)] true (some (12244560,30755,11461062,27727)),
   make "nft among multiple inputs" [(false,base,0xcc),(false,nft,0xbb),(false,base,0xaa)] true
     (some (17129982,44166,15661615,37374)),
   make "nft with other tokens" [(false,.Map [(bytes "",.Map [(bytes "",.I 10000000)]),
     (nftCurrency,.Map [(nftToken,.I 1)]),(otherCurrency,.Map [(otherToken,.I 1)])],0xaa)] true
     (some (12244560,30755,11461062,27727)),
   make "no nft" [(false,base,0xaa)] false none,
   make "wrong currency" [(false,tokenValue otherCurrency otherToken,0xaa)] false none,
   make "wrong token" [(false,tokenValue nftCurrency otherToken,0xaa)] false none,
   make "empty inputs" [] false none,
   make "multiple inputs no nft" [(false,tokenValue otherCurrency otherToken,0xcc),
     (false,base,0xbb),(false,base,0xaa)] false none,
   ⟨"Voting","wrong purpose",[nftCurrency,nftToken,votingContext [(false,nft,0xaa)] false],false,none⟩] ++
  [-1,0,2,100].map (fun quantity => make s!"quantity {quantity}"
    [(false,tokenValue nftCurrency nftToken quantity,0xaa)] false none)

def expiration : Int := 1700000000000
def certCredential := credential true (bytes "aabbccdd")
def abstain : Data := .Constr 1 [.Constr 1 []]
def certificate (tag : Int) (delegatee : Data := abstain) : Data :=
  if tag == 0 || tag == 1 then .Constr tag [certCredential,.Constr 0 [.I 2000000]]
  else if tag == 2 then .Constr tag [certCredential,delegatee]
  else if tag == 3 then .Constr tag [certCredential,delegatee,.I 2000000]
  else if tag == 5 || tag == 10 then .Constr tag [certCredential]
  else if tag == 7 then .Constr tag [bytes "11223344",bytes "11223344"]
  else if tag == 8 then .Constr tag [bytes "11223344",.I 100]
  else if tag == 9 then .Constr tag [certCredential,certCredential]
  else .Constr tag [certCredential,.I 100]
def certContext (cert : Data) (range : Data := alwaysRange) : Data :=
  context (.Constr 3 [.I 0,cert]) (range := range) (certificates := [cert])
    (redeemers := [(.Constr 3 [.I 0,cert],unitData)])

def certifyingScenarios : List Scenario :=
  let make := fun name cert range accepts reference =>
    Scenario.mk "Certifying" name [.I expiration,certContext cert range] accepts reference
  [make "register credential" (certificate 0) alwaysRange true (some (3281634,11753,3235577,11084)),
   make "unregister after expiration" (certificate 1)
     (.Constr 0 [bound (.Constr 1 [.I (expiration+1)]),bound (.Constr 1 [.I (expiration+100000)])])
     true (some (7886843,24094,8633363,26629)),
   make "delegate to abstain" (certificate 2) alwaysRange true (some (5907816,18612,5528026,17948)),
   make "register+delegate to abstain" (certificate 3) alwaysRange true (some (6386093,19946,5832408,19050)),
   make "register no deposit" (.Constr 0 [certCredential,nothingData]) alwaysRange true none] ++
  ([-1,0,1].flatMap fun offset => [false,true].map fun inclusive =>
    make s!"unregister boundary {offset} inclusive={inclusive}" (certificate 1)
      (atTime (expiration+offset) inclusive) (if inclusive then offset > 0 else offset >= 0) none) ++
  [make "unregister negative infinity" (certificate 1) alwaysRange false none,
   make "unregister positive infinity" (certificate 1)
     (.Constr 0 [bound (.Constr 2 []),bound (.Constr 2 [])]) true none] ++
  ([2,3].flatMap fun tag =>
    [.Constr 1 [.Constr 2 []],.Constr 0 [bytes "11223344"],
     .Constr 1 [.Constr 0 [credential false (bytes "11223344")]],
     .Constr 2 [bytes "11223344",.Constr 1 []]].zipIdx |>.map fun (delegatee,index) =>
      make s!"invalid delegate {tag}/{index}" (certificate tag delegatee) alwaysRange false none) ++
  ([4,5,6,7,8,9,10].map fun tag => make s!"unsupported certificate {tag}" (certificate tag) alwaysRange false none) ++
  [⟨"Certifying","wrong purpose",[.I expiration,context (.Constr 0 [nftCurrency])],false,none⟩]

def beneficiary := repeated 0x01
def contractAddress := address true (repeated 0x50)
def ownReference := reference (repeated 0xaa)
def beneficiaryReference := reference (repeated 0xbb)
def vestingDatum (start : Int := 1000) (duration : Int := 10000) (amount : Int := 100000000) : Data :=
  .Constr 0 [beneficiary,.I start,.I duration,.I amount]

def releaseContext (datum : Data) (remaining declared timestamp : Int) (continuing : Bool)
    (fee : Int := 200000) (signer : Data := beneficiary) (outputDelta : Int := 0)
    (continuationDatum : Option Data := none) (split : Bool := false) : Data :=
  let redeemer := .Constr 0 [.I declared]
  let total := declared + 5000000 - fee + outputDelta
  let amounts := if split then [total / 2,total - total / 2] else [total]
  let outputs := amounts.map (fun amount => output (address false beneficiary) (ada amount))
  let outputs := outputs ++ if continuing then
    [output contractAddress (ada (remaining-declared)) (.Constr 2 [continuationDatum.getD datum])] else []
  context (.Constr 1 [ownReference,.Constr 0 [datum]])
    [input beneficiaryReference (output (address false beneficiary) (ada 5000000)),
     input ownReference (output contractAddress (ada remaining) (.Constr 2 [datum]))]
    outputs (atTime timestamp) [signer] fee redeemer
    (redeemers := [(.Constr 1 [ownReference],redeemer)])

def vestingScenarios : List Scenario :=
  let make := fun name datum remaining declared timestamp continuing fee split reference =>
    Scenario.mk "Vesting" name [releaseContext datum remaining declared timestamp continuing fee (split := split)] true (some reference)
  let full := (38909388,112264,35340687,101467)
  let partialCost := (66088455,183674,56291830,157014)
  [make "full withdrawal after vesting" vestingDatum 100000000 100000000 11001 false 200000 false full,
   make "partial withdrawal midpoint" vestingDatum 100000000 50000000 6000 true 200000 false partialCost,
   make "second partial withdrawal" vestingDatum 50000000 20000000 8000 true 200000 false partialCost,
   make "full withdrawal at end" vestingDatum 100000000 100000000 11000 false 200000 false (39425890,113469,35857189,102672),
   make "small withdrawal early" vestingDatum 100000000 10000 1001 true 200000 false partialCost,
   make "third partial drains" vestingDatum 30000000 30000000 11001 false 200000 false full,
   make "odd division partial" (vestingDatum 0 7 100) 100 42 3 true 200000 false partialCost,
   make "multi beneficiary outputs" vestingDatum 100000000 100000000 11001 false 200000 true (43484191,126070,39313502,113109),
   make "zero fee" vestingDatum 100000000 100000000 11001 false 0 false full,
   make "quarter vested" vestingDatum 100000000 25000000 3500 true 200000 false partialCost,
   make "ninety percent" vestingDatum 100000000 90000000 10000 true 200000 false partialCost] ++
  [("not signed",releaseContext vestingDatum 100000000 100000000 11001 false (signer := repeated 0x02)),
   ("wrong amount",releaseContext vestingDatum 100000000 50000001 6000 true),
   ("under claiming",releaseContext vestingDatum 100000000 49999999 6000 true),
   ("wrong beneficiary output",releaseContext vestingDatum 100000000 100000000 11001 false (outputDelta := 1)),
   ("partial wrong datum",releaseContext vestingDatum 100000000 50000000 6000 true (continuationDatum := some (vestingDatum 1001))),
   ("partial no output",releaseContext vestingDatum 100000000 50000000 6000 false),
   ("before vesting",releaseContext vestingDatum 100000000 1 999 true),
   ("odd division off by one",releaseContext (vestingDatum 0 7 100) 100 43 3 true),
   ("zero duration division",releaseContext (vestingDatum 1000 0) 100000000 0 1000 true)].map
    (fun (name,context) => ⟨"Vesting",name,[context],false,none⟩)

def scenarios := votingScenarios ++ certifyingScenarios ++ vestingScenarios

def replaceField (value : Data) (index : Nat) (replacement : Data) : Data :=
  match value with
  | .Constr tag values => .Constr tag (values.set index replacement)
  | _ => value

def replaceInfoField (value : Data) (index : Nat) (replacement : Data) : Data :=
  match value with
  | .Constr tag (info :: rest) => .Constr tag (replaceField info index replacement :: rest)
  | _ => value

def generatedVoting : List Scenario :=
  (List.range 9).flatMap fun count =>
    (List.range (count+1)).flatMap fun position =>
      [-1,0,1,2].map fun quantity =>
        let entries := (List.range count).map fun index =>
          (false,if index == position then tokenValue nftCurrency nftToken quantity else ada 5000000,index.toUInt8)
        ⟨"Voting",s!"generated {count}/{position}/{quantity}",
          [nftCurrency,nftToken,votingContext entries],position < count && quantity == 1,none⟩

def generatedVesting : List Scenario :=
  [-1,0,1,3,7,8].flatMap fun timestamp =>
    [0,42,100].flatMap fun released =>
      [-1,0,1].map fun delta =>
        let vested := if timestamp < 0 then 0 else if timestamp > 7 then 100 else 100*timestamp/7
        let declared := vested-released+delta
        ⟨"Vesting",s!"generated {timestamp}/{released}/{delta}",
          [releaseContext (vestingDatum 0 7 100) (100-released) declared timestamp true],delta == 0,none⟩

def vestingEdges : List Scenario :=
  let full := releaseContext vestingDatum 100000000 100000000 11001 false
  let partialContext := releaseContext vestingDatum 100000000 50000000 6000 true
  let validOutput := output contractAddress (ada 50000000) (.Constr 2 [vestingDatum])
  let beneOutput := output (address false beneficiary) (ada 54800000)
  let invalid := fun name value => Scenario.mk "Vesting" name [value] false none
  [invalid "wrong purpose" (replaceField full 2 (.Constr 4 [voter])),
   invalid "missing spending datum" (replaceField full 2 (.Constr 1 [ownReference,nothingData])),
   invalid "missing own input" (replaceInfoField full 0 (.List [])),
   invalid "two continuing outputs" (replaceInfoField partialContext 2 (.List [beneOutput,validOutput,validOutput])),
   invalid "continuing hashed datum" (replaceInfoField partialContext 2 (.List [beneOutput,
     output contractAddress (ada 50000000) (.Constr 1 [repeated 0x03])])),
   invalid "continuing no datum" (replaceInfoField partialContext 2 (.List [beneOutput,
     output contractAddress (ada 50000000)])),
   invalid "wrong continuing address" (replaceInfoField partialContext 2 (.List [beneOutput,
     output (address true (repeated 0x51)) (ada 50000000) (.Constr 2 [vestingDatum])])),
   invalid "negative infinity claim" (replaceInfoField full 7 alwaysRange),
   invalid "positive infinity claim" (replaceInfoField full 7
     (.Constr 0 [bound (.Constr 2 []),bound (.Constr 2 [])])),
   ⟨"Vesting","zero claim before start",[releaseContext vestingDatum 100000000 0 999 true],true,none⟩,
   ⟨"Vesting","exclusive lower bound ignored",[replaceInfoField partialContext 7 (atTime 6000 false)],true,none⟩,
   ⟨"Vesting","continuation value unchecked",[replaceInfoField partialContext 2 (.List [beneOutput,
     output contractAddress (ada 1) (.Constr 2 [vestingDatum])])],true,none⟩]

def validationScenarios := scenarios ++ generatedVoting ++ generatedVesting ++ vestingEdges

end Test.Comparison.Fixtures
