import Moist.Onchain
import Moist.Cardano.V3

namespace Test.Cape

open Moist.Onchain (dataBeq)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

@[onchain] def signedBy (key : PubKeyHash) : List PubKeyHash → Bool
  | [] => false
  | signer :: rest => if equalsByteString signer key then true else signedBy key rest

@[onchain] def signedByAddress (address : Address) (signers : List PubKeyHash) : Bool :=
  match address.credential with
  | .pubKeyCredential key => signedBy key signers
  | .scriptCredential _ => false

@[onchain] noncomputable def ownOutput (reference : TxOutRef) : List TxInInfo → TxOut
  | [] => pError
  | input :: rest =>
    if dataBeq input.outRef reference then input.resolved else ownOutput reference rest

@[onchain] def countInputs (credential : Credential) : List TxInInfo → Int
  | [] => 0
  | input :: rest =>
    let count := countInputs credential rest
    if dataBeq input.resolved.address.credential credential then addInteger count 1 else count

@[onchain] noncomputable def finiteTime : Extended → Int
  | .finite time => time
  | _ => pError

@[onchain] noncomputable def earliest (bound : LowerBound) : Int :=
  let time := finiteTime bound.bound
  match bound.closure with
  | .inclusive => time
  | .exclusive => addInteger time 1

@[onchain] noncomputable def latest (bound : UpperBound) : Int :=
  let time := finiteTime bound.bound
  match bound.closure with
  | .inclusive => time
  | .exclusive => subtractInteger time 1

@[onchain] def quantity (value : Value) (policy : CurrencySymbol) (token : TokenName) : Int :=
  match Moist.Onchain.AssocMap.lookup policy value with
  | none => 0
  | some tokens =>
    match Moist.Onchain.AssocMap.lookup token tokens with
    | none => 0
    | some amount => amount

end Test.Cape
