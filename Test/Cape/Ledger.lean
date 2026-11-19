import Moist.Onchain
import Moist.Cardano.V3

namespace Test.Cape

open Moist.Onchain (PlutusData dataBeq)
open Moist.Plutus (ByteString Data)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

@[onchain] def signedBy (key : PubKeyHash) : List PubKeyHash → Bool
  | [] => false
  | signer :: rest => if equalsByteString signer key then true else signedBy key rest

@[onchain] def signedByAddress (address : Address) (signers : List PubKeyHash) : Bool :=
  match address.credential with
  | .pubKeyCredential key => signedBy key signers
  | .scriptCredential _ => false

@[onchain] def noOtherInput (credential : Credential) : List TxInInfo → Bool
  | [] => true
  | input :: rest =>
    if dataBeq input.resolved.address.credential credential then false else noOtherInput credential rest

@[onchain] def uniqueOwnOutput (reference : TxOutRef) : List TxInInfo → Option TxOut
  | [] => none
  | input :: rest =>
    if dataBeq input.outRef reference then
      let own := input.resolved
      if rest.isEmpty || noOtherInput own.address.credential rest then some own else none
    else match uniqueOwnOutput reference rest with
      | none => none
      | some own => if dataBeq input.resolved.address.credential own.address.credential then none else some own

@[onchain] noncomputable def finiteTime : Extended → Int
  | .finite time => time
  | _ => pError

@[onchain] noncomputable def earliest (bound : LowerBound) : Int :=
  let ⟨extended, closure⟩ := bound
  let time := finiteTime extended
  match closure with
  | .inclusive => time
  | .exclusive => addInteger time 1

@[onchain] noncomputable def latest (bound : UpperBound) : Int :=
  let ⟨extended, closure⟩ := bound
  let time := finiteTime extended
  match closure with
  | .inclusive => time
  | .exclusive => subtractInteger time 1

@[onchain] def lookupBytes (key : ByteString) (missing : α) (found : Data → α) : List (Data × Data) → α
  | [] => missing
  | entry :: rest =>
    if equalsByteString key (unBData entry.1) then found entry.2 else lookupBytes key missing found rest

@[onchain] def quantity (value : Value) (policy : CurrencySymbol) (token : TokenName) : Int :=
  lookupBytes policy 0 (fun tokens => lookupBytes token 0 unIData (unMapData tokens))
    (unMapData (PlutusData.toData value))

end Test.Cape
