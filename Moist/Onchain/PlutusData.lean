import Moist.Plutus.Types
import Moist.Onchain.Prelude

namespace Moist.Onchain

open Moist.Plutus (Data ByteString)
open Moist.Onchain.Prelude (equalsData)

class PlutusData (α : Type) where
  private mk ::
  toData : α → Data
  fromData : Data → Option α
  unsafeFromData : Data → α

def dataBeq [PlutusData α] (a b : α) : Bool :=
  equalsData (PlutusData.toData a) (PlutusData.toData b)

instance : PlutusData Data where
  toData d := d
  fromData d := some d
  unsafeFromData d := d

instance : PlutusData Int where
  toData := Data.I
  fromData
    | .I n => some n
    | _ => none
  unsafeFromData
    | .I n => n
    | _ => panic! "PlutusData.unsafeFromData: expected Data.I"

instance : PlutusData ByteString where
  toData := Data.B
  fromData
    | .B bs => some bs
    | _ => none
  unsafeFromData
    | .B bs => bs
    | _ => panic! "PlutusData.unsafeFromData: expected Data.B"

instance [PlutusData k] [PlutusData v] : PlutusData (Moist.Plutus.AssocMap k v) where
  toData m := Data.Map (m.toList.map fun (a, b) => (PlutusData.toData a, PlutusData.toData b))
  fromData
    | .Map ps => some ⟨ps.map fun (a, b) => (PlutusData.unsafeFromData a, PlutusData.unsafeFromData b)⟩
    | _ => none
  unsafeFromData
    | .Map ps => ⟨ps.map fun (a, b) => (PlutusData.unsafeFromData a, PlutusData.unsafeFromData b)⟩
    | _ => panic! "PlutusData.unsafeFromData: expected Data.Map"

instance [PlutusData α] : PlutusData (List α) where
  toData xs := Data.List (xs.map PlutusData.toData)
  fromData
    | .List xs => some (xs.map PlutusData.unsafeFromData)
    | _ => none
  unsafeFromData
    | .List xs => xs.map PlutusData.unsafeFromData
    | _ => panic! "PlutusData.unsafeFromData: expected Data.List"

end Moist.Onchain
