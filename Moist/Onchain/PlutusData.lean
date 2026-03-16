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

end Moist.Onchain
