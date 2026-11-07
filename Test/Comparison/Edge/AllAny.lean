import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.AllAny

open Moist.Plutus (ByteString Data)
open Moist.Onchain (PlutusData)
open Moist.Onchain.Prelude

/-! 1 when every item has `low < high` and some item carries `target`, else 0. -/

@[plutus_data]
structure Item where
  low : Int
  high : Int
  tag : ByteString

@[onchain] def allOrdered : List Data → Bool
  | [] => true
  | item :: rest =>
    let item : Item := PlutusData.unsafeFromData item
    if lessThanInteger item.low item.high then allOrdered rest else false

@[onchain] def anyTagged (target : ByteString) : List Data → Bool
  | [] => false
  | item :: rest =>
    let item : Item := PlutusData.unsafeFromData item
    if equalsByteString item.tag target then true else anyTagged target rest

@[onchain] def allAny (items target : Data) : Int :=
  let items := unListData items
  if allOrdered items then (if anyTagged (unBData target) items then 1 else 0) else 0

set_option maxRecDepth 10000 in
def script := compile! allAny

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! allAny

end Test.Comparison.Edge.AllAny
