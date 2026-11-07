import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.ValueLookup

open Moist.Plutus (ByteString AssocMap Data)
open Moist.Onchain (PlutusData)
open Moist.Onchain.Prelude

/-! Quantity of `token` under `policy` in a value-shaped nested map, or 0. -/

@[onchain] def valueLookup (value policy token : Data) : Int :=
  let value : AssocMap ByteString (AssocMap ByteString Int) := PlutusData.unsafeFromData value
  match Moist.Onchain.AssocMap.lookup (unBData policy) value with
  | none => 0
  | some tokens =>
    match Moist.Onchain.AssocMap.lookup (unBData token) tokens with
    | none => 0
    | some quantity => quantity

set_option maxRecDepth 10000 in
def script := compile! valueLookup

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! valueLookup

end Test.Comparison.Edge.ValueLookup
