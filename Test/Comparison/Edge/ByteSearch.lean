import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.ByteSearch

open Moist.Plutus (ByteString Data)
open Moist.Onchain.Prelude

/-! Position of the first occurrence of `target`, or -1. -/

@[onchain] def indexFrom (target : ByteString) (index : Int) : List Data → Int
  | [] => -1
  | key :: rest =>
    if equalsByteString (unBData key) target then index else indexFrom target (addInteger index 1) rest

@[onchain] def byteSearch (keys target : Data) : Int :=
  indexFrom (unBData target) 0 (unListData keys)

set_option maxRecDepth 10000 in
def script := compile! byteSearch

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! byteSearch

end Test.Comparison.Edge.ByteSearch
