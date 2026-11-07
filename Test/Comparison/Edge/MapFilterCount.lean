import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.MapFilterCount

open Moist.Plutus (Data)
open Moist.Onchain.Prelude

/-! How many values `x` have `2x + 1 > threshold`, written as a map, a filter and a length. -/

@[onchain] def affine : List Data → List Int
  | [] => []
  | value :: rest => addInteger (multiplyInteger 2 (unIData value)) 1 :: affine rest

@[onchain] def keepAbove (threshold : Int) : List Int → List Int
  | [] => []
  | value :: rest =>
    if lessThanInteger threshold value then value :: keepAbove threshold rest
    else keepAbove threshold rest

@[onchain] def lengthOf : List Int → Int
  | [] => 0
  | _ :: rest => addInteger 1 (lengthOf rest)

@[onchain] def mapFilterCount (values threshold : Data) : Int :=
  lengthOf (keepAbove (unIData threshold) (affine (unListData values)))

set_option maxRecDepth 10000 in
def script := compile! mapFilterCount

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! mapFilterCount

end Test.Comparison.Edge.MapFilterCount
