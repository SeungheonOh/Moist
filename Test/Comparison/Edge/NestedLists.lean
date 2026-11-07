import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.NestedLists

open Moist.Plutus (Data)
open Moist.Onchain.Prelude

/-! Total length of the inner lists whose first element is even. -/

@[onchain] def lengthOf : List Data → Int
  | [] => 0
  | _ :: rest => addInteger 1 (lengthOf rest)

@[onchain] def evenHeadedTotal (total : Int) : List Data → Int
  | [] => total
  | inner :: rest =>
    let inner := unListData inner
    match inner with
    | [] => evenHeadedTotal total rest
    | first :: _ =>
      if equalsInteger (modInteger (unIData first) 2) 0 then
        evenHeadedTotal (addInteger total (lengthOf inner)) rest
      else evenHeadedTotal total rest

@[onchain] def nestedLists (lists : Data) : Int := evenHeadedTotal 0 (unListData lists)

set_option maxRecDepth 10000 in
def script := compile! nestedLists

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! nestedLists

end Test.Comparison.Edge.NestedLists
