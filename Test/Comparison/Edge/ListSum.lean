import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.ListSum

open Moist.Plutus (Data)
open Moist.Onchain.Prelude

/-! Sum of a list of integers. -/

@[onchain] def sumFrom (accumulator : Int) : List Data → Int
  | [] => accumulator
  | value :: rest => sumFrom (addInteger accumulator (unIData value)) rest

@[onchain] def listSum (values : Data) : Int := sumFrom 0 (unListData values)

set_option maxRecDepth 10000 in
def script := compile! listSum

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! listSum

end Test.Comparison.Edge.ListSum
