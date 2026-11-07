import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.Horner

open Moist.Plutus (Data)
open Moist.Onchain.Prelude

/-! Value at `x` of the polynomial whose coefficients are listed from the highest degree down. -/

@[onchain] def hornerFrom (x accumulator : Int) : List Data → Int
  | [] => accumulator
  | coefficient :: rest => hornerFrom x (addInteger (multiplyInteger accumulator x) (unIData coefficient)) rest

@[onchain] def horner (coefficients x : Data) : Int :=
  hornerFrom (unIData x) 0 (unListData coefficients)

set_option maxRecDepth 10000 in
def script := compile! horner

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! horner

end Test.Comparison.Edge.Horner
