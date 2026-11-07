import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.GuardOrder

open Moist.Plutus (Data)
open Moist.Onchain.Prelude

/-! The sum of `values`, provided `flag` is 1; fails otherwise. -/

@[onchain] def sumFrom (accumulator : Int) : List Data → Int
  | [] => accumulator
  | value :: rest => sumFrom (addInteger accumulator (unIData value)) rest

@[onchain] noncomputable def guardOrder (values flag : Data) : Int :=
  let total := sumFrom 0 (unListData values)
  if equalsInteger (unIData flag) 1 then total else pError

set_option maxRecDepth 10000 in
def script := compile! guardOrder

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! guardOrder

end Test.Comparison.Edge.GuardOrder
