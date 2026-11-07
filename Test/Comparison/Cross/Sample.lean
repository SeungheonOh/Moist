import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Cross.Sample

open Moist.Onchain.Prelude

/-! Port of `Sample.SamplePlinth.netWithdraw`: the net amount of a nested withdrawal. -/

@[plutus_data]
inductive Withdraw where
  | amount : Int → Withdraw
  | joint : Withdraw → Withdraw → Withdraw
  | deduct : Int → Withdraw → Withdraw

@[onchain] def netWithdraw : Withdraw → Int
  | .amount quantity => quantity
  | .joint left right => addInteger (netWithdraw left) (netWithdraw right)
  | .deduct quantity source => subtractInteger (netWithdraw source) quantity

set_option maxRecDepth 10000 in
def script := compile! netWithdraw

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! netWithdraw

end Test.Comparison.Cross.Sample
