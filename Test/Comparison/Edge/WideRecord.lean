import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.WideRecord

open Moist.Plutus (ByteString)
open Moist.Onchain.Prelude

/-! Sum of the first, middle and last fields of a twelve-field record. -/

@[plutus_data]
structure Wide where
  f0 : Int
  f1 : Int
  f2 : Int
  f3 : Int
  f4 : Int
  f5 : Int
  f6 : Int
  f7 : Int
  f8 : Int
  f9 : Int
  f10 : Int
  f11 : Int

@[onchain] def wideRecord (record : Wide) : Int :=
  addInteger (addInteger record.f0 record.f6) record.f11

set_option maxRecDepth 10000 in
def script := compile! wideRecord

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! wideRecord

end Test.Comparison.Edge.WideRecord
