import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Comparison.Edge.EnumDispatch

open Moist.Plutus (ByteString)
open Moist.Onchain.Prelude

/-! Evaluate one arithmetic operation. -/

@[plutus_data]
inductive Op where
  | add : Int → Int → Op
  | sub : Int → Int → Op
  | mul : Int → Int → Op
  | neg : Int → Op
  | mulAdd : Int → Int → Int → Op
  | div : Int → Int → Op
  | mod : Int → Int → Op
  | clamp : Int → Int → Int → Op

@[onchain] def enumDispatch (op : Op) : Int :=
  match op with
  | .add a b => addInteger a b
  | .sub a b => subtractInteger a b
  | .mul a b => multiplyInteger a b
  | .neg a => subtractInteger 0 a
  | .mulAdd a b c => addInteger (multiplyInteger a b) c
  | .div a b => divideInteger a b
  | .mod a b => modInteger a b
  | .clamp x low high =>
    if lessThanInteger x low then low
    else if lessThanInteger high x then high
    else x

set_option maxRecDepth 10000 in
def script := compile! enumDispatch

set_option moist.optimize.shareBuiltinStates true in
set_option moist.optimize.poolConstants true in
set_option maxRecDepth 10000 in
def scriptSize := compile! enumDispatch

end Test.Comparison.Edge.EnumDispatch
