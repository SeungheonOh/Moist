import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude

namespace Test.Debug

@[plutus_data]
inductive Foo where
  | foo : Int → Int → Int → Int → Foo

def Plus (x y : Int) : Int := addInteger x y

@[onchain]
def factorial (n : Int) : Int :=
  ifThenElse (equalsInteger n 0) 1 (multiplyInteger n (factorial (subtractInteger n 1)))
decreasing_by sorry

@[onchain]
def aaa (x : Foo) : Int :=
  match x with
  | .foo a _ _ d =>
    let x := factorial a
    x + a + d + x

def aaaa : Term := compile! aaa

#show_raw_expr aaa
#show_optimized_mir aaa

#eval compile! aaa

end Test.Debug
