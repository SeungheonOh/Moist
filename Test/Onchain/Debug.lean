import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude

namespace Test.Debug

@[plutus_data]
inductive Foo where
  | foo : Int → Int → Int → Int → Int → Int → Int → Foo

def Plus (x y : Int) : Int := addInteger x y

@[onchain]
def factorial (n : Int) : Int :=
  ifThenElse (equalsInteger n 0) 1 (n * (factorial (n - 1)))
decreasing_by sorry

@[onchain]
def aaa (x : Foo) : Int :=
  match x with
  | .foo a b c d e f g =>
    a + g + e + c

@[onchain]
def bbb : Foo := Foo.foo 1 2 3 4 5 6 7

def aaaa : Term := compile! aaa

#show_optimized_mir aaa

#show_mir aaa

#show_optimized_mir bbb

#eval compile! aaa

end Test.Debug
