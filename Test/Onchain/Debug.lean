import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude
import Moist.Plutus.Eval

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude
open Moist.Plutus.Eval
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
def bbb : Foo := Foo.foo 1 2 3 4 5 6 42

def aaaa : Term := compile! aaa

def bbbb : Term := compile! bbb

@[plutus_data]
structure Bar where
  (x : Int)
  (y : Int)
  (z : Int)

@[onchain]
def ccc : Bar := { x := 1, y := 2, z := 3 }

@[plutus_data]
inductive Baz where
  | baz : Int → Int → Int → Baz
  | bar : Int -> Int → Baz
  | aaa : Int -> Int -> Baz
  | foo : Int → Baz
  | qux : Baz

@[onchain]
def ddd (x : Baz) : Int :=
  match x with
    | Baz.baz a b c => a + b + c
    | Baz.bar a b => a + b
    | Baz.aaa a b => a + b
    | Baz.foo a => a + 1
    | Baz.qux => 0

def dddd : Term := compile! ddd

@[onchain]
def eee : Baz := Baz.bar 1 2

def eeee : Term := compile! eee

#show_optimized_mir ddd

#show_mir ddd

#eval ddd.compile!

#eval ((compile! ddd).Apply eeee).evaluatePretty

#evaluatePrettyTerm ddd (Baz.foo 2)

#show_optimized_mir ccc

#eval (aaaa.Apply bbbb).evaluatePretty

#show_mir bbb

#show_optimized_mir aaa
