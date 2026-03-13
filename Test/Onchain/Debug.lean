import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude
import Moist.Plutus.Eval

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude
open Moist.Plutus.Eval
namespace Test.Debug

@[plutus_sop]
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

#evaluatePrettyTerm factorial (1 : Int)

#show_mir aaa
#show_beta_mir aaa
#show_optimized_mir aaa

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

@[plutus_data]
inductive SOPHi where
  | sophi : Int → SOPHi
  | sopbye : SOPHi
  | fooooo : Int → SOPHi

@[plutus_data]
inductive Maybe α where
  | none : Maybe α
  | some : α → Maybe α

@[onchain]
def fff : Int :=
  let bad (x : Maybe SOPHi) : Int :=
    match x with
    | Maybe.none => 0
    | Maybe.some (.sophi a) => a
    | _ => 42
  bad .none

@[onchain]
def ddd (x : Baz) : Int :=
  match x with
    | Baz.baz a b c => a + b + c
    | Baz.bar a b => a + b
    | Baz.aaa a b => a + b
    | Baz.foo a => a + 1
    | Baz.qux => 0

#show_mir ddd

#show_beta_mir ddd

#show_optimized_mir ddd

def dddd : Term := compile! ddd

@[plutus_data]
structure A where
  x : Int
  y : Int
  z : Int
  a : Int

@[onchain]
def testing (x : A) : Int := x.y + x.a

def testing2 (x : A) : Int :=
  match x with
    | { x, y, z, a } => y + a

@[onchain]
def eee : Baz := Baz.bar 1 2

def eeee : Term := compile! eee

#show_mir testing

#show_mir testing2

#show_opt_trace testing

#show_beta_mir testing

#show_beta_mir testing2

#show_optimized_mir testing

#show_optimized_mir testing2

#show_beta_mir testing

#evaluatePrettyTerm testing ({ x := 1, y := 2, z := 3, a := 4 } : A)

#evaluatePrettyTerm testing2 ({ x := 1, y := 2, z := 3, a := 4 } : A)

#eval ((compile! ddd).Apply eeee).evaluatePretty

#evaluatePrettyTerm (Baz.aaa 1 123)

#show_optimized_mir ccc

#eval (aaaa.Apply bbbb).evaluatePretty

#show_mir bbb

#show_optimized_mir aaa


/-
let anf_1001 = force (force sndPair)
let anf_1002 = force tailList
let anf_1003 = force headList
in
  λx_0.
    let pair_2 = unConstrData x_0
    in
      addInteger
        (unIData (anf_1003 (anf_1002 (anf_1001 pair_2))))
        (unIData (anf_1003 (anf_1002 (anf_1002 (anf_1002 (anf_1001 pair_2))))))
-/
