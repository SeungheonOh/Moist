import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude

/-! # Recursion Tests

Tests for recursive function compilation via WellFounded.fix.
-/

-- ## Basic recursion: factorial

@[onchain]
def factorial (n : Int) : Int :=
  ifThenElse (equalsInteger n 0) 1 (multiplyInteger n (factorial (subtractInteger n 1)))
decreasing_by sorry

def factorialUPLC : Term := compile! factorial

#eval IO.println s!"factorial:\n{prettyTerm factorialUPLC}"

-- ## Recursion: sum from 1 to n

@[onchain]
def sumTo (n : Int) : Int :=
  ifThenElse (lessThanEqInteger n 0) 0 (addInteger n (sumTo (subtractInteger n 1)))
decreasing_by sorry

def sumToUPLC : Term := compile! sumTo

#eval IO.println s!"sumTo:\n{prettyTerm sumToUPLC}"

-- ## Recursion: power function

@[onchain]
def power (base : Int) (exp : Int) : Int :=
  ifThenElse (equalsInteger exp 0) 1 (multiplyInteger base (power base (subtractInteger exp 1)))
decreasing_by sorry

def powerUPLC : Term := compile! power

#eval IO.println s!"power:\n{prettyTerm powerUPLC}"
