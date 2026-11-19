import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Ptah.Prelude

namespace Test.Cape

open Moist.Onchain.Prelude

@[onchain] def factorial (number : Int) : Int :=
  if lessThanInteger number 4 then
    if lessThanEqInteger number 1 then 1 else multiplyInteger number (subtractInteger number 1)
  else
    let outer := multiplyInteger number (subtractInteger number 3)
    multiplyInteger (multiplyInteger outer (addInteger outer 2))
      (factorial (subtractInteger number 4))
termination_by number.toNat
decreasing_by simp_all [lessThanInteger, subtractInteger]; omega

open Moist.Ptah

def factorialNaive : Term (PInteger → PInteger) :=
  plet (paddInteger # pconstant (-1 : Int)) fun predecessor =>
  plet (plessThanInteger # 0) fun positive =>
    pfix fun recur number =>
      pif (positive # number) (number * (recur # (predecessor # number))) 1

def fibonacciNaive : Term (PInteger → PInteger) :=
  plet (paddInteger # pconstant (-1 : Int)) fun minusOne =>
  plet (paddInteger # pconstant (-2 : Int)) fun minusTwo =>
  plet (plessThanInteger # 1) fun aboveOne =>
    pfix fun recur number =>
      pif (aboveOne # number) ((recur # (minusOne # number)) + (recur # (minusTwo # number))) number

private def fibPair : Nat → Int × Int
  | 0 => (0, 1)
  | index + 1 => let (previous, current) := fibPair index; (current, previous + current)

private def windowSize := 26

private def fibWindow (index : Term PInteger) : Term PInteger := ⟨do
  let entries ← (List.range windowSize).mapM fun offset => (pconstant (a := PInteger) (fibPair offset).1).build
  return .Case (← index.build) entries⟩

def fibonacci : Term (PInteger → PInteger) :=
  plam fun (number : Term PInteger) =>
    pif (plessThanInteger # number # 2) number <|
      pif (plessThanEqualsInteger # number # pconstant (Int.ofNat (windowSize - 1))) (fibWindow number) <|
        let loop := pfix fun (recur : Term (PInteger → PInteger → PInteger → PInteger))
            (remaining : Term PInteger) => plam fun (previous current : Term PInteger) =>
          pif (pequalsInteger # remaining # 0) previous
            (recur # (remaining - 1) # current # (previous + current))
        let (previous, current) := fibPair windowSize
        loop # (number - pconstant (a := PInteger) (Int.ofNat windowSize)) # pconstant previous # pconstant current

def ecd : Term (PInteger → PInteger → PInteger) :=
  pfix fun (recur : Term (PInteger → PInteger → PInteger)) (dividend : Term PInteger) =>
    plam fun (divisor : Term PInteger) =>
      pif (pequalsInteger # 0 # divisor)
        (pif (plessThanInteger # dividend # 0) (-dividend) dividend)
        (recur # divisor # (dividend % divisor))

def factorialScript := compile! factorial

end Test.Cape
