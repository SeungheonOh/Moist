import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.Cape

open Moist.Onchain.Prelude

@[onchain] def factorialNaive (number : Int) : Int :=
  if lessThanEqInteger number 0 then 1
  else multiplyInteger number (factorialNaive (subtractInteger number 1))
termination_by number.toNat
decreasing_by simp_all [lessThanEqInteger, subtractInteger]; omega

@[onchain] def fibonacciNaive (number : Int) : Int :=
  if lessThanEqInteger number 1 then number
  else addInteger (fibonacciNaive (subtractInteger number 1))
                  (fibonacciNaive (subtractInteger number 2))
termination_by number.toNat
decreasing_by all_goals simp_all [lessThanEqInteger, subtractInteger] <;> omega

@[onchain] def factorialLoop (number : Int) : Int → Int := fun product =>
  if lessThanEqInteger number 1 then product
  else factorialLoop (subtractInteger number 1) (multiplyInteger product number)
termination_by number.toNat
decreasing_by simp_all [lessThanEqInteger, subtractInteger]; omega

@[onchain] def factorial (number : Int) := factorialLoop number 1

@[onchain] def fibonacciLoop (remaining : Int) : Int → Int → Int := fun previous current =>
  if lessThanEqInteger remaining 0 then previous
  else fibonacciLoop (subtractInteger remaining 1) current (addInteger previous current)
termination_by remaining.toNat
decreasing_by simp_all [lessThanEqInteger, subtractInteger]; omega

@[onchain] def fibonacci (number : Int) :=
  if lessThanEqInteger number 1 then number else fibonacciLoop number 0 1

private theorem mod_decreases (dividend divisor : Int) (nonzero : divisor ≠ 0) :
    (dividend % divisor).natAbs < divisor.natAbs := by
  have := Int.emod_lt dividend nonzero
  have := Int.emod_nonneg dividend nonzero
  omega

@[onchain] def euclid (divisor : Int) : Int → Int := fun dividend =>
  if equalsInteger divisor 0 then
    if lessThanInteger dividend 0 then subtractInteger 0 dividend else dividend
  else euclid (modInteger dividend divisor) divisor
termination_by divisor.natAbs
decreasing_by
  simp_all [equalsInteger, modInteger]
  apply mod_decreases
  assumption

@[onchain] def ecd (dividend divisor : Int) := euclid divisor dividend

def factorialScript := compile! factorial
def factorialNaiveScript := compile! factorialNaive
def fibonacciScript := compile! fibonacci
def fibonacciNaiveScript := compile! fibonacciNaive
def ecdScript := compile! ecd

end Test.Cape
