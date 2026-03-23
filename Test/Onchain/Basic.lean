import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude

open PlutusCore.UPLC.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude

/-! # Onchain Compilation Tests

Basic tests for the compile! elaborator pipeline.
Each @[onchain] definition is compiled to UPLC at elaboration time.
-/

-- ## Phase 1: Identity function

@[onchain]
def myIdentity (x : Int) : Int := x

def myIdentityUPLC : Term := compile! myIdentity

#eval IO.println s!"identity:\n{prettyTerm myIdentityUPLC}"

-- ## Lambda with application

@[onchain]
def applyToSelf (f : Int → Int) (x : Int) : Int := f x

def applyToSelfUPLC : Term := compile! applyToSelf

#eval IO.println s!"applyToSelf:\n{prettyTerm applyToSelfUPLC}"

-- ## Let binding

@[onchain]
def withLet (x : Int) : Int :=
  let y := x
  y

def withLetUPLC : Term := compile! withLet

#eval IO.println s!"withLet:\n{prettyTerm withLetUPLC}"

-- ## Prelude builtins: addInteger

@[onchain]
def addTwo (x : Int) : Int :=
  addInteger x (addInteger x x)

def addTwoUPLC : Term := compile! addTwo

#eval IO.println s!"addTwo:\n{prettyTerm addTwoUPLC}"

-- ## Multiple args and nested application

@[onchain]
def addThree (x : Int) (y : Int) (z : Int) : Int :=
  addInteger (addInteger x y) z

def addThreeUPLC : Term := compile! addThree

#eval IO.println s!"addThree:\n{prettyTerm addThreeUPLC}"

-- ## Constant function (dead argument)

@[onchain]
def constFn (x : Int) (y : Int) : Int := x

def constFnUPLC : Term := compile! constFn

#eval IO.println s!"constFn:\n{prettyTerm constFnUPLC}"

-- ## Nested lambdas

@[onchain]
def compose (f : Int → Int) (g : Int → Int) (x : Int) : Int := f (g x)

def composeUPLC : Term := compile! compose

#eval IO.println s!"compose:\n{prettyTerm composeUPLC}"

-- ## Cross-module export verification
#eval IO.println s!"identity is Lam: {match myIdentityUPLC with | .Lam _ _ => true | _ => false}"

-- ## ifThenElse (unfolds to Bool.casesOn → Case)

@[onchain]
def chooseByBool (b : Bool) (x : Int) (y : Int) : Int :=
  ifThenElse b x y

def chooseByBoolUPLC : Term := compile! chooseByBool

#eval IO.println s!"chooseByBool:\n{prettyTerm chooseByBoolUPLC}"

-- ## Bool matching via casesOn

@[onchain]
def boolToInt (b : Bool) : Int :=
  match b with
  | true => 1
  | false => 0

def boolToIntUPLC : Term := compile! boolToInt

#eval IO.println s!"boolToInt:\n{prettyTerm boolToIntUPLC}"

-- ## Integer constants (Int.ofNat handling)

@[onchain]
def addFortyTwo (x : Int) : Int :=
  addInteger x 42

def addFortyTwoUPLC : Term := compile! addFortyTwo

#eval IO.println s!"addFortyTwo:\n{prettyTerm addFortyTwoUPLC}"

-- ## Auto-unfolding: helper function gets inlined

def doubleHelper (x : Int) : Int :=
  addInteger x x

@[onchain]
def quadruple (x : Int) : Int :=
  doubleHelper (doubleHelper x)

def quadrupleUPLC : Term := compile! quadruple

#eval IO.println s!"quadruple:\n{prettyTerm quadrupleUPLC}"

-- ## Comparison producing Bool + conditional

@[onchain]
def absValue (x : Int) : Int :=
  ifThenElse (lessThanInteger x 0) (subtractInteger 0 x) x

def absValueUPLC : Term := compile! absValue

#eval IO.println s!"absValue:\n{prettyTerm absValueUPLC}"
