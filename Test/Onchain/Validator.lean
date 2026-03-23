import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude
import Moist.Cardano.V3
import Moist.Plutus.Types

open PlutusCore.UPLC.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude
open Moist.Cardano.V3
open Moist.Plutus (Data)

/-! # Validator Tests

End-to-end tests simulating real Plutus validator patterns.
-/

-- ## Always-succeeds validator

@[onchain]
def alwaysSucceeds (_datum : Data) (_redeemer : Data) (_ctx : Data) : Bool :=
  true

def alwaysSucceedsUPLC : Term := compile! alwaysSucceeds

#eval IO.println s!"alwaysSucceeds:\n{prettyTerm alwaysSucceedsUPLC}"

-- ## Check-signature validator pattern
-- Validates that a specific pubkey signed the transaction.
-- Simplified: checks if the redeemer matches a known hash.

@[onchain]
def checkSignature (expectedHash : Data) (redeemer : Data) (_ctx : Data) : Bool :=
  equalsData expectedHash redeemer

def checkSignatureUPLC : Term := compile! checkSignature

#eval IO.println s!"checkSignature:\n{prettyTerm checkSignatureUPLC}"

-- ## Datum-checking validator
-- Extracts an integer from the datum and checks it's positive.

@[onchain]
def positiveIntDatum (datum : Data) (_redeemer : Data) (_ctx : Data) : Bool :=
  lessThanInteger 0 (unIData datum)

def positiveIntDatumUPLC : Term := compile! positiveIntDatum

#eval IO.println s!"positiveIntDatum:\n{prettyTerm positiveIntDatumUPLC}"

-- ## Redeemer-dispatched validator using @[plutus_data]

@[plutus_data]
inductive VestingAction where
  | claim : Int → VestingAction
  | cancel : VestingAction

@[onchain]
def vestingValidator (action : VestingAction) : Bool :=
  match action with
  | .claim amount => lessThanInteger 0 amount
  | .cancel => true

def vestingValidatorUPLC : Term := compile! vestingValidator

#eval IO.println s!"vestingValidator:\n{prettyTerm vestingValidatorUPLC}"

-- ## Multi-argument function composition

@[onchain]
def clampValue (lo : Int) (hi : Int) (x : Int) : Int :=
  ifThenElse (lessThanInteger x lo) lo
    (ifThenElse (lessThanInteger hi x) hi x)

def clampValueUPLC : Term := compile! clampValue

#eval IO.println s!"clampValue:\n{prettyTerm clampValueUPLC}"
