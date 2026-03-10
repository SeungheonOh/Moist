import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude

/-! # @[plutus_data] Encoding Tests

Tests for Data-encoded inductive types using ConstrData/UnConstrData.
-/

-- ## Simple enum (no fields)

@[plutus_data]
inductive Color where
  | red : Color
  | green : Color
  | blue : Color

@[onchain]
noncomputable def colorToInt (c : Color) : Int :=
  match c with
  | .red => 0
  | .green => 1
  | .blue => 2

def colorToIntUPLC : Term := compile! colorToInt

#eval IO.println s!"colorToInt:\n{prettyTerm colorToIntUPLC}"

-- ## Single constructor with fields

@[plutus_data]
inductive Pair where
  | mkPair : Int → Int → Pair

@[onchain]
noncomputable def pairSum (p : Pair) : Int :=
  match p with
  | .mkPair x y => addInteger x y

def pairSumUPLC : Term := compile! pairSum

#eval IO.println s!"pairSum:\n{prettyTerm pairSumUPLC}"

-- ## Constructor with Data encoding

@[onchain]
noncomputable def mkPair (x : Int) (y : Int) : Pair :=
  .mkPair x y

def mkPairUPLC : Term := compile! mkPair

#eval IO.println s!"mkPair:\n{prettyTerm mkPairUPLC}"

-- ## Multi-constructor with fields

@[plutus_data]
inductive Action where
  | mint : Int → Action
  | burn : Int → Action
  | transfer : Int → Int → Action

@[onchain]
noncomputable def actionAmount (a : Action) : Int :=
  match a with
  | .mint x => x
  | .burn x => x
  | .transfer x y => addInteger x y

def actionAmountUPLC : Term := compile! actionAmount

#eval IO.println s!"actionAmount:\n{prettyTerm actionAmountUPLC}"

-- ## Nested @[plutus_data] types

@[plutus_data]
inductive TxRef where
  | txRef : Int → Int → TxRef

@[onchain]
noncomputable def txRefIndex (r : TxRef) : Int :=
  match r with
  | .txRef _hash idx => idx

def txRefIndexUPLC : Term := compile! txRefIndex

#eval IO.println s!"txRefIndex:\n{prettyTerm txRefIndexUPLC}"
