import Moist.Onchain.Attribute
import Moist.Plutus.Types

namespace Moist.Onchain.Prelude

/-! # Plutus-Compatible Prelude

Functions that map directly to Plutus builtins.
The `compile!` translator recognizes these by name (via the builtin map)
and emits the corresponding UPLC builtin — it never unfolds them.

Having real implementations means user code does NOT need `noncomputable`,
and functions can be `#eval`'d in Lean for testing.
-/

/-! ## Integer operations -/

def addInteger (a b : Int) : Int := a + b
def subtractInteger (a b : Int) : Int := a - b
def multiplyInteger (a b : Int) : Int := a * b
def divideInteger (a b : Int) : Int := a / b
def modInteger (a b : Int) : Int := a % b
def equalsInteger (a b : Int) : Bool := a == b
def lessThanInteger (a b : Int) : Bool := a < b
def lessThanEqInteger (a b : Int) : Bool := a ≤ b

/-! ## Control flow -/

universe u

/-- ifThenElse unfolds to Bool.casesOn, producing Case in MIR.
    This avoids needing Force/Delay wrapping that the IfThenElse builtin requires. -/
def ifThenElse {α : Type u} (b : Bool) (t f : α) : α :=
  match b with
  | true => t
  | false => f

def trace {α : Type u} (msg : String) (a : α) : α :=
  dbg_trace msg; a

/-! ## Data operations -/

open Moist.Plutus (Data)

def constrData (tag : Int) (fields : List Data) : Data :=
  .Constr tag fields

def unConstrData (d : Data) : Int × List Data :=
  match d with
  | .Constr tag fields => (tag, fields)
  | _ => (0, [])

def iData (n : Int) : Data := .I n

def unIData (d : Data) : Int :=
  match d with
  | .I n => n
  | _ => 0

def listData (xs : List Data) : Data := .List xs

def unListData (d : Data) : List Data :=
  match d with
  | .List xs => xs
  | _ => []

def mapData (xs : List (Data × Data)) : Data := .Map xs

def unMapData (d : Data) : List (Data × Data) :=
  match d with
  | .Map xs => xs
  | _ => []

def equalsData (a b : Data) : Bool := a == b

open Moist.Plutus (ByteString)

def bData (bs : ByteString) : Data := .B bs

def unBData (d : Data) : ByteString :=
  match d with
  | .B bs => bs
  | _ => ByteArray.empty

/-! ## List operations -/

def headList (xs : List Data) : Data :=
  match xs with
  | x :: _ => x
  | [] => .I 0  -- error in Plutus, but we need a value

def tailList (xs : List Data) : List Data :=
  match xs with
  | _ :: rest => rest
  | [] => []

def nullList (xs : List Data) : Bool := xs.isEmpty

def mkCons (x : Data) (xs : List Data) : List Data := x :: xs

/-! ## Pair operations -/

def fstPair (p : Int × List Data) : Int := p.1
def sndPair (p : Int × List Data) : List Data := p.2

/-! ## ByteString operations -/

def appendByteString (a b : ByteString) : ByteString := a ++ b
def lengthOfByteString (bs : ByteString) : Int := bs.size
def indexByteString (bs : ByteString) (i : Int) : Int := bs.get! i.toNat |>.toNat
def sliceByteString (start len : Int) (bs : ByteString) : ByteString :=
  bs.extract start.toNat (start.toNat + len.toNat)
def equalsByteString (a b : ByteString) : Bool := a == b
def lessThanByteString (a b : ByteString) : Bool := a < b
def lessThanEqualsByteString (a b : ByteString) : Bool := a ≤ b
def consByteString (byte : Int) (bs : ByteString) : ByteString :=
  ByteArray.mk (#[byte.toNat.toUInt8] ++ bs.toList.toArray)

/-! ## Crypto (no Lean implementation — keep as axioms) -/

axiom sha2_256 : ByteString → ByteString
axiom blake2b_256 : ByteString → ByteString
axiom blake2b_224 : ByteString → ByteString
axiom verifyEd25519Signature : ByteString → ByteString → ByteString → Bool
axiom verifyEcdsaSecp256k1Signature : ByteString → ByteString → ByteString → Bool
axiom verifySchnorrSecp256k1Signature : ByteString → ByteString → ByteString → Bool
axiom keccak_256 : ByteString → ByteString

/-! ## String operations -/

def encodeUtf8 (s : String) : ByteString := s.toUTF8
def decodeUtf8 (bs : ByteString) : String :=
  String.fromUTF8! bs
def appendString (a b : String) : String := a ++ b
def equalsString (a b : String) : Bool := a == b

/-! ## Unit / Error -/

axiom pError {α : Type u} : α

def chooseUnit {α : Type u} (_ : Unit) (a : α) : α := a

/-! ## Pair operations (polymorphic) -/

def mkPairData (a b : Data) : Data × Data := (a, b)

def mkNilData (_ : Unit) : List Data := []

end Moist.Onchain.Prelude
