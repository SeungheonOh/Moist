import Moist.Plutus.Types

namespace Moist.CEK

/-- Builtin semantics variant (plutus-core 1.65): C = PlutusV3 before PV11, E = PlutusV3 from PV11 (conformance `def`). -/
class inductive SemVariant where
  | C | E
deriving DecidableEq, Repr
/-- `ensurable` in Builtins.hs:2725 (true for D/E). -/
def SemVariant.ensurable : SemVariant → Bool | .C => false | .E => true
def maxBoundInteger : Int := ((2 ^ 262143 : Nat) : Int) - 1
def minBoundInteger : Int := -((2 ^ 262143 : Nat) : Int)
def maxBoundByteString : Nat := 65536
/-- CInteger unlifting check (Universe.hs:844). -/
def cIntegerOk (sv : SemVariant) (i : Int) : Bool := !sv.ensurable || (decide (minBoundInteger ≤ i) && decide (i ≤ maxBoundInteger))
/-- CByteString unlifting check (Universe.hs:870). -/
def cByteStringOk (sv : SemVariant) (bs : ByteArray) : Bool := !sv.ensurable || decide (bs.size ≤ maxBoundByteString)
