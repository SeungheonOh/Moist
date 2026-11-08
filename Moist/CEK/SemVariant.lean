import Moist.Plutus.Types

namespace Moist.CEK

/-- Builtin semantics variant (plutus-core 1.65): C = PlutusV3 before PV11, E = PlutusV3 from PV11 (conformance `def`). -/
class inductive SemVariant where
  | C | E
deriving DecidableEq, Repr

/-- `ensurable` in Builtins.hs:2725 (true for D/E). -/
def SemVariant.ensurable : SemVariant → Bool | .C => false | .E => true

/-- `2^262143 - 1` (Universe/Cardano.hs). Irreducible so that elaboration never tries to
evaluate the power. -/
@[irreducible] def maxBoundInteger : Int := ((2 ^ 262143 : Nat) : Int) - 1
/-- `-2^262143` (Universe/Cardano.hs). -/
@[irreducible] def minBoundInteger : Int := -((2 ^ 262143 : Nat) : Int)
def maxBoundByteString : Nat := 65536

/-- CInteger unlifting check (Universe.hs:844). -/
def cIntegerOk (sv : SemVariant) (i : Int) : Bool := !sv.ensurable || (decide (minBoundInteger ≤ i) && decide (i ≤ maxBoundInteger))

/-- CByteString unlifting check (Universe.hs:870). -/
def cByteStringOk (sv : SemVariant) (bs : ByteArray) : Bool := !sv.ensurable || decide (bs.size ≤ maxBoundByteString)

theorem two_pow_64_le_bound : (2 ^ 64 : Nat) ≤ 2 ^ 262143 :=
  Nat.pow_le_pow_right (by decide) (by decide)

/-- Integers below `2^64` in magnitude pass the `CInteger` check of every variant. -/
theorem cIntegerOk_of_natAbs_lt (sv : SemVariant) (i : Int) (h : i.natAbs < 2 ^ 64) :
    cIntegerOk sv i = true := by
  cases sv
  · rfl
  · have hb := two_pow_64_le_bound
    simp only [cIntegerOk, SemVariant.ensurable, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq]
    unfold maxBoundInteger minBoundInteger
    generalize (2 ^ 262143 : Nat) = B at hb
    generalize (2 ^ 64 : Nat) = C at hb h
    omega

/-- Variant C performs no `CInteger` check. -/
@[simp] theorem cIntegerOk_C (i : Int) : cIntegerOk .C i = true := rfl

/-- Variant C performs no `CByteString` check. -/
@[simp] theorem cByteStringOk_C (bs : ByteArray) : cByteStringOk .C bs = true := rfl

end Moist.CEK
