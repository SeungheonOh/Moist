import Moist.SMT.Soundness.BuiltinFailureLemmas

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekValue)

/-! CEK argument-shape inversions for the advanced binary builtins. -/

theorem evalBuiltin_none_of_length_of_const_none
    (b : BuiltinFun) (arity : Nat)
    (hpass : ∀ args, Moist.CEK.evalBuiltinPassThrough b args = none)
    (hconst : ∀ cs, cs.length ≠ arity →
      Moist.CEK.evalBuiltinConst b cs = none)
    {args : List CekValue} (hlen : args.length ≠ arity) :
    Moist.CEK.evalBuiltin b args = none := by
  rw [Moist.CEK.evalBuiltin, hpass]
  cases hc : Moist.CEK.extractConsts args with
  | none => simp
  | some cs =>
      have hcsLen := extractConsts_length hc
      have hne : cs.length ≠ arity := by omega
      simp [hconst cs hne]

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_advanced_binary_none_of_length
    (b : BuiltinFun)
    (hb : b = .ByteStringToInteger ∨ b = .ReadBit ∨
      b = .ReplicateByte ∨ b = .ShiftByteString ∨
      b = .RotateByteString)
    {cs : List Const} (hlen : cs.length ≠ 2) :
    Moist.CEK.evalBuiltinConst b cs = none := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    cases cs with
    | nil => rfl
    | cons c rest =>
        cases rest with
        | nil => cases c <;> rfl
        | cons c2 rest2 =>
            cases rest2 with
            | nil => exact (hlen rfl).elim
            | cons c3 rest3 => cases c <;> cases c2 <;> rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinConst_advanced_ternary_none_of_length
    (b : BuiltinFun)
    (hb : b = .IntegerToByteString ∨ b = .AndByteString ∨
      b = .OrByteString ∨ b = .XorByteString ∨ b = .WriteBits ∨
      b = .ExpModInteger)
    {cs : List Const} (hlen : cs.length ≠ 3) :
    Moist.CEK.evalBuiltinConst b cs = none := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases cs with
    | nil => rfl
    | cons c rest =>
        cases rest with
        | nil => cases c <;> rfl
        | cons c2 rest2 =>
            cases rest2 with
            | nil => cases c <;> cases c2 <;> rfl
            | cons c3 rest3 =>
                cases rest3 with
                | nil => exact (hlen rfl).elim
                | cons c4 rest4 =>
                    cases c <;> cases c2 <;> cases c3 <;> rfl

theorem evalBuiltin_advanced_binary_none_of_length
    (b : BuiltinFun)
    (hb : b = .ByteStringToInteger ∨ b = .ReadBit ∨
      b = .ReplicateByte ∨ b = .ShiftByteString ∨
      b = .RotateByteString)
    {args : List CekValue} (hlen : args.length ≠ 2) :
    Moist.CEK.evalBuiltin b args = none := by
  apply evalBuiltin_none_of_length_of_const_none b 2
  · intro xs
    apply Moist.CEK.evalBuiltinPassThrough_none_of_not_passthrough
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro cs h
    exact evalBuiltinConst_advanced_binary_none_of_length b hb h
  · exact hlen

theorem evalBuiltin_advanced_ternary_none_of_length
    (b : BuiltinFun)
    (hb : b = .IntegerToByteString ∨ b = .AndByteString ∨
      b = .OrByteString ∨ b = .XorByteString ∨ b = .WriteBits ∨
      b = .ExpModInteger)
    {args : List CekValue} (hlen : args.length ≠ 3) :
    Moist.CEK.evalBuiltin b args = none := by
  apply evalBuiltin_none_of_length_of_const_none b 3
  · intro xs
    apply Moist.CEK.evalBuiltinPassThrough_none_of_not_passthrough
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro cs h
    exact evalBuiltinConst_advanced_ternary_none_of_length b hb h
  · exact hlen

set_option maxHeartbeats 0 in
theorem evalBuiltin_ByteStringToInteger_some_shape {a b cv : CekValue}
    (h : Moist.CEK.evalBuiltin .ByteStringToInteger [a, b] = some cv) :
    ∃ (bs : ByteArray) (endian : Bool),
      a = .VCon (.ByteString bs) ∧ b = .VCon (.Bool endian) := by
  cases a <;>
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts] at h
  case VCon ca =>
    cases b <;>
      simp [Moist.CEK.extractConsts] at h
    case VCon cb =>
      cases ca <;>
        simp [Moist.CEK.evalBuiltinConst,
          Moist.CEK.evalByteStringToIntegerConst] at h
      case ByteString bs =>
        cases cb <;>
          simp at h
        case Bool endian => exact ⟨bs, endian, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem evalBuiltin_IntBytes_some_shape (b : BuiltinFun)
    (hb : b = .ReadBit ∨ b = .ShiftByteString ∨ b = .RotateByteString)
    {a c cv : CekValue} (h : Moist.CEK.evalBuiltin b [a, c] = some cv) :
    ∃ (i : Int) (bs : ByteArray),
      a = .VCon (.Integer i) ∧ c = .VCon (.ByteString bs) := by
  rcases hb with rfl | rfl | rfl <;>
    cases a <;>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
        Moist.CEK.extractConsts] at h
  all_goals
    case VCon ca =>
      cases c <;>
        simp [Moist.CEK.extractConsts] at h
      case VCon cc =>
        cases ca <;>
          simp [Moist.CEK.evalBuiltinConst, Moist.CEK.evalReadBitConst,
            Moist.CEK.evalShiftByteStringConst,
            Moist.CEK.evalRotateByteStringConst] at h
        case Integer i =>
          cases cc <;>
            simp at h
          case ByteString bs => exact ⟨i, bs, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem evalBuiltin_ReplicateByte_some_shape {a c cv : CekValue}
    (h : Moist.CEK.evalBuiltin .ReplicateByte [a, c] = some cv) :
    ∃ (byte count : Int), a = .VCon (.Integer byte) ∧
      c = .VCon (.Integer count) := by
  cases a <;>
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts] at h
  case VCon ca =>
    cases c <;>
      simp [Moist.CEK.extractConsts] at h
    case VCon cc =>
      cases ca <;>
        simp [Moist.CEK.evalBuiltinConst,
          Moist.CEK.evalReplicateByteConst] at h
      case Integer byte =>
        cases cc <;>
          simp at h
        case Integer count => exact ⟨byte, count, rfl, rfl⟩

end Moist.SMT.UPLC.Soundness
