import Moist.SMT.Soundness.AdvancedBuiltinFailureBinary

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekValue)

/-! CEK argument-shape inversions for the advanced ternary builtins. -/

set_option maxHeartbeats 0 in
theorem evalBuiltin_Bitwise_some_shape (b : BuiltinFun)
    (hb : b = .AndByteString ∨ b = .OrByteString ∨ b = .XorByteString)
    {x y z cv : CekValue} (h : Moist.CEK.evalBuiltin b [x, y, z] = some cv) :
    ∃ (bx byBytes : ByteArray) (pad : Bool),
      x = .VCon (.ByteString bx) ∧
      y = .VCon (.ByteString byBytes) ∧ z = .VCon (.Bool pad) := by
  rcases hb with rfl | rfl | rfl <;>
    cases x <;>
      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
        Moist.CEK.extractConsts] at h
  all_goals
    case VCon cx =>
      cases y <;>
        simp [Moist.CEK.extractConsts] at h
      case VCon cy =>
        cases z <;>
          simp [Moist.CEK.extractConsts] at h
        case VCon cz =>
          cases cx <;>
            simp [Moist.CEK.evalBuiltinConst,
              Moist.CEK.evalAndByteStringConst,
              Moist.CEK.evalOrByteStringConst,
              Moist.CEK.evalXorByteStringConst] at h
          case ByteString bx =>
            cases cy <;>
              try simp at h
            case ByteString byBytes =>
              cases cz <;>
                simp at h
              case Bool pad => exact ⟨bx, byBytes, pad, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem evalBuiltin_IntegerToByteString_some_shape {x y z cv : CekValue}
    (h : Moist.CEK.evalBuiltin .IntegerToByteString [x, y, z] = some cv) :
    ∃ (n width : Int) (endian : Bool), x = .VCon (.Integer n) ∧
      y = .VCon (.Integer width) ∧ z = .VCon (.Bool endian) := by
  cases x <;>
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts] at h
  case VCon cx =>
    cases y <;>
      simp [Moist.CEK.extractConsts] at h
    case VCon cy =>
      cases z <;>
        simp [Moist.CEK.extractConsts] at h
      case VCon cz =>
        cases cx <;>
          simp [Moist.CEK.evalBuiltinConst,
            Moist.CEK.evalIntegerToByteStringConst] at h
        case Integer n =>
          cases cy <;>
            try simp at h
          case Integer width =>
            cases cz <;>
              simp at h
            case Bool endian => exact ⟨n, width, endian, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem evalBuiltin_WriteBits_some_shape {x y z cv : CekValue}
    (h : Moist.CEK.evalBuiltin .WriteBits [x, y, z] = some cv) :
    ∃ (value : Bool) (indices : List Const) (bs : ByteArray),
      x = .VCon (.Bool value) ∧
      y = .VCon (.ConstList indices) ∧ z = .VCon (.ByteString bs) := by
  cases x <;>
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts] at h
  case VCon cx =>
    cases y <;>
      simp [Moist.CEK.extractConsts] at h
    case VCon cy =>
      cases z <;>
        simp [Moist.CEK.extractConsts] at h
      case VCon cz =>
        cases cx <;>
          simp [Moist.CEK.evalBuiltinConst, Moist.CEK.evalWriteBitsConst] at h
        case Bool value =>
          cases cy <;>
            try simp at h
          case ConstList indices =>
            cases cz <;>
              simp at h
            case ByteString bs => exact ⟨value, indices, bs, rfl, rfl, rfl⟩

set_option maxHeartbeats 0 in
theorem evalBuiltin_ExpModInteger_some_shape {x y z cv : CekValue}
    (h : Moist.CEK.evalBuiltin .ExpModInteger [x, y, z] = some cv) :
    ∃ (modulus exponent base : Int), x = .VCon (.Integer modulus) ∧
      y = .VCon (.Integer exponent) ∧ z = .VCon (.Integer base) := by
  cases x <;>
    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
      Moist.CEK.extractConsts] at h
  case VCon cx =>
    cases y <;>
      simp [Moist.CEK.extractConsts] at h
    case VCon cy =>
      cases z <;>
        simp [Moist.CEK.extractConsts] at h
      case VCon cz =>
        cases cx <;>
          simp [Moist.CEK.evalBuiltinConst,
            Moist.CEK.evalExpModIntegerConst] at h
        case Integer modulus =>
          cases cy <;>
            try simp at h
          case Integer exponent =>
            cases cz <;>
              simp at h
            case Integer base => exact ⟨modulus, exponent, base, rfl, rfl, rfl⟩

end Moist.SMT.UPLC.Soundness
