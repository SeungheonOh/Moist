import Moist.Plutus.BitBuffer
import Moist.Plutus.Lemma
import Moist.Plutus.CBOR
import Moist.Plutus.Term
import PlutusCore.Data
import PlutusCore.ByteString

namespace Moist.Plutus.Encode

open PlutusCore.Data
open PlutusCore.ByteString
open Moist.Plutus.BitBuffer
open Moist.Plutus.Lemma
open Moist.Plutus
open Moist.Plutus.Term

/-- A bit-level encoder matches the shape of `ℰ_X` in the specification. -/
abbrev Encoder (α : Type) := BitBuffer → α → BitBuffer

/-- Encode a fixed-width natural number (`ℰ_n`). -/
-- Encode a fixed-width natural number (ℰ_n).
abbrev ℰ_n : Encoder (Nat × Nat) := fun buf (input : Nat × Nat) =>
  let (width, value) := input
  buf.appendNatBE width value

/-- Encode a list using the combinator from Section 3.3.2 (`ℰ_list_X`). -/
-- Encode a list using the combinator from Section 3.3.2 (ℰ_list_X).
def ℰ_list (ℰ_elem : Encoder α) : Encoder (List α)
  | buf, [] => buf.pushBit false
  | buf, x :: xs =>
      let buf := buf.pushBit true
      let buf := ℰ_elem buf x
      ℰ_list ℰ_elem buf xs

/-- Encode natural numbers as described in Section 3.3.3 (`ℰ_ℕ`). -/
-- Encode natural numbers as described in Section 3.3.3 (ℰ_ℕ).
def ℰ_ℕ : Encoder Nat := fun buf value =>
  let digits := base128Digits value
  let (rest, last) := splitInitLast digits
  let buf := ℰ_list (fun buf digit => ℰ_n buf (7, digit)) buf rest
  ℰ_n buf (7, last)

/-- Encode signed integers via zig-zag and `ℰ_ℕ` (Section 3.3.4, `ℰ_ℤ`). -/
-- Encode signed integers via zig-zag and ℰ_ℕ (Section 3.3.4, ℰ_ℤ).
def ℰ_ℤ : Encoder Int := fun buf value =>
  ℰ_ℕ buf (zigZag value)

/-- Split a bytestring into canonical 255-byte chunks (the final chunk may be smaller). -/
def chunkByteString (bytes : List UInt8) : List (List UInt8) :=
  if bytes = [] then []
  else
    (List.take 255 bytes) :: (List.drop 255 bytes |> chunkByteString)
    termination_by (List.length bytes)
    decreasing_by
      apply List.drop_decreases_length <;> try assumption
      omega

/-- Encode a bytestring chunk (length byte followed by the payload). -/
def ℰ_C (buf : BitBuffer) (chunk : List UInt8) : BitBuffer :=
  let buf := buf.appendNatBE 8 chunk.length
  chunk.foldl (fun b byte => b.appendByte byte) buf

/-- Encode an arbitrary byte sequence using the bytestring rules (E_{B*}). -/
def ℰ_B : Encoder (List UInt8) := fun buf bytes =>
  let buf := BitBuffer.pad buf
  let chunks := chunkByteString bytes
  let buf := chunks.foldl ℰ_C buf
  buf.appendNatBE 8 0

/-- Convert a string to its UTF-8 byte representation. -/
def stringToUTF8Bytes (s : String) : List UInt8 :=
  s.toUTF8.toList

/-- Encode a UTF-8 string (ℰ_U). -/
def ℰ_U : Encoder String := fun buf s =>
  ℰ_B buf (stringToUTF8Bytes s)


/-- Encode a `Data` object by first CBOR-serialising it, then applying E_{B*}. -/
def ℰ_Data : Encoder Data := fun buf d =>
  match CBOR.dataToCBORBytes d with
  | some bytes => ℰ_B buf bytes
  | none => buf

--#eval (encodeDataValue BitBuffer.empty (Data.List (Data.I 1 :: Data.I 2 :: Data.I 10 :: []))).pad.toBitString
#eval (ℰ_U BitBuffer.empty "hi").pad.toBitString

-- Convert an atomic type to its 4-bit tag (0–4 or 8).
def atomicTypeTag (t : AtomicType) : Nat :=
  match t with
  | AtomicType.TypeInteger => 0
  | AtomicType.TypeByteString => 1
  | AtomicType.TypeString => 2
  | AtomicType.TypeUnit => 3
  | AtomicType.TypeBool => 4
  | AtomicType.TypeData => 8

-- Convert a BuiltinType to a list of 4-bit tags following the spec (e_type).
def e_type : BuiltinType → List Nat
  | BuiltinType.AtomicType t => [atomicTypeTag t]
  | BuiltinType.TypeOperator (TypeOperator.TypeList t) => [7,5] ++ e_type t
  | BuiltinType.TypeOperator (TypeOperator.TypePair t₁ t₂) => [7,7,6] ++ e_type t₁ ++ e_type t₂

-- Encode a BuiltinType as a list of 4-bit nibbles using ℰ_list (ℰ_type).
def ℰ_type (buf : BitBuffer) (t : BuiltinType) : BitBuffer :=
  let nibbles := e_type t
  ℰ_list (fun buf n => buf.appendNibble n) buf nibbles

-- Encode a variable name (de Bruijn index) using ℰ_ℕ (ℰ_name).
def ℰ_name (buf : BitBuffer) (n : Nat) : BitBuffer :=
  ℰ_ℕ buf n

-- Encode a binder name (always 0 for de Bruijn; consumes no input, ℰ_binder).
def ℰ_binder (buf : BitBuffer) (_ : Nat) : BitBuffer :=
  buf

/-- Encode a constant value following spec/flat-serialisation.tex:531-540.
    Type is inferred from the constant via constType.
    NOTE: Uses partial to skip termination proof; recursion is on structural
    sub-constants (lists/pairs), which are guaranteed to terminate. -/
partial def ℰ_constant : Encoder Const
  | buf, Const.Integer n =>
    ℰ_ℤ buf n
  | buf, Const.ByteString bs =>
    let bytes := bs.data.toList
    ℰ_B buf bytes
  | buf, Const.String s =>
    ℰ_U buf s
  | buf, Const.Unit =>
      buf
  | buf, Const.Bool b =>
      buf.pushBit b
    | buf, Const.Data d =>
      ℰ_Data buf d
    | buf, Const.ConstList elems =>
      ℰ_list (fun buf elem => ℰ_constant buf elem) buf elems
    | buf, Const.Pair (c1, c2) =>
      let buf := ℰ_constant buf c1
      ℰ_constant buf c2
    | buf, Const.ConstDataList elems =>
      let ℰ_elem buf elem := ℰ_constant buf (Const.Data elem)
      ℰ_list ℰ_elem buf elems
    | buf, Const.ConstPairDataList pairs =>
      let ℰ_pair buf (p : Data × Data) :=
      let buf := ℰ_constant buf (Const.Data p.1)
      ℰ_constant buf (Const.Data p.2)
      ℰ_list ℰ_pair buf pairs
    | buf, Const.PairData (d1, d2) =>
      let buf := ℰ_constant buf (Const.Data d1)
      ℰ_constant buf (Const.Data d2)
  | buf, _ => buf

/-- Map a BuiltinFun to its 7-bit tag per spec/flat-serialisation.tex:600-748. -/
def builtinFunTag : BuiltinFun → Nat
  -- Batch 1: Core operations (0–50)
  | BuiltinFun.AddInteger => 0
  | BuiltinFun.SubtractInteger => 1
  | BuiltinFun.MultiplyInteger => 2
  | BuiltinFun.DivideInteger => 3
  | BuiltinFun.QuotientInteger => 4
  | BuiltinFun.RemainderInteger => 5
  | BuiltinFun.ModInteger => 6
  | BuiltinFun.EqualsInteger => 7
  | BuiltinFun.LessThanInteger => 8
  | BuiltinFun.LessThanEqualsInteger => 9
  | BuiltinFun.AppendByteString => 10
  | BuiltinFun.ConsByteString => 11
  | BuiltinFun.SliceByteString => 12
  | BuiltinFun.LengthOfByteString => 13
  | BuiltinFun.IndexByteString => 14
  | BuiltinFun.EqualsByteString => 15
  | BuiltinFun.LessThanByteString => 16
  | BuiltinFun.LessThanEqualsByteString => 17
  | BuiltinFun.Sha2_256 => 18
  | BuiltinFun.Sha3_256 => 19
  | BuiltinFun.Blake2b_256 => 20
  | BuiltinFun.VerifyEd25519Signature => 21
  | BuiltinFun.AppendString => 22
  | BuiltinFun.EqualsString => 23
  | BuiltinFun.EncodeUtf8 => 24
  | BuiltinFun.DecodeUtf8 => 25
  | BuiltinFun.IfThenElse => 26
  | BuiltinFun.ChooseUnit => 27
  | BuiltinFun.Trace => 28
  | BuiltinFun.FstPair => 29
  | BuiltinFun.SndPair => 30
  | BuiltinFun.ChooseList => 31
  | BuiltinFun.MkCons => 32
  | BuiltinFun.HeadList => 33
  | BuiltinFun.TailList => 34
  | BuiltinFun.NullList => 35
  | BuiltinFun.ChooseData => 36
  | BuiltinFun.ConstrData => 37
  | BuiltinFun.MapData => 38
  | BuiltinFun.ListData => 39
  | BuiltinFun.IData => 40
  | BuiltinFun.BData => 41
  | BuiltinFun.UnConstrData => 42
  | BuiltinFun.UnMapData => 43
  | BuiltinFun.UnListData => 44
  | BuiltinFun.UnIData => 45
  | BuiltinFun.UnBData => 46
  | BuiltinFun.EqualsData => 47
  | BuiltinFun.MkPairData => 48
  | BuiltinFun.MkNilData => 49
  | BuiltinFun.MkNilPairData => 50
  -- Batch 2 (51)
  | BuiltinFun.SerializeData => 51
  -- Batch 3 (52–53)
  | BuiltinFun.VerifyEcdsaSecp256k1Signature => 52
  | BuiltinFun.VerifySchnorrSecp256k1Signature => 53
  -- Batch 4: BLS and Keccak (54–74)
  | BuiltinFun.Bls12_381_G1_add => 54
  | BuiltinFun.Bls12_381_G1_neg => 55
  | BuiltinFun.Bls12_381_G1_scalarMul => 56
  | BuiltinFun.Bls12_381_G1_equal => 57
  | BuiltinFun.Bls12_381_G1_hashToGroup => 58
  | BuiltinFun.Bls12_381_G1_compress => 59
  | BuiltinFun.Bls12_381_G1_uncompress => 60
  | BuiltinFun.Bls12_381_G2_add => 61
  | BuiltinFun.Bls12_381_G2_neg => 62
  | BuiltinFun.Bls12_381_G2_scalarMul => 63
  | BuiltinFun.Bls12_381_G2_equal => 64
  | BuiltinFun.Bls12_381_G2_hashToGroup => 65
  | BuiltinFun.Bls12_381_G2_compress => 66
  | BuiltinFun.Bls12_381_G2_uncompress => 67
  | BuiltinFun.Bls12_381_millerLoop => 68
  | BuiltinFun.Bls12_381_mulMlResult => 69
  | BuiltinFun.Bls12_381_finalVerify => 70
  | BuiltinFun.Keccak_256 => 71
  | BuiltinFun.Blake2b_224 => 72
  | BuiltinFun.IntegerToByteString => 73
  | BuiltinFun.ByteStringToInteger => 74
  -- Batch 5: Bitwise operations (75–86)
  | BuiltinFun.AndByteString => 75
  | BuiltinFun.OrByteString => 76
  | BuiltinFun.XorByteString => 77
  | BuiltinFun.ComplementByteString => 78
  | BuiltinFun.ReadBit => 79
  | BuiltinFun.WriteBits => 80
  | BuiltinFun.ReplicateByte => 81
  | BuiltinFun.ShiftByteString => 82
  | BuiltinFun.RotateByteString => 83
  | BuiltinFun.CountSetBits => 84
  | BuiltinFun.FindFirstSetBit => 85
  | BuiltinFun.Ripemd_160 => 86
  -- Batch 6: Advanced (87–93)
  | BuiltinFun.ExpModInteger => 87
  --| BuiltinFun.AndByteString => 88  -- Note: Spec has "dropList" but Term has AndByteString; using placeholder
  --| BuiltinFun.OrByteString => 89   -- Note: Spec has "lengthOfArray"
  --| BuiltinFun.XorByteString => 90  -- Note: Spec has "listToArray"
  --| BuiltinFun.ComplementByteString => 91  -- Note: Spec has "indexArray"
  --| BuiltinFun.Bls12_381_G1_add => 92  -- Note: Spec has "bls12_381_G1_multiScalarMul"
  --| BuiltinFun.Bls12_381_G2_add => 93  -- Note: Spec has "bls12_381_G2_multiScalarMul"

/-- Encode a builtin function as a 7-bit value. -/
def ℰ_builtin (buf : BitBuffer) (b : BuiltinFun) : BitBuffer :=
  ℰ_n buf (7, builtinFunTag b)

/-- Encode a term recursively following spec/flat-serialisation.tex:362-408.
    NOTE: Uses partial def to handle recursion on sub-terms. -/
partial def ℰ_term : Encoder Term
  -- Variable: tag 0000, then ℰ_name(x) where x is de Bruijn index
  | buf, Term.Var x =>
    let buf := buf.appendNibble 0
    ℰ_name buf x
  -- Delay: tag 0001, then recursive encode
  | buf, Term.Delay t =>
    let buf := buf.appendNibble 1
    ℰ_term buf t
  -- Lambda: tag 0010, then ℰ_binder(x), then recursive encode
  | buf, Term.Lam x t =>
    let buf := buf.appendNibble 2
    let buf := ℰ_binder buf x
    ℰ_term buf t
  -- Application: tag 0011, encode t1, then encode t2
  | buf, Term.Apply t1 t2 =>
    let buf := buf.appendNibble 3
    let buf := ℰ_term buf t1
    ℰ_term buf t2
  -- Constant: tag 0100, encode type via ℰ_type, then encode constant value
  | buf, Moist.Plutus.Term.Term.Constant c =>
    let buf := buf.appendNibble 4
    let buf := ℰ_type buf c.2
    ℰ_constant buf c.1
  -- Force: tag 0101, then recursive encode
  | buf, Term.Force t =>
    let buf := buf.appendNibble 5
    ℰ_term buf t
  -- Error: tag 0110 (no additional data)
  | buf, Term.Error =>
    buf.appendNibble 6
  -- Builtin: tag 0111, then encode builtin function
  | buf, Term.Builtin b =>
    let buf := buf.appendNibble 7
    ℰ_builtin buf b
  -- Constr: tag 1000, encode tag i, then encode term list
  | buf, Term.Constr i terms =>
    let buf := buf.appendNibble 8
    let buf := ℰ_ℕ buf i
    ℰ_list ℰ_term buf terms
  -- Case: tag 1001, encode scrutinee, then encode alternatives
  | buf, Term.Case scrutinee alts =>
    let buf := buf.appendNibble 9
    let buf := ℰ_term buf scrutinee
    ℰ_list ℰ_term buf alts

/-- Encode a program by encoding the version triple, then the term body,
    then padding to byte boundary following spec/flat-serialisation.tex:333-357. -/
def encode_program : Program → BitBuffer
  | ⟨⟨a, b, c⟩, t⟩ =>
      let buf := BitBuffer.empty
      -- Encode version triple: ℰ_ℕ(ℰ_ℕ(ℰ_ℕ(ε, a), b), c)
      let buf := ℰ_ℕ buf a
      let buf := ℰ_ℕ buf b
      let buf := ℰ_ℕ buf c
      -- Encode term body
      let buf := ℰ_term buf t
      -- Pad to byte boundary and convert to bytestring
      let padded := buf.pad
      padded

/-
(program 5.0.2
[
  [(builtin indexByteString)(con bytestring #1a5f783625ee8c)]
  (con integer 54321)
])
-/

def testProg : Program :=
  Program.Program (Version.Version 5 0 2)
    (Term.Apply
      (Term.Apply
        (Term.Builtin BuiltinFun.IndexByteString)
        (Term.Constant (Prod.mk (Const.ByteString (ByteArray.mk (Array.mk ([26, 95, 120, 54, 37, 238, 140] : List UInt8)))) (BuiltinType.AtomicType AtomicType.TypeByteString)))
      )
      (Term.Constant (Prod.mk (Const.Integer 54321) (BuiltinType.AtomicType AtomicType.TypeInteger))))

#eval (encode_program testProg).toHexString

/-
00000101 00000000 00000010 00110011 01110001 11001001
00010001 00000111 00011010 01011111 01111000 00110110
00100101 11101110 10001100 00000000 01001000 00111000
10110100 00000001 10000001"
-/
/-
00000101 00000000 00000010 00110011 01110001 11001001 ...3q.
00010001 00000111 00011010 01011111 01111000 00110110 ..._x6
00100101 11101110 10001100 00000000 01001000 00111000 %...H8
10110100 00000001 10000001
-/

end Moist.Plutus.Encode

namespace Moist.Plutus.Term.Program
def encode : Moist.Plutus.Term.Program → BitBuffer := Moist.Plutus.Encode.encode_program
end Moist.Plutus.Term.Program
