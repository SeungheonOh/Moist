import Moist.Plutus.BitBuffer
import Moist.Plutus.Lemma
import Moist.Plutus.CBOR
import Moist.Plutus.Term
import PlutusCore.Data
import PlutusCore.ByteString

namespace Moist.Plutus.Flat

open PlutusCore.Data
open PlutusCore.ByteString
open Moist.Plutus.BitBuffer
open Moist.Plutus.Lemma
open Moist.Plutus
open Moist.Plutus.Term


/-- A bit-level encoder matches the shape of `ℰ_X` in the specification. -/
abbrev Encoder (α : Type) := BitBuffer → α → BitBuffer

/-- Encode a fixed-width natural number (`ℰ_n`). -/
def encodeFixedWidth : Encoder (Nat × Nat) := fun buf (input : Nat × Nat) =>
  let (width, value) := input
  buf.appendNatBE width value

/-- Encode a list using the combinator from Section 3.3.2. -/
def encodeList (encodeElem : Encoder α) : Encoder (List α)
  | buf, [] => buf.pushBit false
  | buf, x :: xs =>
      let buf := buf.pushBit true
      let buf := encodeElem buf x
      encodeList encodeElem buf xs

/-- Encode natural numbers as described in Section 3.3.3. -/
def encodeNat : Encoder Nat := fun buf value =>
  let digits := base128Digits value
  let (rest, last) := splitInitLast digits
  let buf := encodeList (fun buf digit => encodeFixedWidth buf (7, digit)) buf rest
  encodeFixedWidth buf (7, last)

/-- Encode signed integers via zig-zag and `encodeNat` (Section 3.3.4). -/
def encodeInt : Encoder Int := fun buf value =>
  encodeNat buf (zigZag value)

/-
################################################################################
Stage 2: ByteString/String/Data primitives
################################################################################
-/

/-- Split a bytestring into canonical 255-byte chunks (the final chunk may be smaller). -/
def chunkByteString (bytes : List UInt8) : List (List UInt8) :=
  if bytes = [] then []
  else
    (List.take 255 bytes) :: (List.drop 255 bytes |> chunkByteString)
    termination_by (List.length bytes)
    decreasing_by
      apply List.drop_decreases_length <;> try assumption
      omega

def splitToChunks (s : String) : List String :=
  if s = "" then []
  else ⟨List.take 64 s.data⟩ :: splitToChunks ⟨List.drop 64 s.data⟩

  termination_by (List.length s.data)
  decreasing_by
    apply String.drop_decreases_data_length <;> try assumption
    omega

/-- Encode a bytestring chunk (length byte followed by the payload). -/
def encodeChunk (buf : BitBuffer) (chunk : List UInt8) : BitBuffer :=
  let buf := buf.appendNatBE 8 chunk.length
  chunk.foldl (fun b byte => b.appendByte byte) buf

/-- Encode an arbitrary byte sequence using the bytestring rules (E_{B*}). -/
def encodeByteSeq : Encoder (List UInt8) := fun buf bytes =>
  let buf := BitBuffer.pad buf
  let chunks := chunkByteString bytes
  let buf := chunks.foldl encodeChunk buf
  buf.appendNatBE 8 0

/-- Convert a string to its UTF-8 byte representation. -/
def stringToUTF8Bytes (s : String) : List UInt8 :=
  s.toUTF8.toList

/-- Encode a UTF-8 string (E_{U*}). -/
def encodeString : Encoder String := fun buf s =>
  encodeByteSeq buf (stringToUTF8Bytes s)


/-- Encode a `Data` object by first CBOR-serialising it, then applying E_{B*}. -/
def encodeDataValue : Encoder Data := fun buf d =>
  match CBOR.dataToCBORBytes d with
  | some bytes => encodeByteSeq buf bytes
  | none => buf

--#eval (encodeDataValue BitBuffer.empty (Data.List (Data.I 1 :: Data.I 2 :: Data.I 10 :: []))).pad.toBitString
#eval (encodeString BitBuffer.empty "hi").pad.toBitString

/-
################################################################################
Stage 3: Type + Name encoders
################################################################################
-/

/-- Encode an atomic type as a 4-bit nibble (0–4 or 8). -/
def encodeAtomicType (buf : BitBuffer) (t : AtomicType) : BitBuffer :=
  let tag : Nat :=
    match t with
    | AtomicType.TypeInteger => 0
    | AtomicType.TypeByteString => 1
    | AtomicType.TypeString => 2
    | AtomicType.TypeUnit => 3
    | AtomicType.TypeBool => 4
    | AtomicType.TypeData => 8
  buf.appendNibble tag

/-- Recursively encode a BuiltinType as a sequence of 4-bit tags. -/
def encodeType : Encoder BuiltinType
  | buf, (BuiltinType.AtomicType t) => encodeAtomicType buf t
  | buf, BuiltinType.TypeOperator (TypeOperator.TypeList t) =>
      let buf := buf.appendNibble 7  -- type application tag
      let buf := buf.appendNibble 5  -- list tag
      encodeType buf t
  | buf, BuiltinType.TypeOperator (TypeOperator.TypePair t) =>
      let buf := buf.appendNibble 7  -- type application tag
      let buf := buf.appendNibble 7  -- nested application
      let buf := buf.appendNibble 6  -- pair tag
      encodeType buf t

/-- Convert a BuiltinType to a list of 4-bit tags following spec/flat-serialisation.tex:523-528.
    Returns a list of nibbles representing the type encoding per e_type function. -/
def typeToNibbles : BuiltinType → List Nat
  | BuiltinType.AtomicType t =>
      let tag : Nat :=
        match t with
        | AtomicType.TypeInteger => 0
        | AtomicType.TypeByteString => 1
        | AtomicType.TypeString => 2
        | AtomicType.TypeUnit => 3
        | AtomicType.TypeBool => 4
        | AtomicType.TypeData => 8
      [tag]
  | BuiltinType.TypeOperator (TypeOperator.TypeList t) =>
      [7, 5] ++ typeToNibbles t
  | BuiltinType.TypeOperator (TypeOperator.TypePair t) =>
      [7, 7, 6] ++ typeToNibbles t ++ typeToNibbles t

/-- Encode a BuiltinType as a list of 4-bit nibbles using E_list_4 encoder. -/
def encodeTypeViaList (buf : BitBuffer) (t : BuiltinType) : BitBuffer :=
  let nibbles := typeToNibbles t
  encodeList (fun buf n => buf.appendNibble n) buf nibbles

/-- Encode a variable name (de Bruijn index) using E_ℕ. -/
def encodeName (buf : BitBuffer) (n : Nat) : BitBuffer :=
  encodeNat buf n

/-- Encode a binder name (always 0 for de Bruijn; consumes no input). -/
def encodeBinder (buf : BitBuffer) (_ : Nat) : BitBuffer :=
  buf

/-
################################################################################
Stage 4: Constant encoder
################################################################################
-/

/-- Encode a constant value following spec/flat-serialisation.tex:531-540.
    Type is inferred from the constant via constType.
    NOTE: Uses partial to skip termination proof; recursion is on structural
    sub-constants (lists/pairs), which are guaranteed to terminate. -/
partial def encodeConstant : Encoder Const
  | buf, Const.Integer n =>
      encodeInt buf n
  | buf, Const.ByteString bs =>
      let bytes := bs.data.toList
      encodeByteSeq buf bytes
  | buf, Const.String s =>
      encodeString buf s
  | buf, Const.Unit =>
      buf
  | buf, Const.Bool b =>
      buf.pushBit b
  | buf, Const.Data d =>
      encodeDataValue buf d
  | buf, Const.ConstList elems =>
      encodeList (fun buf elem => encodeConstant buf elem) buf elems
  | buf, Const.Pair (c1, c2) =>
      let buf := encodeConstant buf c1
      encodeConstant buf c2
  | buf, Const.ConstDataList elems =>
      let encodeElem buf elem := encodeConstant buf (Const.Data elem)
      encodeList encodeElem buf elems
  | buf, Const.ConstPairDataList pairs =>
      let encodePair buf (p : Data × Data) :=
        let buf := encodeConstant buf (Const.Data p.1)
        encodeConstant buf (Const.Data p.2)
      encodeList encodePair buf pairs
  | buf, Const.PairData (d1, d2) =>
      let buf := encodeConstant buf (Const.Data d1)
      encodeConstant buf (Const.Data d2)
  | buf, _ => buf

/-
################################################################################
Stage 5: Builtin function tags
################################################################################
-/

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
def encodeBuiltin (buf : BitBuffer) (b : BuiltinFun) : BitBuffer :=
  encodeFixedWidth buf (7, builtinFunTag b)

/-
################################################################################
Stage 6: Term encoder
################################################################################
-/

/-- Encode a term recursively following spec/flat-serialisation.tex:362-408.
    NOTE: Uses partial def to handle recursion on sub-terms. -/
partial def encodeTerm : Encoder Term
  -- Variable: tag 0000, then E_name(x) where x is de Bruijn index
  | buf, Term.Var x =>
      let buf := buf.appendNibble 0
      encodeName buf x
  -- Delay: tag 0001, then recursive encode
  | buf, Term.Delay t =>
      let buf := buf.appendNibble 1
      encodeTerm buf t
  -- Lambda: tag 0010, then E_binder(x), then recursive encode
  | buf, Term.Lam x t =>
      let buf := buf.appendNibble 2
      let buf := encodeBinder buf x
      encodeTerm buf t
  -- Application: tag 0011, encode t1, then encode t2
  | buf, Term.Apply t1 t2 =>
      let buf := buf.appendNibble 3
      let buf := encodeTerm buf t1
      encodeTerm buf t2
  -- Constant: tag 0100, encode type via E_type, then encode constant value
  | buf, Term.Constant c =>
      let buf := buf.appendNibble 4
      let ty := constType c
      let buf := encodeTypeViaList buf ty
      encodeConstant buf c
  -- Force: tag 0101, then recursive encode
  | buf, Term.Force t =>
      let buf := buf.appendNibble 5
      encodeTerm buf t
  -- Error: tag 0110 (no additional data)
  | buf, Term.Error =>
      buf.appendNibble 6
  -- Builtin: tag 0111, then encode builtin function
  | buf, Term.Builtin b =>
      let buf := buf.appendNibble 7
      encodeBuiltin buf b
  -- Constr: tag 1000, encode tag i, then encode term list
  | buf, Term.Constr i terms =>
      let buf := buf.appendNibble 8
      let buf := encodeNat buf i
      encodeList encodeTerm buf terms
  -- Case: tag 1001, encode scrutinee, then encode alternatives
  | buf, Term.Case scrutinee alts =>
      let buf := buf.appendNibble 9
      let buf := encodeTerm buf scrutinee
      encodeList encodeTerm buf alts

/-
################################################################################
Stage 7: Program encoder
################################################################################
-/

/-- Encode a program by encoding the version triple, then the term body,
    then padding to byte boundary following spec/flat-serialisation.tex:333-357. -/
def encodeProgram : Program → BitBuffer
  | ⟨⟨a, b, c⟩, t⟩ =>
      let buf := BitBuffer.empty
      -- Encode version triple: E_N(E_N(E_N(ε, a), b), c)
      let buf := encodeNat buf a
      let buf := encodeNat buf b
      let buf := encodeNat buf c
      -- Encode term body
      let buf := encodeTerm buf t
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
        (Term.Constant (Const.ByteString (ByteArray.mk (Array.mk ([26, 95, 120, 54, 37, 238, 140] : List UInt8)))))
      )
      (Term.Constant (Const.Integer 54321)))

#eval (encodeProgram testProg).formatBitString


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

end Moist.Plutus.Flat
