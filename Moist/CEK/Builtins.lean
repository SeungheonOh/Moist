import Moist.CEK.Value
import Moist.Plutus.Types

namespace Moist.CEK

open Moist.Plutus.Term (Const BuiltinType BuiltinFun AtomicType)
open Moist.Plutus (Data ByteString Integer)

/-! # Builtin Argument Signatures and Evaluation

Defines the expected argument signature for each Plutus builtin
(forces via ArgQ, values via ArgV) and the evaluation function
for saturated builtins.

Following sc-fvt's `ExpectedBuiltinArgs` mechanism. Each builtin
has a fixed signature. When arguments/forces are applied, the
signature is consumed one step at a time. When fully consumed,
the builtin is saturated and evaluated.

## Argument accumulation

Arguments accumulate in **reverse** order in the `VBuiltin` value's
argument list. The most recently applied argument is at the head.
Builtin evaluation functions match arguments in this reversed order.
-/

/-! ## Argument Signatures -/

private def v : ArgKind := .argV
private def q : ArgKind := .argQ

/-- Build the expected argument signature for a builtin.
Notation: `q` = Force (type instantiation), `v` = Apply (value). -/
def expectedArgs : BuiltinFun → ExpectedArgs
  -- Integer (all: v v)
  | .AddInteger | .SubtractInteger | .MultiplyInteger
  | .DivideInteger | .QuotientInteger | .RemainderInteger | .ModInteger
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger =>
    .more v (.one v)
  -- ByteString
  | .AppendByteString | .EqualsByteString
  | .LessThanByteString | .LessThanEqualsByteString
  | .ConsByteString | .IndexByteString =>
    .more v (.one v)
  | .SliceByteString => .more v (.more v (.one v))
  | .LengthOfByteString => .one v
  -- Cryptography (batch 1)
  | .Sha2_256 | .Sha3_256 | .Blake2b_256 => .one v
  | .VerifyEd25519Signature => .more v (.more v (.one v))
  -- Strings
  | .AppendString | .EqualsString => .more v (.one v)
  | .EncodeUtf8 | .DecodeUtf8 => .one v
  -- Bool: IfThenElse is polymorphic (1 force + 3 values)
  | .IfThenElse => .more q (.more v (.more v (.one v)))
  -- Unit: ChooseUnit (1 force + 2 values)
  | .ChooseUnit => .more q (.more v (.one v))
  -- Tracing: Trace (1 force + 2 values)
  | .Trace => .more q (.more v (.one v))
  -- Pairs (2 forces + 1 value)
  | .FstPair | .SndPair => .more q (.more q (.one v))
  -- Lists
  | .ChooseList => .more q (.more q (.more v (.more v (.one v))))
  | .MkCons => .more q (.more v (.one v))
  | .HeadList | .TailList | .NullList => .more q (.one v)
  -- Data
  | .ChooseData => .more q (.more v (.more v (.more v (.more v (.more v (.one v))))))
  | .ConstrData => .more v (.one v)
  | .MapData | .ListData | .IData | .BData => .one v
  | .UnConstrData | .UnMapData | .UnListData | .UnIData | .UnBData => .one v
  | .EqualsData => .more v (.one v)
  -- Misc constructors
  | .MkPairData => .more v (.one v)
  | .MkNilData | .MkNilPairData => .one v
  -- Batch 2
  | .SerializeData => .one v
  -- Batch 3
  | .VerifyEcdsaSecp256k1Signature | .VerifySchnorrSecp256k1Signature =>
    .more v (.more v (.one v))
  -- BLS
  | .Bls12_381_G1_add | .Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal | .Bls12_381_G1_hashToGroup =>
    .more v (.one v)
  | .Bls12_381_G1_neg | .Bls12_381_G1_compress | .Bls12_381_G1_uncompress =>
    .one v
  | .Bls12_381_G2_add | .Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal | .Bls12_381_G2_hashToGroup =>
    .more v (.one v)
  | .Bls12_381_G2_neg | .Bls12_381_G2_compress | .Bls12_381_G2_uncompress =>
    .one v
  | .Bls12_381_millerLoop | .Bls12_381_mulMlResult | .Bls12_381_finalVerify =>
    .more v (.one v)
  -- Crypto batch 4
  | .Keccak_256 | .Blake2b_224 => .one v
  | .IntegerToByteString => .more v (.more v (.one v))
  | .ByteStringToInteger => .more v (.one v)
  -- Batch 5
  | .AndByteString | .OrByteString | .XorByteString =>
    .more v (.more v (.one v))
  | .ComplementByteString => .one v
  | .ReadBit => .more v (.one v)
  | .WriteBits => .more v (.more v (.one v))
  | .ReplicateByte => .more v (.one v)
  | .ShiftByteString | .RotateByteString => .more v (.one v)
  | .CountSetBits | .FindFirstSetBit => .one v
  | .Ripemd_160 => .one v
  -- Batch 6
  | .ExpModInteger => .more v (.more v (.one v))
  -- Batch 7
  | .DropList => .more q (.more v (.one v))
  | .IndexArray => .more q (.more v (.one v))
  | .LengthOfArray => .more q (.one v)
  | .ListToArray => .more q (.one v)
  | .InsertCoin => .more v (.more v (.more v (.one v)))
  | .LookupCoin => .more v (.more v (.one v))
  | .ScaleValue => .more v (.one v)
  | .UnionValue => .more v (.one v)
  | .ValueContains => .more v (.one v)
  | .ValueData => .one v
  | .UnValueData => .one v
  | .Bls12_381_G1_multiScalarMul => .more v (.one v)
  | .Bls12_381_G2_multiScalarMul => .more v (.one v)

/-! ## Builtin Evaluation

Comprehensive implementation of Plutus builtins. Returns `none` on
type error or runtime failure (e.g. division by zero), which the
machine maps to `State.error`.

Arguments are in **reversed** order (most recent first).
-/

/-! ### Integer Division Helpers

Haskell-style `div` rounds toward negative infinity, while Lean's `/`
truncates toward zero. We implement `haskellDiv` and `haskellMod`
to match Plutus semantics for `divideInteger` and `modInteger`.
-/

/-- Haskell `div`: rounds toward negative infinity.
Uses `Int.tdiv` (truncation toward zero) as a base. -/
private def haskellDiv (a b : Int) : Int :=
  let q := a.tdiv b
  let r := a.tmod b
  if r == 0 || (a >= 0) == (b >= 0) then q else q - 1

/-- Haskell `mod`: result has sign of divisor. -/
private def haskellMod (a b : Int) : Int :=
  a - b * haskellDiv a b

/-! ### ByteString Helpers -/

/-- Lexicographic less-than for ByteArrays. -/
private def bsLt (a b : ByteArray) : Bool :=
  let len := min a.size b.size
  go 0 len a b
where
  go (i len : Nat) (a b : ByteArray) : Bool :=
    if i >= len then a.size < b.size
    else
      let ai := a.get! i
      let bi := b.get! i
      if ai < bi then true
      else if ai > bi then false
      else go (i + 1) len a b

/-- Lexicographic less-than-or-equal for ByteArrays. -/
private def bsLe (a b : ByteArray) : Bool :=
  let len := min a.size b.size
  go 0 len a b
where
  go (i len : Nat) (a b : ByteArray) : Bool :=
    if i >= len then a.size <= b.size
    else
      let ai := a.get! i
      let bi := b.get! i
      if ai < bi then true
      else if ai > bi then false
      else go (i + 1) len a b

/-! ### Bitwise ByteString Helpers -/

/-- Bitwise operation with padding. `padByte` is the identity element for padding:
AND uses 0xFF, OR/XOR use 0x00. -/
private def bitwiseOp (f : UInt8 → UInt8 → UInt8) (pad : Bool) (padByte : UInt8)
    (bs1 bs2 : ByteArray) : ByteArray := Id.run do
  if pad then
    let len := max bs1.size bs2.size
    let mut result := ByteArray.emptyWithCapacity len
    for i in [:len] do
      let a := if i < bs1.size then bs1.get! i else padByte
      let b := if i < bs2.size then bs2.get! i else padByte
      result := result.push (f a b)
    return result
  else
    let len := min bs1.size bs2.size
    let mut result := ByteArray.emptyWithCapacity len
    for i in [:len] do
      result := result.push (f (bs1.get! i) (bs2.get! i))
    return result

private def complementBS (bs : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.emptyWithCapacity bs.size
  for i in [:bs.size] do
    result := result.push (bs.get! i ^^^ 0xFF)
  return result

private def readBitBS (bs : ByteArray) (idx : Nat) : Option Bool :=
  let byteIdx := bs.size - 1 - idx / 8
  let bitIdx := idx % 8
  if idx / 8 >= bs.size then none
  else
    let byte := bs.get! byteIdx
    let mask : UInt8 := 1 <<< bitIdx.toUInt8
    some ((byte &&& mask) != 0)

private def writeBitBS (bs : ByteArray) (idx : Nat) (val : Bool) : Option ByteArray :=
  let byteIdx := bs.size - 1 - idx / 8
  let bitIdx := idx % 8
  if idx / 8 >= bs.size then none
  else
    let byte := bs.get! byteIdx
    let mask : UInt8 := 1 <<< bitIdx.toUInt8
    let newByte := if val then byte ||| mask else byte &&& (mask ^^^ 0xFF)
    some (bs.set! byteIdx newByte)

private def writeBitsHelper (bs : ByteArray) (indices : List Int)
    (val : Bool) : Option ByteArray :=
  match indices with
  | [] => some bs
  | i :: is =>
    if i < 0 then none
    else match writeBitBS bs i.toNat val with
      | some bs' => writeBitsHelper bs' is val
      | none => none

private def shiftBS (bs : ByteArray) (n : Int) : ByteArray := Id.run do
  if bs.size == 0 then return bs
  let totalBits := bs.size * 8
  let absN := n.natAbs
  if absN >= totalBits then return ByteArray.mk (Array.replicate bs.size 0)
  if n > 0 then
    -- Shift left: high bits disappear, low bits filled with 0
    let byteShift := absN / 8
    let bitShift := absN % 8
    let mut result := ByteArray.mk (Array.replicate bs.size 0)
    for i in [:bs.size] do
      let srcIdx := i + byteShift
      if srcIdx < bs.size then
        let current := bs.get! srcIdx
        let shifted := current <<< bitShift.toUInt8
        let carry := if srcIdx + 1 < bs.size then
          bs.get! (srcIdx + 1) >>> (8 - bitShift).toUInt8
        else 0
        result := result.set! i (shifted ||| carry)
    return result
  else if n < 0 then
    -- Shift right: low bits disappear, high bits filled with 0
    let byteShift := absN / 8
    let bitShift := absN % 8
    let mut result := ByteArray.mk (Array.replicate bs.size 0)
    for i in [:bs.size] do
      if i >= byteShift then
        let srcIdx := i - byteShift
        let current := bs.get! srcIdx
        let shifted := current >>> bitShift.toUInt8
        let carry := if srcIdx > 0 then
          bs.get! (srcIdx - 1) <<< (8 - bitShift).toUInt8
        else 0
        result := result.set! i (shifted ||| carry)
    return result
  else return bs

private def rotateBS (bs : ByteArray) (n : Int) : ByteArray := Id.run do
  if bs.size == 0 then return bs
  let totalBits := bs.size * 8
  -- Normalize rotation to [0, totalBits)
  let norm := n % Int.ofNat totalBits
  let norm := if norm < 0 then norm + Int.ofNat totalBits else norm
  if norm == 0 then return bs
  -- Rotate left by norm bits: shifted = (bs << norm) | (bs >> (total - norm))
  let left := shiftBS bs norm
  let right := shiftBS bs (norm - Int.ofNat totalBits)
  let mut result := ByteArray.emptyWithCapacity bs.size
  for i in [:bs.size] do
    result := result.push (left.get! i ||| right.get! i)
  return result

private def popcount8 (b : UInt8) : Nat :=
  let c0 := if b &&& 0x01 != 0 then 1 else 0
  let c1 := if b &&& 0x02 != 0 then 1 else 0
  let c2 := if b &&& 0x04 != 0 then 1 else 0
  let c3 := if b &&& 0x08 != 0 then 1 else 0
  let c4 := if b &&& 0x10 != 0 then 1 else 0
  let c5 := if b &&& 0x20 != 0 then 1 else 0
  let c6 := if b &&& 0x40 != 0 then 1 else 0
  let c7 := if b &&& 0x80 != 0 then 1 else 0
  c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7

private def countSetBitsBS (bs : ByteArray) : Nat :=
  go bs 0 0
where
  go (bs : ByteArray) (i acc : Nat) : Nat :=
    if i >= bs.size then acc
    else go bs (i + 1) (acc + popcount8 (bs.get! i))

private def findFirstSetBitBS (bs : ByteArray) : Int :=
  go bs 0 (bs.size * 8)
where
  go (bs : ByteArray) (bitIdx totalBits : Nat) : Int :=
    if bitIdx >= totalBits then -1
    else
      let byteIdx := bs.size - 1 - bitIdx / 8
      let bitInByte := bitIdx % 8
      let byte := bs.get! byteIdx
      let mask : UInt8 := 1 <<< bitInByte.toUInt8
      if (byte &&& mask) != 0 then Int.ofNat bitIdx
      else go bs (bitIdx + 1) totalBits
  termination_by totalBits - bitIdx

/-! ### Integer/ByteString Conversion Helpers -/

/-- Convert a non-negative integer to big-endian ByteString with minimal encoding.
Zero produces an empty ByteArray (Plutus convention for unbounded width). -/
private partial def intToBytesBE (n : Int) : ByteArray :=
  if n == 0 then ByteArray.empty
  else go n.toNat []
where
  go (remaining : Nat) (acc : List UInt8) : ByteArray :=
    if remaining == 0 then ByteArray.mk acc.toArray
    else go (remaining / 256) (remaining.toUInt8 :: acc)

/-- Convert a big-endian ByteString to a non-negative integer. -/
private def bytesToIntBE (bs : ByteArray) : Int :=
  go bs 0 0
where
  go (bs : ByteArray) (i : Nat) (acc : Nat) : Int :=
    if i >= bs.size then Int.ofNat acc
    else go bs (i + 1) (acc * 256 + (bs.get! i).toNat)

/-- Convert a little-endian ByteString to a non-negative integer. -/
private def bytesToIntLE (bs : ByteArray) : Int :=
  go bs 0 0 1
where
  go (bs : ByteArray) (i : Nat) (acc base : Nat) : Int :=
    if i >= bs.size then Int.ofNat acc
    else go bs (i + 1) (acc + (bs.get! i).toNat * base) (base * 256)

/-- Reverse a ByteArray. -/
private def reverseBA (bs : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.emptyWithCapacity bs.size
  for i in [:bs.size] do
    result := result.push (bs.get! (bs.size - 1 - i))
  return result

/-- Convert a non-negative integer to ByteString.
`endian`: 0=big-endian, 1=little-endian.
`size`: 0=minimal, >0=pad or clamp to exact size. -/
private def integerToBS (n : Int) (size : Nat) (endian : Int) : Option ByteArray :=
  if n < 0 then none
  else
    let be := intToBytesBE n
    let padded :=
      if size == 0 then some be
      else if be.size > size then none
      else
        -- Pad with leading zeros (big-endian)
        let padding := ByteArray.mk (Array.replicate (size - be.size) 0)
        some (padding ++ be)
    match padded with
    | none => none
    | some bs => if endian == 1 then some (reverseBA bs) else some bs

/-! ### Modular Arithmetic Helpers -/

/-- Modular exponentiation: `b ^ e mod m` for `e >= 0`, `m > 0`.
Uses binary exponentiation (square-and-multiply). -/
private partial def modPow (b e m : Int) : Int :=
  if m == 1 then 0
  else go (((b % m) + m) % m) e 1  -- normalize base to [0, m)
where
  go (base exp acc : Int) : Int :=
    if exp <= 0 then acc % m
    else
      let acc' := if exp % 2 == 1 then (acc * base) % m else acc
      go ((base * base) % m) (exp / 2) acc'

/-- Extended GCD: returns (g, x, y) such that a*x + b*y = g = gcd(a, b). -/
private partial def extGcd (a b : Int) : Int × Int × Int :=
  if a == 0 then (b, 0, 1)
  else
    let (g, x, y) := extGcd (b.tmod a) a
    (g, y - (b.tdiv a) * x, x)

/-- Modular inverse of `a` modulo `m`. Returns `none` if gcd(a, m) > 1. -/
private def modInverse (a m : Int) : Option Int :=
  let (g, x, _) := extGcd (((a % m) + m) % m) m
  if g != 1 then none
  else some (((x % m) + m) % m)

/-! ### ConstList helpers for extracting typed elements -/

private def constListToInts : List Const → Option (List Int)
  | [] => some []
  | .Integer i :: rest => do
    let tail ← constListToInts rest
    some (i :: tail)
  | _ => none

/-! ## Two-Stage Builtin Evaluation

Stage 1: `evalBuiltinConst` — pure computation on `List Const`, returns `Option Const`.
Stage 2: `evalBuiltinPassThrough` — handles builtins that return a `CekValue` arg unchanged.
`evalBuiltin` composes both stages.
-/

/-- Pure builtin computation on constants. Every argument is a `Const`.
Returns `none` on type error or runtime failure (e.g. division by zero). -/
def evalBuiltinConst (b : BuiltinFun) (args : List Const) : Option Const :=
  match b, args with
  -- Integer arithmetic
  | .AddInteger, [.Integer b, .Integer a] => some (.Integer (a + b))
  | .SubtractInteger, [.Integer b, .Integer a] => some (.Integer (a - b))
  | .MultiplyInteger, [.Integer b, .Integer a] => some (.Integer (a * b))
  | .DivideInteger, [.Integer b, .Integer a] =>
    if b == 0 then none else some (.Integer (haskellDiv a b))
  | .QuotientInteger, [.Integer b, .Integer a] =>
    if b == 0 then none else some (.Integer (a.tdiv b))
  | .RemainderInteger, [.Integer b, .Integer a] =>
    if b == 0 then none else some (.Integer (a.tmod b))
  | .ModInteger, [.Integer b, .Integer a] =>
    if b == 0 then none else some (.Integer (haskellMod a b))

  -- Integer comparison
  | .EqualsInteger, [.Integer b, .Integer a] => some (.Bool (a == b))
  | .LessThanInteger, [.Integer b, .Integer a] => some (.Bool (a < b))
  | .LessThanEqualsInteger, [.Integer b, .Integer a] => some (.Bool (a ≤ b))

  -- ByteString operations
  | .AppendByteString, [.ByteString bs2, .ByteString bs1] =>
    some (.ByteString (bs1 ++ bs2))
  | .EqualsByteString, [.ByteString bs2, .ByteString bs1] =>
    some (.Bool (bs1 == bs2))
  | .LessThanByteString, [.ByteString bs2, .ByteString bs1] =>
    some (.Bool (bsLt bs1 bs2))
  | .LessThanEqualsByteString, [.ByteString bs2, .ByteString bs1] =>
    some (.Bool (bsLe bs1 bs2))
  | .SliceByteString, [.ByteString bs, .Integer len, .Integer start] =>
    let startN := if start < 0 then 0 else start.toNat
    let lenN := if len < 0 then 0 else len.toNat
    let endN := min (startN + lenN) bs.size
    let startN := min startN bs.size
    some (.ByteString (bs.extract startN endN))
  | .LengthOfByteString, [.ByteString bs] =>
    some (.Integer (Int.ofNat bs.size))
  | .IndexByteString, [.Integer idx, .ByteString bs] =>
    if idx < 0 || idx >= Int.ofNat bs.size then none
    else some (.Integer (Int.ofNat (bs.get! idx.toNat).toNat))
  | .ConsByteString, [.ByteString bs, .Integer n] =>
    if n < 0 || n > 255 then none
    else some (.ByteString (ByteArray.mk #[n.toNat.toUInt8] ++ bs))

  -- String operations
  | .AppendString, [.String s2, .String s1] => some (.String (s1 ++ s2))
  | .EqualsString, [.String s2, .String s1] => some (.Bool (s1 == s2))
  | .EncodeUtf8, [.String s] => some (.ByteString s.toUTF8)
  | .DecodeUtf8, [.ByteString bs] =>
    if h : String.validateUTF8 bs then
      some (.String (String.fromUTF8 bs h))
    else none

  -- Data constructors
  | .ConstrData, [.ConstDataList fields, .Integer tag] =>
    some (.Data (.Constr tag fields))
  | .IData, [.Integer i] => some (.Data (.I i))
  | .BData, [.ByteString bs] => some (.Data (.B bs))
  | .ListData, [.ConstDataList ds] => some (.Data (.List ds))
  | .MapData, [.ConstPairDataList ps] => some (.Data (.Map ps))

  -- Data destructors
  | .UnConstrData, [.Data (.Constr tag fields)] =>
    some (.PairData (Data.I tag, Data.List fields))
  | .UnIData, [.Data (.I i)] => some (.Integer i)
  | .UnBData, [.Data (.B bs)] => some (.ByteString bs)
  | .UnListData, [.Data (.List ds)] => some (.ConstDataList ds)
  | .UnMapData, [.Data (.Map ps)] => some (.ConstPairDataList ps)

  -- Data comparison
  | .EqualsData, [.Data b, .Data a] => some (.Bool (a == b))

  -- Pair construction
  | .MkPairData, [.Data d2, .Data d1] => some (.PairData (d1, d2))
  | .MkNilData, [.Unit] => some (.ConstDataList [])
  | .MkNilPairData, [.Unit] => some (.ConstPairDataList [])

  -- Pair destructors
  | .FstPair, [.PairData (a, _)] => some (.Data a)
  | .FstPair, [.Pair (a, _)] => some a
  | .SndPair, [.PairData (_, b)] => some (.Data b)
  | .SndPair, [.Pair (_, b)] => some b

  -- List operations (ConstDataList)
  | .HeadList, [.ConstDataList (h :: _)] => some (.Data h)
  | .HeadList, [.ConstDataList []] => none
  | .TailList, [.ConstDataList (_ :: t)] => some (.ConstDataList t)
  | .TailList, [.ConstDataList []] => none
  | .NullList, [.ConstDataList l] => some (.Bool l.isEmpty)
  | .MkCons, [.ConstDataList tail, .Data h] =>
    some (.ConstDataList (h :: tail))
  | .MkCons, [.ConstList tail, c] =>
    some (.ConstList (c :: tail))

  -- List operations (ConstList)
  | .HeadList, [.ConstList (h :: _)] => some h
  | .HeadList, [.ConstList []] => none
  | .TailList, [.ConstList (_ :: t)] => some (.ConstList t)
  | .TailList, [.ConstList []] => none
  | .NullList, [.ConstList l] => some (.Bool l.isEmpty)

  -- Bitwise ByteString operations
  | .AndByteString, [.ByteString bs2, .ByteString bs1, .Bool padMode] =>
    some (.ByteString (bitwiseOp (· &&& ·) padMode 0xFF bs1 bs2))
  | .OrByteString, [.ByteString bs2, .ByteString bs1, .Bool padMode] =>
    some (.ByteString (bitwiseOp (· ||| ·) padMode 0x00 bs1 bs2))
  | .XorByteString, [.ByteString bs2, .ByteString bs1, .Bool padMode] =>
    some (.ByteString (bitwiseOp (· ^^^ ·) padMode 0x00 bs1 bs2))
  | .ComplementByteString, [.ByteString bs] =>
    some (.ByteString (complementBS bs))
  | .ReadBit, [.Integer idx, .ByteString bs] =>
    if idx < 0 then none
    else match readBitBS bs idx.toNat with
      | some v => some (.Bool v)
      | none => none
  | .WriteBits, [.Bool val, .ConstList idxConsts, .ByteString bs] =>
    match constListToInts idxConsts with
    | some indices =>
      match writeBitsHelper bs indices val with
      | some result => some (.ByteString result)
      | none => none
    | none => none
  | .ReplicateByte, [.Integer byte, .Integer count] =>
    if count < 0 || count > 8192 || byte < 0 || byte > 255 then none
    else
      some (.ByteString (ByteArray.mk (Array.replicate count.toNat byte.toNat.toUInt8)))
  | .ShiftByteString, [.Integer n, .ByteString bs] =>
    some (.ByteString (shiftBS bs n))
  | .RotateByteString, [.Integer n, .ByteString bs] =>
    some (.ByteString (rotateBS bs n))
  | .CountSetBits, [.ByteString bs] =>
    some (.Integer (Int.ofNat (countSetBitsBS bs)))
  | .FindFirstSetBit, [.ByteString bs] =>
    some (.Integer (findFirstSetBitBS bs))

  -- Integer/ByteString conversions
  | .IntegerToByteString, [.Integer n, .Integer width, .Bool endian] =>
    if n < 0 || width < 0 || width > 8192 then none
    else
      let endianInt : Int := if endian then 0 else 1
      match integerToBS n width.toNat endianInt with
      | some bs =>
        if width == 0 && bs.size > 8192 then none
        else some (.ByteString bs)
      | none => none
  | .ByteStringToInteger, [.ByteString bs, .Bool endian] =>
    if endian then some (.Integer (bytesToIntBE bs))
    else some (.Integer (bytesToIntLE bs))

  -- Modular exponentiation
  | .ExpModInteger, [.Integer m, .Integer e, .Integer b] =>
    if m <= 0 then none
    else if m == 1 then some (.Integer 0)
    else if e == 0 then some (.Integer 1)
    else if e > 0 then some (.Integer (modPow b e m))
    else
      match modInverse b m with
      | some bInv => some (.Integer (modPow bInv (-e) m))
      | none => none

  -- DropList
  | .DropList, [.ConstList l, .Integer n] =>
    if n < 0 then some (.ConstList l)
    else some (.ConstList (l.drop n.toNat))
  | .DropList, [.ConstDataList l, .Integer n] =>
    if n < 0 then some (.ConstDataList l)
    else some (.ConstDataList (l.drop n.toNat))

  -- Fallthrough
  | _, _ => none

/-- Pass-through builtins: return a `CekValue` argument unchanged based on a
`VCon` condition. Only 5 builtins (+MkCons ConstList) need this treatment. -/
def evalBuiltinPassThrough (b : BuiltinFun) (args : List CekValue) : Option CekValue :=
  match b, args with
  -- IfThenElse [elseV, thenV, VCon (Bool cond)]
  | .IfThenElse, [elseV, thenV, .VCon (.Bool cond)] =>
    some (if cond then thenV else elseV)

  -- ChooseUnit [result, VCon Unit]
  | .ChooseUnit, [result, .VCon .Unit] => some result

  -- Trace [result, VCon (String _)]
  | .Trace, [result, .VCon (.String _)] => some result

  -- ChooseData [bCase, iCase, listCase, mapCase, constrCase, VCon (Data d)]
  | .ChooseData, [bCase, iCase, listCase, mapCase, constrCase,
                   .VCon (.Data d)] =>
    match d with
    | .Constr _ _ => some constrCase
    | .Map _ => some mapCase
    | .List _ => some listCase
    | .I _ => some iCase
    | .B _ => some bCase

  -- ChooseList [consCase, nilCase, VCon (ConstDataList l)]
  | .ChooseList, [consCase, nilCase, .VCon (.ConstDataList l)] =>
    some (if l.isEmpty then nilCase else consCase)
  -- ChooseList [consCase, nilCase, VCon (ConstList l)]
  | .ChooseList, [consCase, nilCase, .VCon (.ConstList l)] =>
    some (if l.isEmpty then nilCase else consCase)

  -- MkCons ConstList: the element can be any CekValue (pass-through of sorts)
  | .MkCons, [.VCon (.ConstList tail), elem] =>
    match elem with
    | .VCon c => some (.VCon (.ConstList (c :: tail)))
    | _ => none

  | _, _ => none

/-- Extract constants from a list of `CekValue`s. Returns `none` if any
element is not `VCon`. -/
def extractConsts : List CekValue → Option (List Const)
  | [] => some []
  | .VCon c :: rest => do let cs ← extractConsts rest; some (c :: cs)
  | _ :: _ => none

/-- Evaluate a fully saturated builtin. Returns `none` on failure.

Tries pass-through builtins first (which may return non-VCon args unchanged),
then falls back to extracting all constants and running `evalBuiltinConst`. -/
def evalBuiltin (b : BuiltinFun) (args : List CekValue) : Option CekValue :=
  match evalBuiltinPassThrough b args with
  | some v => some v
  | none =>
    match extractConsts args with
    | some consts =>
      match evalBuiltinConst b consts with
      | some c => some (.VCon c)
      | none => none
    | none => none

/-! ## evalBuiltinPassThrough relational lemmas

Each pass-through builtin gets a small relV lemma. The VCon condition arg
is determined by pattern matching (same on both sides when vconProj matches).
The pass-through args are returned unchanged, preserving any relation. -/

/-- evalBuiltinPassThrough only matches on BuiltinFun + arg-list shape.
For non-matching builtins it returns none. We can case-split on b cheaply
because evalBuiltinPassThrough is tiny (~7 arms). -/
theorem evalBuiltinPassThrough_none_of_not_passthrough (b : BuiltinFun) (args : List CekValue)
    (hb : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧ b ≠ .ChooseData ∧
          b ≠ .ChooseList ∧ b ≠ .MkCons) :
    evalBuiltinPassThrough b args = none := by
  cases b <;> simp_all [evalBuiltinPassThrough]

end Moist.CEK
