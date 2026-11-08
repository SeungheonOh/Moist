import Moist.CEK.Value
import Moist.CEK.SemVariant
import Moist.CEK.OpaqueBuiltins
import Moist.Plutus.Types
import Moist.Plutus.DecidableEq
import Moist.Plutus.Value

namespace Moist.CEK

open Moist.Plutus.Term (Const BuiltinType BuiltinFun AtomicType constType dataType pairDataType)
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

/-- Big-endian bytes as a natural number. Bit `i` of a bytestring (CIP-122: bit `i % 8`
of byte `size - 1 - i / 8`) is bit `i` of this number. -/
private def bytesToNatBE (bs : ByteArray) : Nat :=
  bs.data.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The low `len` bytes of `n`, big-endian. -/
private def natToBytesBE (len n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range len).map fun i => (n / 256 ^ (len - 1 - i) % 256).toUInt8)

/-- `shiftByteString` (Bitwise.hs:596): result bit `i` is input bit `i - n`, zero outside. -/
private def shiftBS (bs : ByteArray) (n : Int) : ByteArray :=
  if bs.size == 0 || n == 0 then bs
  else
    let bitLen := bs.size * 8
    if n.natAbs ≥ bitLen then ByteArray.mk (Array.replicate bs.size 0)
    else
      let v := bytesToNatBE bs
      let r := if n > 0 then (v <<< n.toNat) % 2 ^ bitLen else v >>> n.natAbs
      natToBytesBE bs.size r

/-- `rotateByteString` (Bitwise.hs:619): result bit `i` is input bit `(i - n) mod bitLen`. -/
private def rotateBS (bs : ByteArray) (n : Int) : ByteArray :=
  if bs.size == 0 then bs
  else
    let bitLen := bs.size * 8
    let k := (n % (bitLen : Int)).toNat
    if k == 0 then bs
    else
      let v := bytesToNatBE bs
      natToBytesBE bs.size (((v <<< k) ||| (v >>> (bitLen - k))) % 2 ^ bitLen)

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

/-! ### Typed-list helpers -/

private def constListToInts : List Const → Option (List Int)
  | [] => some []
  | .Integer i :: rest => do
    let tail ← constListToInts rest
    some (i :: tail)
  | _ => none

def constListToData : List Const → Option (List Data)
  | [] => some []
  | .Data datum :: rest => return datum :: (← constListToData rest)
  | _ => none

def constListToPairData : List Const → Option (List (Data × Data))
  | [] => some []
  | .Pair (.Data k, .Data v) :: rest => return (k, v) :: (← constListToPairData rest)
  | _ => none

theorem constListToData_map (data : List Data) :
    constListToData (data.map Const.Data) = some data := by
  induction data with
  | nil => rfl
  | cons head tail ih => simp [constListToData, ih]

theorem constListToPairData_map (entries : List (Data × Data)) :
    constListToPairData (entries.map Const.pairData) = some entries := by
  induction entries with
  | nil => rfl
  | cons head tail ih => obtain ⟨k, v⟩ := head; simp [constListToPairData, Const.pairData, ih]

/-! ### Unlifting checks -/

/-- `Int` unlifting (Universe.hs `readKnownAsInteger` for `Int64`): the integer must fit
in 64 signed bits. -/
def int64Ok (i : Int) : Bool := decide (-((2 ^ 63 : Nat) : Int) ≤ i) && decide (i < ((2 ^ 63 : Nat) : Int))

/-- `Word64` unlifting. -/
def word64Ok (i : Int) : Bool := decide (0 ≤ i) && decide (i < ((2 ^ 64 : Nat) : Int))

/-- `Word8` unlifting. -/
def word8Ok (i : Int) : Bool := decide (0 ≤ i) && decide (i < 256)

/-- `maxBoundI` in PlutusCore/Crypto/ExpMod.hs: `2^8191 - 1`. -/
@[irreducible] def expModBound : Int := ((2 ^ 8191 : Nat) : Int) - 1

/-! ### `serialiseData` (PlutusCore/Data.hs `encodeData`) -/

namespace Serialise

/-- CBOR head: major type `m`, argument `n` (minimal encoding, `n < 2^64`). -/
def head (m : Nat) (n : Nat) : List UInt8 :=
  let mt := (m * 32)
  if n < 24 then [(mt + n).toUInt8]
  else if n < 256 then [(mt + 24).toUInt8, n.toUInt8]
  else if n < 65536 then [(mt + 25).toUInt8] ++ (List.range 2).reverse.map (fun i => (n / 256 ^ i % 256).toUInt8)
  else if n < 4294967296 then [(mt + 26).toUInt8] ++ (List.range 4).reverse.map (fun i => (n / 256 ^ i % 256).toUInt8)
  else [(mt + 27).toUInt8] ++ (List.range 8).reverse.map (fun i => (n / 256 ^ i % 256).toUInt8)

/-- Minimal big-endian bytes of a positive natural (`integerToBytesBE`). -/
def natBytes (n : Nat) : List UInt8 :=
  if n = 0 then [0] else go n []
where
  go (n : Nat) (acc : List UInt8) : List UInt8 :=
    if h : n = 0 then acc else go (n / 256) ((n % 256).toUInt8 :: acc)
  termination_by n
  decreasing_by omega

/-- 64-byte chunks. -/
def chunks (bs : List UInt8) : List (List UInt8) :=
  if h : bs.length ≤ 64 then [bs]
  else bs.take 64 :: chunks (bs.drop 64)
termination_by bs.length
decreasing_by simp; omega

/-- `encodeBs`: definite when at most 64 bytes, otherwise indefinite with 64-byte chunks. -/
def bytes (bs : List UInt8) : List UInt8 :=
  if bs.length ≤ 64 then head 2 bs.length ++ bs
  else [0x5f] ++ (chunks bs).flatMap (fun c => head 2 c.length ++ c) ++ [0xff]

/-- `encodeInteger` (PlutusCore/Data.hs:173). -/
def integer (i : Int) : List UInt8 :=
  if 0 ≤ i ∧ i < ((2 ^ 64 : Nat) : Int) then head 0 i.toNat
  else if i < 0 ∧ -((2 ^ 64 : Nat) : Int) ≤ i then head 1 (-1 - i).toNat
  else if 0 ≤ i then head 6 2 ++ bytes (natBytes i.toNat)
  else head 6 3 ++ bytes (natBytes (-1 - i).toNat)

/-- cborg's `encodeInteger` (big integers as tagged definite bytestrings), used for
constructor tags outside `Word64`. -/
def cborgInteger (i : Int) : List UInt8 :=
  if 0 ≤ i ∧ i < ((2 ^ 64 : Nat) : Int) then head 0 i.toNat
  else if i < 0 ∧ -((2 ^ 64 : Nat) : Int) ≤ i then head 1 (-1 - i).toNat
  else if 0 ≤ i then head 6 2 ++ (let b := natBytes i.toNat; head 2 b.length ++ b)
  else head 6 3 ++ (let b := natBytes (-1 - i).toNat; head 2 b.length ++ b)

mutual
  /-- `encodeData`. -/
  def data : Data → List UInt8
    | .Constr i ds =>
      if 0 ≤ i ∧ i < 7 then head 6 (121 + i.toNat) ++ list ds
      else if 7 ≤ i ∧ i < 128 then head 6 (1280 + (i - 7).toNat) ++ list ds
      else head 6 102 ++ head 4 2 ++ cborgInteger i ++ list ds
    | .Map es => head 5 es.length ++ pairs es
    | .List ds => list ds
    | .I i => integer i
    | .B b => bytes b.data.toList
  /-- serialise's list encoding: `[]` is definite, others are indefinite. -/
  def list : List Data → List UInt8
    | [] => [0x80]
    | ds => [0x9f] ++ items ds ++ [0xff]
  def items : List Data → List UInt8
    | [] => []
    | d :: ds => data d ++ items ds
  def pairs : List (Data × Data) → List UInt8
    | [] => []
    | (k, v) :: es => data k ++ data v ++ pairs es
end

end Serialise

/-- `serialiseData`. -/
def serialiseData (d : Data) : ByteArray := ByteArray.mk (Serialise.data d).toArray

/-! ### Helpers for the uninterpreted (crypto) and `Value` builtins -/

/-- The integers of a list constant (`multiScalarMul` scalars). -/
def constListInts : List Const → Option (List Int)
  | [] => some []
  | .Integer i :: rest => return i :: (← constListInts rest)
  | _ => none

/-- The G1 points of a list constant. -/
def constListG1 : List Const → Option (List ByteString)
  | [] => some []
  | .Bls12_381_G1_element p :: rest => return p :: (← constListG1 rest)
  | _ => none

/-- The G2 points of a list constant. -/
def constListG2 : List Const → Option (List ByteString)
  | [] => some []
  | .Bls12_381_G2_element p :: rest => return p :: (← constListG2 rest)
  | _ => none


/-! ## Two-Stage Builtin Evaluation

Stage 1: `evalBuiltinConst` — pure computation on `List Const`, returns `Option Const`.
Stage 2: `evalBuiltinPassThrough` — handles builtins that return a `CekValue` arg unchanged.
`evalBuiltin` composes both stages.

Both are exact transcriptions of the denotations in plutus-core 1.65
`PlutusCore/Default/Builtins.hs` for the semantics variant `sv` (C or E). Type checks
on polymorphic list builtins compare the constants' exact types (`constType`), as the
reference does with `geq` on universe tags.
-/

/-- Pure builtin computation on constants. Every argument is a `Const`.
Returns `none` on type error or runtime failure (e.g. division by zero). -/
def evalBuiltinConst [sv : SemVariant] (b : BuiltinFun) (args : List Const) : Option Const :=
  match b, args with
  -- Integer arithmetic (variant E unlifts both arguments as `CInteger`)
  | .AddInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b then some (.Integer (a + b)) else none
  | .SubtractInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b then some (.Integer (a - b)) else none
  | .MultiplyInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b then some (.Integer (a * b)) else none
  | .DivideInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b && b != 0 then some (.Integer (haskellDiv a b)) else none
  | .QuotientInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b && b != 0 then some (.Integer (a.tdiv b)) else none
  | .RemainderInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b && b != 0 then some (.Integer (a.tmod b)) else none
  | .ModInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b && b != 0 then some (.Integer (haskellMod a b)) else none

  -- Integer comparison
  | .EqualsInteger, [.Integer b, .Integer a] => some (.Bool (a == b))
  | .LessThanInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b then some (.Bool (decide (a < b))) else none
  | .LessThanEqualsInteger, [.Integer b, .Integer a] =>
    if cIntegerOk sv a && cIntegerOk sv b then some (.Bool (decide (a ≤ b))) else none

  -- ByteString operations (variant E unlifts `CByteString` arguments)
  | .AppendByteString, [.ByteString bs2, .ByteString bs1] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then some (.ByteString (bs1 ++ bs2)) else none
  | .EqualsByteString, [.ByteString bs2, .ByteString bs1] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then some (.Bool (bs1 == bs2)) else none
  | .LessThanByteString, [.ByteString bs2, .ByteString bs1] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then some (.Bool (bsLt bs1 bs2)) else none
  | .LessThanEqualsByteString, [.ByteString bs2, .ByteString bs1] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then some (.Bool (bsLe bs1 bs2)) else none
  | .SliceByteString, [.ByteString bs, .Integer len, .Integer start] =>
    if int64Ok start && int64Ok len && cByteStringOk sv bs then
      let startN := if start < 0 then 0 else start.toNat
      let lenN := if len < 0 then 0 else len.toNat
      let endN := min (startN + lenN) bs.size
      let startN := min startN bs.size
      some (.ByteString (bs.extract startN endN))
    else none
  | .LengthOfByteString, [.ByteString bs] =>
    some (.Integer (Int.ofNat bs.size))
  | .IndexByteString, [.Integer idx, .ByteString bs] =>
    if cByteStringOk sv bs && int64Ok idx && 0 ≤ idx && idx < Int.ofNat bs.size then
      some (.Integer (Int.ofNat (bs.get! idx.toNat).toNat))
    else none
  | .ConsByteString, [.ByteString bs, .Integer n] =>
    if word8Ok n && cByteStringOk sv bs then
      some (.ByteString (ByteArray.mk #[n.toNat.toUInt8] ++ bs))
    else none

  -- String operations
  | .AppendString, [.String s2, .String s1] => some (.String (s1 ++ s2))
  | .EqualsString, [.String s2, .String s1] => some (.Bool (s1 == s2))
  | .EncodeUtf8, [.String s] => some (.ByteString s.toUTF8)
  | .DecodeUtf8, [.ByteString bs] =>
    if cByteStringOk sv bs then
      if h : String.validateUTF8 bs then
        some (.String (String.fromUTF8 bs h))
      else none
    else none

  -- Data constructors
  | .ConstrData, [.ConstList ty fields, .Integer tag] =>
    if ty = dataType && (!sv.ensurable || word64Ok tag) then
      return .Data (.Constr tag (← constListToData fields))
    else none
  | .IData, [.Integer i] => some (.Data (.I i))
  | .BData, [.ByteString bs] => some (.Data (.B bs))
  | .ListData, [.ConstList ty fields] =>
    if ty = dataType then return .Data (.List (← constListToData fields)) else none
  | .MapData, [.ConstList ty ps] =>
    if ty = pairDataType then return .Data (.Map (← constListToPairData ps)) else none

  -- Data destructors
  | .UnConstrData, [.Data (.Constr tag fields)] =>
    some (.Pair (.Integer tag, .dataList fields))
  | .UnIData, [.Data (.I i)] => some (.Integer i)
  | .UnBData, [.Data (.B bs)] => some (.ByteString bs)
  | .UnListData, [.Data (.List ds)] => some (.dataList ds)
  | .UnMapData, [.Data (.Map ps)] => some (.pairDataList ps)

  -- Data comparison and serialisation
  | .EqualsData, [.Data b, .Data a] => some (.Bool (a == b))
  | .SerializeData, [.Data d] => some (.ByteString (serialiseData d))

  -- Pair construction
  | .MkPairData, [.Data d2, .Data d1] => some (.pairData (d1, d2))
  | .MkNilData, [.Unit] => some (.dataList [])
  | .MkNilPairData, [.Unit] => some (.pairDataList [])

  -- Pair destructors
  | .FstPair, [.Pair (a, _)] => some a
  | .SndPair, [.Pair (_, b)] => some b

  -- List operations (any element type)
  | .HeadList, [.ConstList _ (h :: _)] => some h
  | .TailList, [.ConstList ty (_ :: t)] => some (.ConstList ty t)
  | .NullList, [.ConstList _ l] => some (.Bool l.isEmpty)
  | .MkCons, [.ConstList ty tail, h] =>
    if constType h = ty then some (.ConstList ty (h :: tail)) else none
  | .DropList, [.ConstList ty l, .Integer n] =>
    if n < 0 then some (.ConstList ty l)
    else if n < ((2 ^ 63 : Nat) : Int) then some (.ConstList ty (l.drop n.toNat))
    -- `drop maxBound`, then a structural failure if anything remains (Builtins.hs DropList)
    else if l.length ≤ 2 ^ 63 - 1 then some (.ConstList ty [])
    else none

  -- Arrays
  | .LengthOfArray, [.ConstArray _ l] => some (.Integer l.length)
  | .ListToArray, [.ConstList ty l] => some (.ConstArray ty l)
  | .IndexArray, [.Integer i, .ConstArray _ l] =>
    if int64Ok i && 0 ≤ i then l[i.toNat]? else none

  -- Bitwise ByteString operations
  | .AndByteString, [.ByteString bs2, .ByteString bs1, .Bool padMode] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then
      some (.ByteString (bitwiseOp (· &&& ·) padMode 0xFF bs1 bs2))
    else none
  | .OrByteString, [.ByteString bs2, .ByteString bs1, .Bool padMode] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then
      some (.ByteString (bitwiseOp (· ||| ·) padMode 0x00 bs1 bs2))
    else none
  | .XorByteString, [.ByteString bs2, .ByteString bs1, .Bool padMode] =>
    if cByteStringOk sv bs1 && cByteStringOk sv bs2 then
      some (.ByteString (bitwiseOp (· ^^^ ·) padMode 0x00 bs1 bs2))
    else none
  | .ComplementByteString, [.ByteString bs] =>
    if cByteStringOk sv bs then some (.ByteString (complementBS bs)) else none
  | .ReadBit, [.Integer idx, .ByteString bs] =>
    if cByteStringOk sv bs && int64Ok idx && 0 ≤ idx then
      match readBitBS bs idx.toNat with
      | some v => some (.Bool v)
      | none => none
    else none
  | .WriteBits, [.Bool val, .ConstList ty idxConsts, .ByteString bs] =>
    if ty = .AtomicType .TypeInteger && (!sv.ensurable || decide (bs.size ≤ 4096)) then
      match constListToInts idxConsts with
      | some indices =>
        match writeBitsHelper bs indices val with
        | some result => some (.ByteString result)
        | none => none
      | none => none
    else none
  | .ReplicateByte, [.Integer byte, .Integer count] =>
    if count < 0 || count > 8192 || !word8Ok byte then none
    else
      some (.ByteString (ByteArray.mk (Array.replicate count.toNat byte.toNat.toUInt8)))
  | .ShiftByteString, [.Integer n, .ByteString bs] =>
    if !sv.ensurable || int64Ok n then some (.ByteString (shiftBS bs n)) else none
  | .RotateByteString, [.Integer n, .ByteString bs] =>
    if !sv.ensurable || int64Ok n then some (.ByteString (rotateBS bs n)) else none
  | .CountSetBits, [.ByteString bs] =>
    if cByteStringOk sv bs then some (.Integer (Int.ofNat (countSetBitsBS bs))) else none
  | .FindFirstSetBit, [.ByteString bs] =>
    if cByteStringOk sv bs then some (.Integer (findFirstSetBitBS bs)) else none

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
    if cByteStringOk sv bs then
      if endian then some (.Integer (bytesToIntBE bs))
      else some (.Integer (bytesToIntLE bs))
    else none

  -- Modular exponentiation (PlutusCore/Crypto/ExpMod.hs)
  | .ExpModInteger, [.Integer m, .Integer e, .Integer b] =>
    if m <= 0 || m > expModBound then none
    else if m == 1 then some (.Integer 0)
    else if b == 0 && e < 0 then none
    else if b > expModBound || b < -expModBound - 1 || e > expModBound || e < -expModBound - 1 then none
    else if e == 0 then some (.Integer 1)
    else if e > 0 then some (.Integer (modPow b e m))
    else
      match modInverse b m with
      | some bInv => some (.Integer (modPow bInv (-e) m))
      | none => none

  -- Hashes and signature verification: uninterpreted (see `Moist.CEK.Opaque`)
  | .Sha2_256, [.ByteString bs] => (Opaque.hash .sha2_256 bs).map .ByteString
  | .Sha3_256, [.ByteString bs] => (Opaque.hash .sha3_256 bs).map .ByteString
  | .Blake2b_224, [.ByteString bs] => (Opaque.hash .blake2b_224 bs).map .ByteString
  | .Blake2b_256, [.ByteString bs] => (Opaque.hash .blake2b_256 bs).map .ByteString
  | .Keccak_256, [.ByteString bs] => (Opaque.hash .keccak_256 bs).map .ByteString
  | .Ripemd_160, [.ByteString bs] => (Opaque.hash .ripemd_160 bs).map .ByteString
  | .VerifyEd25519Signature, [.ByteString sig, .ByteString msg, .ByteString pk] =>
    (Opaque.verifySignature .ed25519 pk msg sig).map .Bool
  | .VerifyEcdsaSecp256k1Signature, [.ByteString sig, .ByteString msg, .ByteString pk] =>
    (Opaque.verifySignature .ecdsaSecp256k1 pk msg sig).map .Bool
  | .VerifySchnorrSecp256k1Signature, [.ByteString sig, .ByteString msg, .ByteString pk] =>
    (Opaque.verifySignature .schnorrSecp256k1 pk msg sig).map .Bool

  -- BLS12-381: uninterpreted (see `Moist.CEK.Opaque`)
  | .Bls12_381_G1_add, [.Bls12_381_G1_element q, .Bls12_381_G1_element p] =>
    (Opaque.blsAdd .g1 p q).map .Bls12_381_G1_element
  | .Bls12_381_G1_neg, [.Bls12_381_G1_element p] =>
    (Opaque.blsNeg .g1 p).map .Bls12_381_G1_element
  | .Bls12_381_G1_scalarMul, [.Bls12_381_G1_element p, .Integer k] =>
    (Opaque.blsScalarMul .g1 k p).map .Bls12_381_G1_element
  | .Bls12_381_G1_equal, [.Bls12_381_G1_element q, .Bls12_381_G1_element p] =>
    (Opaque.blsEqual .g1 p q).map .Bool
  | .Bls12_381_G1_hashToGroup, [.ByteString dst, .ByteString msg] =>
    (Opaque.blsHashToGroup .g1 msg dst).map .Bls12_381_G1_element
  | .Bls12_381_G1_compress, [.Bls12_381_G1_element p] =>
    (Opaque.blsCompress .g1 p).map .ByteString
  | .Bls12_381_G1_uncompress, [.ByteString bs] =>
    (Opaque.blsUncompress .g1 bs).map .Bls12_381_G1_element
  | .Bls12_381_G1_multiScalarMul, [.ConstList pointType points, .ConstList scalarType scalars] => do
    if !(decide (scalarType = .AtomicType .TypeInteger) &&
        decide (pointType = .AtomicType .TypeBls12_381_G1_element)) then none
    let ss ← constListInts scalars
    let ps ← constListG1 points
    (Opaque.blsMultiScalarMul .g1 ss ps).map .Bls12_381_G1_element
  | .Bls12_381_G2_add, [.Bls12_381_G2_element q, .Bls12_381_G2_element p] =>
    (Opaque.blsAdd .g2 p q).map .Bls12_381_G2_element
  | .Bls12_381_G2_neg, [.Bls12_381_G2_element p] =>
    (Opaque.blsNeg .g2 p).map .Bls12_381_G2_element
  | .Bls12_381_G2_scalarMul, [.Bls12_381_G2_element p, .Integer k] =>
    (Opaque.blsScalarMul .g2 k p).map .Bls12_381_G2_element
  | .Bls12_381_G2_equal, [.Bls12_381_G2_element q, .Bls12_381_G2_element p] =>
    (Opaque.blsEqual .g2 p q).map .Bool
  | .Bls12_381_G2_hashToGroup, [.ByteString dst, .ByteString msg] =>
    (Opaque.blsHashToGroup .g2 msg dst).map .Bls12_381_G2_element
  | .Bls12_381_G2_compress, [.Bls12_381_G2_element p] =>
    (Opaque.blsCompress .g2 p).map .ByteString
  | .Bls12_381_G2_uncompress, [.ByteString bs] =>
    (Opaque.blsUncompress .g2 bs).map .Bls12_381_G2_element
  | .Bls12_381_G2_multiScalarMul, [.ConstList pointType points, .ConstList scalarType scalars] => do
    if !(decide (scalarType = .AtomicType .TypeInteger) &&
        decide (pointType = .AtomicType .TypeBls12_381_G2_element)) then none
    let ss ← constListInts scalars
    let ps ← constListG2 points
    (Opaque.blsMultiScalarMul .g2 ss ps).map .Bls12_381_G2_element
  | .Bls12_381_millerLoop, [.Bls12_381_G2_element q, .Bls12_381_G1_element p] =>
    (Opaque.millerLoop p q).map .Bls12_381_MlResult
  | .Bls12_381_mulMlResult, [.Bls12_381_MlResult b, .Bls12_381_MlResult a] =>
    (Opaque.mulMlResult a b).map .Bls12_381_MlResult
  | .Bls12_381_finalVerify, [.Bls12_381_MlResult b, .Bls12_381_MlResult a] =>
    (Opaque.finalVerify a b).map .Bool

  -- Value (faithful, see `Moist.Plutus.Value`)
  | .InsertCoin, [.Value v, .Integer amount, .ByteString token, .ByteString currency] =>
    (Moist.Plutus.Value.insertCoin currency token amount v).map .Value
  | .LookupCoin, [.Value v, .ByteString token, .ByteString currency] =>
    some (.Integer (Moist.Plutus.Value.lookupCoin currency token v))
  | .UnionValue, [.Value b, .Value a] =>
    (Moist.Plutus.Value.unionValue a b).map .Value
  | .ValueContains, [.Value b, .Value a] =>
    (Moist.Plutus.Value.valueContains a b).map .Bool
  | .ValueData, [.Value v] => (Moist.Plutus.Value.valueData v).map .Data
  | .UnValueData, [.Data d] => (Moist.Plutus.Value.unValueData d).map .Value
  | .ScaleValue, [.Value v, .Integer factor] =>
    (Moist.Plutus.Value.scaleValue factor v).map .Value

  -- Fallthrough
  | _, _ => none

/-- Pass-through builtins: return a `CekValue` argument unchanged based on a
`VCon` condition. -/
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

  -- ChooseList [consCase, nilCase, VCon (ConstList l)]
  | .ChooseList, [consCase, nilCase, .VCon (.ConstList _ l)] =>
    some (if l.isEmpty then nilCase else consCase)

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
def evalBuiltin [sv : SemVariant] (b : BuiltinFun) (args : List CekValue) : Option CekValue :=
  match evalBuiltinPassThrough b args with
  | some v => some v
  | none =>
    match extractConsts args with
    | some consts =>
      match evalBuiltinConst b consts with
      | some c => some (.VCon c)
      | none => none
    | none => none

theorem extractConsts_map (cs : List Const) : extractConsts (cs.map CekValue.VCon) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [extractConsts, ih]

/-- A non-pass-through saturated builtin over constants is `evalBuiltinConst`. -/
theorem evalBuiltin_consts [SemVariant] (b : BuiltinFun) (cs : List Const)
    (hp : evalBuiltinPassThrough b (cs.map CekValue.VCon) = none) :
    evalBuiltin b (cs.map CekValue.VCon) = (evalBuiltinConst b cs).map CekValue.VCon := by
  unfold evalBuiltin
  rw [hp]
  simp only [extractConsts_map]
  cases evalBuiltinConst b cs <;> rfl

/-- A guarded builtin arm that succeeded produced its guarded result. -/
theorem eq_of_ite_some {α : Type} {p : Prop} {inst : Decidable p} {a c : α}
    (h : @ite (Option α) p inst (some a) none = some c) : c = a := by
  by_cases hp : p
  · rw [if_pos hp] at h; cases h; rfl
  · rw [if_neg hp] at h; cases h

/-- A guarded builtin arm that succeeded had its guard satisfied. -/
theorem cond_of_ite_some {α : Type} {p : Prop} {inst : Decidable p} {a c : α}
    (h : @ite (Option α) p inst (some a) none = some c) : p := by
  by_cases hp : p
  · exact hp
  · rw [if_neg hp] at h; cases h

/-- The constant result of a saturated builtin when every semantics variant agrees on
it. Compile-time folding uses this so that a fold is sound whichever variant runs. -/
def evalBuiltinAgreed (b : BuiltinFun) (args : List CekValue) : Option Const :=
  match evalBuiltin (sv := .C) b args, evalBuiltin (sv := .E) b args with
  | some (.VCon c), some (.VCon c') => if c = c' then some c else none
  | _, _ => none

theorem evalBuiltinAgreed_spec {b : BuiltinFun} {args : List CekValue} {c : Const}
    (h : evalBuiltinAgreed b args = some c) [sv : SemVariant] :
    evalBuiltin b args = some (.VCon c) := by
  unfold evalBuiltinAgreed at h
  split at h
  · rename_i c₁ c₂ hC hE
    split at h
    · rename_i heq
      cases h
      cases sv
      · exact hC
      · rw [hE, ← heq]
    · contradiction
  · contradiction

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
