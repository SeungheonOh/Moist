-- --import PlutusCore.ByteString
import PlutusCore.Data
import PlutusCore.ByteString
-- import Flat.CBOR

namespace Moist
namespace Plutus

open PlutusCore.ByteString
open PlutusCore.Data

/-- Produce the big-endian list of bits representing `value` using `width` bits. -/
def bitsOfNatBE (width value : Nat) : List Bool :=
  (List.range width).map fun idx =>
    let bitIndex := width - 1 - idx
    Nat.testBit value bitIndex

/--
Decompose a natural number into base-128 digits (least significant digit first).
The resulting list is never empty (`0` encodes as `[0]`).
-/
def base128Digits (n : Nat) : List Nat :=
  if n = 0 then
    [0]
  else
    let rec loop (value : Nat) (acc : List Nat) : List Nat :=
      let digit := value % 128
      let next := value / 128
      let acc := digit :: acc
      if next = 0 then
        acc
      else
        loop next acc
    (loop n []).reverse

/--
Split a list into the prefix (everything except the last element) together with
the final element.  This function is only used with lists that are known to be
nonempty.
-/
def splitInitLast (xs : List Nat) : List Nat × Nat :=
  match xs with
  | [] => ([], 0)
  | [x] => ([], x)
  | x :: rest =>
      let (init, last) := splitInitLast rest
      (x :: init, last)

/-- Zig-zag encoding for signed integers (Definition 3.4.5). -/
def zigZag : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * (n.succ) - 1

/--
`BitBuffer` stores the bits that have been emitted so far while constructing a
`flat` encoding.  Bits are kept in the order they were emitted (most recent bits
are appended to the end of `bits`), matching the `s ⋅ …` presentation in the
specification.
-/
structure BitBuffer where
  bits : List Bool := []
deriving Repr, Inhabited, BEq

namespace BitBuffer

def empty : BitBuffer :=
  {}

/-- The number of bits in the buffer. -/
@[simp] def length (buf : BitBuffer) : Nat :=
  buf.bits.length

/-- Append a single bit to the buffer. -/
@[inline] def pushBit (buf : BitBuffer) (bit : Bool) : BitBuffer :=
  { bits := buf.bits ++ [bit] }

/-- Append a sequence of bits to the buffer. -/
def appendBits (buf : BitBuffer) (more : List Bool) : BitBuffer :=
  { bits := buf.bits ++ more }

/-- Append the big-endian representation of `value` using `width` bits. -/
def appendNatBE (buf : BitBuffer) (width value : Nat) : BitBuffer :=
  buf.appendBits (bitsOfNatBE width value)

/-- Append a nibble (4 bits). -/
def appendNibble (buf : BitBuffer) (value : Nat) : BitBuffer :=
  buf.appendNatBE 4 value

/-- Append a byte (8 bits). -/
def appendByte (buf : BitBuffer) (value : UInt8) : BitBuffer :=
  buf.appendNatBE 8 value.toNat

/--
Apply the `pad` function from the specification: append `0`s followed by `1`
until the total number of bits is a multiple of 8.  Even if the buffer length is
already a multiple of 8, an additional padding byte (`00000001`) is appended.
-/
def pad (buf : BitBuffer) : BitBuffer :=
  let k := buf.length % 8
  let zeros := List.replicate (7 - k) false
  buf.appendBits (zeros ++ [true])

/--
Remove a trailing padding fragment if present.  Returns `none` if the input does
not end with one of the valid padding fragments `pp{k}` from the specification.
-/
def unpad? (buf : BitBuffer) : Option BitBuffer :=
  match buf.bits.reverse with
  | [] => none
  | true :: tail =>
      let rec dropZeros (count : Nat) (rest : List Bool) : Option (List Bool) :=
        match rest with
        | [] => some []
        | false :: more =>
            if count = 7 then
              none
            else
              dropZeros (count + 1) more
        | remaining =>
            some remaining
      dropZeros 0 tail |>.map fun remaining =>
        ⟨remaining.reverse⟩
  | _ => none

/-- Convert a `BitBuffer` to a human-readable bit string like "010110". -/
def toBitString (buf : BitBuffer) : String :=
  let chars := buf.bits.map fun b => if b then '1' else '0'
  String.mk chars

/- Pack a list of bits (big-endian within each byte) into bytes. The input
   list is assumed to have length multiple of 8; callers should `pad` first if
   necessary. -/
partial def packToBytes : List Bool → List UInt8
  | [] => []
  | bits =>
    let (chunk, rest) := bits.splitAt 8
    let n := chunk.foldl (fun acc b => acc * 2 + (if b then 1 else 0)) 0
    n.toUInt8 :: packToBytes rest

/-- Convert a `BitBuffer` into a `List UInt8` by padding to a byte boundary and
    packing each consecutive 8 bits into a `UInt8`. -/
def toByteList (buf : BitBuffer) : List UInt8 :=
  --let padded := BitBuffer.pad buf
  packToBytes buf.bits

/-- Convert a nibble (0..15) to its lowercase hexadecimal `Char`. -/
def nibbleToHexChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E' | 15 => 'F'
  | _ => '?'

/-- Convert a `BitBuffer` into a lower-case hexadecimal `String` representing
    the padded bytes (two hex digits per byte). -/
def toHexString (buf : BitBuffer) : String :=
  let bytes := buf.toByteList
  let chars := bytes.flatMap fun (b : UInt8) =>
    let n := b.toNat
    let hi := n / 16
    let lo := n % 16
    [nibbleToHexChar hi, nibbleToHexChar lo]
  String.mk chars

/-- Format a bitstring into 8-bit chunks, 6 chunks per line.
    Useful for displaying encoded data in a readable format. -/
def formatBitString (buf : BitBuffer) : String :=
  let bitStr := toBitString buf
  let chunks := (List.range (bitStr.length / 8)).map fun idx =>
    String.take (String.drop bitStr (idx * 8)) 8

  let rec formatChunks (cs : List String) (acc : List String) (lineChunks : Nat) : List String :=
    match cs with
    | [] => acc
    | c :: rest =>
        if lineChunks = 6 then
          formatChunks rest (acc ++ ["\n" ++ c]) 1
        else
          let sep := if lineChunks = 0 then "" else " "
          formatChunks rest (acc ++ [sep ++ c]) (lineChunks + 1)

  let formatted := formatChunks chunks [] 0
  String.mk (formatted.flatMap String.toList)

end BitBuffer

end Plutus
end Moist
