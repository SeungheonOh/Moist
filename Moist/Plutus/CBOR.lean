import Moist.Plutus.Types
import Moist.Plutus.Lemma

namespace Moist
namespace Plutus
namespace CBOR

open Moist.Plutus.Lemma
open Moist.Plutus (Data ByteString Integer)

/-- Convert a small natural to a k-byte big-endian list, failing if it does not fit. -/
def intToBS_k (k : Nat) (n : Nat) : Option (List UInt8) :=
  let max := (Nat.pow 256 k) - 1
  if n <= max then
    some (List.range k |>.map fun idx =>
      let i := k - 1 - idx
      let byte := (n / (256 ^ i)) % 256
      byte.toUInt8)
  else
    none

/-- Encode a CBOR head (major type `m`, argument `n`) as bytes. -/
def eHead (m : Nat) (n : Nat) : Option (List UInt8) :=
  if n <= 23 then
    some [((32 * m + n).toUInt8)]
  else if n <= 255 then
    match intToBS_k 1 n with
    | some bs => some (((32 * m + 24).toUInt8) :: bs)
    | none => none
  else if n <= 65535 then
    match intToBS_k 2 n with
    | some bs => some (((32 * m + 25).toUInt8) :: bs)
    | none => none
  else if n <= 4294967295 then
    match intToBS_k 4 n with
    | some bs => some (((32 * m + 26).toUInt8) :: bs)
    | none => none
  else if n <= 18446744073709551615 then
    match intToBS_k 8 n with
    | some bs => some (((32 * m + 27).toUInt8) :: bs)
    | none => none
  else
    none

/-- Indefinite-length head for given major type (m in {2,3,4,5}). -/
def eIndef (m : Nat) : List UInt8 :=
  [((32 * m + 31).toUInt8)]

/-- Convert a natural to the minimal big-endian byte list (itos). -/
def itos : Nat → List UInt8
  | 0 => []
  | n =>
    let rec loop (x : Nat) (acc : List UInt8) :=
      if x = 0 then acc
      else
        let b := (x % 256).toUInt8
        loop (x / 256) (b :: acc)
    loop n []

/-- Break a byte list into canonical 64-byte chunks. -/
def chunk64 (bs : List UInt8) : List (List UInt8) :=
  if bs = [] then []
  else
    (List.take 64 bs) :: chunk64 (List.drop 64 bs)
    termination_by (List.length bs)
    decreasing_by
      apply List.drop_decreases_length <;> try assumption
      omega

/-- Encode a bytestring using restricted CBOR bytestring rules (eBS). -/
def eBS (bs : List UInt8) : Option (List UInt8) :=
  if bs.length <= 64 then
    match eHead 2 bs.length with
    | some h => some (h ++ bs)
    | none => none
  else
    let chunks := chunk64 bs
    let enc := (eIndef 2) ++ (chunks.foldl (fun acc c =>
      match eHead 2 c.length with
      | some h => acc ++ h ++ c
      | none => acc) [])
    some (enc ++ [(255 : Nat).toUInt8])

/-- Encode integers using eZ from the spec. -/
def eZ (z : Integer) : Option (List UInt8) :=
  let two64 : Integer := Int.ofNat (Nat.pow 2 64)
  if Int.ofNat 0 <= z && z <= two64 - 1 then
    -- non-negative small integer
    let n := Int.toNat z
    eHead 0 n
  else if z < 0 && z >= -two64 then
    -- negative small integer encoded as (1, -n-1)
    let n := Int.toNat ((-z) - 1)
    eHead 1 n
  else if Int.ofNat 0 <= z then
    -- large positive integer: tag 2 followed by bytestring of magnitude
    let n := Int.toNat z
    let b := itos n
    match eBS b with
    | some bs =>
      match eHead 6 2 with
      | some h => some (h ++ bs)
      | none => none
    | none => none
  else
    -- large negative integer: tag 3 and bytestring of (-n-1)
    let n := Int.toNat ((-z) - 1)
    let b := itos n
    match eBS b with
    | some bs =>
      match eHead 6 3 with
      | some h => some (h ++ bs)
      | none => none
    | none => none

/-- Encode constructor tag `i` as ecTag (long form). -/
def ecTag (i : Integer) : Option (List UInt8) :=
  match eHead 6 102 with
  | some h1 =>
    match eHead 4 2 with
    | some h2 =>
      match eZ i with
      | some zbs => some (h1 ++ h2 ++ zbs)
      | none => none
    | none => none
  | none => none

/-- Recursive encoder for `Data`. -/
partial def eData : Data → Option (List UInt8)
  | .Map pairs =>
    let len := pairs.length
    match eHead 5 len with
    | some h =>
      pairs.foldl (fun acc p =>
        match acc, eData p.fst, eData p.snd with
        | some a, some k, some v => some (a ++ k ++ v)
        | _, _, _ => none) (some h)
    | none => none
  | .List xs =>
    match xs.foldl (fun acc x =>
      match acc, eData x with
      | some a, some b => some (a ++ b)
      | _, _ => none) (some (eIndef 4)) with
    | some b => some (b ++ [(255 : Nat).toUInt8])
    | none => none
  | .Constr idx fields =>
    match ecTag idx with
    | some tag =>
      match fields.foldl (fun acc x =>
        match acc, eData x with
        | some a, some b => some (a ++ b)
        | _, _ => none) (some (eIndef 4)) with
      | some b => some (tag ++ b ++ [(255 : Nat).toUInt8])
      | none => none
    | none => none
  | .I n => eZ n
  | .B bs =>
    let payload := bs.data.toList
    eBS payload

/-- Top-level CBOR serialiser for `Data`. -/
def dataToCBORBytes (d : Data) : Option (List UInt8) := eData d

/-- Decode a fixed-size big-endian natural number from the start of a byte list. -/
def bsToInt_k : Nat → List UInt8 → Option (List UInt8 × Nat)
  | 0, s => .some (s, 0)
  | _ + 1, [] => .none
  | k + 1, b :: s => do
      let (s', n) ← bsToInt_k k s
      .some (s', b.toNat * 256 ^ k + n)

/-- Decode a CBOR head into the remaining bytes, major type, and argument. -/
def dHead : List UInt8 → Option (List UInt8 × Nat × Nat)
  | [] => .none
  | b :: s =>
      let major := b.toNat / 32
      let arg := b.toNat % 32
      if arg <= 23 then
        .some (s, major, arg)
      else
        match arg with
        | 24 => do
            let (s', n) ← bsToInt_k 1 s
            .some (s', major, n)
        | 25 => do
            let (s', n) ← bsToInt_k 2 s
            .some (s', major, n)
        | 26 => do
            let (s', n) ← bsToInt_k 4 s
            .some (s', major, n)
        | 27 => do
            let (s', n) ← bsToInt_k 8 s
            .some (s', major, n)
        | _ => .none

/-- Decode an indefinite-length CBOR head for major types 2 through 5. -/
def dIndef : List UInt8 → Option (List UInt8 × Nat)
  | [] => .none
  | b :: s =>
      let major := b.toNat / 32
      let arg := b.toNat % 32
      if arg = 31 && 2 <= major && major <= 5 then
        .some (s, major)
      else
        .none

/-- Consume exactly `n` bytes from the front of a byte list. -/
def dBytes : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, s => .some (s, [])
  | _ + 1, [] => .none
  | n + 1, b :: s => do
      let (s', rest) ← dBytes n s
      .some (s', b :: rest)

/-- Decode one restricted CBOR bytestring block (maximum 64 bytes). -/
def dBlock (s : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (s', major, n) ← dHead s
  if major = 2 && n <= 64 then
    dBytes n s'
  else
    .none

/-- Decode an indefinite sequence of restricted CBOR bytestring blocks. -/
partial def dBlocks : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => .none
  | b :: s =>
      if b = (255 : UInt8) then
        .some (s, [])
      else do
        let (s', block) ← dBlock (b :: s)
        let (s'', blocks) ← dBlocks s'
        .some (s'', block ++ blocks)

/-- Decode a restricted CBOR bytestring. -/
def dBS (s : List UInt8) : Option (List UInt8 × List UInt8) :=
  match dBlock s with
  | .some result => .some result
  | .none => do
      let (s', major) ← dIndef s
      if major = 2 then
        dBlocks s'
      else
        .none

/-- Interpret a big-endian byte sequence as a natural number. -/
def stoi : List UInt8 → Nat :=
  List.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- Decode an integer using the restricted CBOR rules from the spec appendix. -/
def dZ (s : List UInt8) : Option (List UInt8 × Integer) := do
  let (s', major, n) ← dHead s
  if major = 0 then
    .some (s', Int.ofNat n)
  else if major = 1 then
    .some (s', -((Int.ofNat n) + 1))
  else if major = 6 && n = 2 then do
    let (s'', bytes) ← dBS s'
    .some (s'', Int.ofNat (stoi bytes))
  else if major = 6 && n = 3 then do
    let (s'', bytes) ← dBS s'
    .some (s'', -((Int.ofNat (stoi bytes)) + 1))
  else
    .none

mutual
  /-- Decode a CBOR-encoded `Data` value. -/
  partial def dData (s : List UInt8) : Option (List UInt8 × Data) :=
    match dHead s with
    | .some (s', 5, n) => Prod.map id .Map <$> dDataStarSq n s'
    | _ =>
        match dDataStar s with
        | .some (s', xs) => .some (s', .List xs)
        | .none =>
            match dcTag s with
            | .some (s', i) => do
                let (s'', xs) ← dDataStar s'
                .some (s'', .Constr i xs)
            | .none =>
                match dZ s with
                | .some (s', n) => .some (s', .I n)
                | .none => do
                    let (s', bytes) ← dBS s
                    .some (s', .B (ByteArray.mk bytes.toArray))

  /-- Decode either a definite-length or indefinite-length CBOR list of data items. -/
  partial def dDataStar (s : List UInt8) : Option (List UInt8 × List Data) :=
    match dHead s with
    | .some (s', 4, n) => dDataStarN n s'
    | _ =>
        match dIndef s with
        | .some (s', 4) => dDataStarIndef s'
        | _ => .none

  /-- Decode exactly `n` CBOR-encoded data items. -/
  partial def dDataStarN : Nat → List UInt8 → Option (List UInt8 × List Data)
    | 0, s => .some (s, [])
    | n + 1, s => do
        let (s', d) ← dData s
        let (s'', ds) ← dDataStarN n s'
        .some (s'', d :: ds)

  /-- Decode an indefinite-length CBOR list of data items. -/
  partial def dDataStarIndef : List UInt8 → Option (List UInt8 × List Data)
    | [] => .none
    | b :: s =>
        if b = (255 : UInt8) then
          .some (s, [])
        else do
          let (s', d) ← dData (b :: s)
          let (s'', ds) ← dDataStarIndef s'
          .some (s'', d :: ds)

  /-- Decode exactly `n` CBOR-encoded pairs of data items. -/
  partial def dDataStarSq : Nat → List UInt8 → Option (List UInt8 × List (Data × Data))
    | 0, s => .some (s, [])
    | n + 1, s => do
        let (s', k) ← dData s
        let (s'', d) ← dData s'
        let (s''', rest) ← dDataStarSq n s''
        .some (s''', (k, d) :: rest)

  /-- Decode a constructor tag, accepting the compact forms and the long form. -/
  partial def dcTag (s : List UInt8) : Option (List UInt8 × Integer) := do
    let (s', major, n) ← dHead s
    if major = 6 && 121 <= n && n <= 127 then
      .some (s', Int.ofNat (n - 121))
    else if major = 6 && 1280 <= n && n <= 1400 then
      .some (s', Int.ofNat (n - 1280 + 7))
    else if major = 6 && n = 102 then do
      let (s'', major', n') ← dHead s'
      if major' = 4 && n' = 2 then do
        let (s''', i) ← dZ s''
        let two64 : Integer := Int.ofNat (Nat.pow 2 64)
        if 0 <= i && i < two64 then
          .some (s''', i)
        else
          .none
      else
        .none
    else
      .none
end

/-- Top-level CBOR decoder for `Data`. -/
def dataFromCBORBytes (bs : ByteString) : Option (ByteString × Data) := do
  let (rest, d) ← dData bs.data.toList
  .some (ByteArray.mk rest.toArray, d)

/-- Parse a single hex character to its 4-bit value. -/
def hexCharToNat : Char → Option Nat
  | '0' => some 0  | '1' => some 1  | '2' => some 2  | '3' => some 3
  | '4' => some 4  | '5' => some 5  | '6' => some 6  | '7' => some 7
  | '8' => some 8  | '9' => some 9
  | 'a' | 'A' => some 10 | 'b' | 'B' => some 11
  | 'c' | 'C' => some 12 | 'd' | 'D' => some 13
  | 'e' | 'E' => some 14 | 'f' | 'F' => some 15
  | _ => none

/-- Parse a hex string into a ByteArray. Returns none for odd-length or invalid chars. -/
def hexStringToByteArray (s : String) : Option ByteArray := do
  let chars := s.data
  if chars.length % 2 != 0 then none
  else
    let rec go : List Char → ByteArray → Option ByteArray
      | [], acc => some acc
      | c1 :: c2 :: rest, acc => do
        let hi ← hexCharToNat c1
        let lo ← hexCharToNat c2
        go rest (acc.push (hi * 16 + lo).toUInt8)
      | _, _ => none
    go chars ByteArray.empty

/-- Decode a Data value from a CBOR hex string. -/
def dataFromCBORHex (hex : String) : Option Data := do
  let bytes ← hexStringToByteArray hex
  let (_, d) ← dataFromCBORBytes bytes
  some d

/-- Encode a ByteArray to a lowercase hex string. -/
def byteArrayToHex (ba : ByteArray) : String :=
  let hexChar (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n - 10 + 97)
  String.mk (ba.toList.flatMap fun b =>
    let n := b.toNat
    [hexChar (n / 16), hexChar (n % 16)])

/-- Encode a Data value to a CBOR hex string. -/
def dataToCBORHex (d : Data) : Option String := do
  let bytes ← dataToCBORBytes d
  some (byteArrayToHex (ByteArray.mk bytes.toArray))

end CBOR
end Plutus
end Moist
