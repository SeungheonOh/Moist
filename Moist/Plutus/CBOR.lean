import PlutusCore.ByteString
import PlutusCore.Data
import PlutusCore.Integer
import Moist.Plutus.Lemma

namespace Moist
namespace Plutus
namespace CBOR

open Moist.Plutus.Lemma
open PlutusCore.ByteString
open PlutusCore.Data
open PlutusCore.Integer

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

end CBOR
end Plutus
end Moist
