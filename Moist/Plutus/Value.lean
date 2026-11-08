import Moist.Plutus.Types

/-! # Builtin `Value` (multi-asset values)

A faithful model of `PlutusCore.Value` (plutus-core 1.65). A value is a map from
currency symbol to a map from token name to quantity, represented as an
association list sorted by key. Every value the parser, the flat decoder and the
builtins produce is *well formed*:

* outer keys (currency symbols) and inner keys (token names) are strictly
  ascending in the unsigned lexicographic byte order and at most 32 bytes long;
* no inner map is empty;
* every quantity is nonzero and lies in the signed 128-bit range.

Under that invariant the association list is the unique representation of the
underlying map, so equal values have equal payloads. The operations below follow
`PlutusCore.Value` clause by clause; the reference function is named in each
docstring.
-/

namespace Moist.Plutus.Value

open Moist.Plutus (ByteString Data)

/-- The payload of a `Value` constant. -/
abbrev Entries := List (ByteString × List (ByteString × Int))

/-- `maxKeyLen`. -/
def maxKeyLen : Nat := 32

/-- `valueDataMaxSize`. -/
def valueDataMaxSize : Nat := 40000

/-- The `K` smart constructor's check. -/
def keyOk (key : ByteString) : Bool := key.size ≤ maxKeyLen

/-- `minBound :: Quantity`. -/
def minQuantity : Int := -((2 ^ 127 : Nat) : Int)

/-- `maxBound :: Quantity`. -/
def maxQuantity : Int := ((2 ^ 127 : Nat) : Int) - 1

/-- The `quantity` smart constructor's check. -/
def quantityOk (amount : Int) : Bool := decide (minQuantity ≤ amount) && decide (amount ≤ maxQuantity)

/-- Unsigned lexicographic order on byte strings (`Ord ByteString`). -/
def keyLt (a b : ByteString) : Bool := decide (a.data.toList < b.data.toList)

/-- Strictly ascending keys. -/
def ascending {α : Type} : List (ByteString × α) → Bool
  | [] | [_] => true
  | (a, _) :: (b, x) :: rest => keyLt a b && ascending ((b, x) :: rest)

/-- Inner-map validity as checked by `buildValueWith`'s `goInner`. -/
def innerOk (inner : List (ByteString × Int)) : Bool :=
  ascending inner && inner.all (fun (token, amount) => keyOk token && quantityOk amount && amount != 0)

/-- `buildValueWith`: validate the entries of a value literal, a flat-decoded value
or an `unValueData` argument. Fails unless keys are valid and strictly ascending,
inner maps are nonempty and every quantity is nonzero and in bounds. -/
def build? (entries : Entries) : Option Entries :=
  if ascending entries && entries.all (fun (currency, inner) =>
      keyOk currency && !inner.isEmpty && innerOk inner)
  then some entries else none

/-- `totalSize`: the number of `(currency, token)` entries. -/
def totalSize (entries : Entries) : Nat :=
  entries.foldl (fun acc entry => acc + entry.2.length) 0

/-- `maxInnerSize`. -/
def maxInnerSize (entries : Entries) : Nat :=
  entries.foldl (fun acc entry => max acc entry.2.length) 0

/-- `negativeAmounts`. -/
def negativeAmounts (entries : Entries) : Nat :=
  entries.foldl (fun acc entry => acc + (entry.2.filter (fun item => decide (item.2 < 0))).length) 0

/-- Look up a key in a sorted association list. -/
def find? {α : Type} (key : ByteString) : List (ByteString × α) → Option α
  | [] => none
  | (k, v) :: rest => if k == key then some v else find? key rest

/-- Insert or replace a key in a sorted association list, keeping it sorted. -/
def upsert {α : Type} (key : ByteString) (value : α) : List (ByteString × α) → List (ByteString × α)
  | [] => [(key, value)]
  | (k, v) :: rest =>
    if k == key then (key, value) :: rest
    else if keyLt key k then (key, value) :: (k, v) :: rest
    else (k, v) :: upsert key value rest

/-- Remove a key from an association list. -/
def erase {α : Type} (key : ByteString) : List (ByteString × α) → List (ByteString × α)
  | [] => []
  | (k, v) :: rest => if k == key then rest else (k, v) :: erase key rest

/-- `deleteCoin`: remove one entry, dropping the inner map when it becomes empty.
Keys are not validated. -/
def deleteCoin (currency token : ByteString) (entries : Entries) : Entries :=
  match find? currency entries with
  | none => entries
  | some inner =>
    let inner' := erase token inner
    if inner'.isEmpty then erase currency entries else upsert currency inner' entries

/-- `insertCoin`. A zero amount deletes the entry (without validating the keys);
otherwise both keys must be at most 32 bytes and the amount in the 128-bit range. -/
def insertCoin (currency token : ByteString) (amount : Int) (entries : Entries) : Option Entries :=
  if amount == 0 then some (deleteCoin currency token entries)
  else if !(keyOk currency && keyOk token && quantityOk amount) then none
  else
    let inner := (find? currency entries).getD []
    some (upsert currency (upsert token amount inner) entries)

/-- `lookupCoin`: the quantity of an entry, zero when absent. -/
def lookupCoin (currency token : ByteString) (entries : Entries) : Int :=
  match find? currency entries with
  | none => 0
  | some inner => (find? token inner).getD 0

/-- `Map.isSubmapOfBy (Map.isSubmapOfBy (<=)) small big`. -/
def submap (small big : Entries) : Bool :=
  small.all fun (currency, innerSmall) =>
    match find? currency big with
    | none => false
    | some innerBig => innerSmall.all fun (token, amount) =>
      match find? token innerBig with
      | none => false
      | some bigAmount => decide (amount ≤ bigAmount)

/-- `valueContains`: fails if either value has a negative amount. -/
def valueContains (big small : Entries) : Option Bool :=
  if negativeAmounts big > 0 then none
  else if negativeAmounts small > 0 then none
  else if totalSize big < totalSize small then some false
  else some (submap small big)

/-- Merge two sorted association lists, combining values present in both with
`combine` (which may drop the entry with `none`, or fail). -/
def mergeWith {α : Type} (combine : α → α → Option (Option α)) :
    List (ByteString × α) → List (ByteString × α) → Option (List (ByteString × α))
  | [], ys => some ys
  | xs, [] => some xs
  | (kx, vx) :: xs, (ky, vy) :: ys =>
    if kx == ky then do
      let merged ← combine vx vy
      let rest ← mergeWith combine xs ys
      match merged with
      | some v => some ((kx, v) :: rest)
      | none => some rest
    else if keyLt kx ky then do
      let rest ← mergeWith combine xs ((ky, vy) :: ys)
      some ((kx, vx) :: rest)
    else do
      let rest ← mergeWith combine ((kx, vx) :: xs) ys
      some ((ky, vy) :: rest)
termination_by xs ys => xs.length + ys.length

/-- `unionValue`: pointwise sum; zero sums and empty inner maps disappear; fails
when a sum leaves the 128-bit range. -/
def unionValue (a b : Entries) : Option Entries :=
  if totalSize a == 0 then some b
  else if totalSize b == 0 then some a
  else
    mergeWith (fun innerA innerB => do
      let inner ← mergeWith (fun x y =>
        let z := x + y
        if !quantityOk z then none
        else if z == 0 then some none else some (some z)) innerA innerB
      if inner.isEmpty then some none else some (some inner)) a b

/-- `scaleValue`: multiply every quantity; scaling by zero gives the empty value;
fails when a product leaves the 128-bit range. -/
def scaleValue (factor : Int) (entries : Entries) : Option Entries :=
  if factor == 0 then some []
  else entries.mapM fun (currency, inner) => do
    let inner' ← inner.mapM fun (token, amount) =>
      let product := factor * amount
      if quantityOk product then some (token, product) else none
    some (currency, inner')

/-- `valueData`: encode as nested `Map`s of `B` keys and `I` quantities. -/
def valueData (entries : Entries) : Option Data :=
  if totalSize entries ≤ valueDataMaxSize then
    some (.Map (entries.map fun (currency, inner) =>
      (.B currency, .Map (inner.map fun (token, amount) => (.B token, .I amount)))))
  else none

/-- Decode the token map of one currency for `unValueData`. -/
def unTokens : List (Data × Data) → Option (List (ByteString × Int))
  | [] => some []
  | (.B token, .I amount) :: rest =>
    if keyOk token && quantityOk amount then
      return (token, amount) :: (← unTokens rest)
    else none
  | _ :: _ => none

/-- Decode the currency map for `unValueData`. -/
def unCurrencies : List (Data × Data) → Option Entries
  | [] => some []
  | (.B currency, .Map tokens) :: rest =>
    if keyOk currency then do
      let inner ← unTokens tokens
      return (currency, inner) :: (← unCurrencies rest)
    else none
  | _ :: _ => none

/-- `unValueData`: decode nested `Map`s, then validate with `buildValueWith`. -/
def unValueData : Data → Option Entries
  | .Map currencies => unCurrencies currencies >>= build?
  | _ => none

end Moist.Plutus.Value
