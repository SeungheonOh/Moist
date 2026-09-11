import Moist.Onchain.PlutusData
import Moist.Onchain.Repr

namespace Moist.Onchain.AssocMap

open Moist.Plutus (Data AssocMap)
open Moist.Onchain.Prelude

private def lookupData (key : Data) : List (Data × Data) → Option Data
  | [] => none
  | entry :: rest => if equalsData key entry.1 then some entry.2 else lookupData key rest

private def deleteData (key : Data) : List (Data × Data) → List (Data × Data)
  | [] => []
  | entry :: rest => if equalsData key entry.1 then rest else entry :: deleteData key rest

private def insertData (key value : Data) : List (Data × Data) → List (Data × Data)
  | [] => [(key, value)]
  | entry :: rest =>
    if equalsData key entry.1 then (key, value) :: rest else entry :: insertData key value rest

private def foldData (step : α → Data → Data → α) (initial : α) : List (Data × Data) → α
  | [] => initial
  | entry :: rest => foldData step (step initial entry.1 entry.2) rest

private def foldRightData (step : Data → Data → α → α) (initial : α) : List (Data × Data) → α
  | [] => initial
  | entry :: rest => step entry.1 entry.2 (foldRightData step initial rest)

private def dropData (count : Int) : List (Data × Data) → List (Data × Data)
  | [] => []
  | entry :: rest =>
    if lessThanEqInteger count 0 then entry :: rest else dropData (subtractInteger count 1) rest

private def foldRightLazyData (step : Data → Data → List (Data × Data) → (Unit → α) → α)
    (initial : α) : List (Data × Data) → α
  | [] => initial
  | entry :: rest => step entry.1 entry.2 rest (fun _ => foldRightLazyData step initial rest)

def withHead [PlutusData key] [PlutusData value] (empty : Unit → α)
    (cons : key → value → AssocMap key value → α) (map : AssocMap key value) : α :=
  match unMapData (PlutusData.toData map) with
  | [] => empty ()
  | entry :: rest => cons (PlutusData.unsafeFromData entry.1) (PlutusData.unsafeFromData entry.2)
      (PlutusData.unsafeFromData (mapData rest))

def drop [PlutusData key] [PlutusData value] (count : Int) (map : AssocMap key value) : AssocMap key value :=
  PlutusData.unsafeFromData (mapData (dropData count (unMapData (PlutusData.toData map))))

def foldrLazy [PlutusData key] [PlutusData value]
    (step : key → value → AssocMap key value → (Unit → α) → α) (initial : α)
    (map : AssocMap key value) : α :=
  foldRightLazyData (fun key value rest next =>
    step (PlutusData.unsafeFromData key) (PlutusData.unsafeFromData value)
      (PlutusData.unsafeFromData (mapData rest)) next) initial (unMapData (PlutusData.toData map))

private def prependResult (key : Data) (value : Option Data) (rest : List (Data × Data)) : List (Data × Data) :=
  match value with
  | none => rest
  | some value => (key, value) :: rest

private def mapMaybeData (transform : Data → Option Data) : List (Data × Data) → List (Data × Data)
  | [] => []
  | entry :: rest => prependResult entry.1 (transform entry.2) (mapMaybeData transform rest)

@[plutus_sop] private structure MergeState where
  left : List (Data × Data)
  right : List (Data × Data)

private def mergeData (less : Data → Data → Bool) (both : Data → Data → Option Data)
    (leftOnly rightOnly : Data → Option Data) (state : MergeState) : List (Data × Data) :=
  match state with
  | ⟨[], right⟩ => mapMaybeData rightOnly right
  | ⟨left, []⟩ => mapMaybeData leftOnly left
  | ⟨first :: leftRest, second :: rightRest⟩ =>
    if equalsData first.1 second.1 then
      prependResult first.1 (both first.2 second.2) (mergeData less both leftOnly rightOnly ⟨leftRest, rightRest⟩)
    else if less first.1 second.1 then
      prependResult first.1 (leftOnly first.2) (mergeData less both leftOnly rightOnly ⟨leftRest, second :: rightRest⟩)
    else prependResult second.1 (rightOnly second.2) (mergeData less both leftOnly rightOnly ⟨first :: leftRest, rightRest⟩)
termination_by state.left.length + state.right.length

def mergeWith [PlutusData key] [PlutusData value] (less : key → key → Bool)
    (both : value → value → Option value) (leftOnly rightOnly : value → Option value)
    (left right : AssocMap key value) : AssocMap key value :=
  let encode := fun (result : Option value) => result.map (fun entry => PlutusData.toData entry)
  let result := mergeData (fun left right => less (PlutusData.unsafeFromData left) (PlutusData.unsafeFromData right))
    (fun left right => encode (both (PlutusData.unsafeFromData left) (PlutusData.unsafeFromData right)))
    (fun value => encode (leftOnly (PlutusData.unsafeFromData value)))
    (fun value => encode (rightOnly (PlutusData.unsafeFromData value)))
    ⟨unMapData (PlutusData.toData left), unMapData (PlutusData.toData right)⟩
  PlutusData.unsafeFromData (mapData result)

def lookup [PlutusData key] [PlutusData value] (wanted : key) (map : AssocMap key value) : Option value :=
  match lookupData (PlutusData.toData wanted) (unMapData (PlutusData.toData map)) with
  | none => none
  | some value => some (PlutusData.unsafeFromData value)

def delete [PlutusData key] [PlutusData value] (wanted : key) (map : AssocMap key value) : AssocMap key value :=
  PlutusData.unsafeFromData (mapData (deleteData (PlutusData.toData wanted) (unMapData (PlutusData.toData map))))

def foldl [PlutusData key] [PlutusData value] (step : α → key → value → α) (initial : α)
    (map : AssocMap key value) : α :=
  foldData (fun accumulator key value =>
    step accumulator (PlutusData.unsafeFromData key) (PlutusData.unsafeFromData value))
    initial (unMapData (PlutusData.toData map))

def firstValue? [PlutusData key] [PlutusData value] (map : AssocMap key value) : Option value :=
  match unMapData (PlutusData.toData map) with
  | [] => none
  | entry :: _ => some (PlutusData.unsafeFromData entry.2)

def foldr [PlutusData key] [PlutusData value] (step : key → value → α → α) (initial : α)
    (map : AssocMap key value) : α :=
  foldRightData (fun key value accumulator =>
    step (PlutusData.unsafeFromData key) (PlutusData.unsafeFromData value) accumulator)
    initial (unMapData (PlutusData.toData map))

def hasMultiple [PlutusData key] [PlutusData value] (map : AssocMap key value) : Bool :=
  match unMapData (PlutusData.toData map) with
  | _ :: _ :: _ => true
  | _ => false

def empty [PlutusData key] [PlutusData value] : AssocMap key value :=
  ⟨[]⟩

def singleton [PlutusData key] [PlutusData value] (entryKey : key) (entryValue : value) : AssocMap key value :=
  PlutusData.unsafeFromData (mapData [(PlutusData.toData entryKey, PlutusData.toData entryValue)])

def insert [PlutusData key] [PlutusData value] (entryKey : key) (entryValue : value)
    (map : AssocMap key value) : AssocMap key value :=
  let encodedKey := PlutusData.toData entryKey
  let entries := unMapData (PlutusData.toData map)
  PlutusData.unsafeFromData (mapData (insertData encodedKey (PlutusData.toData entryValue) entries))

end Moist.Onchain.AssocMap
