import Moist.Onchain.PlutusData

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
