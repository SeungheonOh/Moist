import Moist.Onchain
import Moist.Plutus.Eval
import Moist.Plutus.Pretty
import Test.Framework

namespace Test.CollectionEncoding

open Moist.Plutus (Data ByteString AssocMap)
open Moist.Onchain Moist.Onchain.Prelude
open Moist.Plutus.Term
open Test.Framework

@[onchain] def encodeInteger : Int → Data := PlutusData.toData
@[onchain] def decodeInteger : Data → Int := PlutusData.unsafeFromData
@[onchain] def roundtripBytes (datum : Data) : Data :=
  PlutusData.toData (PlutusData.unsafeFromData datum : ByteString)
@[onchain] def roundtripList (datum : Data) : Data :=
  PlutusData.toData (PlutusData.unsafeFromData datum : List (List Int))
@[onchain] def sumList : List Int → Int
  | [] => 0
  | value :: rest => addInteger value (sumList rest)
@[onchain] def decodeAndSum (datum : Data) : Int :=
  sumList (PlutusData.unsafeFromData datum)
@[onchain] def roundtripMap (datum : Data) : Data :=
  PlutusData.toData (PlutusData.unsafeFromData datum : AssocMap ByteString (AssocMap ByteString Int))
@[onchain] def findAmount (datum : Data) : Int :=
  let map : AssocMap ByteString (AssocMap ByteString Int) := PlutusData.unsafeFromData datum
  match Moist.Onchain.AssocMap.lookup "policy".toUTF8 map with
  | none => 0
  | some tokens => match Moist.Onchain.AssocMap.lookup "token".toUTF8 tokens with
    | none => 0
    | some quantity => quantity
@[onchain] def deleteAmount (datum : Data) : Data :=
  let map : AssocMap ByteString Int := PlutusData.unsafeFromData datum
  PlutusData.toData (Moist.Onchain.AssocMap.delete "key".toUTF8 map)
@[onchain] def insertAmount (datum : Data) : Data :=
  let map : AssocMap ByteString Int := PlutusData.unsafeFromData datum
  PlutusData.toData (Moist.Onchain.AssocMap.insert "key".toUTF8 42 map)
@[onchain] def foldAmounts (datum : Data) : Int :=
  let map : AssocMap ByteString Int := PlutusData.unsafeFromData datum
  Moist.Onchain.AssocMap.foldl (fun accumulator _ quantity => addInteger accumulator quantity) 0 map
@[onchain] def firstAmount (datum : Data) : Int :=
  let map : AssocMap ByteString Int := PlutusData.unsafeFromData datum
  match Moist.Onchain.AssocMap.firstValue? map with
  | none => -1
  | some amount => amount
@[onchain] def foldRightAmounts (datum : Data) : Int :=
  let map : AssocMap ByteString Int := PlutusData.unsafeFromData datum
  Moist.Onchain.AssocMap.foldr (fun _ quantity accumulator => subtractInteger quantity accumulator) 0 map
@[onchain] def singletonAmount (quantity : Int) : Data :=
  PlutusData.toData (Moist.Onchain.AssocMap.singleton "key".toUTF8 quantity)
@[onchain] def emptyAmounts : Data :=
  PlutusData.toData (Moist.Onchain.AssocMap.empty : AssocMap ByteString Int)
@[onchain] def multipleAmounts (datum : Data) : Bool :=
  Moist.Onchain.AssocMap.hasMultiple (PlutusData.unsafeFromData datum : AssocMap ByteString Int)
@[onchain] def literalAmounts (quantity : Int) : Data :=
  PlutusData.toData (AssocMap.mk [("key".toUTF8, quantity)] : AssocMap ByteString Int)

@[onchain] def nativeEntries (map : AssocMap ByteString Int) : List (ByteString × Int) := map.toList
@[onchain] def dynamicMap (entries : List (ByteString × Int)) : AssocMap ByteString Int := ⟨entries⟩
@[onchain] def nativeSafeDecoder (datum : Data) : Option Int := PlutusData.fromData datum

@[onchain] def genericMember [PlutusData value] (wanted : value) : List value → Bool
  | [] => false
  | entry :: rest => dataBeq wanted entry || genericMember wanted rest

@[onchain] def byteMember (wanted : ByteString) (values : List ByteString) : Bool :=
  genericMember wanted values

open Lean Elab Term in
elab "rejectCodec! " target:ident message:str : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let failure : Option String ← try
    let _ ← Moist.Onchain.translateDefByName name body
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some failure := failure | throwError "Unsupported representation unexpectedly compiled"
  unless (failure.splitOn message.getString).length > 1 do throwError "{failure}"
  return mkConst ``Bool.true

private def rejectsNativeEntries := rejectCodec! nativeEntries "encoded entries"
private def rejectsDynamicMap := rejectCodec! dynamicMap "encoded entries"
private def rejectsNativeDecoder := rejectCodec! nativeSafeDecoder "native decoder"
private def rejectsUnspecializedCodec := rejectCodec! byteMember "Cannot specialize"

private def integerEncoder := compile! encodeInteger
private def integerDecoder := compile! decodeInteger
private def bytesRoundtrip := compile! roundtripBytes
private def listRoundtrip := compile! roundtripList
private def listSum := compile! decodeAndSum
private def mapRoundtrip := compile! roundtripMap
private def mapFind := compile! findAmount
private def mapDelete := compile! deleteAmount
private def mapInsert := compile! insertAmount
private def mapFold := compile! foldAmounts
private def mapFirst := compile! firstAmount
private def mapFoldRight := compile! foldRightAmounts
private def mapSingleton := compile! singletonAmount
private def mapEmpty := compile! emptyAmounts
private def mapMultiple := compile! multipleAmounts
private def mapLiteral := compile! literalAmounts

private def dataTerm (value : Data) : Term := .Constant (.Data value, .AtomicType .TypeData)
private def integerTerm (value : Int) : Term := .Constant (.Integer value, .AtomicType .TypeInteger)
private def booleanTerm (value : Bool) : Term := .Constant (.Bool value, .AtomicType .TypeBool)

private def check (term expected : Term) : IO Unit := do
  match ← Moist.Plutus.Eval.evalTerm term with
  | .ok result =>
    unless Moist.Plutus.Pretty.prettyTerm result.term == Moist.Plutus.Pretty.prettyTerm expected do
      throw (IO.userError s!"Expected {expected}, got {result.term}")
  | .error error => throw (IO.userError s!"Evaluation failed: {repr error}")

def tests : TestTree := suite "collection_encoding" do
  test "primitive_codec_partial_applications" do
    check (.Apply integerEncoder (integerTerm 42)) (dataTerm (.I 42))
    check (.Apply integerDecoder (dataTerm (.I (-12)))) (integerTerm (-12))
    check (.Apply bytesRoundtrip (dataTerm (.B "bytes".toUTF8))) (dataTerm (.B "bytes".toUTF8))
  test "lists_decode_elements_and_empty_list_types" do
    for values in [[], [1], [-2, 0, 5]] do
      check (.Apply listSum (dataTerm (PlutusData.toData values))) (integerTerm (values.foldl (· + ·) 0))
    for values in [[], [[]], [[1, -2], [], [3]]] do
      let encoded := PlutusData.toData (values : List (List Int))
      check (.Apply listRoundtrip (dataTerm encoded)) (dataTerm encoded)
  test "nested_maps_preserve_data_backed_entries" do
    let value := Data.Map [(.B "policy".toUTF8, .Map [(.B "token".toUTF8, .I 7)])]
    check (.Apply mapRoundtrip (dataTerm value)) (dataTerm value)
    check (.Apply mapFind (dataTerm value)) (integerTerm 7)
    check (.Apply mapFind (dataTerm (.Map []))) (integerTerm 0)
  test "map_operations_preserve_order_and_first_duplicate_rules" do
    let first := (Data.B "key".toUTF8, Data.I 1)
    let second := (Data.B "other".toUTF8, Data.I 2)
    let duplicate := (Data.B "key".toUTF8, Data.I 3)
    let input := Data.Map [first, second, duplicate]
    check (.Apply mapDelete (dataTerm input)) (dataTerm (.Map [second, duplicate]))
    check (.Apply mapInsert (dataTerm input))
      (dataTerm (.Map [(.B "key".toUTF8, .I 42), second, duplicate]))
    check (.Apply mapInsert (dataTerm (.Map [second, first, duplicate])))
      (dataTerm (.Map [second, (.B "key".toUTF8, .I 42), duplicate]))
    check (.Apply mapInsert (dataTerm (.Map [second])))
      (dataTerm (.Map [second, (.B "key".toUTF8, .I 42)]))
    check (.Apply mapFold (dataTerm input)) (integerTerm 6)
    check (.Apply mapFoldRight (dataTerm input)) (integerTerm 2)
    check (.Apply mapFoldRight (dataTerm (.Map [first, second]))) (integerTerm (-1))
    check (.Apply mapFoldRight (dataTerm (.Map []))) (integerTerm 0)
    check (.Apply mapFirst (dataTerm input)) (integerTerm 1)
    check (.Apply mapFirst (dataTerm (.Map []))) (integerTerm (-1))
    check (.Apply mapSingleton (integerTerm 7)) (dataTerm (.Map [(.B "key".toUTF8, .I 7)]))
    check (.Apply mapLiteral (integerTerm 7)) (dataTerm (.Map [(.B "key".toUTF8, .I 7)]))
    check mapEmpty (dataTerm (.Map []))
    for entries in [[], [first], [first, second], [first, second, duplicate]] do
      check (.Apply mapMultiple (dataTerm (.Map entries))) (booleanTerm (entries.length > 1))
  test "malformed_primitive_and_list_entries_fail" do
    for (script, input) in [(integerDecoder, Data.B "wrong".toUTF8), (listSum, .List [.B "wrong".toUTF8]),
        (mapFind, .Map [(.B "policy".toUTF8, .Map [(.B "token".toUTF8, .B "wrong".toUTF8)])])] do
      match ← Moist.Plutus.Eval.evalTerm (.Apply script (dataTerm input)) with
      | .ok _ => throw (IO.userError "Malformed value unexpectedly accepted")
      | .error (kind, _, _) =>
        unless kind == .builtinError || kind == .typeMismatch do
          throw (IO.userError s!"Unexpected failure: {kind}")
  test "unsupported_native_map_views_and_safe_decoder_are_rejected" do
    unless rejectsNativeEntries && rejectsDynamicMap && rejectsNativeDecoder && rejectsUnspecializedCodec do
      throw (IO.userError "Missing representation diagnostic")

end Test.CollectionEncoding
