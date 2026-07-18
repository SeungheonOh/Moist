import Test.SMT.SupportedQueries

/-!
# Basic builtin SMT/CEK differential regression

This runnable test covers every builtin in the proved basic fragment.  For
each case it checks three independently executable views of the same program:

* the pure CEK transition system, started in the environment decoded from the
  test model;
* `Moist.SMT.Semantics.eval` on the compiler's generated assertion; and
* Z3 on the reference-rendered SMT-LIB script.

Integer cases additionally ask Z3 for a deliberately wrong result, and every
successful case asks for the mutually exclusive runtime-error result.  The
edge cases exercise representative value/type failures and partial selectors.
-/

namespace Test.SMT.BasicBuiltinDifferential

open Moist.Plutus
open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

abbrev tyInteger : BuiltinType := .AtomicType .TypeInteger
abbrev tyBool : BuiltinType := .AtomicType .TypeBool
abbrev tyBytes : BuiltinType := .AtomicType .TypeByteString
abbrev tyString : BuiltinType := .AtomicType .TypeString
abbrev tyUnit : BuiltinType := .AtomicType .TypeUnit
abbrev tyData : BuiltinType := .AtomicType .TypeData
abbrev tyListInteger : BuiltinType := .TypeOperator (.TypeList tyInteger)
abbrev tyListData : BuiltinType := .TypeOperator (.TypeList tyData)
abbrev tyPairData : BuiltinType := .TypeOperator (.TypePair tyData tyData)
abbrev tyListPairData : BuiltinType := .TypeOperator (.TypeList tyPairData)
abbrev tyPairInteger : BuiltinType := .TypeOperator (.TypePair tyInteger tyInteger)
abbrev tyArrayInteger : BuiltinType := .TypeOperator (.TypeArray tyInteger)

def int (value : Int) : Term := .Constant (.Integer value, tyInteger)
def bool (value : Bool) : Term := .Constant (.Bool value, tyBool)
def bytes (value : Array UInt8) : Term :=
  .Constant (.ByteString (ByteArray.mk value), tyBytes)
def string (value : String) : Term := .Constant (.String value, tyString)
def unit : Term := .Constant (.Unit, tyUnit)
def data (value : Data) : Term := .Constant (.Data value, tyData)
def listInteger (values : List Int) : Term :=
  .Constant (.ConstList (values.map Const.Integer), tyListInteger)
def listData (values : List Data) : Term :=
  .Constant (.ConstDataList values, tyListData)
def listPairData (values : List (Data × Data)) : Term :=
  .Constant (.ConstPairDataList values, tyListPairData)
def pairInteger (first second : Int) : Term :=
  .Constant (.Pair (.Integer first, .Integer second), tyPairInteger)
def arrayInteger (values : List Int) : Term :=
  .Constant (.ConstArray (values.map Const.Integer), tyArrayInteger)

def apply (function argument : Term) : Term := .Apply function argument

def applyAll (function : Term) (arguments : List Term) : Term :=
  arguments.foldl apply function

def forceN : Nat → Term → Term
  | 0, term => term
  | count + 1, term => forceN count (.Force term)

/-- Apply a builtin in source order, after its required type forces. -/
def call (builtin : BuiltinFun) (forces : Nat) (arguments : List Term) : Term :=
  applyAll (forceN forces (.Builtin builtin)) arguments

inductive Expected where
  | integer : Int → Expected
  | boolean : Bool → Expected
  | error : Expected
deriving Repr

structure Case where
  name : String
  primaryBuiltin : Option BuiltinFun := none
  declarations : List SymDecl := []
  model : Moist.SMT.Semantics.Model := Moist.SMT.Semantics.Model.empty
  term : Term
  expected : Expected

def primary (builtin : BuiltinFun) (name : String) (term : Term)
    (expected : Expected) : Case :=
  { name, primaryBuiltin := some builtin, term, expected }

def edge (name : String) (term : Term) (expected : Expected) : Case :=
  { name, term, expected }

private def euroBytes : Array UInt8 := #[0xE2, 0x82, 0xAC]
private def mapValue : Data := .Map [(.I 1, .B (ByteArray.mk #[2, 3]))]

/-- Exactly one primary case for every builtin admitted by the basic proof
dispatcher at the baseline of this test. -/
def primaryCases : List Case :=
  [ primary .AddInteger "add-integer"
      (call .AddInteger 0 [int 2, int 3]) (.integer 5)
  , primary .SubtractInteger "subtract-integer"
      (call .SubtractInteger 0 [int 2, int 7]) (.integer (-5))
  , primary .MultiplyInteger "multiply-integer"
      (call .MultiplyInteger 0 [int (-3), int 7]) (.integer (-21))
  , primary .DivideInteger "divide-integer"
      (call .DivideInteger 0 [int (-5), int 2]) (.integer (-3))
  , primary .QuotientInteger "quotient-integer"
      (call .QuotientInteger 0 [int (-5), int 2]) (.integer (-2))
  , primary .RemainderInteger "remainder-integer"
      (call .RemainderInteger 0 [int (-5), int 2]) (.integer (-1))
  , primary .ModInteger "mod-integer"
      (call .ModInteger 0 [int (-5), int 2]) (.integer 1)
  , primary .EqualsInteger "equals-integer"
      (call .EqualsInteger 0 [int 4, int 4]) (.boolean true)
  , primary .LessThanInteger "less-than-integer"
      (call .LessThanInteger 0 [int (-1), int 0]) (.boolean true)
  , primary .LessThanEqualsInteger "less-than-equals-integer"
      (call .LessThanEqualsInteger 0 [int 3, int 3]) (.boolean true)

  , primary .AppendByteString "append-byte-string"
      (call .LengthOfByteString 0
        [call .AppendByteString 0 [bytes #[1, 2], bytes #[3, 4]]])
      (.integer 4)
  , primary .ConsByteString "cons-byte-string"
      (call .IndexByteString 0
        [call .ConsByteString 0 [int 255, bytes #[1, 2]], int 0])
      (.integer 255)
  , primary .SliceByteString "slice-byte-string"
      (call .LengthOfByteString 0
        [call .SliceByteString 0 [int (-2), int 9, bytes #[1, 2, 3]]])
      (.integer 3)
  , primary .LengthOfByteString "length-of-byte-string"
      (call .LengthOfByteString 0 [bytes #[1, 2, 3]]) (.integer 3)
  , primary .IndexByteString "index-byte-string"
      (call .IndexByteString 0 [bytes #[9, 8], int 1]) (.integer 8)
  , primary .EqualsByteString "equals-byte-string"
      (call .EqualsByteString 0 [bytes #[1, 2], bytes #[1, 2]])
      (.boolean true)
  , primary .LessThanByteString "less-than-byte-string"
      (call .LessThanByteString 0 [bytes #[1], bytes #[1, 0]])
      (.boolean true)
  , primary .LessThanEqualsByteString "less-than-equals-byte-string"
      (call .LessThanEqualsByteString 0 [bytes #[1, 255], bytes #[1, 255]])
      (.boolean true)

  , primary .AppendString "append-string"
      (call .EqualsString 0
        [call .AppendString 0 [string "a", string "€"], string "a€"])
      (.boolean true)
  , primary .EqualsString "equals-string"
      (call .EqualsString 0 [string "same", string "same"]) (.boolean true)
  , primary .EncodeUtf8 "encode-utf8"
      (call .EqualsByteString 0
        [call .EncodeUtf8 0 [string "€"], bytes euroBytes])
      (.boolean true)
  , primary .DecodeUtf8 "decode-utf8"
      (call .EqualsString 0
        [call .DecodeUtf8 0 [bytes euroBytes], string "€"])
      (.boolean true)

  , primary .IfThenElse "if-then-else"
      (call .IfThenElse 1 [bool true, int 11, int 22]) (.integer 11)
  , primary .ChooseUnit "choose-unit"
      (call .ChooseUnit 1 [unit, int 9]) (.integer 9)
  , primary .Trace "trace"
      (call .Trace 1 [string "message", int 8]) (.integer 8)
  , primary .FstPair "fst-pair"
      (call .FstPair 2 [pairInteger 4 5]) (.integer 4)
  , primary .SndPair "snd-pair"
      (call .SndPair 2 [pairInteger 4 5]) (.integer 5)
  , primary .ChooseList "choose-list"
      (call .ChooseList 2 [listInteger [], int 10, int 20]) (.integer 10)
  , primary .MkCons "mk-cons"
      (call .HeadList 1
        [call .MkCons 1 [int 7, listInteger [8]]]) (.integer 7)
  , primary .HeadList "head-list"
      (call .HeadList 1 [listInteger [9, 8]]) (.integer 9)
  , primary .TailList "tail-list"
      (call .HeadList 1
        [call .TailList 1 [listInteger [9, 8]]]) (.integer 8)
  , primary .NullList "null-list"
      (call .NullList 1 [listInteger []]) (.boolean true)

  , primary .ChooseData "choose-data"
      (call .ChooseData 1
        [data (.I 3), int 0, int 1, int 2, int 3, int 4])
      (.integer 3)
  , primary .ConstrData "constr-data"
      (call .EqualsData 0
        [call .ConstrData 0 [int 7, listData [.I 2]],
         data (.Constr 7 [.I 2])])
      (.boolean true)
  , primary .MapData "map-data"
      (call .EqualsData 0
        [call .MapData 0 [listPairData [(.I 1, .B (ByteArray.mk #[2, 3]))]],
         data mapValue])
      (.boolean true)
  , primary .ListData "list-data"
      (call .EqualsData 0
        [call .ListData 0 [listData [.I 1, .I 2]],
         data (.List [.I 1, .I 2])])
      (.boolean true)
  , primary .IData "i-data"
      (call .EqualsData 0 [call .IData 0 [int (-12)], data (.I (-12))])
      (.boolean true)
  , primary .BData "b-data"
      (call .EqualsData 0
        [call .BData 0 [bytes #[1, 2]], data (.B (ByteArray.mk #[1, 2]))])
      (.boolean true)
  , primary .UnConstrData "un-constr-data"
      (call .UnIData 0
        [call .FstPair 2 [call .UnConstrData 0 [data (.Constr 7 [.I 2])]]])
      (.integer 7)
  , primary .UnMapData "un-map-data"
      (call .EqualsData 0
        [call .MapData 0 [call .UnMapData 0 [data mapValue]], data mapValue])
      (.boolean true)
  , primary .UnListData "un-list-data"
      (call .NullList 1 [call .UnListData 0 [data (.List [])]])
      (.boolean true)
  , primary .UnIData "un-i-data"
      (call .UnIData 0 [data (.I (-12))]) (.integer (-12))
  , primary .UnBData "un-b-data"
      (call .LengthOfByteString 0
        [call .UnBData 0 [data (.B (ByteArray.mk #[1, 2]))]])
      (.integer 2)
  , primary .EqualsData "equals-data"
      (call .EqualsData 0
        [data (.Constr 7 [.I 2]), data (.Constr 7 [.I 2])])
      (.boolean true)
  , primary .MkPairData "mk-pair-data"
      (call .UnIData 0
        [call .FstPair 2
          [call .MkPairData 0 [data (.I 1), data (.I 2)]]])
      (.integer 1)
  , primary .MkNilData "mk-nil-data"
      (call .NullList 1 [call .MkNilData 0 [unit]]) (.boolean true)
  , primary .MkNilPairData "mk-nil-pair-data"
      (call .EqualsData 0
        [call .MapData 0 [call .MkNilPairData 0 [unit]], data (.Map [])])
      (.boolean true)

  , primary .DropList "drop-list"
      (call .HeadList 1
        [call .DropList 1 [int 1, listInteger [6, 7]]]) (.integer 7)
  , primary .IndexArray "index-array"
      (call .IndexArray 1 [arrayInteger [4, 5, 6], int 2]) (.integer 6)
  , primary .LengthOfArray "length-of-array"
      (call .LengthOfArray 1 [arrayInteger [4, 5, 6]]) (.integer 3)
  , primary .ListToArray "list-to-array"
      (call .LengthOfArray 1
        [call .ListToArray 1 [listInteger [1, 2, 3, 4]]])
      (.integer 4)
  ]

def basicBuiltins : List BuiltinFun :=
  [ .AddInteger, .SubtractInteger, .MultiplyInteger, .DivideInteger,
    .QuotientInteger, .RemainderInteger, .ModInteger, .EqualsInteger,
    .LessThanInteger, .LessThanEqualsInteger, .AppendByteString,
    .ConsByteString, .SliceByteString, .LengthOfByteString, .IndexByteString,
    .EqualsByteString, .LessThanByteString, .LessThanEqualsByteString,
    .AppendString, .EqualsString, .EncodeUtf8, .DecodeUtf8, .IfThenElse,
    .ChooseUnit, .Trace, .FstPair, .SndPair, .ChooseList, .MkCons,
    .HeadList, .TailList, .NullList, .ChooseData, .ConstrData, .MapData,
    .ListData, .IData, .BData, .UnConstrData, .UnMapData, .UnListData,
    .UnIData, .UnBData, .EqualsData, .MkPairData, .MkNilData,
    .MkNilPairData, .DropList, .IndexArray, .LengthOfArray, .ListToArray ]

def advancedBuiltins : List BuiltinFun :=
  [ .IntegerToByteString, .ByteStringToInteger,
    .AndByteString, .OrByteString, .XorByteString,
    .ComplementByteString, .ReadBit, .WriteBits, .ReplicateByte,
    .ShiftByteString, .RotateByteString, .CountSetBits,
    .FindFirstSetBit, .ExpModInteger ]

def advancedPartialBuiltins : List BuiltinFun :=
  [ .IntegerToByteString, .ReadBit, .WriteBits, .ReplicateByte,
    .ExpModInteger ]

/-- Closed calls exercise the CEK-backed exact folding path for every
advanced non-cryptographic builtin.  ByteString results are consumed by
proved basic builtins so the existing exact Boolean/integer harness can
compare CEK, internal SMT semantics, and rendered Z3 queries. -/
def advancedPrimaryCases : List Case :=
  [ primary .IntegerToByteString "integer-to-byte-string"
      (call .EqualsByteString 0
        [call .IntegerToByteString 0 [bool true, int 2, int 258],
         bytes #[1, 2]]) (.boolean true)
  , primary .ByteStringToInteger "byte-string-to-integer"
      (call .ByteStringToInteger 0 [bool false, bytes #[1, 2]])
      (.integer 513)
  , primary .AndByteString "and-byte-string"
      (call .EqualsByteString 0
        [call .AndByteString 0
          [bool true, bytes #[0xf0, 0x0f], bytes #[0xaa]],
         bytes #[0xa0, 0x0f]]) (.boolean true)
  , primary .OrByteString "or-byte-string"
      (call .EqualsByteString 0
        [call .OrByteString 0
          [bool true, bytes #[0xf0, 0x0f], bytes #[0xaa]],
         bytes #[0xfa, 0x0f]]) (.boolean true)
  , primary .XorByteString "xor-byte-string"
      (call .EqualsByteString 0
        [call .XorByteString 0
          [bool true, bytes #[0xf0, 0x0f], bytes #[0xaa]],
         bytes #[0x5a, 0x0f]]) (.boolean true)
  , primary .ComplementByteString "complement-byte-string"
      (call .EqualsByteString 0
        [call .ComplementByteString 0 [bytes #[0x00, 0xaa, 0xff]],
         bytes #[0xff, 0x55, 0x00]]) (.boolean true)
  , primary .ReadBit "read-bit"
      (call .ReadBit 0 [bytes #[0x01], int 0]) (.boolean true)
  , primary .WriteBits "write-bits"
      (call .EqualsByteString 0
        [call .WriteBits 0
          [bytes #[0x00, 0x00], listInteger [0, 15], bool true],
         bytes #[0x80, 0x01]]) (.boolean true)
  , primary .ReplicateByte "replicate-byte"
      (call .EqualsByteString 0
        [call .ReplicateByte 0 [int 3, int 0xab],
         bytes #[0xab, 0xab, 0xab]]) (.boolean true)
  , primary .ShiftByteString "shift-byte-string"
      (call .EqualsByteString 0
        [call .ShiftByteString 0 [bytes #[0x12, 0x34], int 4],
         bytes #[0x23, 0x40]]) (.boolean true)
  , primary .RotateByteString "rotate-byte-string"
      (call .EqualsByteString 0
        [call .RotateByteString 0 [bytes #[0x12, 0x34], int (-4)],
         bytes #[0x41, 0x23]]) (.boolean true)
  , primary .CountSetBits "count-set-bits"
      (call .CountSetBits 0 [bytes #[0x00, 0xff, 0x81]]) (.integer 10)
  , primary .FindFirstSetBit "find-first-set-bit"
      (call .FindFirstSetBit 0 [bytes #[0x04, 0x00]]) (.integer 10)
  , primary .ExpModInteger "exp-mod-integer"
      (call .ExpModInteger 0 [int 3, int 4, int 5]) (.integer 1)
  ]

/-- Every advanced builtin is also exercised on a closed failing call.  For
total operations this is a CEK runtime type error; partial operations use a
domain error, ensuring the ground fast path preserves `none` exactly. -/
def advancedGroundErrorCases : List Case :=
  [ { name := "ground-error-integer-to-byte-string"
      primaryBuiltin := some .IntegerToByteString
      term := call .IntegerToByteString 0 [bool true, int 1, int 256]
      expected := .error }
  , { name := "ground-error-byte-string-to-integer"
      primaryBuiltin := some .ByteStringToInteger
      term := call .ByteStringToInteger 0 [unit, bytes #[]]
      expected := .error }
  , { name := "ground-error-and-byte-string"
      primaryBuiltin := some .AndByteString
      term := call .AndByteString 0 [unit, bytes #[], bytes #[]]
      expected := .error }
  , { name := "ground-error-or-byte-string"
      primaryBuiltin := some .OrByteString
      term := call .OrByteString 0 [unit, bytes #[], bytes #[]]
      expected := .error }
  , { name := "ground-error-xor-byte-string"
      primaryBuiltin := some .XorByteString
      term := call .XorByteString 0 [unit, bytes #[], bytes #[]]
      expected := .error }
  , { name := "ground-error-complement-byte-string"
      primaryBuiltin := some .ComplementByteString
      term := call .ComplementByteString 0 [unit]
      expected := .error }
  , { name := "ground-error-read-bit"
      primaryBuiltin := some .ReadBit
      term := call .ReadBit 0 [bytes #[0], int 8]
      expected := .error }
  , { name := "ground-error-write-bits"
      primaryBuiltin := some .WriteBits
      term := call .WriteBits 0 [bytes #[0], listInteger [8], bool true]
      expected := .error }
  , { name := "ground-error-replicate-byte"
      primaryBuiltin := some .ReplicateByte
      term := call .ReplicateByte 0 [int (-1), int 0]
      expected := .error }
  , { name := "ground-error-shift-byte-string"
      primaryBuiltin := some .ShiftByteString
      term := call .ShiftByteString 0 [unit, int 1]
      expected := .error }
  , { name := "ground-error-rotate-byte-string"
      primaryBuiltin := some .RotateByteString
      term := call .RotateByteString 0 [unit, int 1]
      expected := .error }
  , { name := "ground-error-count-set-bits"
      primaryBuiltin := some .CountSetBits
      term := call .CountSetBits 0 [unit]
      expected := .error }
  , { name := "ground-error-find-first-set-bit"
      primaryBuiltin := some .FindFirstSetBit
      term := call .FindFirstSetBit 0 [unit]
      expected := .error }
  , { name := "ground-error-exp-mod-integer"
      primaryBuiltin := some .ExpModInteger
      term := call .ExpModInteger 0 [int 2, int (-1), int 4]
      expected := .error }
  ]

/-- Failures are checked both as positive error queries and as negative value
queries.  These cover arithmetic-domain, UTF-8, projection, list, data, array,
and dynamic-type rejection. -/
def edgeCases : List Case :=
  [ edge "equals-integer-false"
      (call .EqualsInteger 0 [int 1, int 2]) (.boolean false)
  , edge "divide-by-zero"
      (call .DivideInteger 0 [int 7, int 0]) .error
  , edge "cons-byte-out-of-range"
      (call .ConsByteString 0 [int 256, bytes #[]]) .error
  , edge "index-byte-negative"
      (call .IndexByteString 0 [bytes #[1], int (-1)]) .error
  , edge "index-byte-at-end"
      (call .IndexByteString 0 [bytes #[1], int 1]) .error
  , edge "decode-overlong-utf8"
      (call .DecodeUtf8 0 [bytes #[0xC0, 0x80]]) .error
  , edge "decode-surrogate-utf8"
      (call .DecodeUtf8 0 [bytes #[0xED, 0xA0, 0x80]]) .error
  , edge "choose-unit-wrong-type"
      (call .ChooseUnit 1 [int 0, int 9]) .error
  , edge "trace-wrong-message-type"
      (call .Trace 1 [int 0, int 9]) .error
  , edge "fst-pair-wrong-type"
      (call .FstPair 2 [int 0]) .error
  , edge "choose-list-wrong-type"
      (call .ChooseList 2 [int 0, int 1, int 2]) .error
  , edge "head-empty-list"
      (call .HeadList 1 [listInteger []]) .error
  , edge "mk-cons-runtime-constructor"
      (call .MkCons 1 [.Constr 0 [], listInteger []]) .error
  , edge "choose-data-wrong-type"
      (call .ChooseData 1 [int 0, int 1, int 2, int 3, int 4, int 5]) .error
  , edge "un-i-data-wrong-constructor"
      (call .UnIData 0 [data (.B (ByteArray.mk #[1]))]) .error
  , edge "index-array-negative"
      (call .IndexArray 1 [arrayInteger [4], int (-1)]) .error
  , edge "index-array-at-end"
      (call .IndexArray 1 [arrayInteger [4], int 1]) .error
  , edge "list-to-array-wrong-list-kind"
      (call .ListToArray 1 [listData [.I 1]]) .error
  ]

private def constrainedInt : SymDecl :=
  let declaration := symInt "i"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.int (-5))]

private def constrainedBytes : SymDecl :=
  let declaration := symBytes "bytes"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.bytes (ByteArray.mk #[1, 255]))]

private def constrainedString : SymDecl :=
  let declaration := symString "string"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name)
      (.str (String.singleton (Char.ofNat 0x10FFFF)))]

private def constrainedData : SymDecl :=
  let declaration := symData "data"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.dataLit (.I (-12)))]

private def constrainedValInt : SymDecl :=
  let declaration := symVal "val_int"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.app "VInt" [.int (-3)])]

private def constrainedValList : SymDecl :=
  let declaration := symVal "val_list"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name)
      (.app "VList"
        [.app "VCons"
          [.app "VInt" [.int 2],
           .app "VCons" [.app "VInt" [.int 3], .app "VNil" []]]])]

private def constrainedValArray : SymDecl :=
  let declaration := symVal "val_array"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name)
      (.app "VArray"
        [.app "VCons" [.app "VInt" [.int 4], .app "VNil" []]])]

private def constrainedValConstr : SymDecl :=
  let declaration := symVal "val_constr"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name)
      (.app "VConstr"
        [.int 0,
         .app "VCons" [.app "VInt" [.int 7], .app "VNil" []]])]

private def constrainedValWrong : SymDecl :=
  let declaration := symVal "val_wrong"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name)
      (.app "VBytes" [.bytes (ByteArray.mk #[1])])]

private def constrainedField : SymDecl :=
  let declaration := symInt "field"
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.int 8)]

private def constrainedTag : SymDecl :=
  let declaration :=
    symConstr "tag" [.const (.integer (.sym constrainedField.name))]
  declaration.withAssumptions
    [SExpr.eq (.sym declaration.name) (.int 0)]

private def bindModel (name : String) (value : Moist.SMT.Semantics.SVal) :
    Moist.SMT.Semantics.Model → Moist.SMT.Semantics.Model :=
  fun model => Moist.SMT.Semantics.Model.bind model name value

private def emptyModel : Moist.SMT.Semantics.Model :=
  Moist.SMT.Semantics.Model.empty

private def constrainedIntCase (builtin : BuiltinFun) (name : String)
    (value : Int) (build : Term → Term) (expected : Expected) : Case :=
  let base := symInt (name ++ "-integer")
  let declaration := base.withAssumptions
    [SExpr.eq (.sym base.name) (.int value)]
  { name
    primaryBuiltin := some builtin
    declarations := [declaration]
    model := bindModel declaration.name (.int value) emptyModel
    term := build (.Var 1)
    expected }

private def constrainedBoolCase (builtin : BuiltinFun) (name : String)
    (value : Bool) (build : Term → Term) (expected : Expected) : Case :=
  let base := symBool (name ++ "-boolean")
  let declaration := base.withAssumptions
    [SExpr.eq (.sym base.name) (.bool value)]
  { name
    primaryBuiltin := some builtin
    declarations := [declaration]
    model := bindModel declaration.name (.bool value) emptyModel
    term := build (.Var 1)
    expected }

private def constrainedBytesCase (builtin : BuiltinFun) (name : String)
    (value : Array UInt8) (build : Term → Term) (expected : Expected) : Case :=
  let bytesValue := ByteArray.mk value
  let base := symBytes (name ++ "-bytes")
  let declaration := base.withAssumptions
    [SExpr.eq (.sym base.name) (.bytes bytesValue)]
  { name
    primaryBuiltin := some builtin
    declarations := [declaration]
    model := bindModel declaration.name (.bytes bytesValue) emptyModel
    term := build (.Var 1)
    expected }

private def constrainedStringCase (builtin : BuiltinFun) (name value : String)
    (build : Term → Term) (expected : Expected) : Case :=
  let base := symString (name ++ "-string")
  let declaration := base.withAssumptions
    [SExpr.eq (.sym base.name) (.str value)]
  { name
    primaryBuiltin := some builtin
    declarations := [declaration]
    model := bindModel declaration.name (.string value) emptyModel
    term := build (.Var 1)
    expected }

private def constrainedDataCase (builtin : BuiltinFun) (name : String)
    (value : Data) (build : Term → Term) (expected : Expected) : Case :=
  let base := symData (name ++ "-data")
  let declaration := base.withAssumptions
    [SExpr.eq (.sym base.name) (.dataLit value)]
  { name
    primaryBuiltin := some builtin
    declarations := [declaration]
    model := bindModel declaration.name (.data value) emptyModel
    term := build (.Var 1)
    expected }

private def constrainedValCase (builtin : BuiltinFun) (name : String)
    (expression : SExpr) (value : Moist.SMT.Semantics.Val)
    (build : Term → Term) (expected : Expected) : Case :=
  let base := symVal (name ++ "-value")
  let declaration := base.withAssumptions
    [SExpr.eq (.sym base.name) expression]
  { name
    primaryBuiltin := some builtin
    declarations := [declaration]
    model := bindModel declaration.name (.val value) emptyModel
    term := build (.Var 1)
    expected }

private def vIntExpr (value : Int) : SExpr := .app "VInt" [.int value]
private def vUnitExpr : SExpr := .app "VUnit" []
private def vPairIntExpr (first second : Int) : SExpr :=
  .app "VPair" [vIntExpr first, vIntExpr second]
private def vListIntegerExpr (values : List Int) : SExpr :=
  .app "VList" [.constListLit (values.map Const.Integer)]
private def vDataListExpr (values : List Data) : SExpr :=
  .app "VDataList" [.dataListLit values]
private def vPairDataListExpr (values : List (Data × Data)) : SExpr :=
  .app "VPairDataList" [.dataPairListLit values]
private def vArrayIntegerExpr (values : List Int) : SExpr :=
  .app "VArray" [.constListLit (values.map Const.Integer)]

/-!
Every proved basic builtin is exercised below with a declaration-backed input.
The declaration is constrained to a concrete model value, but the compiler
still receives a genuine symbolic expression (`.Var 1`), so this tests the
symbolic path rather than merely another constant-folding path.
-/
def symbolicBuiltinCases : List Case :=
  [ constrainedIntCase .AddInteger "symbolic-add-integer" 2
      (fun x => call .AddInteger 0 [x, int 3]) (.integer 5)
  , constrainedIntCase .SubtractInteger "symbolic-subtract-integer" 2
      (fun x => call .SubtractInteger 0 [x, int 7]) (.integer (-5))
  , constrainedIntCase .MultiplyInteger "symbolic-multiply-integer" (-3)
      (fun x => call .MultiplyInteger 0 [x, int 7]) (.integer (-21))
  , constrainedIntCase .DivideInteger "symbolic-divide-integer" (-5)
      (fun x => call .DivideInteger 0 [x, int 2]) (.integer (-3))
  , constrainedIntCase .QuotientInteger "symbolic-quotient-integer" (-5)
      (fun x => call .QuotientInteger 0 [x, int 2]) (.integer (-2))
  , constrainedIntCase .RemainderInteger "symbolic-remainder-integer" (-5)
      (fun x => call .RemainderInteger 0 [x, int 2]) (.integer (-1))
  , constrainedIntCase .ModInteger "symbolic-mod-integer" (-5)
      (fun x => call .ModInteger 0 [x, int 2]) (.integer 1)
  , constrainedIntCase .EqualsInteger "symbolic-equals-integer" 4
      (fun x => call .EqualsInteger 0 [x, int 4]) (.boolean true)
  , constrainedIntCase .LessThanInteger "symbolic-less-than-integer" (-1)
      (fun x => call .LessThanInteger 0 [x, int 0]) (.boolean true)
  , constrainedIntCase .LessThanEqualsInteger
      "symbolic-less-than-equals-integer" 3
      (fun x => call .LessThanEqualsInteger 0 [x, int 3]) (.boolean true)

  , constrainedBytesCase .AppendByteString "symbolic-append-byte-string" #[1, 2]
      (fun x => call .LengthOfByteString 0
        [call .AppendByteString 0 [x, bytes #[3, 4]]]) (.integer 4)
  , constrainedIntCase .ConsByteString "symbolic-cons-byte-string" 255
      (fun x => call .IndexByteString 0
        [call .ConsByteString 0 [x, bytes #[1, 2]], int 0]) (.integer 255)
  , constrainedIntCase .SliceByteString "symbolic-slice-byte-string" (-2)
      (fun x => call .LengthOfByteString 0
        [call .SliceByteString 0 [x, int 9, bytes #[1, 2, 3]]]) (.integer 3)
  , constrainedBytesCase .LengthOfByteString
      "symbolic-length-of-byte-string" #[1, 2, 3]
      (fun x => call .LengthOfByteString 0 [x]) (.integer 3)
  , constrainedBytesCase .IndexByteString "symbolic-index-byte-string" #[9, 8]
      (fun x => call .IndexByteString 0 [x, int 1]) (.integer 8)
  , constrainedBytesCase .EqualsByteString
      "symbolic-equals-byte-string" #[1, 2]
      (fun x => call .EqualsByteString 0 [x, bytes #[1, 2]]) (.boolean true)
  , constrainedBytesCase .LessThanByteString
      "symbolic-less-than-byte-string" #[1]
      (fun x => call .LessThanByteString 0 [x, bytes #[1, 0]]) (.boolean true)
  , constrainedBytesCase .LessThanEqualsByteString
      "symbolic-less-than-equals-byte-string" #[1, 255]
      (fun x => call .LessThanEqualsByteString 0 [x, bytes #[1, 255]])
      (.boolean true)

  , constrainedStringCase .AppendString "symbolic-append-string" "a"
      (fun x => call .EqualsString 0
        [call .AppendString 0 [x, string "€"], string "a€"]) (.boolean true)
  , constrainedStringCase .EqualsString "symbolic-equals-string" "same"
      (fun x => call .EqualsString 0 [x, string "same"]) (.boolean true)
  , constrainedStringCase .EncodeUtf8 "symbolic-encode-utf8" "€"
      (fun x => call .EqualsByteString 0
        [call .EncodeUtf8 0 [x], bytes euroBytes]) (.boolean true)
  , constrainedBytesCase .DecodeUtf8 "symbolic-decode-utf8" euroBytes
      (fun x => call .EqualsString 0
        [call .DecodeUtf8 0 [x], string "€"]) (.boolean true)

  , constrainedBoolCase .IfThenElse "symbolic-if-then-else" true
      (fun x => call .IfThenElse 1 [x, int 11, int 22]) (.integer 11)
  , constrainedValCase .ChooseUnit "symbolic-choose-unit" vUnitExpr .unit
      (fun x => call .ChooseUnit 1 [x, int 9]) (.integer 9)
  , constrainedIntCase .Trace "symbolic-trace" 8
      (fun x => call .Trace 1 [string "message", x]) (.integer 8)
  , constrainedValCase .FstPair "symbolic-fst-pair" (vPairIntExpr 4 5)
      (.pair (.int 4) (.int 5))
      (fun x => call .FstPair 2 [x]) (.integer 4)
  , constrainedValCase .SndPair "symbolic-snd-pair" (vPairIntExpr 4 5)
      (.pair (.int 4) (.int 5))
      (fun x => call .SndPair 2 [x]) (.integer 5)
  , constrainedValCase .ChooseList "symbolic-choose-list"
      (vListIntegerExpr []) (.list [])
      (fun x => call .ChooseList 2 [x, int 10, int 20]) (.integer 10)
  , constrainedIntCase .MkCons "symbolic-mk-cons" 7
      (fun x => call .HeadList 1
        [call .MkCons 1 [x, listInteger [8]]]) (.integer 7)
  , constrainedValCase .HeadList "symbolic-head-list"
      (vListIntegerExpr [9, 8]) (.list [.int 9, .int 8])
      (fun x => call .HeadList 1 [x]) (.integer 9)
  , constrainedValCase .TailList "symbolic-tail-list"
      (vListIntegerExpr [9, 8]) (.list [.int 9, .int 8])
      (fun x => call .HeadList 1 [call .TailList 1 [x]]) (.integer 8)
  , constrainedValCase .NullList "symbolic-null-list"
      (vListIntegerExpr []) (.list [])
      (fun x => call .NullList 1 [x]) (.boolean true)

  , constrainedDataCase .ChooseData "symbolic-choose-data" (.I 3)
      (fun x => call .ChooseData 1 [x, int 0, int 1, int 2, int 3, int 4])
      (.integer 3)
  , constrainedIntCase .ConstrData "symbolic-constr-data" 7
      (fun x => call .EqualsData 0
        [call .ConstrData 0 [x, listData [.I 2]], data (.Constr 7 [.I 2])])
      (.boolean true)
  , constrainedValCase .MapData "symbolic-map-data"
      (vPairDataListExpr [(.I 1, .B (ByteArray.mk #[2, 3]))])
      (.pairDataList [(.I 1, .B (ByteArray.mk #[2, 3]))])
      (fun x => call .EqualsData 0 [call .MapData 0 [x], data mapValue])
      (.boolean true)
  , constrainedValCase .ListData "symbolic-list-data"
      (vDataListExpr [.I 1, .I 2]) (.dataList [.I 1, .I 2])
      (fun x => call .EqualsData 0
        [call .ListData 0 [x], data (.List [.I 1, .I 2])]) (.boolean true)
  , constrainedIntCase .IData "symbolic-i-data" (-12)
      (fun x => call .EqualsData 0 [call .IData 0 [x], data (.I (-12))])
      (.boolean true)
  , constrainedBytesCase .BData "symbolic-b-data" #[1, 2]
      (fun x => call .EqualsData 0
        [call .BData 0 [x], data (.B (ByteArray.mk #[1, 2]))]) (.boolean true)
  , constrainedDataCase .UnConstrData "symbolic-un-constr-data"
      (.Constr 7 [.I 2])
      (fun x => call .UnIData 0 [call .FstPair 2 [call .UnConstrData 0 [x]]])
      (.integer 7)
  , constrainedDataCase .UnMapData "symbolic-un-map-data" mapValue
      (fun x => call .EqualsData 0 [call .MapData 0 [call .UnMapData 0 [x]],
        data mapValue]) (.boolean true)
  , constrainedDataCase .UnListData "symbolic-un-list-data" (.List [])
      (fun x => call .NullList 1 [call .UnListData 0 [x]]) (.boolean true)
  , constrainedDataCase .UnIData "symbolic-un-i-data" (.I (-12))
      (fun x => call .UnIData 0 [x]) (.integer (-12))
  , constrainedDataCase .UnBData "symbolic-un-b-data"
      (.B (ByteArray.mk #[1, 2]))
      (fun x => call .LengthOfByteString 0 [call .UnBData 0 [x]]) (.integer 2)
  , constrainedDataCase .EqualsData "symbolic-equals-data" (.Constr 7 [.I 2])
      (fun x => call .EqualsData 0 [x, data (.Constr 7 [.I 2])]) (.boolean true)
  , constrainedDataCase .MkPairData "symbolic-mk-pair-data" (.I 1)
      (fun x => call .UnIData 0
        [call .FstPair 2 [call .MkPairData 0 [x, data (.I 2)]]]) (.integer 1)
  , constrainedValCase .MkNilData "symbolic-mk-nil-data" vUnitExpr .unit
      (fun x => call .NullList 1 [call .MkNilData 0 [x]]) (.boolean true)
  , constrainedValCase .MkNilPairData "symbolic-mk-nil-pair-data"
      vUnitExpr .unit
      (fun x => call .EqualsData 0
        [call .MapData 0 [call .MkNilPairData 0 [x]], data (.Map [])])
      (.boolean true)

  , constrainedIntCase .DropList "symbolic-drop-list" 1
      (fun x => call .HeadList 1
        [call .DropList 1 [x, listInteger [6, 7]]]) (.integer 7)
  , constrainedValCase .IndexArray "symbolic-index-array"
      (vArrayIntegerExpr [4, 5, 6]) (.array [.int 4, .int 5, .int 6])
      (fun x => call .IndexArray 1 [x, int 2]) (.integer 6)
  , constrainedValCase .LengthOfArray "symbolic-length-of-array"
      (vArrayIntegerExpr [4, 5, 6]) (.array [.int 4, .int 5, .int 6])
      (fun x => call .LengthOfArray 1 [x]) (.integer 3)
  , constrainedValCase .ListToArray "symbolic-list-to-array"
      (vListIntegerExpr [1, 2, 3, 4]) (.list [.int 1, .int 2, .int 3, .int 4])
      (fun x => call .LengthOfArray 1 [call .ListToArray 1 [x]]) (.integer 4)
  ]

/-- Genuine declaration-backed success paths for every advanced builtin. -/
def advancedSymbolicBuiltinCases : List Case :=
  [ constrainedIntCase .IntegerToByteString
      "symbolic-integer-to-byte-string" 258
      (fun x => call .EqualsByteString 0
        [call .IntegerToByteString 0 [bool true, int 2, x],
         bytes #[1, 2]]) (.boolean true)
  , constrainedBytesCase .ByteStringToInteger
      "symbolic-byte-string-to-integer" #[1, 2]
      (fun x => call .ByteStringToInteger 0 [bool false, x]) (.integer 513)
  , constrainedBytesCase .AndByteString "symbolic-and-byte-string"
      #[0xf0, 0x0f]
      (fun x => call .EqualsByteString 0
        [call .AndByteString 0 [bool true, x, bytes #[0xaa]],
         bytes #[0xa0, 0x0f]]) (.boolean true)
  , constrainedBytesCase .OrByteString "symbolic-or-byte-string"
      #[0xf0, 0x0f]
      (fun x => call .EqualsByteString 0
        [call .OrByteString 0 [bool true, x, bytes #[0xaa]],
         bytes #[0xfa, 0x0f]]) (.boolean true)
  , constrainedBytesCase .XorByteString "symbolic-xor-byte-string"
      #[0xf0, 0x0f]
      (fun x => call .EqualsByteString 0
        [call .XorByteString 0 [bool true, x, bytes #[0xaa]],
         bytes #[0x5a, 0x0f]]) (.boolean true)
  , constrainedBytesCase .ComplementByteString
      "symbolic-complement-byte-string" #[0x00, 0xaa, 0xff]
      (fun x => call .EqualsByteString 0
        [call .ComplementByteString 0 [x], bytes #[0xff, 0x55, 0x00]])
      (.boolean true)
  , constrainedBytesCase .ReadBit "symbolic-read-bit" #[0x01]
      (fun x => call .ReadBit 0 [x, int 0]) (.boolean true)
  , constrainedBytesCase .WriteBits "symbolic-write-bits" #[0x00, 0x00]
      (fun x => call .EqualsByteString 0
        [call .WriteBits 0 [x, listInteger [0, 15], bool true],
         bytes #[0x80, 0x01]]) (.boolean true)
  , constrainedIntCase .ReplicateByte "symbolic-replicate-byte" 3
      (fun x => call .EqualsByteString 0
        [call .ReplicateByte 0 [x, int 0xab], bytes #[0xab, 0xab, 0xab]])
      (.boolean true)
  , constrainedBytesCase .ShiftByteString "symbolic-shift-byte-string"
      #[0x12, 0x34]
      (fun x => call .EqualsByteString 0
        [call .ShiftByteString 0 [x, int 4], bytes #[0x23, 0x40]])
      (.boolean true)
  , constrainedBytesCase .RotateByteString "symbolic-rotate-byte-string"
      #[0x12, 0x34]
      (fun x => call .EqualsByteString 0
        [call .RotateByteString 0 [x, int (-4)], bytes #[0x41, 0x23]])
      (.boolean true)
  , constrainedBytesCase .CountSetBits "symbolic-count-set-bits"
      #[0x00, 0xff, 0x81]
      (fun x => call .CountSetBits 0 [x]) (.integer 10)
  , constrainedBytesCase .FindFirstSetBit "symbolic-find-first-set-bit"
      #[0x04, 0x00]
      (fun x => call .FindFirstSetBit 0 [x]) (.integer 10)
  , constrainedIntCase .ExpModInteger "symbolic-exp-mod-integer" 3
      (fun x => call .ExpModInteger 0 [x, int 4, int 5]) (.integer 1)
  ]

private def wrongUnitCase (builtin : BuiltinFun) (name : String)
    (build : Term → Term) : Case :=
  constrainedValCase builtin name vUnitExpr .unit build .error

private def wrongIntegerCase (builtin : BuiltinFun) (name : String)
    (build : Term → Term) : Case :=
  constrainedValCase builtin name (vIntExpr 0) (.int 0) build .error

/-! Every basic builtin also gets a declaration-backed dynamic type failure.
This drives the compiler's error condition through CEK, the executable SMT
semantics, and Z3 instead of checking only successful branches. -/
def symbolicBuiltinErrorCases : List Case :=
  [ wrongUnitCase .AddInteger "symbolic-error-add-integer"
      (fun x => call .AddInteger 0 [x, int 1])
  , wrongUnitCase .SubtractInteger "symbolic-error-subtract-integer"
      (fun x => call .SubtractInteger 0 [x, int 1])
  , wrongUnitCase .MultiplyInteger "symbolic-error-multiply-integer"
      (fun x => call .MultiplyInteger 0 [x, int 1])
  , wrongUnitCase .DivideInteger "symbolic-error-divide-integer"
      (fun x => call .DivideInteger 0 [x, int 1])
  , wrongUnitCase .QuotientInteger "symbolic-error-quotient-integer"
      (fun x => call .QuotientInteger 0 [x, int 1])
  , wrongUnitCase .RemainderInteger "symbolic-error-remainder-integer"
      (fun x => call .RemainderInteger 0 [x, int 1])
  , wrongUnitCase .ModInteger "symbolic-error-mod-integer"
      (fun x => call .ModInteger 0 [x, int 1])
  , wrongUnitCase .EqualsInteger "symbolic-error-equals-integer"
      (fun x => call .EqualsInteger 0 [x, int 1])
  , wrongUnitCase .LessThanInteger "symbolic-error-less-than-integer"
      (fun x => call .LessThanInteger 0 [x, int 1])
  , wrongUnitCase .LessThanEqualsInteger "symbolic-error-less-than-equals-integer"
      (fun x => call .LessThanEqualsInteger 0 [x, int 1])

  , wrongUnitCase .AppendByteString "symbolic-error-append-byte-string"
      (fun x => call .AppendByteString 0 [x, bytes #[]])
  , wrongUnitCase .ConsByteString "symbolic-error-cons-byte-string"
      (fun x => call .ConsByteString 0 [x, bytes #[]])
  , wrongUnitCase .SliceByteString "symbolic-error-slice-byte-string"
      (fun x => call .SliceByteString 0 [x, int 1, bytes #[]])
  , wrongUnitCase .LengthOfByteString "symbolic-error-length-of-byte-string"
      (fun x => call .LengthOfByteString 0 [x])
  , wrongUnitCase .IndexByteString "symbolic-error-index-byte-string"
      (fun x => call .IndexByteString 0 [x, int 0])
  , wrongUnitCase .EqualsByteString "symbolic-error-equals-byte-string"
      (fun x => call .EqualsByteString 0 [x, bytes #[]])
  , wrongUnitCase .LessThanByteString "symbolic-error-less-than-byte-string"
      (fun x => call .LessThanByteString 0 [x, bytes #[]])
  , wrongUnitCase .LessThanEqualsByteString
      "symbolic-error-less-than-equals-byte-string"
      (fun x => call .LessThanEqualsByteString 0 [x, bytes #[]])

  , wrongUnitCase .AppendString "symbolic-error-append-string"
      (fun x => call .AppendString 0 [x, string ""])
  , wrongUnitCase .EqualsString "symbolic-error-equals-string"
      (fun x => call .EqualsString 0 [x, string ""])
  , wrongUnitCase .EncodeUtf8 "symbolic-error-encode-utf8"
      (fun x => call .EncodeUtf8 0 [x])
  , wrongUnitCase .DecodeUtf8 "symbolic-error-decode-utf8"
      (fun x => call .DecodeUtf8 0 [x])

  , wrongUnitCase .IfThenElse "symbolic-error-if-then-else"
      (fun x => call .IfThenElse 1 [x, int 1, int 2])
  , wrongIntegerCase .ChooseUnit "symbolic-error-choose-unit"
      (fun x => call .ChooseUnit 1 [x, int 1])
  , wrongUnitCase .Trace "symbolic-error-trace"
      (fun x => call .Trace 1 [x, int 1])
  , wrongUnitCase .FstPair "symbolic-error-fst-pair"
      (fun x => call .FstPair 2 [x])
  , wrongUnitCase .SndPair "symbolic-error-snd-pair"
      (fun x => call .SndPair 2 [x])
  , wrongUnitCase .ChooseList "symbolic-error-choose-list"
      (fun x => call .ChooseList 2 [x, int 1, int 2])
  , wrongUnitCase .MkCons "symbolic-error-mk-cons"
      (fun x => call .MkCons 1 [int 1, x])
  , wrongUnitCase .HeadList "symbolic-error-head-list"
      (fun x => call .HeadList 1 [x])
  , wrongUnitCase .TailList "symbolic-error-tail-list"
      (fun x => call .TailList 1 [x])
  , wrongUnitCase .NullList "symbolic-error-null-list"
      (fun x => call .NullList 1 [x])

  , wrongUnitCase .ChooseData "symbolic-error-choose-data"
      (fun x => call .ChooseData 1 [x, int 0, int 1, int 2, int 3, int 4])
  , wrongUnitCase .ConstrData "symbolic-error-constr-data"
      (fun x => call .ConstrData 0 [x, listData []])
  , wrongUnitCase .MapData "symbolic-error-map-data"
      (fun x => call .MapData 0 [x])
  , wrongUnitCase .ListData "symbolic-error-list-data"
      (fun x => call .ListData 0 [x])
  , wrongUnitCase .IData "symbolic-error-i-data"
      (fun x => call .IData 0 [x])
  , wrongUnitCase .BData "symbolic-error-b-data"
      (fun x => call .BData 0 [x])
  , wrongUnitCase .UnConstrData "symbolic-error-un-constr-data"
      (fun x => call .UnConstrData 0 [x])
  , wrongUnitCase .UnMapData "symbolic-error-un-map-data"
      (fun x => call .UnMapData 0 [x])
  , wrongUnitCase .UnListData "symbolic-error-un-list-data"
      (fun x => call .UnListData 0 [x])
  , wrongUnitCase .UnIData "symbolic-error-un-i-data"
      (fun x => call .UnIData 0 [x])
  , wrongUnitCase .UnBData "symbolic-error-un-b-data"
      (fun x => call .UnBData 0 [x])
  , wrongUnitCase .EqualsData "symbolic-error-equals-data"
      (fun x => call .EqualsData 0 [x, data (.I 0)])
  , wrongUnitCase .MkPairData "symbolic-error-mk-pair-data"
      (fun x => call .MkPairData 0 [x, data (.I 0)])
  , wrongIntegerCase .MkNilData "symbolic-error-mk-nil-data"
      (fun x => call .MkNilData 0 [x])
  , wrongIntegerCase .MkNilPairData "symbolic-error-mk-nil-pair-data"
      (fun x => call .MkNilPairData 0 [x])

  , wrongUnitCase .DropList "symbolic-error-drop-list"
      (fun x => call .DropList 1 [x, listInteger []])
  , wrongUnitCase .IndexArray "symbolic-error-index-array"
      (fun x => call .IndexArray 1 [x, int 0])
  , wrongUnitCase .LengthOfArray "symbolic-error-length-of-array"
      (fun x => call .LengthOfArray 1 [x])
  , wrongUnitCase .ListToArray "symbolic-error-list-to-array"
      (fun x => call .ListToArray 1 [x])
  ]

/-- Declaration-backed runtime type failures for every advanced builtin. -/
def advancedSymbolicBuiltinErrorCases : List Case :=
  [ wrongUnitCase .IntegerToByteString
      "symbolic-error-integer-to-byte-string"
      (fun x => call .IntegerToByteString 0 [bool true, int 2, x])
  , wrongUnitCase .ByteStringToInteger
      "symbolic-error-byte-string-to-integer"
      (fun x => call .ByteStringToInteger 0 [x, bytes #[]])
  , wrongUnitCase .AndByteString "symbolic-error-and-byte-string"
      (fun x => call .AndByteString 0 [bool false, x, bytes #[]])
  , wrongUnitCase .OrByteString "symbolic-error-or-byte-string"
      (fun x => call .OrByteString 0 [bool false, x, bytes #[]])
  , wrongUnitCase .XorByteString "symbolic-error-xor-byte-string"
      (fun x => call .XorByteString 0 [bool false, x, bytes #[]])
  , wrongUnitCase .ComplementByteString
      "symbolic-error-complement-byte-string"
      (fun x => call .ComplementByteString 0 [x])
  , wrongUnitCase .ReadBit "symbolic-error-read-bit"
      (fun x => call .ReadBit 0 [x, int 0])
  , wrongUnitCase .WriteBits "symbolic-error-write-bits"
      (fun x => call .WriteBits 0 [x, listInteger [], bool false])
  , wrongUnitCase .ReplicateByte "symbolic-error-replicate-byte"
      (fun x => call .ReplicateByte 0 [x, int 0])
  , wrongUnitCase .ShiftByteString "symbolic-error-shift-byte-string"
      (fun x => call .ShiftByteString 0 [x, int 0])
  , wrongUnitCase .RotateByteString "symbolic-error-rotate-byte-string"
      (fun x => call .RotateByteString 0 [x, int 0])
  , wrongUnitCase .CountSetBits "symbolic-error-count-set-bits"
      (fun x => call .CountSetBits 0 [x])
  , wrongUnitCase .FindFirstSetBit "symbolic-error-find-first-set-bit"
      (fun x => call .FindFirstSetBit 0 [x])
  , wrongUnitCase .ExpModInteger "symbolic-error-exp-mod-integer"
      (fun x => call .ExpModInteger 0 [x, int 0, int 1])
  ]

/-! Declaration-backed domain failures for every partial advanced builtin.
Unlike the dynamic-type matrix above, these drive each raw SMT `_defined`
guard with correctly typed symbolic data constrained to a failing CEK value. -/
def advancedSymbolicDomainErrorCases : List Case :=
  [ constrainedIntCase .IntegerToByteString
      "symbolic-domain-error-integer-to-byte-string" 1
      (fun x => call .IntegerToByteString 0 [bool true, x, int 256]) .error
  , constrainedIntCase .ReadBit "symbolic-domain-error-read-bit" 8
      (fun x => call .ReadBit 0 [bytes #[0], x]) .error
  , constrainedIntCase .WriteBits "symbolic-domain-error-write-bits" 8
      (fun x => call .WriteBits 0
        [bytes #[0], call .MkCons 1 [x, listInteger []], bool true]) .error
  , constrainedIntCase .ReplicateByte
      "symbolic-domain-error-replicate-byte" (-1)
      (fun x => call .ReplicateByte 0 [x, int 0]) .error
  , constrainedIntCase .ExpModInteger
      "symbolic-domain-error-exp-mod-integer" (-1)
      (fun x => call .ExpModInteger 0 [int 2, x, int 4]) .error
  ]

/-- Symbolic cases exercise every first-order declaration sort, generic `Val`
selectors, constructors, and a constructor field that references another
declaration. -/
def symbolicCases : List Case :=
  [ { name := "symbolic-int-division"
      declarations := [constrainedInt]
      model := bindModel constrainedInt.name (.int (-5)) emptyModel
      term := call .DivideInteger 0 [.Var 1, int 2]
      expected := .integer (-3) }
  , { name := "symbolic-bytes-index"
      declarations := [constrainedBytes]
      model := bindModel constrainedBytes.name
        (.bytes (ByteArray.mk #[1, 255])) emptyModel
      term := call .IndexByteString 0 [.Var 1, int 1]
      expected := .integer 255 }
  , { name := "symbolic-string-encode"
      declarations := [constrainedString]
      model := bindModel constrainedString.name
        (.string (String.singleton (Char.ofNat 0x10FFFF))) emptyModel
      term := call .LengthOfByteString 0 [call .EncodeUtf8 0 [.Var 1]]
      expected := .integer 4 }
  , { name := "symbolic-data-project"
      declarations := [constrainedData]
      model := bindModel constrainedData.name (.data (.I (-12))) emptyModel
      term := call .UnIData 0 [.Var 1]
      expected := .integer (-12) }
  , { name := "symbolic-val-int"
      declarations := [constrainedValInt]
      model := bindModel constrainedValInt.name (.val (.int (-3))) emptyModel
      term := call .AddInteger 0 [.Var 1, int 5]
      expected := .integer 2 }
  , { name := "symbolic-val-list"
      declarations := [constrainedValList]
      model := bindModel constrainedValList.name
        (.val (.list [.int 2, .int 3])) emptyModel
      term := call .HeadList 1 [.Var 1]
      expected := .integer 2 }
  , { name := "symbolic-val-array"
      declarations := [constrainedValArray]
      model := bindModel constrainedValArray.name
        (.val (.array [.int 4])) emptyModel
      term := call .IndexArray 1 [.Var 1, int 0]
      expected := .integer 4 }
  , { name := "symbolic-val-constructor"
      declarations := [constrainedValConstr]
      model := bindModel constrainedValConstr.name
        (.val (.constr 0 [.int 7])) emptyModel
      term := .Case (.Var 1) [.Lam 0 (.Var 1)]
      expected := .integer 7 }
  , { name := "symbolic-val-wrong-type"
      declarations := [constrainedValWrong]
      model := bindModel constrainedValWrong.name
        (.val (.bytes (ByteArray.mk #[1]))) emptyModel
      term := call .AddInteger 0 [.Var 1, int 1]
      expected := .error }
  , { name := "symbolic-constructor-field"
      declarations := [constrainedTag, constrainedField]
      model := bindModel constrainedField.name (.int 8)
        (bindModel constrainedTag.name (.int 0) emptyModel)
      term := .Case (.Var 1) [.Lam 0 (.Var 1)]
      expected := .integer 8 }
  ]

def allCases : List Case :=
  primaryCases ++ advancedPrimaryCases ++ edgeCases ++
    advancedGroundErrorCases ++ symbolicCases ++
    symbolicBuiltinCases ++ advancedSymbolicBuiltinCases ++
    symbolicBuiltinErrorCases ++ advancedSymbolicBuiltinErrorCases ++
    advancedSymbolicDomainErrorCases

private def runCek : Nat → Moist.CEK.State → Moist.CEK.CekResult
  | _, .halt value => .success value
  | _, .error => .failure
  | 0, _ => .outOfBudget
  | fuel + 1, state => runCek fuel (Moist.CEK.step state)

private def cekMatches : Expected → Moist.CEK.CekResult → Bool
  | .integer expected, .success (.VCon (.Integer actual)) => actual == expected
  | .boolean expected, .success (.VCon (.Bool actual)) => actual == expected
  | .error, .failure => true
  | _, _ => false

private def assumptionsHold (test : Case) : Bool :=
  (test.declarations.flatMap SymDecl.assumptions).all fun assumption =>
    Moist.SMT.Semantics.evalBoolIs test.model assumption true

/-- Unlike negating `okBoolTrueCond`, this requires an active, successfully
typed Boolean result whose value is false.  Error, timeout, and non-Boolean
outcomes cannot satisfy it. -/
private def okBoolFalseCond (outcomes : List Outcome) : SExpr :=
  SExpr.any <| outcomes.filterMap fun
    | .ok pc value =>
        let boolean := asBool value
        some (SExpr.all [pc, boolean.guard, SExpr.not boolean.val])
    | _ => none

private def okBoolEqCond (outcomes : List Outcome) (expected : Bool) : SExpr :=
  if expected then okBoolTrueCond outcomes else okBoolFalseCond outcomes

private def compiledSemanticsMatch (fuel : Nat) (test : Case) : Bool :=
  let outcomes := evalSym fuel (envOf test.declarations) test.term
  let evaluatesTrue (expression : SExpr) : Bool :=
    Moist.SMT.Semantics.evalBoolIs test.model expression true
  let notTimeout := !evaluatesTrue (timeoutCond outcomes)
  match test.expected with
  | .integer expected =>
      evaluatesTrue (okIntEqCond outcomes (.int expected)) &&
        !evaluatesTrue (okIntEqCond outcomes (.int (expected + 1))) &&
        !evaluatesTrue (errorCond outcomes) && notTimeout
  | .boolean expected =>
      evaluatesTrue (okBoolEqCond outcomes expected) &&
        !evaluatesTrue (okBoolEqCond outcomes (!expected)) &&
        !evaluatesTrue (errorCond outcomes) && notTimeout
  | .error =>
      evaluatesTrue (errorCond outcomes) &&
        !evaluatesTrue (okBoolTrueCond outcomes) &&
        !evaluatesTrue (okBoolFalseCond outcomes) &&
        !evaluatesTrue (okIntEqCond outcomes (.int 0)) && notTimeout

private def firstOutputLine (output : String) : String :=
  (output.splitOn "\n").head?.getD ""

private def z3Status (testName queryName : String) (script : Script) : IO String := do
  let path : System.FilePath :=
    s!"/tmp/moist-basic-differential-{testName}-{queryName}.smt2"
  -- Production scripts request a model because satisfiable queries need one
  -- for the certified boundary.  Negative differential queries are expected
  -- to be unsatisfiable, so omit only that final request and reject every
  -- actual solver error instead of accepting Z3's "model is not available".
  let solverCommands ←
    match script.commands.reverse with
    | .getModel :: reversed => pure reversed.reverse
    | _ => throw (IO.userError
        s!"{testName}/{queryName}: production script no longer ends in get-model")
  let solverScript : Script := ⟨solverCommands⟩
  IO.FS.writeFile path solverScript.render
  let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
  let status := firstOutputLine result.stdout
  unless result.exitCode == 0 && result.stderr.isEmpty &&
      (result.stdout.splitOn "(error").length == 1 &&
      (status == "sat" || status == "unsat") do
    throw <| IO.userError
      (s!"{testName}/{queryName}: expected sat or unsat, got:\n" ++
        result.stdout ++ result.stderr)
  pure status

private def boolScript (fuel : Nat) (test : Case) : IO Script :=
  match BoolTrueQuery.compile? fuel test.declarations test.term with
  | some query => pure query.script
  | none => throw <| IO.userError s!"{test.name}: Boolean query rejected"

private def boolValueScript (fuel : Nat) (test : Case)
    (expected : Bool) : IO Script :=
  match BoolTrueQuery.compile? fuel test.declarations test.term with
  | some _ =>
      let outcomes := evalSym fuel (envOf test.declarations) test.term
      pure <| scriptWith test.declarations [okBoolEqCond outcomes expected]
  | none => throw <| IO.userError s!"{test.name}: Boolean query rejected"

private def intScript (fuel : Nat) (test : Case) (expected : Int) : IO Script :=
  match IntEqQuery.compile? fuel test.declarations test.term expected with
  | some query => pure query.script
  | none => throw <| IO.userError s!"{test.name}: integer query rejected"

private def errorScript (fuel : Nat) (test : Case) : IO Script :=
  match ErrorQuery.compile? fuel test.declarations test.term with
  | some query => pure query.script
  | none => throw <| IO.userError s!"{test.name}: error query rejected"

private def requireStatus (testName queryName expected actual : String) : IO Unit :=
  unless actual == expected do
    throw <| IO.userError
      s!"{testName}/{queryName}: expected {expected}, got {actual}"

mutual
  private def expressionMentions (name : String) : SExpr → Bool
    | .sym candidate => candidate == name
    | .app _ arguments => expressionsMention name arguments
    | .ite condition thenValue elseValue =>
        expressionMentions name condition ||
          expressionMentions name thenValue || expressionMentions name elseValue
    | .int _ | .bytes _ | .dataLit _ | .dataListLit _ |
        .dataPairListLit _ | .constListLit _ | .bool _ | .str _ => false

  private def expressionsMention (name : String) : List SExpr → Bool
    | [] => false
    | expression :: expressions =>
        expressionMentions name expression || expressionsMention name expressions
end

mutual
  private def symConstMentions (name : String) : SymConst → Bool
    | .integer value | .bytes value | .string value | .bool value |
        .data value | .dataList value | .pairDataList value | .array value |
        .g1 value | .g2 value | .ml value => expressionMentions name value
    | .constList value _ => expressionMentions name value
    | .pairData first second =>
        expressionMentions name first || expressionMentions name second
    | .unit => false

  private def symValMentions (name : String) : SymVal → Bool
    | .const value => symConstMentions name value
    | .dyn value => expressionMentions name value
    | .pair first second =>
        symValMentions name first || symValMentions name second
    | .constr tag fields =>
        expressionMentions name tag || symValsMention name fields
    | .lam _ environment | .delay _ environment =>
        symValsMention name environment
    | .builtin _ arguments _ => symValsMention name arguments

  private def symValsMention (name : String) : List SymVal → Bool
    | [] => false
    | value :: values =>
        symValMentions name value || symValsMention name values
end

private def outcomeMentions (name : String) : Outcome → Bool
  | .ok pc value => expressionMentions name pc || symValMentions name value
  | .error pc | .timeout pc => expressionMentions name pc

private def compiledCaseMentionsItsInput (fuel : Nat) (test : Case) : Bool :=
  match test.declarations with
  | [declaration] =>
      (evalSym fuel (envOf test.declarations) test.term).any
        (outcomeMentions declaration.name)
  | _ => false

private def isExactGroundOutcome (expected : Expected) : List Outcome → Bool
  | outcomes =>
      match outcomes.filter (fun outcome => outcome.pc != .bool false) with
      | [.ok (.bool true) (.const (.integer (.int actual)))] =>
          match expected with | .integer value => actual == value | _ => false
      | [.ok (.bool true) (.const (.bool (.bool actual)))] =>
          match expected with | .boolean value => actual == value | _ => false
      | [.error (.bool true)] =>
          match expected with | .error => true | _ => false
      | _ => false

/-- Post-fast-path regression hook.  After discarding only syntactically false
paths, every closed primary case must have a single literal success or literal
error, with no active residual SMT application.  `main` checks the full basic
and advanced success/error corpus before invoking either executable semantics
or Z3. -/
def exactGroundCases : List Case :=
  primaryCases ++ advancedPrimaryCases ++ edgeCases ++
    advancedGroundErrorCases

def saturatedGroundCasesAreExactLiterals (fuel : Nat := 120) : Bool :=
  exactGroundCases.all fun test =>
    isExactGroundOutcome test.expected (evalSym fuel [] test.term)

def inexactGroundCaseDetails (fuel : Nat := 120) : List String :=
  (exactGroundCases.filter fun test =>
    !isExactGroundOutcome test.expected (evalSym fuel [] test.term)).map
      (fun test => test.name ++ ": " ++ reprStr (evalSym fuel [] test.term))

private def checkZ3 (fuel : Nat) (test : Case) : IO Unit := do
  match test.expected with
  | .integer expected =>
      let good ← z3Status test.name "exact" (← intScript fuel test expected)
      requireStatus test.name "exact" "sat" good
      let wrong ← z3Status test.name "wrong" (← intScript fuel test (expected + 1))
      requireStatus test.name "wrong" "unsat" wrong
      let error ← z3Status test.name "error" (← errorScript fuel test)
      requireStatus test.name "error" "unsat" error
  | .boolean expected =>
      let exact ← z3Status test.name "bool-exact"
        (← boolValueScript fuel test expected)
      requireStatus test.name "bool-exact" "sat" exact
      let wrong ← z3Status test.name "bool-wrong"
        (← boolValueScript fuel test (!expected))
      requireStatus test.name "bool-wrong" "unsat" wrong
      let error ← z3Status test.name "error" (← errorScript fuel test)
      requireStatus test.name "error" "unsat" error
      let integer ← z3Status test.name "integer" (← intScript fuel test 0)
      requireStatus test.name "integer" "unsat" integer
  | .error =>
      let error ← z3Status test.name "error" (← errorScript fuel test)
      requireStatus test.name "error" "sat" error
      let boolean ← z3Status test.name "boolean" (← boolScript fuel test)
      requireStatus test.name "boolean" "unsat" boolean
      let booleanFalse ← z3Status test.name "boolean-false"
        (← boolValueScript fuel test false)
      requireStatus test.name "boolean-false" "unsat" booleanFalse
      let integer ← z3Status test.name "integer" (← intScript fuel test 0)
      requireStatus test.name "integer" "unsat" integer

private def checkCoverage : IO Unit := do
  let actual := primaryCases.filterMap Case.primaryBuiltin
  unless actual == basicBuiltins do
    throw <| IO.userError
      s!"basic builtin coverage changed: expected {basicBuiltins.length}, got {actual.length}"
  unless basicBuiltins.all builtinAllowedForSoundness do
    throw <| IO.userError "a basic differential builtin is no longer in the proved fragment"
  let symbolic := symbolicBuiltinCases.filterMap Case.primaryBuiltin
  unless symbolic == basicBuiltins do
    throw <| IO.userError
      s!"symbolic-success coverage changed: expected {basicBuiltins.length}, got {symbolic.length}"
  let symbolicErrors := symbolicBuiltinErrorCases.filterMap Case.primaryBuiltin
  unless symbolicErrors == basicBuiltins do
    throw <| IO.userError
      s!"symbolic-error coverage changed: expected {basicBuiltins.length}, got {symbolicErrors.length}"
  unless basicBuiltins.eraseDups.length == basicBuiltins.length do
    throw <| IO.userError "basic builtin coverage contains a duplicate"
  let advancedPrimary := advancedPrimaryCases.filterMap Case.primaryBuiltin
  unless advancedPrimary == advancedBuiltins do
    throw <| IO.userError
      s!"advanced ground-success coverage changed: expected {advancedBuiltins.length}, got {advancedPrimary.length}"
  let advancedGroundErrors :=
    advancedGroundErrorCases.filterMap Case.primaryBuiltin
  unless advancedGroundErrors == advancedBuiltins do
    throw <| IO.userError
      s!"advanced ground-error coverage changed: expected {advancedBuiltins.length}, got {advancedGroundErrors.length}"
  let advancedSymbolic :=
    advancedSymbolicBuiltinCases.filterMap Case.primaryBuiltin
  unless advancedSymbolic == advancedBuiltins do
    throw <| IO.userError
      s!"advanced symbolic-success coverage changed: expected {advancedBuiltins.length}, got {advancedSymbolic.length}"
  let advancedSymbolicErrors :=
    advancedSymbolicBuiltinErrorCases.filterMap Case.primaryBuiltin
  unless advancedSymbolicErrors == advancedBuiltins do
    throw <| IO.userError
      s!"advanced symbolic-error coverage changed: expected {advancedBuiltins.length}, got {advancedSymbolicErrors.length}"
  let advancedSymbolicDomainErrors :=
    advancedSymbolicDomainErrorCases.filterMap Case.primaryBuiltin
  unless advancedSymbolicDomainErrors == advancedPartialBuiltins do
    throw <| IO.userError
      s!"advanced symbolic domain-error coverage changed: expected {advancedPartialBuiltins.length}, got {advancedSymbolicDomainErrors.length}"
  unless advancedBuiltins.all builtinAllowedForSoundness do
    throw <| IO.userError
      "an advanced differential builtin is no longer in the proved fragment"
  unless advancedBuiltins.eraseDups.length == advancedBuiltins.length do
    throw <| IO.userError "advanced builtin coverage contains a duplicate"
  let exercisedBuiltins := basicBuiltins ++ advancedBuiltins
  let certifiedBuiltins := Test.SMT.SupportedQueries.certifiedBuiltins
  unless certifiedBuiltins.all exercisedBuiltins.contains &&
      exercisedBuiltins.all certifiedBuiltins.contains do
    throw <| IO.userError
      "ground/symbolic differential coverage is not exactly the certified builtin set"
  for test in symbolicBuiltinCases ++ symbolicBuiltinErrorCases do
    unless compiledCaseMentionsItsInput 120 test do
      throw <| IO.userError
        s!"{test.name}: compiler erased the supposedly symbolic declaration"
  for test in advancedSymbolicBuiltinCases ++ advancedSymbolicBuiltinErrorCases ++
      advancedSymbolicDomainErrorCases do
    unless compiledCaseMentionsItsInput 120 test do
      throw <| IO.userError
        s!"{test.name}: compiler erased the supposedly symbolic declaration"

private def checkCase (symbolicFuel cekFuel : Nat) (test : Case) : IO Unit := do
  unless assumptionsHold test do
    throw <| IO.userError s!"{test.name}: internal model violates an assumption"
  let some environment := symEnvToCek? test.model (envOf test.declarations)
    | throw <| IO.userError s!"{test.name}: internal model does not decode"
  let cekResult := runCek cekFuel (.compute [] environment test.term)
  unless cekMatches test.expected cekResult do
    throw <| IO.userError s!"{test.name}: unexpected CEK result {cekResult}"
  unless compiledSemanticsMatch symbolicFuel test do
    throw <| IO.userError s!"{test.name}: compiled internal semantics disagree with CEK"
  checkZ3 symbolicFuel test

unsafe def main : IO Unit := do
  checkCoverage
  unless saturatedGroundCasesAreExactLiterals 120 do
    throw <| IO.userError
      ("saturated ground builtins left residual SMT or disagreed with CEK: " ++
        String.intercalate "\n" (inexactGroundCaseDetails 120))
  for test in allCases do
    checkCase 120 10000 test
  IO.println <|
    s!"SMT/CEK differential passed: " ++
      s!"{primaryCases.length + advancedPrimaryCases.length} ground successes, " ++
      s!"{advancedGroundErrorCases.length} advanced ground errors, " ++
      s!"{symbolicBuiltinCases.length + advancedSymbolicBuiltinCases.length} symbolic successes, " ++
      s!"{symbolicBuiltinErrorCases.length + advancedSymbolicBuiltinErrorCases.length} symbolic errors, " ++
      s!"{advancedSymbolicDomainErrorCases.length} symbolic domain errors, " ++
      s!"{edgeCases.length} failures/edges, {symbolicCases.length} declaration-shape cases"

end Test.SMT.BasicBuiltinDifferential

unsafe def main : IO Unit := Test.SMT.BasicBuiltinDifferential.main
