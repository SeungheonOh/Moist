import Moist.SMT.Soundness.SolverBoundary

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

def allCases : List Case := primaryCases ++ edgeCases ++ symbolicCases

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
      (evaluatesTrue (okBoolTrueCond outcomes) == expected) &&
        !evaluatesTrue (errorCond outcomes) && notTimeout
  | .error =>
      evaluatesTrue (errorCond outcomes) &&
        !evaluatesTrue (okBoolTrueCond outcomes) &&
        !evaluatesTrue (okIntEqCond outcomes (.int 0)) && notTimeout

private def firstOutputLine (output : String) : String :=
  (output.splitOn "\n").head?.getD ""

private def z3Status (testName queryName : String) (script : Script) : IO String := do
  let path : System.FilePath :=
    s!"/tmp/moist-basic-differential-{testName}-{queryName}.smt2"
  IO.FS.writeFile path script.render
  let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
  let status := firstOutputLine result.stdout
  unless status == "sat" || status == "unsat" do
    throw <| IO.userError
      (s!"{testName}/{queryName}: expected sat or unsat, got:\n" ++
        result.stdout ++ result.stderr)
  pure status

private def boolScript (fuel : Nat) (test : Case) : IO Script :=
  match BoolTrueQuery.compile? fuel test.declarations test.term with
  | some query => pure query.script
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
      let value ← z3Status test.name "bool-true" (← boolScript fuel test)
      requireStatus test.name "bool-true" (if expected then "sat" else "unsat") value
      let error ← z3Status test.name "error" (← errorScript fuel test)
      requireStatus test.name "error" "unsat" error
      let integer ← z3Status test.name "integer" (← intScript fuel test 0)
      requireStatus test.name "integer" "unsat" integer
  | .error =>
      let error ← z3Status test.name "error" (← errorScript fuel test)
      requireStatus test.name "error" "sat" error
      let boolean ← z3Status test.name "boolean" (← boolScript fuel test)
      requireStatus test.name "boolean" "unsat" boolean
      let integer ← z3Status test.name "integer" (← intScript fuel test 0)
      requireStatus test.name "integer" "unsat" integer

private def checkCoverage : IO Unit := do
  let actual := primaryCases.filterMap Case.primaryBuiltin
  unless actual == basicBuiltins do
    throw <| IO.userError
      s!"basic builtin coverage changed: expected {basicBuiltins.length}, got {actual.length}"
  unless basicBuiltins.all builtinAllowedForSoundness do
    throw <| IO.userError "a basic differential builtin is no longer in the proved fragment"

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
  for test in allCases do
    checkCase 120 10000 test
  IO.println <|
    s!"basic SMT/CEK differential passed: {primaryCases.length} builtins, " ++
      s!"{edgeCases.length} failures/edges, {symbolicCases.length} symbolic cases"

end Test.SMT.BasicBuiltinDifferential

unsafe def main : IO Unit := Test.SMT.BasicBuiltinDifferential.main
