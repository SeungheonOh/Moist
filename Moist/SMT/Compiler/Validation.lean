import Moist.SMT.UPLC

/-!
# Portable production-input validation

This module contains only executable, structural validation used before
emitting production SMT queries:

* supported-builtin scanning;
* SMT renderer atom and application checks;
* first-order expression sort checking;
* totality and CEK-decodable declaration-shape checks; and
* declaration renderer-safety and name-uniqueness checks.

It deliberately imports neither the executable SMT semantics nor any
soundness proof. Proof-carrying query wrappers and all semantic justification
of these checks remain in `Moist.SMT.Soundness.SolverInput`.

The declarations retain their established
`Moist.SMT.UPLC.Soundness` names for source compatibility. Their module and
import boundary, rather than a namespace rename, is the portable compiler
boundary.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term

/-! ## Supported builtin fragment -/

/-- The exact builtin allow-list backed by symbolic encodings and proof
dispatchers.  This is intentionally a whitelist: extending `BuiltinFun`
cannot silently make a new operation available through the portable checker
before its compiler case, semantics, and soundness proofs exist. -/
def builtinAllowedForSoundness : BuiltinFun → Bool
  | .AddInteger | .SubtractInteger | .MultiplyInteger
  | .DivideInteger | .QuotientInteger | .RemainderInteger | .ModInteger
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger
  | .AppendByteString | .ConsByteString | .SliceByteString
  | .LengthOfByteString | .IndexByteString | .EqualsByteString
  | .LessThanByteString | .LessThanEqualsByteString
  | .AppendString | .EqualsString | .EncodeUtf8 | .DecodeUtf8
  | .IfThenElse | .ChooseUnit | .Trace | .FstPair | .SndPair
  | .ChooseList | .MkCons | .HeadList | .TailList | .NullList
  | .ChooseData | .ConstrData | .MapData | .ListData | .IData | .BData
  | .UnConstrData | .UnMapData | .UnListData | .UnIData | .UnBData
  | .EqualsData | .MkPairData | .MkNilData | .MkNilPairData
  | .IntegerToByteString | .ByteStringToInteger
  | .AndByteString | .OrByteString | .XorByteString
  | .ComplementByteString | .ReadBit | .WriteBits | .ReplicateByte
  | .ShiftByteString | .RotateByteString | .CountSetBits
  | .FindFirstSetBit | .ExpModInteger
  | .DropList | .IndexArray | .LengthOfArray | .ListToArray => true
  | _ => false

def builtinOpaqueForSoundness (b : BuiltinFun) : Bool :=
  !builtinAllowedForSoundness b

mutual
  def termUsesOpaqueBuiltinForSoundness : Term → Bool
    | .Var _ => false
    | .Delay t => termUsesOpaqueBuiltinForSoundness t
    | .Lam _ body => termUsesOpaqueBuiltinForSoundness body
    | .Apply f a =>
        termUsesOpaqueBuiltinForSoundness f || termUsesOpaqueBuiltinForSoundness a
    | .Constant _ => false
    | .Force t => termUsesOpaqueBuiltinForSoundness t
    | .Error => false
    | .Builtin b => builtinOpaqueForSoundness b
    | .Constr _ fields => termsUseOpaqueBuiltinForSoundness fields
    | .Case scrut alts =>
        termUsesOpaqueBuiltinForSoundness scrut ||
          termsUseOpaqueBuiltinForSoundness alts

  def termsUseOpaqueBuiltinForSoundness : List Term → Bool
    | [] => false
    | t :: ts =>
        termUsesOpaqueBuiltinForSoundness t ||
          termsUseOpaqueBuiltinForSoundness ts
end

def termNoOpaqueBuiltinsForSoundness (t : Term) : Prop :=
  termUsesOpaqueBuiltinForSoundness t = false

mutual
  def symValNoOpaqueForSoundness : SymVal → Bool
    | .const _ => true
    | .dyn _ => true
    | .pair a b =>
        symValNoOpaqueForSoundness a && symValNoOpaqueForSoundness b
    | .constr _ fields => symValsNoOpaqueForSoundness fields
    | .lam body ρ =>
        termUsesOpaqueBuiltinForSoundness body == false &&
          symEnvNoOpaqueForSoundness ρ
    | .delay body ρ =>
        termUsesOpaqueBuiltinForSoundness body == false &&
          symEnvNoOpaqueForSoundness ρ
    | .builtin b args _ =>
        builtinAllowedForSoundness b && symValsNoOpaqueForSoundness args

  def symValsNoOpaqueForSoundness : List SymVal → Bool
    | [] => true
    | v :: vs =>
        symValNoOpaqueForSoundness v && symValsNoOpaqueForSoundness vs

  def symEnvNoOpaqueForSoundness : List SymVal → Bool
    | [] => true
    | v :: ρ =>
        symValNoOpaqueForSoundness v && symEnvNoOpaqueForSoundness ρ
end

/-! ## Renderer and first-order sort validation -/

/-! The semantic certificate is the soundness boundary, but checked production
queries should also be impossible to turn into a different SMT-LIB command
stream by embedding delimiters in public `String` fields.  Smart constructors
put declaration names in the private `$u$<code-points>` namespace; the checks
below additionally reject parentheses, comments, quoting and whitespace in
user-supplied expression atoms.  Indexed datatype testers are the only
compiler-generated application heads that are not simple symbols. -/

def sanitizedNameTailChar (c : Char) : Bool :=
  c.isDigit || c == '_'

/-- Recognize the namespace emitted by `Moist.SMT.sanitize`. -/
def declarationNameRendererSafe (name : String) : Bool :=
  name.startsWith "$u$" &&
    (name.toList.drop 3).all sanitizedNameTailChar

def simpleSymbolCharRendererSafe (c : Char) : Bool :=
  c.toNat < 128 &&
    c != '(' && c != ')' && c != '"' && c != ';' &&
    c != '|' && c != '\\' && !c.isWhitespace

def simpleSymbolRendererSafe (name : String) : Bool :=
  !name.isEmpty && name.toList.all simpleSymbolCharRendererSafe

def indexedTesterHeads : List String :=
  [ "(_ is DConstr)", "(_ is DMap)", "(_ is DList)", "(_ is DI)",
    "(_ is DB)", "(_ is DNil)", "(_ is DCons)", "(_ is DPNil)",
    "(_ is DPCons)", "(_ is VInt)", "(_ is VBytes)",
    "(_ is VString)", "(_ is VBool)", "(_ is VUnit)",
    "(_ is VList)", "(_ is VDataList)", "(_ is VPairDataList)",
    "(_ is VPair)", "(_ is VPairData)", "(_ is VData)",
    "(_ is VArray)", "(_ is VG1)", "(_ is VG2)",
    "(_ is VMlResult)", "(_ is VConstr)", "(_ is VNil)",
    "(_ is VCons)" ]

def applicationHeadRendererSafe (name : String) : Bool :=
  simpleSymbolRendererSafe name || indexedTesterHeads.contains name

def nullaryApplicationHeads : List String :=
  ["VUnit", "VNil", "DNil", "DPNil"]

/-- Atomic symbols admitted at the checked renderer boundary.

Arbitrary SMT-LIB simple symbols are not sufficient here.  Tokens such as
`true`, `false`, numerals, and nullary datatype constructors are parsed by Z3
as literals or constructors, while `Semantics.eval` would otherwise treat an
`Expr.sym` carrying the same text as a model lookup.  Compiler declarations
live in the private sanitized namespace; the remaining atoms below are the
exact fixed constants whose SMT and executable interpretations coincide. -/
def symbolAtomRendererSafe (name : String) : Bool :=
  declarationNameRendererSafe name ||
    name == "(as seq.empty Bytes)" ||
    name == "(as seq.empty UString)" ||
    name == "g1_default" ||
    name == "g2_default" ||
    name == "ml_default"

mutual
  /-- A structural expression check sufficient to prevent one AST node from
  rendering as multiple SMT-LIB terms or commands. -/
  def expressionRendererSafe : SExpr → Bool
    | .sym name => symbolAtomRendererSafe name
    | .int _ | .bytes _ | .dataLit _ | .dataListLit _
    | .dataPairListLit _ | .constListLit _ | .bool _ | .str _ => true
    | .app name [] => nullaryApplicationHeads.contains name
    | .app name arguments@(_ :: _) =>
        applicationHeadRendererSafe name && expressionsRendererSafe arguments
    | .ite condition thenBranch elseBranch =>
        expressionRendererSafe condition &&
          expressionRendererSafe thenBranch &&
          expressionRendererSafe elseBranch

def expressionsRendererSafe : List SExpr → Bool
    | [] => true
    | expression :: expressions =>
        expressionRendererSafe expression &&
          expressionsRendererSafe expressions
end

/-! ## Sort-safe declaration expressions

`Bytes` and `UString` are represented by the same underlying SMT sequence
sort for solver performance, but they are intentionally distinct in
`Semantics.SVal` and in CEK constants.  Renderer safety alone therefore cannot
justify the solver-to-executable-semantics transfer: an untyped equality could
compare a byte literal with a string literal, which Z3 identifies but the
executable semantics correctly distinguishes.  The checker below assigns the
same first-order sorts used by the executable semantics and rejects every
unknown, ill-arity, or cross-sort application in public declarations.
-/

structure ApplicationSignature where
  name : String
  arguments : List Moist.SMT.SSort
  result : Moist.SMT.SSort

def applicationSignatures : List ApplicationSignature :=
  [ ⟨"not", [.bool], .bool⟩
  , ⟨"and", [.bool, .bool], .bool⟩
  , ⟨"or", [.bool, .bool], .bool⟩
  , ⟨"+", [.int, .int], .int⟩
  , ⟨"-", [.int, .int], .int⟩
  , ⟨"*", [.int, .int], .int⟩
  , ⟨"<", [.int, .int], .bool⟩
  , ⟨"<=", [.int, .int], .bool⟩
  , ⟨">", [.int, .int], .bool⟩
  , ⟨">=", [.int, .int], .bool⟩
  , ⟨"seq.unit", [.int], .bytes⟩
  , ⟨"seq.++", [.bytes, .bytes], .bytes⟩
  , ⟨"seq.++", [.string, .string], .string⟩
  , ⟨"seq.len", [.bytes], .int⟩
  , ⟨"seq.nth", [.bytes, .int], .int⟩
  , ⟨"seq.extract", [.bytes, .int, .int], .bytes⟩
  , ⟨"uplc_encodeUtf8", [.string], .bytes⟩
  , ⟨"valid_utf8", [.bytes], .bool⟩
  , ⟨"uplc_decodeUtf8", [.bytes], .string⟩
  , ⟨"uplc_integerToByteString_defined", [.bool, .int, .int], .bool⟩
  , ⟨"uplc_integerToByteString", [.bool, .int, .int], .bytes⟩
  , ⟨"uplc_byteStringToInteger", [.bool, .bytes], .int⟩
  , ⟨"uplc_andByteString", [.bool, .bytes, .bytes], .bytes⟩
  , ⟨"uplc_orByteString", [.bool, .bytes, .bytes], .bytes⟩
  , ⟨"uplc_xorByteString", [.bool, .bytes, .bytes], .bytes⟩
  , ⟨"uplc_complementByteString", [.bytes], .bytes⟩
  , ⟨"uplc_readBit_defined", [.bytes, .int], .bool⟩
  , ⟨"uplc_readBit", [.bytes, .int], .bool⟩
  , ⟨"uplc_writeBits_defined", [.bytes, .valList, .bool], .bool⟩
  , ⟨"uplc_writeBits", [.bytes, .valList, .bool], .bytes⟩
  , ⟨"uplc_replicateByte_defined", [.int, .int], .bool⟩
  , ⟨"uplc_replicateByte", [.int, .int], .bytes⟩
  , ⟨"uplc_shiftByteString", [.bytes, .int], .bytes⟩
  , ⟨"uplc_rotateByteString", [.bytes, .int], .bytes⟩
  , ⟨"uplc_countSetBits", [.bytes], .int⟩
  , ⟨"uplc_findFirstSetBit", [.bytes], .int⟩
  , ⟨"uplc_expModInteger_defined", [.int, .int, .int], .bool⟩
  , ⟨"uplc_expModInteger", [.int, .int, .int], .int⟩
  , ⟨"same_sign", [.int, .int], .bool⟩
  , ⟨"abs_int", [.int], .int⟩
  , ⟨"uplc_tdiv", [.int, .int], .int⟩
  , ⟨"uplc_tmod", [.int, .int], .int⟩
  , ⟨"uplc_div", [.int, .int], .int⟩
  , ⟨"uplc_mod", [.int, .int], .int⟩
  , ⟨"bytes_lt", [.bytes, .bytes], .bool⟩
  , ⟨"bytes_le", [.bytes, .bytes], .bool⟩
  , ⟨"bytes_valid", [.bytes], .bool⟩
  , ⟨"ustring_valid", [.string], .bool⟩
  , ⟨"data_valid", [.data], .bool⟩
  , ⟨"dlist_valid", [.dataList], .bool⟩
  , ⟨"dplist_valid", [.dataPairList], .bool⟩
  , ⟨"val_valid", [.val], .bool⟩
  , ⟨"vlist_valid", [.valList], .bool⟩
  , ⟨"const_val_valid", [.val], .bool⟩
  , ⟨"const_vlist_valid", [.valList], .bool⟩
  , ⟨"VInt", [.int], .val⟩
  , ⟨"VBytes", [.bytes], .val⟩
  , ⟨"VString", [.string], .val⟩
  , ⟨"VBool", [.bool], .val⟩
  , ⟨"VUnit", [], .val⟩
  , ⟨"VList", [.valList], .val⟩
  , ⟨"VDataList", [.dataList], .val⟩
  , ⟨"VPairDataList", [.dataPairList], .val⟩
  , ⟨"VPair", [.val, .val], .val⟩
  , ⟨"VPairData", [.data, .data], .val⟩
  , ⟨"VData", [.data], .val⟩
  , ⟨"VArray", [.valList], .val⟩
  , ⟨"VG1", [.g1], .val⟩
  , ⟨"VG2", [.g2], .val⟩
  , ⟨"VMlResult", [.ml], .val⟩
  , ⟨"VConstr", [.int, .valList], .val⟩
  , ⟨"VNil", [], .valList⟩
  , ⟨"VCons", [.val, .valList], .valList⟩
  , ⟨"unVInt", [.val], .int⟩
  , ⟨"unVBytes", [.val], .bytes⟩
  , ⟨"unVString", [.val], .string⟩
  , ⟨"unVBool", [.val], .bool⟩
  , ⟨"unVList", [.val], .valList⟩
  , ⟨"unVDataList", [.val], .dataList⟩
  , ⟨"unVPairDataList", [.val], .dataPairList⟩
  , ⟨"vfst", [.val], .val⟩
  , ⟨"vsnd", [.val], .val⟩
  , ⟨"pdfst", [.val], .data⟩
  , ⟨"pdsnd", [.val], .data⟩
  , ⟨"unVData", [.val], .data⟩
  , ⟨"unVArray", [.val], .valList⟩
  , ⟨"vConstrTag", [.val], .int⟩
  , ⟨"vConstrFields", [.val], .valList⟩
  , ⟨"vhead", [.valList], .val⟩
  , ⟨"vtail", [.valList], .valList⟩
  , ⟨"vlist_length", [.valList], .int⟩
  , ⟨"vlist_drop", [.int, .valList], .valList⟩
  , ⟨"vlist_index", [.int, .valList], .val⟩
  , ⟨"DConstr", [.int, .dataList], .data⟩
  , ⟨"DMap", [.dataPairList], .data⟩
  , ⟨"DList", [.dataList], .data⟩
  , ⟨"DI", [.int], .data⟩
  , ⟨"DB", [.bytes], .data⟩
  , ⟨"dataConstrTag", [.data], .int⟩
  , ⟨"dataConstrFields", [.data], .dataList⟩
  , ⟨"dataMapEntries", [.data], .dataPairList⟩
  , ⟨"dataListItems", [.data], .dataList⟩
  , ⟨"dataInt", [.data], .int⟩
  , ⟨"dataBytes", [.data], .bytes⟩
  , ⟨"DNil", [], .dataList⟩
  , ⟨"DCons", [.data, .dataList], .dataList⟩
  , ⟨"dhead", [.dataList], .data⟩
  , ⟨"dtail", [.dataList], .dataList⟩
  , ⟨"dlist_length", [.dataList], .int⟩
  , ⟨"dlist_drop", [.int, .dataList], .dataList⟩
  , ⟨"DPNil", [], .dataPairList⟩
  , ⟨"DPCons", [.data, .data, .dataPairList], .dataPairList⟩
  , ⟨"dpKey", [.dataPairList], .data⟩
  , ⟨"dpValue", [.dataPairList], .data⟩
  , ⟨"dpTail", [.dataPairList], .dataPairList⟩
  ]

def testerSignature? (name : String) : Option ApplicationSignature :=
  match name with
  | "(_ is DConstr)" | "(_ is DMap)" | "(_ is DList)"
  | "(_ is DI)" | "(_ is DB)" => some ⟨name, [.data], .bool⟩
  | "(_ is DNil)" | "(_ is DCons)" => some ⟨name, [.dataList], .bool⟩
  | "(_ is DPNil)" | "(_ is DPCons)" =>
      some ⟨name, [.dataPairList], .bool⟩
  | "(_ is VNil)" | "(_ is VCons)" => some ⟨name, [.valList], .bool⟩
  | "(_ is VInt)" | "(_ is VBytes)" | "(_ is VString)"
  | "(_ is VBool)" | "(_ is VUnit)" | "(_ is VList)"
  | "(_ is VDataList)" | "(_ is VPairDataList)" | "(_ is VPair)"
  | "(_ is VPairData)" | "(_ is VData)" | "(_ is VArray)"
  | "(_ is VG1)" | "(_ is VG2)" | "(_ is VMlResult)"
  | "(_ is VConstr)" => some ⟨name, [.val], .bool⟩
  | _ => none

def applicationResultSort? (name : String)
    (arguments : List Moist.SMT.SSort) : Option Moist.SMT.SSort :=
  let candidates :=
    match testerSignature? name with
    | some signature => signature :: applicationSignatures
    | none => applicationSignatures
  (candidates.find? fun signature =>
    signature.name == name && signature.arguments == arguments).map
      ApplicationSignature.result

def declarationSort? (declarations : List SymDecl)
    (name : String) : Option Moist.SMT.SSort :=
  (declarations.find? fun declaration => declaration.name == name).map
    SymDecl.sort

mutual
  def expressionSort? (declarations : List SymDecl) : SExpr → Option Moist.SMT.SSort
    | .sym "(as seq.empty Bytes)" => some .bytes
    | .sym "(as seq.empty UString)" => some .string
    | .sym "(as seq.empty (Seq Int))" => some .bytes
    | .sym "g1_default" => some .g1
    | .sym "g2_default" => some .g2
    | .sym "ml_default" => some .ml
    | .sym name => declarationSort? declarations name
    | .int _ => some .int
    | .bytes _ => some .bytes
    | .dataLit _ => some .data
    | .dataListLit _ => some .dataList
    | .dataPairListLit _ => some .dataPairList
    | .constListLit _ => some .valList
    | .bool _ => some .bool
    | .str _ => some .string
    | .ite condition thenBranch elseBranch => do
        guard (expressionSort? declarations condition == some .bool)
        let thenSort ← expressionSort? declarations thenBranch
        let elseSort ← expressionSort? declarations elseBranch
        guard (thenSort == elseSort)
        pure thenSort
    | .app "=" [left, right] => do
        let leftSort ← expressionSort? declarations left
        let rightSort ← expressionSort? declarations right
        guard (leftSort == rightSort)
        pure .bool
    | .app name arguments => do
        let argumentSorts ← expressionSorts? declarations arguments
        applicationResultSort? name argumentSorts

  def expressionSorts? (declarations : List SymDecl) :
      List SExpr → Option (List Moist.SMT.SSort)
    | [] => some []
    | expression :: expressions => do
        let sort ← expressionSort? declarations expression
        let sorts ← expressionSorts? declarations expressions
        pure (sort :: sorts)
end

def expressionHasSort (declarations : List SymDecl)
    (expression : SExpr) (sort : Moist.SMT.SSort) : Bool :=
  expressionSort? declarations expression == some sort

/-! ## Declaration totality and input-shape validation -/

mutual
  def symConstSortSafe (declarations : List SymDecl) : SymConst → Bool
    | .integer expression => expressionHasSort declarations expression .int
    | .bytes expression => expressionHasSort declarations expression .bytes
    | .string expression => expressionHasSort declarations expression .string
    | .bool expression => expressionHasSort declarations expression .bool
    | .unit => true
    | .data expression => expressionHasSort declarations expression .data
    | .constList expression _ =>
        expressionHasSort declarations expression .valList
    | .dataList expression =>
        expressionHasSort declarations expression .dataList
    | .pairDataList expression =>
        expressionHasSort declarations expression .dataPairList
    | .pairData first second =>
        expressionHasSort declarations first .data &&
          expressionHasSort declarations second .data
    | .array expression => expressionHasSort declarations expression .valList
    | .g1 expression => expressionHasSort declarations expression .g1
    | .g2 expression => expressionHasSort declarations expression .g2
    | .ml expression => expressionHasSort declarations expression .ml

  def symValSortSafe (declarations : List SymDecl) : SymVal → Bool
    | .const constant => symConstSortSafe declarations constant
    | .dyn expression => expressionHasSort declarations expression .val
    | .pair first second =>
        symValSortSafe declarations first && symValSortSafe declarations second
    | .constr tag fields =>
        expressionHasSort declarations tag .int &&
          symValsSortSafe declarations fields
    | .lam _ environment | .delay _ environment =>
        symValsSortSafe declarations environment
    | .builtin _ arguments _ => symValsSortSafe declarations arguments

  def symValsSortSafe (declarations : List SymDecl) : List SymVal → Bool
    | [] => true
    | value :: values =>
        symValSortSafe declarations value && symValsSortSafe declarations values
end

def symDeclSortSafe (declarations : List SymDecl)
    (declaration : SymDecl) : Bool :=
  symValSortSafe declarations declaration.value &&
    declaration.assumptions.all fun assumption =>
      expressionHasSort declarations assumption .bool

def declarationsSortSafe (declarations : List SymDecl) : Bool :=
  declarations.all (symDeclSortSafe declarations)

/-! ## Total public declaration expressions

SMT datatype selectors and sequence operations are total, whereas the
executable semantics deliberately returns `none` outside the domain used by
the compiler's guarded formulas.  Public declaration fields and assumptions
must therefore use a fail-closed, always-defined fragment.  This restriction
does not inspect compiler-generated outcomes: their partial selectors are
already guarded and covered by the simulation proof.

The list below contains only operations whose executable interpretation is
total for every well-sorted argument.  In particular, raw selectors,
division, `seq.unit`, `seq.nth`, `seq.extract`, and UTF-8 decoding are absent.
The latter operations can still be exercised through UPLC builtins, where the
compiler emits and proves the required domain guards.
-/

def totalApplicationHeads : List String :=
  [ "not", "and", "or", "=", "+", "-", "*", "<", "<=", ">", ">="
  , "seq.++", "seq.len", "uplc_encodeUtf8", "valid_utf8"
  , "same_sign", "abs_int", "bytes_lt", "bytes_le"
  , "bytes_valid", "ustring_valid", "data_valid", "dlist_valid"
  , "dplist_valid", "val_valid", "vlist_valid", "const_val_valid"
  , "const_vlist_valid"
  , "VInt", "VBytes", "VString", "VBool", "VUnit", "VList"
  , "VDataList", "VPairDataList", "VPair", "VPairData", "VData"
  , "VArray", "VG1", "VG2", "VMlResult", "VConstr", "VNil", "VCons"
  , "vlist_length", "vlist_drop"
  , "DConstr", "DMap", "DList", "DI", "DB", "DNil", "DCons"
  , "dlist_length", "dlist_drop", "DPNil", "DPCons"
  ]

mutual
  /-- The total, semantics-aligned expression fragment admitted in public
  symbolic declaration values and assumptions. -/
  def expressionTotalitySafe : SExpr → Bool
    | .sym _ | .int _ | .bytes _ | .dataLit _ | .dataListLit _
    | .dataPairListLit _ | .constListLit _ | .bool _ | .str _ => true
    | .ite condition thenBranch elseBranch =>
        expressionTotalitySafe condition &&
          expressionTotalitySafe thenBranch &&
          expressionTotalitySafe elseBranch
    | .app name arguments =>
        (totalApplicationHeads.contains name ||
          indexedTesterHeads.contains name) &&
        expressionsTotalitySafe arguments

  def expressionsTotalitySafe : List SExpr → Bool
    | [] => true
    | expression :: expressions =>
        expressionTotalitySafe expression &&
          expressionsTotalitySafe expressions
end

def directValSymbol (declarations : List SymDecl) : SExpr → Bool
  | .sym name =>
      match declarationSort? declarations name with
      | some .val => true
      | _ => false
  | _ => false

def nonnegativeLiteral : SExpr → Bool
  | .int value => decide (0 ≤ value)
  | _ => false

mutual
  /-- Values embedded in a constructor declaration must not merely evaluate;
  they must also be guaranteed to decode to a CEK value. -/
  def inputSymConstSafe (_declarations : List SymDecl) : SymConst → Bool
    | .integer expression => expressionTotalitySafe expression
    | .bytes expression => expressionTotalitySafe expression
    | .string expression => expressionTotalitySafe expression
    | .bool expression => expressionTotalitySafe expression
    | .unit => true
    | .data expression => expressionTotalitySafe expression
    | .constList (.constListLit _) _ => true
    | .constList _ _ => false
    | .dataList expression => expressionTotalitySafe expression
    | .pairDataList expression => expressionTotalitySafe expression
    | .pairData first second =>
        expressionTotalitySafe first && expressionTotalitySafe second
    | .array (.constListLit _) => true
    | .array _ => false
    | .g1 (.sym "g1_default") => true
    | .g1 _ => false
    | .g2 (.sym "g2_default") => true
    | .g2 _ => false
    | .ml (.sym "ml_default") => true
    | .ml _ => false

  /-- A symbolic value guaranteed to decode specifically to `CekValue.VCon`.
  CEK pairs may contain constants only, so the broader decodable-value check
  is insufficient for their children. -/
  def inputConstSymValSafe (declarations : List SymDecl) : SymVal → Bool
    | .const constant => inputSymConstSafe declarations constant
    | .pair first second =>
        inputConstSymValSafe declarations first &&
          inputConstSymValSafe declarations second
    | _ => false

  def inputSymValSafe (declarations : List SymDecl) : SymVal → Bool
    | .const constant => inputSymConstSafe declarations constant
    | .dyn expression => directValSymbol declarations expression
    | .pair first second =>
        inputConstSymValSafe declarations first &&
          inputConstSymValSafe declarations second
    | .constr tag fields =>
        nonnegativeLiteral tag && inputSymValsSafe declarations fields
    | .lam _ environment | .delay _ environment =>
        inputSymValsSafe declarations environment
    | .builtin _ arguments _ => inputSymValsSafe declarations arguments

  def inputSymValsSafe (declarations : List SymDecl) : List SymVal → Bool
    | [] => true
    | value :: values =>
        inputSymValSafe declarations value &&
          inputSymValsSafe declarations values
end

/-- Proof-free, fail-closed syntactic equality for the mandatory-assumption
grammar emitted by `symDeclRequired?`: unary validity predicates and the
binary nonnegative-tag guard.  An unfamiliar future requirement is rejected
until this portable checker and its soundness proof are extended together. -/
def requiredAssumptionMatches : SExpr → SExpr → Bool
  | .app actualFunction [.sym actualName],
      .app expectedFunction [.sym expectedName] =>
        actualFunction == expectedFunction && actualName == expectedName
  | .app actualFunction [.sym actualName, .int actualInteger],
      .app expectedFunction [.sym expectedName, .int expectedInteger] =>
        actualFunction == expectedFunction &&
          (actualName == expectedName && actualInteger == expectedInteger)
  | _, _ => false

/-- Check the mandatory assumptions computed by the single authoritative
`symDeclRequired?` table.  `none` is rejected, and every required expression
must occur syntactically in the supplied assumption list. -/
def requiredAssumptionsPresent (name : String) (sort : Moist.SMT.SSort)
    (value : SymVal) (assumptions : List SExpr) : Bool :=
  match symDeclRequired? name sort value with
  | none => false
  | some required =>
      required.all fun expected =>
        assumptions.any fun actual => requiredAssumptionMatches actual expected

/-- Executable counterpart of the mandatory-assumption part of
`SymDecl.wellFormed`.  Keeping this check at the production boundary makes the
input contract reproducible by ports that do not carry Lean proof fields. -/
def symDeclRequiredAssumptionsPresent (declaration : SymDecl) : Bool :=
  requiredAssumptionsPresent declaration.name declaration.sort
    declaration.value declaration.assumptions

/-- Re-check the exact smart-constructor declaration shape computationally,
including every mandatory validity/nonnegativity assumption, then apply the
CEK-decodable field restriction to constructor declarations. -/
def symDeclInputSafe (declarations : List SymDecl)
    (declaration : SymDecl) : Bool :=
  let valueSafe :=
    match declaration.sort, declaration.value with
    | .int, .const (.integer (.sym name)) => name == declaration.name
    | .bool, .const (.bool (.sym name)) => name == declaration.name
    | .bytes, .const (.bytes (.sym name)) => name == declaration.name
    | .string, .const (.string (.sym name)) => name == declaration.name
    | .data, .const (.data (.sym name)) => name == declaration.name
    | .val, .dyn (.sym name) => name == declaration.name
    | .int, .constr (.sym name) fields =>
        name == declaration.name && inputSymValsSafe declarations fields
    | _, _ => false
  valueSafe &&
    (symDeclRequiredAssumptionsPresent declaration &&
      declaration.assumptions.all expressionTotalitySafe)

def declarationsInputSafe (declarations : List SymDecl) : Bool :=
  declarations.all (symDeclInputSafe declarations)

/-! ## Complete declaration renderer validation -/

/-- Z3 rejects repeated constant declarations, but may continue processing and
print a later `sat` status after the error.  Production scripts therefore
require every rendered declaration name to occur exactly once. -/
def declarationNamesDistinct : List SymDecl → Bool
  | [] => true
  | declaration :: declarations =>
      !declarations.any (fun other => other.name == declaration.name) &&
        declarationNamesDistinct declarations

def symConstRendererSafe : SymConst → Bool
  | .integer expression | .bytes expression | .string expression
  | .bool expression | .data expression | .constList expression _
  | .dataList expression | .pairDataList expression | .array expression
  | .g1 expression | .g2 expression | .ml expression =>
      expressionRendererSafe expression
  | .unit => true
  | .pairData first second =>
      expressionRendererSafe first && expressionRendererSafe second

mutual
  def symValRendererSafe : SymVal → Bool
    | .const constant => symConstRendererSafe constant
    | .dyn expression => expressionRendererSafe expression
    | .pair first second =>
        symValRendererSafe first && symValRendererSafe second
    | .constr tag fields =>
        expressionRendererSafe tag && symValsRendererSafe fields
    | .lam _ environment | .delay _ environment =>
        symValsRendererSafe environment
    | .builtin _ arguments _ => symValsRendererSafe arguments

  def symValsRendererSafe : List SymVal → Bool
    | [] => true
    | value :: values =>
        symValRendererSafe value && symValsRendererSafe values
end

def symDeclRendererSafe (declaration : SymDecl) : Bool :=
  declarationNameRendererSafe declaration.name &&
    symValRendererSafe declaration.value &&
    expressionsRendererSafe declaration.assumptions

def declarationsRendererSafe (declarations : List SymDecl) : Bool :=
  declarations.all symDeclRendererSafe

/-! ## Generated output validation -/

/-- Exact comparison for the two command forms used by the fixed raw
prelude.  Keeping this deliberately narrow means that a new raw or otherwise
unstructured command is rejected until the production boundary is reviewed. -/
def matchesFixedPreludeCommand : Moist.SMT.Command → Moist.SMT.Command → Bool
  | .raw actual, .raw expected => actual == expected
  | .declareConst actualName actualSort,
      .declareConst expectedName expectedSort =>
      actualName == expectedName && actualSort == expectedSort
  | _, _ => false

/-- A command belongs byte-for-byte (for raw text) or field-for-field (for the
opaque default declarations) to the compiler's fixed prelude. -/
def fixedPreludeCommand (command : Moist.SMT.Command) : Bool :=
  prelude.any (matchesFixedPreludeCommand command)

/-- Match a generated declaration command against the checked declaration
environment. -/
def checkedDeclarationCommand (declarations : List SymDecl)
    (name : String) (sort : Moist.SMT.SSort) : Bool :=
  declarations.any fun declaration =>
    declaration.name == name && declaration.sort == sort

/-- Structural command-stream allowlist for production output.

Expression safety and Boolean sorting are checked separately below so the
potentially large generated assertion DAG is not traversed a third time.
Every raw command must be one of the exact fixed prelude commands; every
declaration must come from the checked input (or be a fixed prelude default),
and the only admitted solver-control commands are the fixed tactic and final
model request. -/
def generatedCommandSafe (declarations : List SymDecl) :
    Moist.SMT.Command → Bool
  | command@(.raw _) => fixedPreludeCommand command
  | command@(.declareConst name sort) =>
      fixedPreludeCommand command ||
        checkedDeclarationCommand declarations name sort
  | .assert _ => true
  | .checkSatUsing tactic => tactic == z3QueryTactic
  | .getModel => true
  | _ => false

def generatedCommandsSafe (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Bool :=
  script.commands.all (generatedCommandSafe declarations)

/-- Production scripts end with exactly the fixed solver tactic followed by a
model request.  The canonical-script equality in the proof wrapper fixes the
entire order; this executable tripwire catches accidental generator changes
before a script reaches a solver. -/
def generatedSolverControlSafe (script : Moist.SMT.Script) : Bool :=
  match script.commands.reverse with
  | .getModel :: .checkSatUsing tactic :: _ => tactic == z3QueryTactic
  | _ => false

/-- Every logical assertion in a generated script renders through the
reviewed expression grammar.  This checks the typed AST before rendering. -/
def generatedAssertionsRendererSafe (script : Moist.SMT.Script) : Bool :=
  expressionsRendererSafe script.assertions

/-- Every logical assertion in a generated script has the `Bool` sort
required by SMT-LIB's `assert` command. -/
def generatedAssertionsSortSafe (declarations : List SymDecl)
    (script : Moist.SMT.Script) : Bool :=
  script.assertions.all fun expression =>
    expressionHasSort declarations expression .bool

end Moist.SMT.UPLC.Soundness
