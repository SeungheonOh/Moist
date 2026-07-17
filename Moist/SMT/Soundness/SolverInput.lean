import Moist.SMT.Soundness
import Moist.SMT.DagRender

/-!
# Checked solver inputs

This module contains the proof-carrying fragment checks used before a
production SMT query is emitted.  It deliberately contains no solver-status
or CEK endpoint: those stay in `SolverBoundary`.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekEnv)

/-! ## Checked production queries

The unrestricted `scriptFor*` functions are low-level compiler primitives:
they are useful for inspecting output, but do not by themselves certify that
the input is in the modeled fragment.  Production integrations construct one
of the query types below.  Their only checked constructors return `none` for
an opaque term or declaration environment; their direct constructors require
the corresponding kernel proof.

Declaration well-formedness alone is intentionally not used as a fragment
certificate.  In particular, `symConstr` permits arbitrary symbolic fields,
which can include higher-order values containing opaque builtins.
-/

/-- A UPLC term whose every builtin is modeled by the symbolic compiler's
soundness proof. -/
structure SupportedTerm where
  term : Term
  noOpaque : termNoOpaqueBuiltinsForSoundness term

namespace SupportedTerm

/-- Check an untrusted term before admitting it to the production query API. -/
def check (term : Term) : Option SupportedTerm :=
  if h : termUsesOpaqueBuiltinForSoundness term = false then
    some ⟨term, h⟩
  else
    none

@[simp] theorem check_isSome (term : Term) :
    (check term).isSome = !termUsesOpaqueBuiltinForSoundness term := by
  unfold check
  split <;> simp_all

end SupportedTerm

/-! The semantic certificate is the soundness boundary, but checked production
queries should also be impossible to turn into a different SMT-LIB command
stream by embedding delimiters in public `String` fields.  Smart constructors
put declaration names in the private `$u$<code-points>` namespace; the checks
below additionally reject parentheses, comments, quoting and whitespace in
user-supplied expression atoms.  Indexed datatype testers are the only
compiler-generated application heads that are not simple symbols. -/

private def sanitizedNameTailChar (c : Char) : Bool :=
  c.isDigit || c == '_'

/-- Recognize the namespace emitted by `Moist.SMT.sanitize`. -/
def declarationNameRendererSafe (name : String) : Bool :=
  name.startsWith "$u$" &&
    (name.toList.drop 3).all sanitizedNameTailChar

private def simpleSymbolCharRendererSafe (c : Char) : Bool :=
  c.toNat < 128 &&
    c != '(' && c != ')' && c != '"' && c != ';' &&
    c != '|' && c != '\\' && !c.isWhitespace

private def simpleSymbolRendererSafe (name : String) : Bool :=
  !name.isEmpty && name.toList.all simpleSymbolCharRendererSafe

private def indexedTesterHeads : List String :=
  [ "(_ is DConstr)", "(_ is DMap)", "(_ is DList)", "(_ is DI)",
    "(_ is DB)", "(_ is DNil)", "(_ is DCons)", "(_ is DPNil)",
    "(_ is DPCons)", "(_ is VInt)", "(_ is VBytes)",
    "(_ is VString)", "(_ is VBool)", "(_ is VUnit)",
    "(_ is VList)", "(_ is VDataList)", "(_ is VPairDataList)",
    "(_ is VPair)", "(_ is VPairData)", "(_ is VData)",
    "(_ is VArray)", "(_ is VG1)", "(_ is VG2)",
    "(_ is VMlResult)", "(_ is VConstr)", "(_ is VNil)",
    "(_ is VCons)" ]

private def applicationHeadRendererSafe (name : String) : Bool :=
  simpleSymbolRendererSafe name || indexedTesterHeads.contains name

private def nullaryApplicationHeads : List String :=
  ["VUnit", "VNil", "DNil", "DPNil"]

/-- Atomic symbols admitted at the checked renderer boundary.

Arbitrary SMT-LIB simple symbols are not sufficient here.  Tokens such as
`true`, `false`, numerals, and nullary datatype constructors are parsed by Z3
as literals or constructors, while `Semantics.eval` would otherwise treat an
`Expr.sym` carrying the same text as a model lookup.  Compiler declarations
live in the private sanitized namespace; the remaining atoms below are the
exact fixed constants whose SMT and executable interpretations coincide. -/
private def symbolAtomRendererSafe (name : String) : Bool :=
  declarationNameRendererSafe name ||
    name == "(as seq.empty Bytes)" ||
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

private structure ApplicationSignature where
  name : String
  arguments : List Moist.SMT.SSort
  result : Moist.SMT.SSort

private def applicationSignatures : List ApplicationSignature :=
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

private def testerSignature? (name : String) : Option ApplicationSignature :=
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

private def applicationResultSort? (name : String)
    (arguments : List Moist.SMT.SSort) : Option Moist.SMT.SSort :=
  let candidates :=
    match testerSignature? name with
    | some signature => signature :: applicationSignatures
    | none => applicationSignatures
  (candidates.find? fun signature =>
    signature.name == name && signature.arguments == arguments).map
      ApplicationSignature.result

private def declarationSort? (declarations : List SymDecl)
    (name : String) : Option Moist.SMT.SSort :=
  (declarations.find? fun declaration => declaration.name == name).map
    SymDecl.sort

mutual
  def expressionSort? (declarations : List SymDecl) : SExpr → Option Moist.SMT.SSort
    | .sym "(as seq.empty Bytes)" => some .bytes
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

private def totalApplicationHeads : List String :=
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

private def directValSymbol (declarations : List SymDecl) : SExpr → Bool
  | .sym name => declarationSort? declarations name == some .val
  | _ => false

private def nonnegativeLiteral : SExpr → Bool
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

/-- Re-check the exact smart-constructor declaration shape computationally,
then apply the CEK-decodable field restriction to constructor declarations. -/
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
    declaration.assumptions.all expressionTotalitySafe

def declarationsInputSafe (declarations : List SymDecl) : Bool :=
  declarations.all (symDeclInputSafe declarations)

/-! ## Checked-input decoding

The checker above is syntactic.  The two premises below are the precise
semantic facts a solver/model integration must establish for its decoded
internal model:

* every admitted, well-sorted total expression evaluates to a value of that
  sort; and
* a direct symbolic `Val` satisfies the generated validity assumption and
  therefore decodes to a CEK value.

These premises deliberately stop at the user-accepted SMT-LIB/Z3 bridge.  The
theorems following them prove, in the kernel, that the recursive declaration
grammar adds no further decoding assumption.
-/

/-- Runtime sort evidence for the executable SMT semantics. -/
inductive SValHasSort : SmtSem.SVal → Moist.SMT.SSort → Prop where
  | boolVal (value : Bool) : SValHasSort (.bool value) .bool
  | intVal (value : Int) : SValHasSort (.int value) .int
  | stringVal (value : String) : SValHasSort (.string value) .string
  | bytesVal (value : ByteArray) : SValHasSort (.bytes value) .bytes
  | dataVal (value : Moist.Plutus.Data) : SValHasSort (.data value) .data
  | dataListVal (value : List Moist.Plutus.Data) :
      SValHasSort (.dataList value) .dataList
  | dataPairListVal (value : List (Moist.Plutus.Data × Moist.Plutus.Data)) :
      SValHasSort (.dataPairList value) .dataPairList
  | valVal (value : SmtSem.Val) : SValHasSort (.val value) .val
  | valListVal (value : List SmtSem.Val) :
      SValHasSort (.valList value) .valList
  | g1Val (value : String) : SValHasSort (.g1 value) .g1
  | g2Val (value : String) : SValHasSort (.g2 value) .g2
  | mlVal (value : String) : SValHasSort (.ml value) .ml

/-- Explicit model-typing and validity premises at the accepted solver bridge.

`expressionEvaluates` says the model interpretation respects the semantic sort
checker on the total public-expression fragment.  `directValDecodes` is the
semantic content of the mandatory `val_valid` assertion attached by `symVal`.
-/
structure SolverInputModel (declarations : List SymDecl)
    (model : SmtSem.Model) : Prop where
  expressionEvaluates : ∀ expression sort,
    expressionTotalitySafe expression = true →
    expressionHasSort declarations expression sort = true →
    ∃ value, SmtSem.eval model expression = some value ∧
      SValHasSort value sort
  directValDecodes : ∀ expression,
    inputSymValSafe declarations (.dyn expression) = true →
    ∃ value, symValToCek? model (.dyn expression) = some value

/-- Every checked symbolic constant decodes specifically to a CEK constant. -/
theorem inputSymConstSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) (constant : SymConst)
    (hsafe : inputSymConstSafe declarations constant = true)
    (hsort : symConstSortSafe declarations constant = true) :
    ∃ value, symConstToCek? model constant = some (.VCon value) := by
  cases constant with
  | integer expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .int (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | intVal value =>
          exact ⟨.Integer value, by simp [symConstToCek?, heval]⟩
  | bytes expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .bytes (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | bytesVal value =>
          exact ⟨.ByteString value, by simp [symConstToCek?, heval]⟩
  | string expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .string (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | stringVal value =>
          exact ⟨.String value, by simp [symConstToCek?, heval]⟩
  | bool expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .bool (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | boolVal value =>
          exact ⟨.Bool value, by simp [symConstToCek?, heval]⟩
  | unit => exact ⟨.Unit, rfl⟩
  | data expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .data (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | dataVal value =>
          exact ⟨.Data value, by simp [symConstToCek?, heval]⟩
  | constList expression hint =>
      cases expression <;> simp [inputSymConstSafe] at hsafe
      case constListLit values =>
        exact ⟨.ConstList values, by
          simp [symConstToCek?, Moist.SMT.Semantics.eval,
            semValListToConstList_constListToVals]⟩
  | dataList expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .dataList (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | dataListVal value =>
          exact ⟨.ConstDataList value, by simp [symConstToCek?, heval]⟩
  | pairDataList expression =>
      obtain ⟨value, heval, hvalue⟩ := bridge.expressionEvaluates
        expression .dataPairList (by simpa [inputSymConstSafe] using hsafe)
        (by simpa [symConstSortSafe] using hsort)
      cases hvalue with
      | dataPairListVal value =>
          exact ⟨.ConstPairDataList value, by simp [symConstToCek?, heval]⟩
  | pairData first second =>
      simp [inputSymConstSafe] at hsafe
      simp [symConstSortSafe] at hsort
      obtain ⟨firstValue, hfirst, hfirstValue⟩ :=
        bridge.expressionEvaluates first .data hsafe.1 hsort.1
      obtain ⟨secondValue, hsecond, hsecondValue⟩ :=
        bridge.expressionEvaluates second .data hsafe.2 hsort.2
      cases hfirstValue with
      | dataVal firstValue =>
          cases hsecondValue with
          | dataVal secondValue =>
              exact ⟨.PairData (firstValue, secondValue), by
                simp [symConstToCek?, hfirst, hsecond]⟩
  | array expression =>
      cases expression <;> simp [inputSymConstSafe] at hsafe
      case constListLit values =>
        exact ⟨.ConstArray values, by
          simp [symConstToCek?, Moist.SMT.Semantics.eval,
            semValListToConstList_constListToVals]⟩
  | g1 expression =>
      cases expression with
      | sym name =>
          by_cases hname : name = "g1_default"
          · subst name
            exact ⟨.Bls12_381_G1_element, by
              simp [symConstToCek?, Moist.SMT.Semantics.eval]⟩
          · simp [inputSymConstSafe, hname] at hsafe
      | _ => simp [inputSymConstSafe] at hsafe
  | g2 expression =>
      cases expression with
      | sym name =>
          by_cases hname : name = "g2_default"
          · subst name
            exact ⟨.Bls12_381_G2_element, by
              simp [symConstToCek?, Moist.SMT.Semantics.eval]⟩
          · simp [inputSymConstSafe, hname] at hsafe
      | _ => simp [inputSymConstSafe] at hsafe
  | ml expression =>
      cases expression with
      | sym name =>
          by_cases hname : name = "ml_default"
          · subst name
            exact ⟨.Bls12_381_MlResult, by
              simp [symConstToCek?, Moist.SMT.Semantics.eval]⟩
          · simp [inputSymConstSafe, hname] at hsafe
      | _ => simp [inputSymConstSafe] at hsafe

private def InputValueDecodeProperty (declarations : List SymDecl)
    (model : SmtSem.Model) (value : SymVal) : Prop :=
  (inputSymValSafe declarations value = true →
    symValSortSafe declarations value = true →
    ∃ decoded, symValToCek? model value = some decoded) ∧
  (inputConstSymValSafe declarations value = true →
    symValSortSafe declarations value = true →
    ∃ constant, symValToCek? model value = some (.VCon constant))

private def InputValuesDecodeProperty (declarations : List SymDecl)
    (model : SmtSem.Model) (values : List SymVal) : Prop :=
  inputSymValsSafe declarations values = true →
  symValsSortSafe declarations values = true →
    (∃ decoded, symValListToCekList? model values = some decoded) ∧
    (∃ environment, symEnvToCek? model values = some environment)

/-- The nested `SymVal` recursor proves value, constant-value, list and
environment decoding together.  Keeping this bundled prevents a hidden
assumption at closures, constructor fields, or partial-builtin arguments. -/
private theorem inputValueDecodeProperties
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) (value : SymVal) :
    InputValueDecodeProperty declarations model value := by
  exact SymVal.rec
    (motive_1 := InputValueDecodeProperty declarations model)
    (motive_2 := InputValuesDecodeProperty declarations model)
    (fun constant => by
      constructor
      · intro hsafe hsort
        obtain ⟨decoded, hdecoded⟩ := inputSymConstSafe_decodes
          bridge constant (by simpa [inputSymValSafe] using hsafe)
          (by simpa [symValSortSafe] using hsort)
        exact ⟨.VCon decoded, by simpa [symValToCek?] using hdecoded⟩
      · intro hsafe hsort
        obtain ⟨decoded, hdecoded⟩ := inputSymConstSafe_decodes
          bridge constant (by simpa [inputConstSymValSafe] using hsafe)
          (by simpa [symValSortSafe] using hsort)
        exact ⟨decoded, by simpa [symValToCek?] using hdecoded⟩)
    (fun expression => by
      constructor
      · intro hsafe _hsort
        exact bridge.directValDecodes expression hsafe
      · intro hsafe _hsort
        simp [inputConstSymValSafe] at hsafe)
    (fun first second firstIH secondIH => by
      constructor
      · intro hsafe hsort
        simp [inputSymValSafe] at hsafe
        simp [symValSortSafe] at hsort
        obtain ⟨firstValue, hfirst⟩ := firstIH.2 hsafe.1 hsort.1
        obtain ⟨secondValue, hsecond⟩ := secondIH.2 hsafe.2 hsort.2
        exact ⟨.VCon (.Pair (firstValue, secondValue)), by
          simp [symValToCek?, hfirst, hsecond]⟩
      · intro hsafe hsort
        simp [inputConstSymValSafe] at hsafe
        simp [symValSortSafe] at hsort
        obtain ⟨firstValue, hfirst⟩ := firstIH.2 hsafe.1 hsort.1
        obtain ⟨secondValue, hsecond⟩ := secondIH.2 hsafe.2 hsort.2
        exact ⟨.Pair (firstValue, secondValue), by
          simp [symValToCek?, hfirst, hsecond]⟩)
    (fun tag fields fieldsIH => by
      constructor
      · intro hsafe hsort
        simp [inputSymValSafe] at hsafe
        simp [symValSortSafe] at hsort
        cases tag with
        | int tag =>
            have hnonnegative : 0 ≤ tag := by
              simpa [nonnegativeLiteral] using hsafe.1
            have hnotnegative : ¬ tag < 0 := by omega
            obtain ⟨decoded, hdecoded⟩ := (fieldsIH hsafe.2 hsort.2).1
            exact ⟨.VConstr tag.toNat decoded, by
              simp [symValToCek?, Moist.SMT.Semantics.eval,
                hdecoded, hnotnegative]⟩
        | _ => simp [nonnegativeLiteral] at hsafe
      · intro hsafe _hsort
        simp [inputConstSymValSafe] at hsafe)
    (fun body environment environmentIH => by
      constructor
      · intro hsafe hsort
        simp [inputSymValSafe] at hsafe
        simp [symValSortSafe] at hsort
        obtain ⟨decoded, hdecoded⟩ := (environmentIH hsafe hsort).2
        exact ⟨.VLam body decoded, by simp [symValToCek?, hdecoded]⟩
      · intro hsafe _hsort
        simp [inputConstSymValSafe] at hsafe)
    (fun body environment environmentIH => by
      constructor
      · intro hsafe hsort
        simp [inputSymValSafe] at hsafe
        simp [symValSortSafe] at hsort
        obtain ⟨decoded, hdecoded⟩ := (environmentIH hsafe hsort).2
        exact ⟨.VDelay body decoded, by simp [symValToCek?, hdecoded]⟩
      · intro hsafe _hsort
        simp [inputConstSymValSafe] at hsafe)
    (fun builtin arguments expected argumentsIH => by
      constructor
      · intro hsafe hsort
        simp [inputSymValSafe] at hsafe
        simp [symValSortSafe] at hsort
        obtain ⟨decoded, hdecoded⟩ := (argumentsIH hsafe hsort).1
        exact ⟨.VBuiltin builtin decoded expected, by
          simp [symValToCek?, hdecoded]⟩
      · intro hsafe _hsort
        simp [inputConstSymValSafe] at hsafe)
    (by
      intro _hsafe _hsort
      exact ⟨⟨[], rfl⟩, ⟨.nil, rfl⟩⟩)
    (fun head tail headIH tailIH => by
      intro hsafe hsort
      simp [inputSymValsSafe] at hsafe
      simp [symValsSortSafe] at hsort
      obtain ⟨headValue, hhead⟩ := headIH.1 hsafe.1 hsort.1
      obtain ⟨⟨tailValues, htailValues⟩, ⟨tailEnv, htailEnv⟩⟩ :=
        tailIH hsafe.2 hsort.2
      constructor
      · exact ⟨headValue :: tailValues, by
          simp [symValListToCekList?, hhead, htailValues]⟩
      · exact ⟨.cons headValue tailEnv, by
          simp [symEnvToCek?, hhead, htailEnv]⟩)
    value

/-- A checked value decodes to some CEK runtime value. -/
theorem inputSymValSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) (value : SymVal)
    (hsafe : inputSymValSafe declarations value = true)
    (hsort : symValSortSafe declarations value = true) :
    ∃ decoded, symValToCek? model value = some decoded :=
  (inputValueDecodeProperties bridge value).1 hsafe hsort

/-- A checked constant-shaped symbolic value decodes specifically to `VCon`. -/
theorem inputConstSymValSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) (value : SymVal)
    (hsafe : inputConstSymValSafe declarations value = true)
    (hsort : symValSortSafe declarations value = true) :
    ∃ constant, symValToCek? model value = some (.VCon constant) :=
  (inputValueDecodeProperties bridge value).2 hsafe hsort

/-- Checked value lists compose through the ordinary list decoder. -/
theorem inputSymValsSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) : ∀ values,
    inputSymValsSafe declarations values = true →
    symValsSortSafe declarations values = true →
    ∃ decoded, symValListToCekList? model values = some decoded
  | [], _, _ => ⟨[], rfl⟩
  | head :: tail, hsafe, hsort => by
      simp [inputSymValsSafe] at hsafe
      simp [symValsSortSafe] at hsort
      obtain ⟨headValue, hhead⟩ := inputSymValSafe_decodes
        bridge head hsafe.1 hsort.1
      obtain ⟨tailValues, htail⟩ := inputSymValsSafe_decodes
        bridge tail hsafe.2 hsort.2
      exact ⟨headValue :: tailValues, by
        simp [symValListToCekList?, hhead, htail]⟩

/-- The same checked list composes as a CEK environment. -/
theorem inputSymEnvSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) : ∀ values,
    inputSymValsSafe declarations values = true →
    symValsSortSafe declarations values = true →
    ∃ environment, symEnvToCek? model values = some environment
  | [], _, _ => ⟨.nil, rfl⟩
  | head :: tail, hsafe, hsort => by
      simp [inputSymValsSafe] at hsafe
      simp [symValsSortSafe] at hsort
      obtain ⟨headValue, hhead⟩ := inputSymValSafe_decodes
        bridge head hsafe.1 hsort.1
      obtain ⟨tailEnv, htail⟩ := inputSymEnvSafe_decodes
        bridge tail hsafe.2 hsort.2
      exact ⟨.cons headValue tailEnv, by
        simp [symEnvToCek?, hhead, htail]⟩

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

/-- Symbolic declarations whose decoded environment cannot contain an opaque
closure, delay, or partial builtin and whose public string fields render as a
single SMT-LIB syntax tree. -/
structure SupportedDeclarations where
  declarations : List SymDecl
  noOpaque :
    symEnvNoOpaqueForSoundness (envOf declarations) = true
  rendererSafe :
    declarationsRendererSafe declarations = true
  sortSafe :
    declarationsSortSafe declarations = true
  inputSafe :
    declarationsInputSafe declarations = true
  namesDistinct :
    declarationNamesDistinct declarations = true

namespace SupportedDeclarations

/-- Check declaration values before admitting them to a production query. -/
def check (declarations : List SymDecl) : Option SupportedDeclarations :=
  if hOpaque : symEnvNoOpaqueForSoundness (envOf declarations) = true then
    if hRenderer : declarationsRendererSafe declarations = true then
      if hSort : declarationsSortSafe declarations = true then
        if hInput : declarationsInputSafe declarations = true then
          if hDistinct : declarationNamesDistinct declarations = true then
            some ⟨declarations, hOpaque, hRenderer, hSort, hInput, hDistinct⟩
          else none
        else none
      else none
    else none
  else none

@[simp] theorem check_isSome (declarations : List SymDecl) :
    (check declarations).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations) := by
  by_cases hOpaque :
      symEnvNoOpaqueForSoundness (envOf declarations) = true <;>
    by_cases hRenderer : declarationsRendererSafe declarations = true <;>
    by_cases hSort : declarationsSortSafe declarations = true <;>
    by_cases hInput : declarationsInputSafe declarations = true <;>
    by_cases hDistinct : declarationNamesDistinct declarations = true <;>
    simp_all [check]

end SupportedDeclarations


end Moist.SMT.UPLC.Soundness
