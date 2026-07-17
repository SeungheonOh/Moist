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

/- `SSort`'s generated `BEq` is structurally lawful.  This proof-only local
instance is intentionally introduced after the executable checker definitions,
and is not exported as part of the public typeclass API. -/
local instance : LawfulBEq Moist.SMT.SSort where
  eq_of_beq {a b} h := by
    change Moist.SMT.instBEqSSort.beq a b = true at h
    cases a <;> cases b <;>
      simp_all [Moist.SMT.instBEqSSort.beq]
  rfl {a} := by
    change Moist.SMT.instBEqSSort.beq a a = true
    cases a <;> simp [Moist.SMT.instBEqSSort.beq]

theorem expressionHasSort_eq_true_iff
    (declarations : List SymDecl) (expression : SExpr)
    (sort : Moist.SMT.SSort) :
    expressionHasSort declarations expression sort = true ↔
      expressionSort? declarations expression = some sort := by
  simp [expressionHasSort]

private theorem expressionSort_app_of_ne_eq
    (declarations : List SymDecl) (name : String) (arguments : List SExpr)
    (hname : name ≠ "=") :
    expressionSort? declarations (.app name arguments) = (do
      let argumentSorts ← expressionSorts? declarations arguments
      applicationResultSort? name argumentSorts) := by
  rw [expressionSort?.eq_def]
  simp [hname]

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
  | .sym name =>
      match declarationSort? declarations name with
      | some .val => true
      | _ => false
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

The checker above is syntactic.  A solver/model integration only has to
establish the interpretation and runtime sort of each symbol declared in the
query.  The theorems below lift that narrow premise, in the kernel, through
every literal, conditional, and total well-sorted application admitted by the
public declaration grammar.  A direct symbolic `Val` then decodes from the
generated validity assertion, so the recursive declaration grammar adds no
further model-typing or decoding assumption.
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

/-- Pointwise evidence that a list of declaration expressions evaluates with
the sorts assigned by the checked expression grammar. -/
inductive ExpressionsEvaluateWithSorts (model : SmtSem.Model) :
    List SExpr → List Moist.SMT.SSort → Prop where
  | nil : ExpressionsEvaluateWithSorts model [] []
  | cons {expression expressions sort sorts value}
      (evaluates : SmtSem.eval model expression = some value)
      (hasSort : SValHasSort value sort)
      (tail : ExpressionsEvaluateWithSorts model expressions sorts) :
      ExpressionsEvaluateWithSorts model
        (expression :: expressions) (sort :: sorts)

private theorem evaluatedArguments0
    {model : SmtSem.Model} {arguments : List SExpr}
    (harguments : ExpressionsEvaluateWithSorts model arguments []) :
    arguments = [] := by
  cases harguments
  rfl

private theorem evaluatedArguments1
    {model : SmtSem.Model} {arguments : List SExpr}
    {sort : Moist.SMT.SSort}
    (harguments : ExpressionsEvaluateWithSorts model arguments [sort]) :
    ∃ expression value, arguments = [expression] ∧
      SmtSem.eval model expression = some value ∧
        SValHasSort value sort := by
  cases harguments with
  | cons heval hvalue tail =>
      cases tail
      exact ⟨_, _, rfl, heval, hvalue⟩

private theorem evaluatedArguments2
    {model : SmtSem.Model} {arguments : List SExpr}
    {firstSort secondSort : Moist.SMT.SSort}
    (harguments : ExpressionsEvaluateWithSorts model arguments
      [firstSort, secondSort]) :
    ∃ first second firstValue secondValue,
      arguments = [first, second] ∧
      SmtSem.eval model first = some firstValue ∧
      SValHasSort firstValue firstSort ∧
      SmtSem.eval model second = some secondValue ∧
      SValHasSort secondValue secondSort := by
  cases harguments with
  | cons hfirst hfirstValue tail =>
      cases tail with
      | cons hsecond hsecondValue tail =>
          cases tail
          exact ⟨_, _, _, _, rfl, hfirst, hfirstValue,
            hsecond, hsecondValue⟩

private theorem evaluatedArguments3
    {model : SmtSem.Model} {arguments : List SExpr}
    {firstSort secondSort thirdSort : Moist.SMT.SSort}
    (harguments : ExpressionsEvaluateWithSorts model arguments
      [firstSort, secondSort, thirdSort]) :
    ∃ first second third firstValue secondValue thirdValue,
      arguments = [first, second, third] ∧
      SmtSem.eval model first = some firstValue ∧
      SValHasSort firstValue firstSort ∧
      SmtSem.eval model second = some secondValue ∧
      SValHasSort secondValue secondSort ∧
      SmtSem.eval model third = some thirdValue ∧
      SValHasSort thirdValue thirdSort := by
  cases harguments with
  | cons hfirst hfirstValue tail =>
      cases tail with
      | cons hsecond hsecondValue tail =>
          cases tail with
          | cons hthird hthirdValue tail =>
              cases tail
              exact ⟨_, _, _, _, _, _, rfl, hfirst, hfirstValue,
                hsecond, hsecondValue, hthird, hthirdValue⟩

/- Reduction equations are enabled only for this exhaustiveness proof.  Each
is a theorem about the single production `Semantics.evalApp` dispatcher. -/
attribute [local simp]
  Moist.SMT.Semantics.evalApp_add
  Moist.SMT.Semantics.evalApp_sub
  Moist.SMT.Semantics.evalApp_mul
  Moist.SMT.Semantics.evalApp_lt
  Moist.SMT.Semantics.evalApp_le
  Moist.SMT.Semantics.evalApp_total_gt
  Moist.SMT.Semantics.evalApp_ge
  Moist.SMT.Semantics.evalApp_seqAppend
  Moist.SMT.Semantics.evalApp_strAppend
  Moist.SMT.Semantics.evalApp_seqLen
  Moist.SMT.Semantics.evalApp_uplcEncodeUtf8
  Moist.SMT.Semantics.evalApp_validUtf8
  Moist.SMT.Semantics.evalApp_total_sameSign
  Moist.SMT.Semantics.evalApp_total_abs
  Moist.SMT.Semantics.evalApp_bytesLt
  Moist.SMT.Semantics.evalApp_bytesLe
  Moist.SMT.Semantics.evalApp_total_bytesValid
  Moist.SMT.Semantics.evalApp_total_stringValid
  Moist.SMT.Semantics.evalApp_total_dataValid
  Moist.SMT.Semantics.evalApp_total_dataListValid
  Moist.SMT.Semantics.evalApp_total_dataPairListValid
  Moist.SMT.Semantics.evalApp_val_valid
  Moist.SMT.Semantics.evalApp_total_valListValid
  Moist.SMT.Semantics.evalApp_total_constValValid
  Moist.SMT.Semantics.evalApp_total_constValListValid
  Moist.SMT.Semantics.evalApp_total_VInt
  Moist.SMT.Semantics.evalApp_total_VBytes
  Moist.SMT.Semantics.evalApp_total_VString
  Moist.SMT.Semantics.evalApp_total_VBool
  Moist.SMT.Semantics.evalApp_total_VUnit
  Moist.SMT.Semantics.evalApp_total_VList
  Moist.SMT.Semantics.evalApp_total_VDataList
  Moist.SMT.Semantics.evalApp_total_VPairDataList
  Moist.SMT.Semantics.evalApp_total_VPair
  Moist.SMT.Semantics.evalApp_total_VPairData
  Moist.SMT.Semantics.evalApp_total_VData
  Moist.SMT.Semantics.evalApp_total_VArray
  Moist.SMT.Semantics.evalApp_total_VG1
  Moist.SMT.Semantics.evalApp_total_VG2
  Moist.SMT.Semantics.evalApp_total_VMlResult
  Moist.SMT.Semantics.evalApp_total_VConstr
  Moist.SMT.Semantics.evalApp_total_VNil
  Moist.SMT.Semantics.evalApp_total_VCons
  Moist.SMT.Semantics.evalApp_total_vlistLength
  Moist.SMT.Semantics.evalApp_total_vlistDrop
  Moist.SMT.Semantics.evalApp_total_DConstr
  Moist.SMT.Semantics.evalApp_total_DMap
  Moist.SMT.Semantics.evalApp_total_DList
  Moist.SMT.Semantics.evalApp_total_DI
  Moist.SMT.Semantics.evalApp_total_DB
  Moist.SMT.Semantics.evalApp_total_DNil
  Moist.SMT.Semantics.evalApp_total_DCons
  Moist.SMT.Semantics.evalApp_total_dlistLength
  Moist.SMT.Semantics.evalApp_total_dlistDrop
  Moist.SMT.Semantics.evalApp_total_DPNil
  Moist.SMT.Semantics.evalApp_total_DPCons

private theorem tableApplication_evaluates_first
    {model : SmtSem.Model} {signature : ApplicationSignature}
    {arguments : List SExpr}
    (hmember : signature ∈ applicationSignatures.take 35)
    (htotal :
      (totalApplicationHeads.contains signature.name ||
        indexedTesterHeads.contains signature.name) = true)
    (harguments :
      ExpressionsEvaluateWithSorts model arguments signature.arguments) :
    ∃ value,
      SmtSem.eval model (.app signature.name arguments) = some value ∧
        SValHasSort value signature.result := by
  simp [applicationSignatures] at hmember
  repeat' rcases hmember with rfl | hmember
  all_goals simp [totalApplicationHeads, indexedTesterHeads] at htotal
  all_goals dsimp at harguments ⊢
  all_goals first
    | obtain rfl := evaluatedArguments0 harguments
    | (obtain ⟨first, firstValue, rfl, hfirst, hfirstSort⟩ :=
          evaluatedArguments1 harguments
       cases hfirstSort)
    | (obtain ⟨first, second, firstValue, secondValue, rfl,
          hfirst, hfirstSort, hsecond, hsecondSort⟩ :=
          evaluatedArguments2 harguments
       cases hfirstSort
       cases hsecondSort)
    | (obtain ⟨first, second, third, firstValue, secondValue, thirdValue,
          rfl, hfirst, hfirstSort, hsecond, hsecondSort,
          hthird, hthirdSort⟩ := evaluatedArguments3 harguments
       cases hfirstSort
       cases hsecondSort
       cases hthirdSort)
  all_goals
    simp [Moist.SMT.Semantics.eval, Moist.SMT.Semantics.evalList, *]
    constructor

private theorem tableApplication_evaluates_middle
    {model : SmtSem.Model} {signature : ApplicationSignature}
    {arguments : List SExpr}
    (hmember : signature ∈ (applicationSignatures.drop 35).take 35)
    (htotal :
      (totalApplicationHeads.contains signature.name ||
        indexedTesterHeads.contains signature.name) = true)
    (harguments :
      ExpressionsEvaluateWithSorts model arguments signature.arguments) :
    ∃ value,
      SmtSem.eval model (.app signature.name arguments) = some value ∧
        SValHasSort value signature.result := by
  simp [applicationSignatures] at hmember
  repeat' rcases hmember with rfl | hmember
  all_goals simp [totalApplicationHeads, indexedTesterHeads] at htotal
  all_goals dsimp at harguments ⊢
  all_goals first
    | obtain rfl := evaluatedArguments0 harguments
    | (obtain ⟨first, firstValue, rfl, hfirst, hfirstSort⟩ :=
          evaluatedArguments1 harguments
       cases hfirstSort)
    | (obtain ⟨first, second, firstValue, secondValue, rfl,
          hfirst, hfirstSort, hsecond, hsecondSort⟩ :=
          evaluatedArguments2 harguments
       cases hfirstSort
       cases hsecondSort)
    | (obtain ⟨first, second, third, firstValue, secondValue, thirdValue,
          rfl, hfirst, hfirstSort, hsecond, hsecondSort,
          hthird, hthirdSort⟩ := evaluatedArguments3 harguments
       cases hfirstSort
       cases hsecondSort
       cases hthirdSort)
  all_goals
    simp [Moist.SMT.Semantics.eval, Moist.SMT.Semantics.evalList, *]
    constructor

private theorem tableApplication_evaluates_last
    {model : SmtSem.Model} {signature : ApplicationSignature}
    {arguments : List SExpr}
    (hmember : signature ∈ applicationSignatures.drop 70)
    (htotal :
      (totalApplicationHeads.contains signature.name ||
        indexedTesterHeads.contains signature.name) = true)
    (harguments :
      ExpressionsEvaluateWithSorts model arguments signature.arguments) :
    ∃ value,
      SmtSem.eval model (.app signature.name arguments) = some value ∧
        SValHasSort value signature.result := by
  simp [applicationSignatures] at hmember
  repeat' rcases hmember with rfl | hmember
  all_goals simp [totalApplicationHeads, indexedTesterHeads] at htotal
  all_goals dsimp at harguments ⊢
  all_goals first
    | obtain rfl := evaluatedArguments0 harguments
    | (obtain ⟨first, firstValue, rfl, hfirst, hfirstSort⟩ :=
          evaluatedArguments1 harguments
       cases hfirstSort)
    | (obtain ⟨first, second, firstValue, secondValue, rfl,
          hfirst, hfirstSort, hsecond, hsecondSort⟩ :=
          evaluatedArguments2 harguments
       cases hfirstSort
       cases hsecondSort)
    | (obtain ⟨first, second, third, firstValue, secondValue, thirdValue,
          rfl, hfirst, hfirstSort, hsecond, hsecondSort,
          hthird, hthirdSort⟩ := evaluatedArguments3 harguments
       cases hfirstSort
       cases hsecondSort
       cases hthirdSort)
  all_goals
    simp [Moist.SMT.Semantics.eval, Moist.SMT.Semantics.evalList, *]
    constructor

private theorem tableApplication_evaluates
    {model : SmtSem.Model} {signature : ApplicationSignature}
    {arguments : List SExpr}
    (hmember : signature ∈ applicationSignatures)
    (htotal :
      (totalApplicationHeads.contains signature.name ||
        indexedTesterHeads.contains signature.name) = true)
    (harguments :
      ExpressionsEvaluateWithSorts model arguments signature.arguments) :
    ∃ value,
      SmtSem.eval model (.app signature.name arguments) = some value ∧
        SValHasSort value signature.result := by
  rw [← List.take_append_drop 35 applicationSignatures] at hmember
  rcases List.mem_append.mp hmember with hfirst | hrest
  · exact tableApplication_evaluates_first hfirst htotal harguments
  rw [← List.take_append_drop 35 (applicationSignatures.drop 35)] at hrest
  rcases List.mem_append.mp hrest with hmiddle | hlast
  · exact tableApplication_evaluates_middle hmiddle htotal harguments
  simpa only [List.drop_drop] using
    tableApplication_evaluates_last hlast htotal harguments

private theorem testerSignature_none_of_totalHead
    {name : String} (htotal : totalApplicationHeads.contains name = true) :
    testerSignature? name = none := by
  simp [totalApplicationHeads] at htotal
  repeat' rcases htotal with htotal | htotal
  all_goals rfl

attribute [local simp]
  Moist.SMT.Semantics.evalApp_isCtor_DConstr
  Moist.SMT.Semantics.evalApp_isCtor_DMap
  Moist.SMT.Semantics.evalApp_isCtor_DList
  Moist.SMT.Semantics.evalApp_isCtor_DI
  Moist.SMT.Semantics.evalApp_isCtor_DB
  Moist.SMT.Semantics.evalApp_isCtor_DNil
  Moist.SMT.Semantics.evalApp_isCtor_DCons
  Moist.SMT.Semantics.evalApp_isCtor_DPNil
  Moist.SMT.Semantics.evalApp_isCtor_DPCons
  Moist.SMT.Semantics.evalApp_isCtor_VInt
  Moist.SMT.Semantics.evalApp_isCtor_VBytes
  Moist.SMT.Semantics.evalApp_isCtor_VString
  Moist.SMT.Semantics.evalApp_isCtor_VBool
  Moist.SMT.Semantics.evalApp_isCtor_VUnit
  Moist.SMT.Semantics.evalApp_isCtor_VList
  Moist.SMT.Semantics.evalApp_isCtor_VDataList
  Moist.SMT.Semantics.evalApp_isCtor_VPairDataList
  Moist.SMT.Semantics.evalApp_isCtor_VPair
  Moist.SMT.Semantics.evalApp_isCtor_VPairData
  Moist.SMT.Semantics.evalApp_isCtor_VData
  Moist.SMT.Semantics.evalApp_isCtor_VArray
  Moist.SMT.Semantics.evalApp_isCtor_VG1
  Moist.SMT.Semantics.evalApp_isCtor_VG2
  Moist.SMT.Semantics.evalApp_isCtor_VMlResult
  Moist.SMT.Semantics.evalApp_isCtor_VConstr
  Moist.SMT.Semantics.evalApp_isCtor_VNil
  Moist.SMT.Semantics.evalApp_isCtor_VCons

private theorem testerApplication_evaluates
    {model : SmtSem.Model} {name : String}
    {signature : ApplicationSignature} {arguments : List SExpr}
    (htester : testerSignature? name = some signature)
    (htotal :
      (totalApplicationHeads.contains name ||
        indexedTesterHeads.contains name) = true)
    (harguments :
      ExpressionsEvaluateWithSorts model arguments signature.arguments) :
    ∃ value, SmtSem.eval model (.app name arguments) = some value ∧
      SValHasSort value signature.result := by
  simp only [Bool.or_eq_true] at htotal
  rcases htotal with htotal | htesterHead
  · rw [testerSignature_none_of_totalHead htotal] at htester
    contradiction
  simp [indexedTesterHeads] at htesterHead
  repeat' rcases htesterHead with htesterHead | htesterHead
  all_goals simp [testerSignature?] at htester
  all_goals subst signature
  all_goals dsimp at harguments ⊢
  all_goals
    obtain ⟨first, firstValue, rfl, hfirst, hfirstSort⟩ :=
      evaluatedArguments1 harguments
    cases hfirstSort
  all_goals
    simp [Moist.SMT.Semantics.eval, Moist.SMT.Semantics.evalList, *]
    constructor

private theorem totalApplication_evaluates
    {model : SmtSem.Model} {name : String} {arguments : List SExpr}
    {argumentSorts : List Moist.SMT.SSort} {resultSort : Moist.SMT.SSort}
    (htotal :
      (totalApplicationHeads.contains name ||
        indexedTesterHeads.contains name) = true)
    (hsignature :
      applicationResultSort? name argumentSorts = some resultSort)
    (harguments :
      ExpressionsEvaluateWithSorts model arguments argumentSorts) :
    ∃ value, SmtSem.eval model (.app name arguments) = some value ∧
      SValHasSort value resultSort := by
  unfold applicationResultSort? at hsignature
  generalize hcandidates :
    (match testerSignature? name with
      | some signature => signature :: applicationSignatures
      | none => applicationSignatures) = candidates at hsignature
  simp only [Option.map_eq_some_iff] at hsignature
  obtain ⟨signature, hfound, hresult⟩ := hsignature
  have hmember := List.mem_of_find?_eq_some hfound
  have hmatches := List.find?_some hfound
  simp only [Bool.and_eq_true] at hmatches
  have hname : signature.name = name := by
    simpa using hmatches.1
  have hsorts : signature.arguments = argumentSorts := by
    simpa using hmatches.2
  subst name
  subst argumentSorts
  subst resultSort
  cases htester : testerSignature? signature.name with
  | none =>
      simp [htester] at hcandidates
      subst candidates
      exact tableApplication_evaluates hmember htotal harguments
  | some tester =>
      simp [htester] at hcandidates
      subst candidates
      simp only [List.mem_cons] at hmember
      rcases hmember with rfl | htable
      · exact testerApplication_evaluates htester htotal harguments
      · exact tableApplication_evaluates htable htotal harguments

mutual
  /-- Constant-compatible semantic values are accepted by the CEK constant
  decoder. -/
  private theorem constValCompatible_decodes : ∀ value,
      Moist.SMT.Semantics.constValCompatible value = true →
      ∃ constant, semValToConst? value = some constant
    | .int value, _ => ⟨.Integer value, rfl⟩
    | .bytes value, _ => ⟨.ByteString value, rfl⟩
    | .string value, _ => ⟨.String value, rfl⟩
    | .bool value, _ => ⟨.Bool value, rfl⟩
    | .unit, _ => ⟨.Unit, rfl⟩
    | .list values, hcompatible => by
        simp [Moist.SMT.Semantics.constValCompatible] at hcompatible
        obtain ⟨constants, hconstants⟩ :=
          constValListCompatible_decodes values hcompatible
        exact ⟨.ConstList constants, by
          simp [semValToConst?, hconstants]⟩
    | .dataList values, _ => ⟨.ConstDataList values, rfl⟩
    | .pairDataList values, _ => ⟨.ConstPairDataList values, rfl⟩
    | .pair first second, hcompatible => by
        simp [Moist.SMT.Semantics.constValCompatible] at hcompatible
        obtain ⟨firstConstant, hfirst⟩ :=
          constValCompatible_decodes first hcompatible.1
        obtain ⟨secondConstant, hsecond⟩ :=
          constValCompatible_decodes second hcompatible.2
        exact ⟨.Pair (firstConstant, secondConstant), by
          simp [semValToConst?, hfirst, hsecond]⟩
    | .pairData first second, _ => ⟨.PairData (first, second), rfl⟩
    | .data value, _ => ⟨.Data value, rfl⟩
    | .array values, hcompatible => by
        simp [Moist.SMT.Semantics.constValCompatible] at hcompatible
        obtain ⟨constants, hconstants⟩ :=
          constValListCompatible_decodes values hcompatible
        exact ⟨.ConstArray constants, by
          simp [semValToConst?, hconstants]⟩
    | .g1 _, _ => ⟨.Bls12_381_G1_element, rfl⟩
    | .g2 _, _ => ⟨.Bls12_381_G2_element, rfl⟩
    | .ml _, _ => ⟨.Bls12_381_MlResult, rfl⟩
    | .constr _ _, hcompatible => by
        simp [Moist.SMT.Semantics.constValCompatible] at hcompatible

  /-- Lists of constant-compatible semantic values are accepted by the CEK
  constant-list decoder. -/
  private theorem constValListCompatible_decodes : ∀ values,
      Moist.SMT.Semantics.constValListCompatible values = true →
      ∃ constants, semValListToConstList? values = some constants
    | [], _ => ⟨[], rfl⟩
    | value :: values, hcompatible => by
        simp [Moist.SMT.Semantics.constValListCompatible] at hcompatible
        obtain ⟨constant, hconstant⟩ :=
          constValCompatible_decodes value hcompatible.1
        obtain ⟨constants, hconstants⟩ :=
          constValListCompatible_decodes values hcompatible.2
        exact ⟨constant :: constants, by
          simp [semValListToConstList?, hconstant, hconstants]⟩
end

mutual
  /-- The executable `val_valid` predicate is sufficient for the actual CEK
  decoder.  This closes the direct-`Val` model boundary without trusting a
  caller-provided decoding witness. -/
  theorem valValid_decodes : ∀ value,
      Moist.SMT.Semantics.valValid value = true →
      ∃ decoded, semValToCek? value = some decoded
    | .int value, _ => ⟨.VCon (.Integer value), rfl⟩
    | .bytes value, _ => ⟨.VCon (.ByteString value), rfl⟩
    | .string value, _ => ⟨.VCon (.String value), rfl⟩
    | .bool value, _ => ⟨.VCon (.Bool value), rfl⟩
    | .unit, _ => ⟨.VCon .Unit, rfl⟩
    | .list values, hvalid => by
        have hcompatible :
            Moist.SMT.Semantics.constValListCompatible values = true := by
          rw [Moist.SMT.Semantics.constValListCompatible_eq_constValListValid]
          simpa [Moist.SMT.Semantics.valValid] using hvalid
        obtain ⟨constants, hconstants⟩ :=
          constValListCompatible_decodes values hcompatible
        exact ⟨.VCon (.ConstList constants), by
          simp [semValToCek?, semValToConst?, hconstants]⟩
    | .dataList values, _ => ⟨.VCon (.ConstDataList values), rfl⟩
    | .pairDataList values, _ => ⟨.VCon (.ConstPairDataList values), rfl⟩
    | .pair first second, hvalid => by
        simp [Moist.SMT.Semantics.valValid] at hvalid
        have hfirstCompatible :
            Moist.SMT.Semantics.constValCompatible first = true := by
          rw [Moist.SMT.Semantics.constValCompatible_eq_constValValid]
          exact hvalid.1
        have hsecondCompatible :
            Moist.SMT.Semantics.constValCompatible second = true := by
          rw [Moist.SMT.Semantics.constValCompatible_eq_constValValid]
          exact hvalid.2
        have hcompatible :
            Moist.SMT.Semantics.constValCompatible (.pair first second) =
              true := by
          simp [Moist.SMT.Semantics.constValCompatible, hfirstCompatible,
            hsecondCompatible]
        obtain ⟨constant, hconstant⟩ :=
          constValCompatible_decodes (.pair first second) hcompatible
        exact ⟨.VCon constant, semValToCek_of_const hconstant⟩
    | .pairData first second, _ =>
        ⟨.VCon (.PairData (first, second)), rfl⟩
    | .data value, _ => ⟨.VCon (.Data value), rfl⟩
    | .array values, hvalid => by
        have hcompatible :
            Moist.SMT.Semantics.constValListCompatible values = true := by
          rw [Moist.SMT.Semantics.constValListCompatible_eq_constValListValid]
          simpa [Moist.SMT.Semantics.valValid] using hvalid
        obtain ⟨constants, hconstants⟩ :=
          constValListCompatible_decodes values hcompatible
        exact ⟨.VCon (.ConstArray constants), by
          simp [semValToCek?, semValToConst?, hconstants]⟩
    | .g1 _, _ => ⟨.VCon .Bls12_381_G1_element, rfl⟩
    | .g2 _, _ => ⟨.VCon .Bls12_381_G2_element, rfl⟩
    | .ml _, _ => ⟨.VCon .Bls12_381_MlResult, rfl⟩
    | .constr tag fields, hvalid => by
        simp [Moist.SMT.Semantics.valValid] at hvalid
        obtain ⟨decodedFields, hfields⟩ :=
          valListValid_decodes fields hvalid.2
        have htag : ¬ tag < 0 := by omega
        exact ⟨.VConstr tag.toNat decodedFields, by
          simp [semValToCek?, htag, hfields]⟩

  /-- List validity likewise composes through the actual CEK list decoder. -/
  theorem valListValid_decodes : ∀ values,
      Moist.SMT.Semantics.valListValid values = true →
      ∃ decoded, semValListToCekList? values = some decoded
    | [], _ => ⟨[], rfl⟩
    | value :: values, hvalid => by
        simp [Moist.SMT.Semantics.valListValid] at hvalid
        obtain ⟨decodedValue, hvalue⟩ := valValid_decodes value hvalid.1
        obtain ⟨decodedValues, hvalues⟩ :=
          valListValid_decodes values hvalid.2
        exact ⟨decodedValue :: decodedValues, by
          simp [semValListToCekList?, hvalue, hvalues]⟩
end

/-- Declared atomic model values and their runtime sorts at the solver bridge.

The external premise is deliberately limited to the symbols actually declared
in the checked query.  Evaluation and sort preservation for literals and every
well-sorted composite expression in the total public fragment are derived
below from the executable semantics.  Direct `Val` decoding is then derived
from that internal theorem and the mandatory `val_valid` assertion; it is not
an additional bridge premise.
-/
structure SolverInputModel (declarations : List SymDecl)
    (model : SmtSem.Model) : Prop where
  declaredSymbolValue : ∀ declaration,
    declaration ∈ declarations →
    ∃ value,
      model.valueOf declaration.name = some value ∧
        SValHasSort value declaration.sort

namespace SolverInputModel

set_option maxHeartbeats 5000000 in
mutual
  /-- Every admitted total expression evaluates in the executable SMT
  semantics, and its value has exactly the sort computed by the checked input
  grammar.  Only declared atomic symbols cross the external model bridge. -/
  theorem expressionEvaluates
      {declarations : List SymDecl} {model : SmtSem.Model}
      (bridge : SolverInputModel declarations model)
      (expression : SExpr) (sort : Moist.SMT.SSort)
      (htotal : expressionTotalitySafe expression = true)
      (hsort : expressionHasSort declarations expression sort = true) :
      ∃ value, SmtSem.eval model expression = some value ∧
        SValHasSort value sort := by
    rw [expressionHasSort_eq_true_iff] at hsort
    match hexpression : expression with
    | .sym name =>
        by_cases hempty : name = "(as seq.empty Bytes)"
        · subst name
          simp [expressionSort?] at hsort
          subst sort
          exact ⟨.bytes Moist.SMT.Semantics.bytesEmpty,
            by simp [Moist.SMT.Semantics.eval],
            .bytesVal Moist.SMT.Semantics.bytesEmpty⟩
        by_cases hemptySeq : name = "(as seq.empty (Seq Int))"
        · subst name
          simp [expressionSort?] at hsort
          subst sort
          exact ⟨.bytes Moist.SMT.Semantics.bytesEmpty,
            by simp [Moist.SMT.Semantics.eval],
            .bytesVal Moist.SMT.Semantics.bytesEmpty⟩
        by_cases hg1 : name = "g1_default"
        · subst name
          simp [expressionSort?] at hsort
          subst sort
          exact ⟨.g1 "g1_default", by simp [Moist.SMT.Semantics.eval],
            .g1Val "g1_default"⟩
        by_cases hg2 : name = "g2_default"
        · subst name
          simp [expressionSort?] at hsort
          subst sort
          exact ⟨.g2 "g2_default", by simp [Moist.SMT.Semantics.eval],
            .g2Val "g2_default"⟩
        by_cases hml : name = "ml_default"
        · subst name
          simp [expressionSort?] at hsort
          subst sort
          exact ⟨.ml "ml_default", by simp [Moist.SMT.Semantics.eval],
            .mlVal "ml_default"⟩
        · have hdeclarationSort :
              declarationSort? declarations name = some sort := by
            simpa [expressionSort?, hempty, hemptySeq, hg1, hg2, hml]
              using hsort
          unfold declarationSort? at hdeclarationSort
          generalize hfind : declarations.find? (fun declaration =>
            declaration.name == name) = found at hdeclarationSort
          cases found with
          | none => simp at hdeclarationSort
          | some declaration =>
              have hmember : declaration ∈ declarations :=
                List.mem_of_find?_eq_some hfind
              have hname : declaration.name = name := by
                have := List.find?_some hfind
                simpa using this
              have hsort : declaration.sort = sort := by
                simpa using hdeclarationSort
              obtain ⟨value, hvalue, hvalueSort⟩ :=
                bridge.declaredSymbolValue declaration hmember
              refine ⟨value, ?_, ?_⟩
              · calc
                  SmtSem.eval model (.sym name) = model.valueOf name := by
                    simp [Moist.SMT.Semantics.eval]
                  _ = some value := by simpa [hname] using hvalue
              · simpa [hsort] using hvalueSort
    | .int value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.int value, by simp [Moist.SMT.Semantics.eval], .intVal value⟩
    | .bytes value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.bytes value, by simp [Moist.SMT.Semantics.eval], .bytesVal value⟩
    | .dataLit value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.data value, by simp [Moist.SMT.Semantics.eval], .dataVal value⟩
    | .dataListLit value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.dataList value, by simp [Moist.SMT.Semantics.eval],
          .dataListVal value⟩
    | .dataPairListLit value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.dataPairList value, by simp [Moist.SMT.Semantics.eval],
          .dataPairListVal value⟩
    | .constListLit constants =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.valList (Moist.SMT.Semantics.constListToVals constants),
          by simp [Moist.SMT.Semantics.eval],
          .valListVal (Moist.SMT.Semantics.constListToVals constants)⟩
    | .bool value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.bool value, by simp [Moist.SMT.Semantics.eval], .boolVal value⟩
    | .str value =>
        simp [expressionSort?] at hsort
        subst sort
        exact ⟨.string value, by simp [Moist.SMT.Semantics.eval],
          .stringVal value⟩
    | .app name arguments =>
        simp only [expressionTotalitySafe, Bool.and_eq_true] at htotal
        by_cases hequality : name = "="
        · subst name
          cases arguments with
          | nil =>
              simp [expressionSort?, applicationResultSort?,
                applicationSignatures, testerSignature?] at hsort
          | cons left tail =>
              cases tail with
              | nil =>
                  simp [expressionSort?, applicationResultSort?,
                    applicationSignatures, testerSignature?] at hsort
              | cons right rest =>
                  cases rest with
                  | cons third rest =>
                      simp [expressionSort?, applicationResultSort?,
                        applicationSignatures, testerSignature?] at hsort
                  | nil =>
                      change (do
                        let leftSort ← expressionSort? declarations left
                        let rightSort ← expressionSort? declarations right
                        guard (leftSort == rightSort)
                        pure .bool) = some sort at hsort
                      generalize hleftSort :
                          expressionSort? declarations left =
                            foundLeftSort
                      cases foundLeftSort with
                      | none =>
                          rw [hleftSort] at hsort
                          simp at hsort
                      | some leftSort =>
                          rw [hleftSort] at hsort
                          generalize hrightSort :
                              expressionSort? declarations right =
                                foundRightSort
                          cases foundRightSort with
                          | none =>
                              rw [hrightSort] at hsort
                              simp at hsort
                          | some rightSort =>
                              rw [hrightSort] at hsort
                              by_cases hsame : leftSort == rightSort
                              · simp [guard, hsame] at hsort
                                have hsameSort : leftSort = rightSort :=
                                  eq_of_beq hsame
                                subst rightSort
                                subst sort
                                simp [expressionsTotalitySafe] at htotal
                                obtain ⟨leftValue, hleftEval,
                                    hleftValue⟩ :=
                                  expressionEvaluates bridge left leftSort
                                    htotal.2.1
                                    ((expressionHasSort_eq_true_iff
                                      declarations left leftSort).mpr
                                        hleftSort)
                                obtain ⟨rightValue, hrightEval,
                                    hrightValue⟩ :=
                                  expressionEvaluates bridge right leftSort
                                    htotal.2.2
                                    ((expressionHasSort_eq_true_iff
                                      declarations right leftSort).mpr
                                        hrightSort)
                                obtain ⟨result, hresult⟩ :=
                                  Moist.SMT.Semantics.evalApp_eq_total
                                    leftValue rightValue
                                exact ⟨.bool result, by
                                  simp [Moist.SMT.Semantics.eval,
                                    Moist.SMT.Semantics.evalList, hleftEval,
                                    hrightEval, hresult],
                                  .boolVal result⟩
                              · simp [guard, hsame] at hsort
                                change (none : Option Moist.SMT.SSort) =
                                    some sort at hsort
                                contradiction
        · rw [expressionSort_app_of_ne_eq declarations name arguments
            hequality] at hsort
          generalize hargumentSorts :
              expressionSorts? declarations arguments = foundSorts
          cases foundSorts with
          | none =>
              rw [hargumentSorts] at hsort
              simp at hsort
          | some argumentSorts =>
              rw [hargumentSorts] at hsort
              simp at hsort
              have harguments := expressionsEvaluateWithSorts bridge arguments
                argumentSorts htotal.2 hargumentSorts
              exact totalApplication_evaluates htotal.1 hsort harguments
    | .ite condition thenBranch elseBranch =>
        change (expressionTotalitySafe condition &&
          expressionTotalitySafe thenBranch &&
          expressionTotalitySafe elseBranch) = true at htotal
        simp only [Bool.and_eq_true] at htotal
        change (do
          guard (expressionSort? declarations condition == some .bool)
          let thenSort ← expressionSort? declarations thenBranch
          let elseSort ← expressionSort? declarations elseBranch
          guard (thenSort == elseSort)
          pure thenSort) = some sort at hsort
        generalize hconditionSort :
            expressionSort? declarations condition = foundConditionSort
        cases foundConditionSort with
        | none =>
            rw [hconditionSort] at hsort
            change (none : Option Moist.SMT.SSort) = some sort at hsort
            contradiction
        | some conditionSort =>
            rw [hconditionSort] at hsort
            cases conditionSort <;>
              try
                { change (none : Option Moist.SMT.SSort) =
                    some sort at hsort
                  contradiction }
            change (do
              let thenSort ← expressionSort? declarations thenBranch
              let elseSort ← expressionSort? declarations elseBranch
              guard (thenSort == elseSort)
              pure thenSort) = some sort at hsort
            generalize hthenSort :
                expressionSort? declarations thenBranch = foundThenSort
            cases foundThenSort with
            | none =>
                rw [hthenSort] at hsort
                simp at hsort
            | some thenSort =>
                rw [hthenSort] at hsort
                generalize helseSort :
                    expressionSort? declarations elseBranch = foundElseSort
                cases foundElseSort with
                | none =>
                    rw [helseSort] at hsort
                    simp at hsort
                | some elseSort =>
                    rw [helseSort] at hsort
                    by_cases hsame : thenSort == elseSort
                    · simp [guard, hsame] at hsort
                      have hsameSort : thenSort = elseSort := eq_of_beq hsame
                      subst elseSort
                      subst sort
                      obtain ⟨conditionValue, hconditionEval,
                          hconditionValue⟩ :=
                        expressionEvaluates bridge condition .bool htotal.1.1
                          ((expressionHasSort_eq_true_iff declarations condition
                            .bool).mpr hconditionSort)
                      obtain ⟨thenValue, hthenEval, hthenValue⟩ :=
                        expressionEvaluates bridge thenBranch thenSort
                          htotal.1.2
                          ((expressionHasSort_eq_true_iff declarations thenBranch
                            thenSort).mpr hthenSort)
                      obtain ⟨elseValue, helseEval, helseValue⟩ :=
                        expressionEvaluates bridge elseBranch thenSort htotal.2
                          ((expressionHasSort_eq_true_iff declarations elseBranch
                            thenSort).mpr helseSort)
                      cases hconditionValue with
                      | boolVal conditionValue =>
                          cases conditionValue with
                          | false =>
                              exact ⟨elseValue, by
                                change Moist.SMT.Semantics.eval model
                                  (.ite condition thenBranch elseBranch) =
                                    some elseValue
                                change Moist.SMT.Semantics.eval model condition =
                                  some (.bool false) at hconditionEval
                                rw [Moist.SMT.Semantics.eval_ite_exact,
                                  hconditionEval]
                                exact helseEval, helseValue⟩
                          | true =>
                              exact ⟨thenValue, by
                                change Moist.SMT.Semantics.eval model
                                  (.ite condition thenBranch elseBranch) =
                                    some thenValue
                                change Moist.SMT.Semantics.eval model condition =
                                  some (.bool true) at hconditionEval
                                rw [Moist.SMT.Semantics.eval_ite_exact,
                                  hconditionEval]
                                exact hthenEval, hthenValue⟩
                    · simp [guard, hsame] at hsort
                      change (none : Option Moist.SMT.SSort) =
                          some sort at hsort
                      contradiction
  termination_by sizeOf expression
  decreasing_by
    all_goals simp_all
    all_goals simp_wf
    all_goals omega

  /-- Pointwise form of `expressionEvaluates` for application arguments. -/
  theorem expressionsEvaluateWithSorts
      {declarations : List SymDecl} {model : SmtSem.Model}
      (bridge : SolverInputModel declarations model)
      (expressions : List SExpr) (sorts : List Moist.SMT.SSort)
      (htotal : expressionsTotalitySafe expressions = true)
      (hsorts : expressionSorts? declarations expressions = some sorts) :
      ExpressionsEvaluateWithSorts model expressions sorts := by
    match expressions with
    | [] =>
        simp [expressionSorts?] at hsorts
        subst sorts
        exact .nil
    | expression :: expressions =>
        simp only [expressionsTotalitySafe, Bool.and_eq_true] at htotal
        change (do
          let sort ← expressionSort? declarations expression
          let sorts ← expressionSorts? declarations expressions
          pure (sort :: sorts)) = some sorts at hsorts
        generalize hsort :
            expressionSort? declarations expression = foundSort
        cases foundSort with
        | none =>
            rw [hsort] at hsorts
            simp at hsorts
        | some sort =>
            rw [hsort] at hsorts
            generalize htailSorts :
                expressionSorts? declarations expressions = foundSorts
            cases foundSorts with
            | none =>
                rw [htailSorts] at hsorts
                simp at hsorts
            | some tailSorts =>
                rw [htailSorts] at hsorts
                simp at hsorts
                subst sorts
                obtain ⟨value, heval, hvalue⟩ :=
                  expressionEvaluates bridge expression sort htotal.1
                    ((expressionHasSort_eq_true_iff declarations expression
                      sort).mpr hsort)
                exact .cons heval hvalue
                  (expressionsEvaluateWithSorts bridge expressions
                    tailSorts htotal.2 htailSorts)
  termination_by sizeOf expressions
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

end SolverInputModel

/-- Every direct symbolic `Val` reference satisfies the exact validity
assertion emitted by its declaration. -/
def DirectValAssertionsHold (declarations : List SymDecl)
    (model : SmtSem.Model) : Prop :=
  ∀ expression, inputSymValSafe declarations (.dyn expression) = true →
    SmtSem.evalBoolIs model (.app "val_valid" [expression]) true = true

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
    (bridge : SolverInputModel declarations model)
    (directValAssertions : DirectValAssertionsHold declarations model)
    (value : SymVal) :
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
      · intro hsafe hsort
        obtain ⟨semanticValue, heval, hsemanticSort⟩ :=
          bridge.expressionEvaluates expression .val
            (by
              cases expression <;>
                simp [inputSymValSafe, directValSymbol] at hsafe ⊢ <;> rfl)
            (by simpa [symValSortSafe] using hsort)
        cases hsemanticSort with
        | valVal semanticValue =>
            have hvalid : Moist.SMT.Semantics.valValid semanticValue = true := by
              have hassumption := directValAssertions expression hsafe
              change Moist.SMT.Semantics.evalBoolIs model
                (.app "val_valid" [expression]) true = true at hassumption
              rw [Moist.SMT.Semantics.evalBoolIs_val_valid_of_eval heval] at hassumption
              exact hassumption
            obtain ⟨decoded, hdecoded⟩ :=
              valValid_decodes semanticValue hvalid
            exact ⟨decoded, by simp [symValToCek?, heval, hdecoded]⟩
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
    (bridge : SolverInputModel declarations model)
    (directValAssertions : DirectValAssertionsHold declarations model)
    (value : SymVal)
    (hsafe : inputSymValSafe declarations value = true)
    (hsort : symValSortSafe declarations value = true) :
    ∃ decoded, symValToCek? model value = some decoded :=
  (inputValueDecodeProperties bridge directValAssertions value).1 hsafe hsort

/-- A checked constant-shaped symbolic value decodes specifically to `VCon`. -/
theorem inputConstSymValSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model)
    (directValAssertions : DirectValAssertionsHold declarations model)
    (value : SymVal)
    (hsafe : inputConstSymValSafe declarations value = true)
    (hsort : symValSortSafe declarations value = true) :
    ∃ constant, symValToCek? model value = some (.VCon constant) :=
  (inputValueDecodeProperties bridge directValAssertions value).2 hsafe hsort

/-- Checked value lists compose through the ordinary list decoder. -/
theorem inputSymValsSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model)
    (directValAssertions : DirectValAssertionsHold declarations model) : ∀ values,
    inputSymValsSafe declarations values = true →
    symValsSortSafe declarations values = true →
    ∃ decoded, symValListToCekList? model values = some decoded
  | [], _, _ => ⟨[], rfl⟩
  | head :: tail, hsafe, hsort => by
      simp [inputSymValsSafe] at hsafe
      simp [symValsSortSafe] at hsort
      obtain ⟨headValue, hhead⟩ := inputSymValSafe_decodes
        bridge directValAssertions head hsafe.1 hsort.1
      obtain ⟨tailValues, htail⟩ := inputSymValsSafe_decodes
        bridge directValAssertions tail hsafe.2 hsort.2
      exact ⟨headValue :: tailValues, by
        simp [symValListToCekList?, hhead, htail]⟩

/-- The same checked list composes as a CEK environment. -/
theorem inputSymEnvSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model)
    (directValAssertions : DirectValAssertionsHold declarations model) : ∀ values,
    inputSymValsSafe declarations values = true →
    symValsSortSafe declarations values = true →
    ∃ environment, symEnvToCek? model values = some environment
  | [], _, _ => ⟨.nil, rfl⟩
  | head :: tail, hsafe, hsort => by
      simp [inputSymValsSafe] at hsafe
      simp [symValsSortSafe] at hsort
      obtain ⟨headValue, hhead⟩ := inputSymValSafe_decodes
        bridge directValAssertions head hsafe.1 hsort.1
      obtain ⟨tailEnv, htail⟩ := inputSymEnvSafe_decodes
        bridge directValAssertions tail hsafe.2 hsort.2
      exact ⟨.cons headValue tailEnv, by
        simp [symEnvToCek?, hhead, htail]⟩

/-- A syntactically admitted direct `Val` symbol points to a declaration that
contains the exact mandatory `val_valid` assertion. -/
theorem directValValidityAssumption_mem
    {declarations : List SymDecl} {expression : SExpr}
    (hsafe : inputSymValSafe declarations (.dyn expression) = true) :
    ∃ declaration, declaration ∈ declarations ∧
      (.app "val_valid" [expression] : SExpr) ∈
        declaration.assumptions := by
  cases expression with
  | sym name =>
      simp [inputSymValSafe, directValSymbol] at hsafe
      unfold declarationSort? at hsafe
      generalize hfind :
        declarations.find? (fun declaration => declaration.name == name) =
          found at hsafe
      cases found with
      | none => simp at hsafe
      | some declaration =>
          have hsort : declaration.sort = .val := by
            cases hsort : declaration.sort <;> simp [hsort] at hsafe
            rfl
          have hmem : declaration ∈ declarations :=
            List.mem_of_find?_eq_some hfind
          have hname : declaration.name = name := by
            simpa using List.find?_some hfind
          have hvalid := SymDecl.valValid_mem_of_sort declaration hsort
          rw [hname] at hvalid
          exact ⟨declaration, hmem, hvalid⟩
  | _ => simp [inputSymValSafe, directValSymbol] at hsafe

private theorem symDeclInputSafe_valueSafeUnlessConstr
    {declarations : List SymDecl} (declaration : SymDecl)
    (hsafe : symDeclInputSafe declarations declaration = true)
    (hsort : symDeclSortSafe declarations declaration = true) :
    match declaration.value with
    | .constr (.sym _) _ => True
    | value => inputSymValSafe declarations value = true := by
  rcases declaration with ⟨name, sort, value, assumptions, hwellFormed⟩
  have hsort' : symValSortSafe declarations value = true ∧
      assumptions.all (fun assumption =>
        expressionHasSort declarations assumption .bool) = true := by
    simpa [symDeclSortSafe] using hsort
  have hvalueSort : symValSortSafe declarations value = true := hsort'.1
  unfold symDeclInputSafe at hsafe
  dsimp only at hsafe
  split at hsafe
  case h_6 nameSym =>
    unfold symValSortSafe expressionHasSort at hvalueSort
    have hempty : nameSym ≠ "(as seq.empty Bytes)" := by
      intro heq
      subst nameSym
      change false = true at hvalueSort
      exact Bool.noConfusion hvalueSort
    have hemptySeq : nameSym ≠ "(as seq.empty (Seq Int))" := by
      intro heq
      subst nameSym
      change false = true at hvalueSort
      exact Bool.noConfusion hvalueSort
    have hg1 : nameSym ≠ "g1_default" := by
      intro heq
      subst nameSym
      change false = true at hvalueSort
      exact Bool.noConfusion hvalueSort
    have hg2 : nameSym ≠ "g2_default" := by
      intro heq
      subst nameSym
      change false = true at hvalueSort
      exact Bool.noConfusion hvalueSort
    have hml : nameSym ≠ "ml_default" := by
      intro heq
      subst nameSym
      change false = true at hvalueSort
      exact Bool.noConfusion hvalueSort
    simp [expressionSort?] at hvalueSort
    simp [inputSymValSafe, directValSymbol, hvalueSort]
  all_goals
    simp_all [symDeclSortSafe, symValSortSafe, inputSymValSafe,
      inputSymConstSafe, expressionTotalitySafe, expressionHasSort]

/-- A declaration admitted by the checked grammar decodes to a CEK value when
its mandatory assumptions hold in the executable SMT model.  The only case
not covered directly by `inputSymValSafe_decodes` is `symConstr`: its outer
tag is symbolic, so nonnegativity comes from the declaration's required
`tag >= 0` assertion. -/
theorem inputSymDeclSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) (declaration : SymDecl)
    (hmember : declaration ∈ declarations)
    (hsafe : symDeclInputSafe declarations declaration = true)
    (hsort : symDeclSortSafe declarations declaration = true)
    (hassumptions : ∀ inputDeclaration,
      inputDeclaration ∈ declarations → ∀ expression,
      expression ∈ inputDeclaration.assumptions →
        SmtSem.evalBoolIs model expression true = true) :
    ∃ decoded, symValToCek? model declaration.value = some decoded := by
  have hsort' : symValSortSafe declarations declaration.value = true ∧
      declaration.assumptions.all (fun assumption =>
        expressionHasSort declarations assumption .bool) = true := by
    simpa [symDeclSortSafe] using hsort
  have hvalueSort : symValSortSafe declarations declaration.value = true :=
    hsort'.1
  have hproperty := symDeclInputSafe_valueSafeUnlessConstr
    declaration hsafe hsort
  have directValAssertions : DirectValAssertionsHold declarations model := by
    intro expression hvalueSafe
    obtain ⟨inputDeclaration, hinputMember, hvalidMember⟩ :=
      directValValidityAssumption_mem hvalueSafe
    exact hassumptions inputDeclaration hinputMember _ hvalidMember
  have decodeOrdinary
      (hvalueSafe : inputSymValSafe declarations declaration.value = true) :
      ∃ decoded, symValToCek? model declaration.value = some decoded :=
    inputSymValSafe_decodes bridge directValAssertions declaration.value
      hvalueSafe hvalueSort
  by_cases houter : ∃ tagName fields,
      declaration.value = .constr (.sym tagName) fields
  · rcases houter with ⟨tagName, fields, hvalue⟩
    rcases declaration with ⟨name, sort, value, assumptions, hwellFormed⟩
    simp only at hvalue
    subst value
    cases sort <;> simp [symDeclInputSafe] at hsafe
    have htagFields : tagName = name ∧
        inputSymValsSafe declarations fields = true := hsafe.1
    rcases htagFields with ⟨rfl, hfieldsSafe⟩
    simp [symValSortSafe] at hvalueSort
    obtain ⟨tag, htagEval, htagSort⟩ := bridge.expressionEvaluates
      (.sym tagName) .int (by rfl) hvalueSort.1
    cases htagSort with
    | intVal tag =>
        obtain ⟨decodedFields, hfieldsDecoded⟩ :=
          inputSymValsSafe_decodes bridge directValAssertions fields
            hfieldsSafe hvalueSort.2
        have hmandatory :
            SExpr.ge (.sym tagName) (.int 0) ∈ assumptions :=
          SymDecl.constrTagNonnegative_mem
            { name := tagName
              sort := .int
              value := .constr (.sym tagName) fields
              assumptions := assumptions
              wellFormed := hwellFormed }
            rfl rfl rfl
        have htagNonnegative : 0 ≤ tag := by
          apply pcHolds_nonneg htagEval
          simpa [pcHolds, nonnegGuard] using
            hassumptions
              { name := tagName
                sort := .int
                value := .constr (.sym tagName) fields
                assumptions := assumptions
                wellFormed := hwellFormed }
              hmember _ hmandatory
        have htagNotNegative : ¬ tag < 0 := by omega
        exact ⟨Moist.CEK.CekValue.VConstr tag.toNat decodedFields, by
          simp [symValToCek?, htagEval, hfieldsDecoded,
            htagNotNegative]⟩
  · apply decodeOrdinary
    cases hvalue : declaration.value with
    | constr tag fields =>
        cases htag : tag <;> simp_all
    | _ => simpa [hvalue] using hproperty

private theorem inputDeclarationsSafe_decodesAux
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model) : ∀ (current : List SymDecl),
    current.all (symDeclInputSafe declarations) = true →
    current.all (symDeclSortSafe declarations) = true →
    (∀ declaration, declaration ∈ current → declaration ∈ declarations) →
    (∀ (declaration : SymDecl), declaration ∈ declarations → ∀ expression,
      expression ∈ declaration.assumptions →
        SmtSem.evalBoolIs model expression true = true) →
    ∃ environment,
      symEnvToCek? model (current.map SymDecl.value) = some environment
  | [], _, _, _, _ => ⟨.nil, rfl⟩
  | declaration :: declarations, hsafe, hsort, hsubset, hassumptions => by
      simp only [List.all_cons, Bool.and_eq_true] at hsafe hsort
      obtain ⟨headValue, hhead⟩ := inputSymDeclSafe_decodes bridge
        declaration (hsubset declaration (by simp)) hsafe.1 hsort.1
          hassumptions
      obtain ⟨tailEnvironment, htail⟩ := inputDeclarationsSafe_decodesAux
        bridge declarations hsafe.2 hsort.2
          (fun tailDeclaration htailMem =>
            hsubset tailDeclaration (by simp [htailMem])) hassumptions
      exact ⟨.cons headValue tailEnvironment, by
        simp [symEnvToCek?, hhead, htail]⟩

/-- All checked declarations compose to one exact CEK environment.  In
particular, this theorem derives the outer `symConstr` tag from its mandatory
solver assertion instead of assuming the final environment decoder result. -/
theorem declarationsInputSafe_decodes
    {declarations : List SymDecl} {model : SmtSem.Model}
    (bridge : SolverInputModel declarations model)
    (hsafe : declarationsInputSafe declarations = true)
    (hsort : declarationsSortSafe declarations = true)
    (hassumptions : ∀ declaration, declaration ∈ declarations →
      ∀ expression, expression ∈ declaration.assumptions →
        SmtSem.evalBoolIs model expression true = true) :
    ∃ environment,
      symEnvToCek? model (envOf declarations) = some environment := by
  exact inputDeclarationsSafe_decodesAux bridge declarations
    (by simpa [declarationsInputSafe] using hsafe)
    (by simpa [declarationsSortSafe] using hsort)
    (fun _ hmem => hmem) hassumptions

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
