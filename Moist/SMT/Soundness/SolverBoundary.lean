import Moist.SMT.Soundness
import Moist.SMT.DagRender

/-!
# Solver/model boundary

The CEK soundness theorems consume the executable semantics in
`Moist.SMT.Semantics`; an untrusted string containing the word `sat` is not a
proof of their premises.  This module makes the one external boundary
explicit: a solver integration must decode its model and certify every
generated assertion under that executable semantics.

The low-level script theorems below establish the fixed prelude syntactically.
The proof-carrying query API rejects terms and declaration environments that
contain opaque builtins before it emits a production query.  The one remaining
trusted step is the user-accepted
rendering/SMT-LIB/Z3 bridge: submit exactly the reference rendering, or the
operational DAG rendering; decode the actual Z3 model; and transfer every
assertion into `Semantics.eval`.  The pointer-based DAG renderer is `unsafe`,
so its equivalence to the reference renderer deliberately remains in that
external boundary rather than being disguised as a kernel theorem.  Once the
semantic certificate is available, all three supported compiler queries
compose directly with the CEK theorems below, without a caller-supplied
fragment premise.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekEnv)

/-- Kernel-checkable equality for integrations using the transparent
reference renderer.  `Script.renderDag` is intentionally absent: it uses
pointer identity and therefore belongs to the explicit external boundary. -/
def IsReferenceRendering (script : Moist.SMT.Script) (text : String) : Prop :=
  text = script.render

/-- A script contains the compiler's complete fixed prelude, in order. -/
def hasCompilerPrelude (script : Moist.SMT.Script) : Prop :=
  ∃ suffix, script.commands = prelude ++ suffix

/--
A decoded solver model at the trusted SMT-LIB boundary.

`assertionsTrue` is the exact semantic-transfer premise: all assertions,
including declaration validity assumptions, are true in the same executable
model used by the CEK simulation.  Neither a `sat` token nor syntactic prelude
membership can construct this field.
-/
structure CertifiedZ3Model (decls : List SymDecl)
    (script : Moist.SMT.Script) where
  model : SmtSem.Model
  /-- The typed CEK environment decoded from exactly the symbolic
  declarations used to build the production script. -/
  cekEnv : CekEnv
  env_decodes : symEnvToCek? model (envOf decls) = some cekEnv
  assertionsTrue : ∀ e, e ∈ script.assertions →
    SmtSem.evalBoolIs model e true = true

/-- Semantic satisfiability exposed to solver integrations.  Raw Z3 `sat`
must be accompanied by a decoded `CertifiedZ3Model`; no theorem treats the
status token alone as evidence. -/
def Z3Sat (decls : List SymDecl) (script : Moist.SMT.Script) : Prop :=
  Nonempty (CertifiedZ3Model decls script)

theorem scriptWith_hasCompilerPrelude (decls : List SymDecl)
    (assertions : List SExpr) :
    hasCompilerPrelude (scriptWith decls assertions) := by
  refine ⟨declCommands decls ++ assumptionCommands decls ++
    assertions.map Moist.SMT.Command.assert ++
      [.checkSatUsing z3QueryTactic, .getModel], ?_⟩
  rfl

theorem scriptForBoolTrue_hasCompilerPrelude (fuel : Nat)
    (decls : List SymDecl) (t : Term) :
    hasCompilerPrelude (scriptForBoolTrue fuel decls t) := by
  exact scriptWith_hasCompilerPrelude _ _

theorem scriptForIntEq_hasCompilerPrelude (fuel : Nat)
    (decls : List SymDecl) (t : Term) (rhs : SExpr) :
    hasCompilerPrelude (scriptForIntEq fuel decls t rhs) := by
  exact scriptWith_hasCompilerPrelude _ _

theorem scriptForError_hasCompilerPrelude (fuel : Nat)
    (decls : List SymDecl) (t : Term) :
    hasCompilerPrelude (scriptForError fuel decls t) := by
  exact scriptWith_hasCompilerPrelude _ _

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

/-- A checked Boolean-success production query. -/
structure BoolTrueQuery where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm

namespace BoolTrueQuery

def script (query : BoolTrueQuery) : Moist.SMT.Script :=
  scriptForBoolTrue query.fuel query.inputs.declarations query.program.term

/-- Check both the term and its symbolic declaration environment. -/
def compile? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option BoolTrueQuery := do
  let inputs ← SupportedDeclarations.check declarations
  let program ← SupportedTerm.check term
  pure ⟨fuel, inputs, program⟩

@[simp] theorem compile_isSome (fuel : Nat) (declarations : List SymDecl)
    (term : Term) :
    (compile? fuel declarations term).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations &&
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hsort : declarationsSortSafe declarations = sortOk
  generalize hsafeInput : declarationsInputSafe declarations = inputOk
  generalize hdistinct : declarationNamesDistinct declarations = distinctOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases sortOk <;>
    cases inputOk <;> cases distinctOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hsort, hsafeInput, hdistinct, hterm]

theorem hasCompilerPrelude (query : BoolTrueQuery) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  exact scriptForBoolTrue_hasCompilerPrelude _ _ _

/-- A certified model of a checked Boolean query yields the actual CEK
result.  Fragment membership is carried by `query`; callers cannot forget it. -/
theorem sound (query : BoolTrueQuery)
    (z3 : CertifiedZ3Model query.inputs.declarations query.script) :
    CekHaltsBoolTrue z3.cekEnv query.program.term := by
  apply evalSym_okBoolTrueCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    z3.env_decodes query.inputs.noOpaque query.program.noOpaque
  apply z3.assertionsTrue
  rw [script, scriptForBoolTrue_assertions]
  exact List.mem_append_right _ (by simp)

end BoolTrueQuery

/-- A checked query for one concrete integer result.  Restricting the public
query to a literal expected integer removes a second avoidable semantic
premise about an arbitrary right-hand SMT expression. -/
structure IntEqQuery where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm
  expected : Int

namespace IntEqQuery

def script (query : IntEqQuery) : Moist.SMT.Script :=
  scriptForIntEq query.fuel query.inputs.declarations query.program.term
    (.int query.expected)

/-- Check both the term and its symbolic declaration environment. -/
def compile? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) : Option IntEqQuery := do
  let inputs ← SupportedDeclarations.check declarations
  let program ← SupportedTerm.check term
  pure ⟨fuel, inputs, program, expected⟩

@[simp] theorem compile_isSome (fuel : Nat) (declarations : List SymDecl)
    (term : Term) (expected : Int) :
    (compile? fuel declarations term expected).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations &&
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hsort : declarationsSortSafe declarations = sortOk
  generalize hsafeInput : declarationsInputSafe declarations = inputOk
  generalize hdistinct : declarationNamesDistinct declarations = distinctOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases sortOk <;>
    cases inputOk <;> cases distinctOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hsort, hsafeInput, hdistinct, hterm]

theorem hasCompilerPrelude (query : IntEqQuery) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  exact scriptForIntEq_hasCompilerPrelude _ _ _ _

/-- A certified model of a checked integer query yields exactly the requested
CEK integer. -/
theorem sound (query : IntEqQuery)
    (z3 : CertifiedZ3Model query.inputs.declarations query.script) :
    CekHaltsInteger z3.cekEnv query.program.term query.expected := by
  apply evalSym_okIntEqCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    (rhs := .int query.expected) (expected := query.expected)
    z3.env_decodes query.inputs.noOpaque query.program.noOpaque
  · exact Moist.SMT.Semantics.eval.eq_7 _ _
  · apply z3.assertionsTrue
    rw [script, scriptForIntEq_assertions]
    exact List.mem_append_right _ (by simp)

end IntEqQuery

/-- A checked runtime-error production query. -/
structure ErrorQuery where
  fuel : Nat
  inputs : SupportedDeclarations
  program : SupportedTerm

namespace ErrorQuery

def script (query : ErrorQuery) : Moist.SMT.Script :=
  scriptForError query.fuel query.inputs.declarations query.program.term

/-- Check both the term and its symbolic declaration environment. -/
def compile? (fuel : Nat) (declarations : List SymDecl)
    (term : Term) : Option ErrorQuery := do
  let inputs ← SupportedDeclarations.check declarations
  let program ← SupportedTerm.check term
  pure ⟨fuel, inputs, program⟩

@[simp] theorem compile_isSome (fuel : Nat) (declarations : List SymDecl)
    (term : Term) :
    (compile? fuel declarations term).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations &&
        declarationsSortSafe declarations &&
        declarationsInputSafe declarations &&
        declarationNamesDistinct declarations &&
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hsort : declarationsSortSafe declarations = sortOk
  generalize hsafeInput : declarationsInputSafe declarations = inputOk
  generalize hdistinct : declarationNamesDistinct declarations = distinctOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases sortOk <;>
    cases inputOk <;> cases distinctOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hsort, hsafeInput, hdistinct, hterm]

theorem hasCompilerPrelude (query : ErrorQuery) :
    Moist.SMT.UPLC.Soundness.hasCompilerPrelude query.script := by
  exact scriptForError_hasCompilerPrelude _ _ _

/-- A certified model of a checked error query reaches the actual CEK
runtime-error state in finitely many transitions. -/
theorem sound (query : ErrorQuery)
    (z3 : CertifiedZ3Model query.inputs.declarations query.script) :
    CekHaltsError z3.cekEnv query.program.term := by
  apply evalSym_errorCond_sound
    (fuel := query.fuel) (ρ := envOf query.inputs.declarations)
    z3.env_decodes query.inputs.noOpaque query.program.noOpaque
  apply z3.assertionsTrue
  rw [script, scriptForError_assertions]
  exact List.mem_append_right _ (by simp)

end ErrorQuery

end Moist.SMT.UPLC.Soundness
