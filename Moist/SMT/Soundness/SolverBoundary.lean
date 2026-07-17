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
    name == "(as seq.empty (Seq Int))" ||
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
    | .app name arguments =>
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

namespace SupportedDeclarations

/-- Check declaration values before admitting them to a production query. -/
def check (declarations : List SymDecl) : Option SupportedDeclarations :=
  if h : (symEnvNoOpaqueForSoundness (envOf declarations) &&
      declarationsRendererSafe declarations) = true then
    some ⟨declarations,
      (by
        have hparts :
            symEnvNoOpaqueForSoundness (envOf declarations) = true ∧
              declarationsRendererSafe declarations = true := by
          simpa only [Bool.and_eq_true] using h
        exact hparts.1),
      (by
        have hparts :
            symEnvNoOpaqueForSoundness (envOf declarations) = true ∧
              declarationsRendererSafe declarations = true := by
          simpa only [Bool.and_eq_true] using h
        exact hparts.2)⟩
  else
    none

@[simp] theorem check_isSome (declarations : List SymDecl) :
    (check declarations).isSome =
      (symEnvNoOpaqueForSoundness (envOf declarations) &&
        declarationsRendererSafe declarations) := by
  unfold check
  split <;> simp_all

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
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hterm]

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
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hterm]

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
        !termUsesOpaqueBuiltinForSoundness term) := by
  generalize hinputs : symEnvNoOpaqueForSoundness (envOf declarations) = inputsOk
  generalize hsafety : declarationsRendererSafe declarations = safetyOk
  generalize hterm : termUsesOpaqueBuiltinForSoundness term = termOpaque
  cases inputsOk <;> cases safetyOk <;> cases termOpaque <;>
    simp [compile?, SupportedDeclarations.check, SupportedTerm.check,
      hinputs, hsafety, hterm]

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
