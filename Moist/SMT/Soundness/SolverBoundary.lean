import Moist.SMT.Soundness
import Moist.SMT.DagRender

/-!
# Solver/model boundary

The CEK soundness theorems consume the executable semantics in
`Moist.SMT.Semantics`; an untrusted string containing the word `sat` is not a
proof of their premises.  This module makes the one external boundary
explicit: a solver integration must decode its model and certify every
generated assertion under that executable semantics.

The production-script theorems below establish the fixed prelude
syntactically.  The one remaining trusted step is the user-accepted
rendering/SMT-LIB/Z3 bridge: submit exactly the reference rendering, or the
operational DAG rendering; decode the actual Z3 model; and transfer every
assertion into `Semantics.eval`.  The pointer-based DAG renderer is `unsafe`,
so its equivalence to the reference renderer deliberately remains in that
external boundary rather than being disguised as a kernel theorem.  Once the
semantic certificate is available, all three public compiler queries compose
directly with the CEK theorems below.
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
  env_noOpaque : symEnvNoOpaqueForSoundness (envOf decls) = true
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

/-- A certified model of the production Boolean script yields the actual CEK
result. -/
theorem certifiedZ3_scriptForBoolTrue_sound
    {fuel : Nat} {decls : List SymDecl} {t : Term}
    (z3 : CertifiedZ3Model decls (scriptForBoolTrue fuel decls t))
    (hno : termNoOpaqueBuiltinsForSoundness t) :
    CekHaltsBoolTrue z3.cekEnv t := by
  apply evalSym_okBoolTrueCond_sound (fuel := fuel) (ρ := envOf decls)
    z3.env_decodes z3.env_noOpaque hno
  apply z3.assertionsTrue
  rw [scriptForBoolTrue_assertions]
  exact List.mem_append_right _ (by simp)

/-- A certified model of the production integer script yields the identical
CEK integer. -/
theorem certifiedZ3_scriptForIntEq_sound
    {fuel : Nat} {decls : List SymDecl} {t : Term} {rhs : SExpr}
    (z3 : CertifiedZ3Model decls (scriptForIntEq fuel decls t rhs))
    {expected : Int}
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hrhs : SmtSem.eval z3.model rhs = some (.int expected)) :
    CekHaltsInteger z3.cekEnv t expected := by
  apply evalSym_okIntEqCond_sound (fuel := fuel) (ρ := envOf decls)
    z3.env_decodes z3.env_noOpaque hno hrhs
  apply z3.assertionsTrue
  rw [scriptForIntEq_assertions]
  exact List.mem_append_right _ (by simp)

/-- A certified model of the production error script composes with the public
fuel-independent CEK error endpoint. -/
theorem certifiedZ3_scriptForError_sound
    {fuel : Nat} {decls : List SymDecl} {t : Term}
    (z3 : CertifiedZ3Model decls (scriptForError fuel decls t))
    (hno : termNoOpaqueBuiltinsForSoundness t) :
    CekDoesNotHalt z3.cekEnv t := by
  apply evalSym_errorCond_sound (fuel := fuel) (ρ := envOf decls)
    z3.env_decodes z3.env_noOpaque hno
  apply z3.assertionsTrue
  rw [scriptForError_assertions]
  exact List.mem_append_right _ (by simp)

end Moist.SMT.UPLC.Soundness
