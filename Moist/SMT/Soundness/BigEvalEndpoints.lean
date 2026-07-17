import Moist.SMT.Soundness.Simulation

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.Verified.BigStep
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekEnv CekValue)

/-! ## Verified opt-in normalization

`scriptWithSimplified` remains available for hand-written assertions.  These
compatibility corollaries use semantic preservation of `Expr.simplifyBool`;
the production UPLC query constructors emit their already-smart-constructed
conditions directly and use the unsuffixed endpoints.
-/

theorem evalSym_simplifiedErrorCond_bigEval {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (errorCond (evalSym fuel ρ t))) true = true) :
    bigEval fuel env t = none := by
  apply evalSym_errorCond_bigEval henv hρno hno
  simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using herror

theorem evalSym_simplifiedOkBoolTrueCond_bigEval {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hokCond : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (okBoolTrueCond (evalSym fuel ρ t))) true = true) :
    bigEval fuel env t = some (.VCon (.Bool true)) := by
  apply evalSym_okBoolTrueCond_bigEval henv hρno hno
  simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using hokCond

def cekFails (t : Term) : Bool :=
  match bigEval 20 .nil t with
  | none => true
  | some _ => false

def smtBoolTrue (m : SmtSem.Model) (e : SExpr) : Bool :=
  SmtSem.evalBoolIs m e true

theorem sha2Refl_cek_fails :
    cekFails sha2Refl = true := by
  native_decide

theorem sha2Refl_opaque_smt_not_executable_in_internal_semantics :
    smtBoolTrue emptyModel (okBoolTrueCond (evalSym 20 [] sha2Refl)) = false ∧
    smtBoolTrue emptyModel (errorCond (evalSym 20 [] sha2Refl)) = false ∧
    smtBoolTrue emptyModel (timeoutCond (evalSym 20 [] sha2Refl)) = false := by
  native_decide

theorem recursiveSum10_bigEval_55 :
    bigEvalIntEq 100 (envInt 10) recursiveSumTerm 55 = true := by
  native_decide

theorem equalsIntegerAdd_smt_semantics_x5 :
    let outs := evalSym 20 (envOf [symInt "x"]) equalsIntegerAddExample
    SmtSem.evalBoolIs (modelInt "x" 5) (okBoolTrueCond outs) true = true ∧
    anyOkBoolTrue (modelInt "x" 5) outs = true := by
  native_decide

theorem equalsIntegerAdd_cek_x5 :
    bigEvalBoolTrue 20 (envInt 5) equalsIntegerAddExample = true := by
  native_decide

theorem caseInteger_smt_semantics_x2 :
    let outs := evalSym 20 (envOf [symInt "x"]) caseIntegerExample
    SmtSem.evalBoolIs (modelInt "x" 2) (okBoolTrueCond outs) true = true ∧
    anyOkBoolTrue (modelInt "x" 2) outs = true := by
  native_decide

theorem caseInteger_cek_x2 :
    bigEvalBoolTrue 20 (envInt 2) caseIntegerExample = true := by
  native_decide

theorem caseIfConstr_smt_semantics_x10 :
    let outs := evalSym 30 (envOf [symInt "x"]) caseIfConstrExample
    SmtSem.evalBoolIs (modelInt "x" 10) (okBoolTrueCond outs) true = true ∧
    anyOkBoolTrue (modelInt "x" 10) outs = true := by
  native_decide

theorem caseIfConstr_cek_x10 :
    bigEvalBoolTrue 30 (envInt 10) caseIfConstrExample = true := by
  native_decide

theorem caseEmptyConstListMissingNil_smt_error :
    let outs := evalSym 20 [] caseEmptyConstListMissingNilExample
    SmtSem.evalBoolIs emptyModel (errorCond outs) true = true ∧
    anyErrorOutcome emptyModel outs = true := by
  native_decide

theorem caseEmptyConstListMissingNil_cek_fails :
    bigEvalFails 20 .nil caseEmptyConstListMissingNilExample = true := by
  native_decide

theorem mkConsRejectsRuntimeConstr_smt_error :
    let outs := evalSym 20 [] mkConsRejectsRuntimeConstrExample
    SmtSem.evalBoolIs emptyModel (errorCond outs) true = true ∧
    anyErrorOutcome emptyModel outs = true := by
  native_decide

theorem mkConsRejectsRuntimeConstr_cek_fails :
    bigEvalFails 20 .nil mkConsRejectsRuntimeConstrExample = true := by
  native_decide

theorem sha2Refl_uses_opaque_builtin :
    termUsesOpaqueBuiltinForSoundness sha2Refl = true := by
  native_decide

theorem equalsIntegerAdd_no_opaque :
    termNoOpaqueBuiltinsForSoundness equalsIntegerAddExample := by
  unfold termNoOpaqueBuiltinsForSoundness
  native_decide

theorem caseInteger_no_opaque :
    termNoOpaqueBuiltinsForSoundness caseIntegerExample := by
  unfold termNoOpaqueBuiltinsForSoundness
  native_decide

theorem caseIfConstr_no_opaque :
    termNoOpaqueBuiltinsForSoundness caseIfConstrExample := by
  unfold termNoOpaqueBuiltinsForSoundness
  native_decide

end Moist.SMT.UPLC.Soundness
