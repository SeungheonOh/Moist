import Moist.SMT.Soundness.Internal

/-!
# SMT-to-CEK soundness

This is the public soundness boundary for the supported symbolic compiler.
The proof implementation lives in `Moist.SMT.Soundness.Internal`; consumers
should normally use the CEK-facing theorems in this file.

The SMT-LIB/Z3 model bridge is intentionally outside this module.  Given a
decoded internal model and environment, these theorems guarantee:

* a satisfiable Boolean-success assertion makes the actual CEK machine halt
  with `true`; and
* a satisfiable integer-equality assertion makes the actual CEK machine halt
  with that same integer; and
* a satisfiable error assertion is not a fuel timeout: the error-aware
  evaluator returns an actual runtime error, and the CEK machine reaches its
  `.error` state in finitely many transitions.

All three results require the explicitly supported (non-opaque-builtin) fragment.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekEnv CekValue State)
open Moist.Verified.BigStep
open Moist.Verified.Equivalence (Reaches)

/-- The actual CEK computation halts with exactly the supplied runtime value.
This value-level predicate is the general statement behind the specialized
Boolean and integer product queries below. -/
def CekHaltsValue (env : CekEnv) (t : Term) (value : CekValue) : Prop :=
  Reaches (.compute [] env t) (.halt value)

/-- The actual CEK computation started with a decoded environment halts with
the Boolean value `true`. -/
def CekHaltsBoolTrue (env : CekEnv) (t : Term) : Prop :=
  CekHaltsValue env t (.VCon (.Bool true))

/-- The actual CEK computation started with a decoded environment halts with
the requested integer. -/
def CekHaltsInteger (env : CekEnv) (t : Term) (expected : Int) : Prop :=
  CekHaltsValue env t (.VCon (.Integer expected))

/-- The actual CEK computation started with a decoded environment reaches the
runtime-error state in finitely many transitions. -/
def CekHaltsError (env : CekEnv) (t : Term) : Prop :=
  Reaches (.compute [] env t) .error

/-- Compatibility predicate: the CEK computation does not halt with a value.
The compiler's error endpoint below proves the strictly stronger
`CekHaltsError` property. -/
def CekDoesNotHalt (env : CekEnv) (t : Term) : Prop :=
  ¬ ∃ v, Reaches (.compute [] env t) (.halt v)

/-- General value-level compiler theorem.  Every active successful symbolic
outcome decodes to the *identical* value reached by the actual CEK transition
system.  This covers all encodable result types, not only the two convenient
product-query projections. -/
theorem evalSym_activeOk_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term} {pc : SExpr} {v : SymVal}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hmem : Outcome.ok pc v ∈ evalSym fuel ρ t)
    (hpc : pcHolds m pc = true) :
    ∃ value, symValToCek? m v = some value ∧
      CekHaltsValue env t value := by
  obtain ⟨value, hvalue, _hvalueNoOpaque, hbig⟩ :=
    evalSym_path_ok_noOpaque henv hρno hno hmem hpc
  exact ⟨value, hvalue,
    (bigEval_iff_halt_env).mp ⟨fuel, hbig⟩⟩

/-- Outcome-level error counterpart to `evalSym_activeOk_sound`. -/
theorem evalSym_activeError_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term} {pc : SExpr}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hmem : Outcome.error pc ∈ evalSym fuel ρ t)
    (hpc : pcHolds m pc = true) :
    CekHaltsError env t := by
  have hexact : Moist.Verified.ExactBigStep.eval fuel env t = .error :=
    evalSym_active_error_noOpaque_le henv hρno hno hmem
      (by simpa [outcomeErrorActive] using hpc) (Nat.le_refl fuel)
  have hforward := Moist.Verified.ExactBigStep.eval_fwd fuel env t []
  simpa [CekHaltsError,
    Moist.Verified.ExactBigStep.Result.ReachesAs, hexact] using hforward

/-- An active generated error remains a genuine runtime error at every larger
error-aware evaluation fuel.  In particular, none of these results is a fuel
timeout. -/
theorem evalSym_errorCond_allFuel {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (errorCond (evalSym fuel ρ t)) true = true) :
    ∀ fuel', fuel ≤ fuel' →
      Moist.Verified.ExactBigStep.eval fuel' env t = .error := by
  obtain ⟨out, hmem, herr⟩ := errorCond_eval_true_mem herror
  intro fuel' hle
  exact evalSym_active_error_noOpaque_le (m := m) (fuel := fuel) (fuel' := fuel')
    (ρ := ρ) (env := env) (t := t) henv hρno hno hmem herr hle

/-- Public compiler error endpoint.  A true generated error assertion cannot
be caused by insufficient symbolic fuel: the corresponding CEK computation
reaches `.error` in finitely many transitions. -/
theorem evalSym_errorCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (errorCond (evalSym fuel ρ t)) true = true) :
    CekHaltsError env t := by
  have herrorExact :=
    evalSym_errorCond_exact henv hρno hno herror
  have hforward :=
    Moist.Verified.ExactBigStep.eval_fwd fuel env t []
  simpa [CekHaltsError,
    Moist.Verified.ExactBigStep.Result.ReachesAs, herrorExact] using hforward

/-- Public compiler success endpoint.  A true rendered Boolean-success
assertion makes the actual CEK transition system halt with the identical
Boolean value. -/
theorem evalSym_okBoolTrueCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hokCond : SmtSem.evalBoolIs m
      (okBoolTrueCond (evalSym fuel ρ t)) true = true) :
    CekHaltsBoolTrue env t := by
  have hbig := evalSym_okBoolTrueCond_bigEval henv hρno hno hokCond
  exact (bigEval_iff_halt_env).mp ⟨fuel, hbig⟩

/-- Public compiler integer endpoint.  If the right-hand SMT expression
denotes `expected`, a true rendered integer-equality assertion makes the
actual CEK transition system halt with exactly `expected`. -/
theorem evalSym_okIntEqCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term} {rhs : SExpr} {expected : Int}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hrhs : SmtSem.eval m rhs = some (.int expected))
    (hcond : SmtSem.evalBoolIs m
      (okIntEqCond (evalSym fuel ρ t) rhs) true = true) :
    CekHaltsInteger env t expected := by
  have hbig := evalSym_okIntEqCond_bigEval henv hρno hno hrhs hcond
  exact (bigEval_iff_halt_env).mp ⟨fuel, hbig⟩

/-! ## Compatibility endpoints for opt-in assertion normalization -/

/-- Semantic compatibility for `scriptWithSimplified`. -/
theorem evalSym_simplifiedErrorCond_allFuel {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (errorCond (evalSym fuel ρ t))) true = true) :
    ∀ fuel', fuel ≤ fuel' →
      Moist.Verified.ExactBigStep.eval fuel' env t = .error := by
  apply evalSym_errorCond_allFuel henv hρno hno
  simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using herror

/-- Semantic compatibility for `scriptWithSimplified`. -/
theorem evalSym_simplifiedErrorCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (errorCond (evalSym fuel ρ t))) true = true) :
    CekHaltsError env t := by
  apply evalSym_errorCond_sound henv hρno hno
  simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using herror

/-- Semantic compatibility for `scriptWithSimplified`. -/
theorem evalSym_simplifiedOkBoolTrueCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hokCond : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (okBoolTrueCond (evalSym fuel ρ t))) true = true) :
    CekHaltsBoolTrue env t := by
  apply evalSym_okBoolTrueCond_sound henv hρno hno
  simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using hokCond

/-- Semantic compatibility for `scriptWithSimplified`. -/
theorem evalSym_simplifiedOkIntEqCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term} {rhs : SExpr} {expected : Int}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hrhs : SmtSem.eval m rhs = some (.int expected))
    (hcond : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool
        (okIntEqCond (evalSym fuel ρ t) rhs)) true = true) :
    CekHaltsInteger env t expected := by
  apply evalSym_okIntEqCond_sound henv hρno hno hrhs
  simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using hcond

end Moist.SMT.UPLC.Soundness
