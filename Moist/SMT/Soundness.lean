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
* a satisfiable error assertion is not a fuel timeout: `bigEval` fails at every
  greater fuel and the actual CEK machine cannot halt with any value.

Both results require the explicitly supported (non-opaque-builtin) fragment.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekEnv CekValue State)
open Moist.Verified.BigStep
open Moist.Verified.Equivalence (Reaches)

/-- The actual CEK computation started with a decoded environment halts with
the Boolean value `true`. -/
def CekHaltsBoolTrue (env : CekEnv) (t : Term) : Prop :=
  Reaches (.compute [] env t) (.halt (.VCon (.Bool true)))

/-- The actual CEK computation started with a decoded environment halts with
the requested integer. -/
def CekHaltsInteger (env : CekEnv) (t : Term) (expected : Int) : Prop :=
  Reaches (.compute [] env t) (.halt (.VCon (.Integer expected)))

/-- The actual CEK computation started with a decoded environment never halts
with a value.  This rules out both a successful result and a fuel artifact.
It deliberately does not claim finite arrival at `.error`; untyped UPLC may
diverge. -/
def CekDoesNotHalt (env : CekEnv) (t : Term) : Prop :=
  ¬ ∃ v, Reaches (.compute [] env t) (.halt v)

/-- An active symbolic error remains an error at every larger big-step fuel.
This is the fuel-independent core used by the CEK-facing endpoint below. -/
theorem evalSym_simplifiedErrorCond_allFuel {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (errorCond (evalSym fuel ρ t))) true = true) :
    ∀ fuel', fuel ≤ fuel' → bigEval fuel' env t = none := by
  obtain ⟨out, hmem, herr⟩ := errorCond_eval_true_mem
    (by simpa only [Moist.SMT.Semantics.evalBoolIs_simplifyBool] using herror)
  intro fuel' hle
  exact evalSym_active_error_noOpaque_le (m := m) (fuel := fuel) (fuel' := fuel')
    (ρ := ρ) (env := env) (t := t) henv hρno hno hmem herr hle

/-- Public error endpoint.  A true generated error assertion cannot be caused
by insufficient symbolic fuel, and the corresponding CEK computation cannot
halt successfully at any value. -/
theorem evalSym_simplifiedErrorCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (herror : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (errorCond (evalSym fuel ρ t))) true = true) :
    CekDoesNotHalt env t := by
  have hall := evalSym_simplifiedErrorCond_allFuel henv hρno hno herror
  rintro ⟨v, hhalt⟩
  obtain ⟨f, hf⟩ := bigEval_complete_env hhalt
  by_cases hle : fuel ≤ f
  · rw [hall f hle] at hf
    contradiction
  · have hflt : f ≤ fuel := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    have hf' := bigEval_mono_le hflt hf
    rw [hall fuel (Nat.le_refl fuel)] at hf'
    contradiction

/-- Public success endpoint.  A true generated Boolean-success assertion makes
the actual CEK transition system halt with the identical Boolean value. -/
theorem evalSym_simplifiedOkBoolTrueCond_sound {m : SmtSem.Model} {fuel : Nat}
    {ρ : List SymVal} {env : CekEnv} {t : Term}
    (henv : symEnvToCek? m ρ = some env)
    (hρno : symEnvNoOpaqueForSoundness ρ = true)
    (hno : termNoOpaqueBuiltinsForSoundness t)
    (hokCond : SmtSem.evalBoolIs m
      (Moist.SMT.Expr.simplifyBool (okBoolTrueCond (evalSym fuel ρ t))) true = true) :
    CekHaltsBoolTrue env t := by
  have hbig := evalSym_simplifiedOkBoolTrueCond_bigEval henv hρno hno hokCond
  exact (bigEval_iff_halt_env).mp ⟨fuel, hbig⟩

/-- Public integer endpoint.  If the right-hand SMT expression denotes
`expected`, a true generated integer-equality assertion makes the actual CEK
transition system halt with exactly `expected`. -/
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
  have hbig := evalSym_simplifiedOkIntEqCond_bigEval
    henv hρno hno hrhs hcond
  exact (bigEval_iff_halt_env).mp ⟨fuel, hbig⟩

end Moist.SMT.UPLC.Soundness
