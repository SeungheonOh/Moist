import Moist.Compile.Adequacy
import Moist.Smt.Print

/-! # Property encoding + end-to-end soundness (`encodeProperty`, `validator_sound`)

The product of the development.  A validator is compiled to its success formula
`e = extract (symEval F ρ̂ t)` (`defined ∧ value`), where `ρ̂` binds the symbolic inputs.
`encodeProperty P e` is the **negation** of "precondition `P` implies success"; asserting it
and getting `unsat` from z3 means the validator is defined and returns `true` for *all*
inputs satisfying `P`.

`validator_sound` is the usable theorem: from z3's `unsat` it concludes a genuine fact about
the **CEK machine** — for every input assignment satisfying `P`, the CEK evaluating the
validator on those inputs halts at `true`.  Its trusted base is exactly:

* `z3_sound` (the one accepted axiom: z3's verdict ⟹ our `evalSmt` meaning),
* the trusted `evalBuiltin_*` denotations (the `#eval`-validated R3 item),
* the Lean kernel.

The well-sortedness of the success formula (`sortOf e = some .bool`) is taken as a
hypothesis — discharged per validator by `rfl`/`decide` on the concrete `e` (the pragmatic
"runtime check with fuel to spare" of §6.5).
-/

namespace Moist.Compile

open Moist.Plutus.Term (Term)
open Moist.CEK
open Moist.Smt
open Moist.Verified.BigStep
open Moist.Verified.Equivalence (Reaches)

/-- The SMT formula asserted to z3: the **negation** of `P → (defined ∧ value)`.
    z3 `unsat` ⟺ the property holds at every model (`∀ σ, P σ → success σ`). -/
def encodeProperty (Psmt success : SmtExpr) : SmtExpr := .not (.impE Psmt success)

/-- From `Unsat (encodeProperty P e)` and a well-sorted boolean success formula `e`: at any
    model satisfying `P`, the success formula is `true`. -/
theorem encodeProperty_unsat_imp {Psmt e : SmtExpr} (hsort : SmtExpr.sortOf e = some .bool)
    (hu : Unsat (encodeProperty Psmt e)) {σ : Model} (hP : evalSmt σ Psmt = .B true) :
    evalSmt σ e = .B true := by
  obtain ⟨b, hb⟩ := evalSmt_bool (σ := σ) hsort
  cases b
  · exact absurd
      (show evalSmt σ (encodeProperty Psmt e) = .B true by
        simp only [encodeProperty, SmtExpr.impE, evalSmt, hP, hb, evalBin]; rfl)
      (hu σ)
  · exact hb

/-- Lift a `bigEval` success to the CEK halting (any environment), via the forward
    simulation `evalFwd`. -/
theorem bigEval_halts {f : Nat} {ρ : CekEnv} {t : Term} {v : CekValue}
    (h : bigEval f ρ t = some v) : Reaches (.compute [] ρ t) (.halt v) :=
  reaches_trans (evalFwd h []) (one_step rfl)

/-- **End-to-end soundness (the usable theorem).**  Given:
    * `hc` — the validator body `t` compiled (in the symbolic input environment `ρ`) to `o`,
    * `hx` — its success formula `e = extract o` (`defined ∧ value`),
    * `hsort` — `e` is a well-sorted boolean (discharged per validator by `rfl`/`decide`),
    * `hz3` — z3 reported `unsat` on `encodeProperty P e` (the trusted input),

    then for **every** input assignment `σ` satisfying the precondition `P`, the CEK machine
    evaluating the validator on those (concretized) inputs **halts at `true`**.

    TCB = `z3_sound` + `evalBuiltin_*` denotations + kernel.  Everything else is proved. -/
theorem validator_sound {F : Nat} {ρ : SymEnv} {t : Term} {o : SymOut} {e Psmt : SmtExpr}
    (hc : symEval F ρ t = some o)
    (hx : extract o = some e)
    (hsort : SmtExpr.sortOf e = some .bool)
    (hz3 : z3_says_unsat (toSMTLIB (encodeProperty Psmt e))) :
    ∀ σ : Model, evalSmt σ Psmt = .B true →
      Reaches (.compute [] (γE σ ρ) t) (.halt (.VCon (.Bool true))) := by
  have hu : Unsat (encodeProperty Psmt e) := z3_sound _ hz3
  intro σ hP
  have he : evalSmt σ e = .B true := encodeProperty_unsat_imp hsort hu hP
  exact bigEval_halts (symEval_extract_true hc hx he)

/-- Closed-term specialization: when the validator body is closed (`ρ = []`, e.g. all inputs
    already substituted as `Constant`s, or a nullary validator), the conclusion is phrased
    against `init` — `unsat` ⟹ the CEK halts at `true`. -/
theorem validator_sound_closed {F : Nat} {t : Term} {o : SymOut} {e Psmt : SmtExpr}
    (hc : symEval F [] t = some o)
    (hx : extract o = some e)
    (hsort : SmtExpr.sortOf e = some .bool)
    (hz3 : z3_says_unsat (toSMTLIB (encodeProperty Psmt e))) :
    ∀ σ : Model, evalSmt σ Psmt = .B true →
      Reaches (Moist.Verified.SmallStep.init t) (.halt (.VCon (.Bool true))) := by
  intro σ hP
  have := validator_sound hc hx hsort hz3 σ hP
  simpa only [γE] using this

end Moist.Compile
