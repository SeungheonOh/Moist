import Moist.Verified.SmallStep

/-! # Examples: using the small-step UPLC semantics and CEK adequacy

A tour of `Moist.Verified.SmallStep`, showing how to:

* recognise values, normal forms, and stuck terms (`Value`/`Normal`/`Stuck`);
* prove single and multi-step reductions (`Step`/`Steps`) with the call-by-value
  congruence rules;
* use determinism (`step_det`); and
* connect the CEK machine to small-step reduction through the adequacy theorems
  (`adequacy_halt`, `adequacy_halt_fwd`), in both directions.

Everything here is `example`/`theorem`, so the file is checked, not merely run.
-/

namespace Test.SmallStepExamples

open Moist.Plutus.Term (Term Const BuiltinType AtomicType BuiltinFun constType)
open Moist.CEK
open Moist.Verified.SmallStep
open Moist.Verified (closedAt substTerm)
open Moist.Verified.Equivalence (Reaches steps)

/-! ## Convenient term builders (canonical: `Lam` labels are `0`). -/

abbrev int (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
abbrev lam (body : Term) : Term := .Lam 0 body
abbrev app (f x : Term) : Term := .Apply f x

/-! ## 1. Values, normal forms, and stuck terms -/

example : Value (int 7) := .constant
example : Value (lam (.Var 1)) := .lam
example {M : Term} : Value (.Delay M) := .delay
example {i : Nat} {vs : List Term} (h : ValueList vs) : Value (.Constr i vs) := .constr h

/-- A *bare* builtin is a value (it is a fully unsaturated partial application). -/
example {b : BuiltinFun} : Value (.Builtin b) := .builtin .builtin

/-- `Error` is not a value. -/
example : ¬ Value (.Error) := not_value_error

/-- Every value is a normal form (cannot reduce). -/
example : Normal (int 7) := value_normal .constant

/-- An ill-typed configuration is *stuck*: a normal form that is not a value.
    Forcing a constant cannot reduce (only `force (delay …)` can) and is not a
    value. -/
example : Stuck (.Force (int 7)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, h⟩
    cases h with
    | satForce hsp => cases hsp
    | congForce h => cases h
  · intro hv
    obtain ⟨_, _, _, hsp⟩ := value_force_inv hv
    cases hsp

/-! ## 2. Single-step reductions -/

/-- β-reduction: `(λ x. x) 7 → 7`.  `Step.betaLam` yields the open substitution
    `substTerm 1 7 (Var 1)`, which computes to `7`. -/
example : Step (app (lam (.Var 1)) (int 7)) (int 7) := by
  have h := @Step.betaLam 0 (.Var 1) (int 7) .constant
  simpa [substTerm_var] using h

/-- `force (delay M) → M`. -/
example {M : Term} : Step (.Force (.Delay M)) M := Step.forceDelay

/-- `case (constr 0 [7]) [λ x. x] → (λ x. x) 7`, the first branch applied to the
    constructor's field. -/
example :
    Step (.Case (.Constr 0 [int 7]) [lam (.Var 1)]) (mkApps (lam (.Var 1)) [int 7]) :=
  Step.caseConstr (.cons .constant .nil) rfl

/-! ## 3. Multi-step reductions (`Steps`)

Call-by-value: the argument is reduced to a value *before* β fires.  Here the
argument `force (delay 7)` is reduced under the application frame (`congAppR`,
guarded by the function being a value) and then β contracts. -/

example : Steps (app (lam (.Var 1)) (.Force (.Delay (int 7)))) (int 7) := by
  refine Steps.step (Step.congAppR .lam Step.forceDelay) (Steps.step ?_ Steps.refl)
  have h := @Step.betaLam 0 (.Var 1) (int 7) .constant
  simpa [substTerm_var] using h

/-! ## 4. Determinism -/

/-- `Step` is deterministic — a term has at most one reduct. -/
example {t a b : Term} (h1 : Step t a) (h2 : Step t b) : a = b := step_det h1 h2

/-! ## 5. CEK ↔ small-step adequacy

`int 7` is closed and canonical, so the adequacy `↔` applies to it. -/

theorem int7_closed : closedAt 0 (int 7) = true := by simp [closedAt]
theorem int7_canonical : Canonical (int 7) := by simp only [Canonical, constType]

/-- The CEK machine evaluates `7` to the value `7` in two steps. -/
example : Reaches (init (int 7)) (.halt (.VCon (.Integer 7))) := ⟨2, rfl⟩

/-- The adequacy `↔` instantiated at `int 7`: the machine halts iff small-step
    reduction reaches a value. -/
example :
    (∃ v, Reaches (init (int 7)) (.halt v)) ↔ (∃ w, Steps (int 7) w ∧ Value w) :=
  adequacy_halt int7_closed int7_canonical

/-- **Forward** direction (CEK ⇒ small-step), exact value: from a concrete CEK
    run we read off that `7` small-steps to `discharge (VCon 7) = 7`. -/
example : Steps (int 7) (int 7) ∧ Value (int 7) := by
  have h := adequacy_halt_fwd int7_closed int7_canonical ⟨2, rfl⟩
  simpa [discharge, constType] using h

/-- **Backward** direction (small-step ⇒ CEK): because the identity applied to `7`
    small-steps to a value, the CEK machine on it is guaranteed to halt — proven
    without ever computing the machine run, just from the small-step witness. -/
example : ∃ v, Reaches (init (app (lam (.Var 1)) (int 7))) (.halt v) := by
  rw [adequacy_halt (by simp [closedAt]) (by simp [Canonical, constType])]
  refine ⟨int 7, ?_, .constant⟩
  have h := @Step.betaLam 0 (.Var 1) (int 7) .constant
  exact Steps.single (by simpa [substTerm_var] using h)

end Test.SmallStepExamples
