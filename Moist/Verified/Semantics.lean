import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.MIR.Lower
import Moist.MIR.LowerTotal

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)
open Moist.MIR (Expr lowerTotal lowerTotalExpr lowerTotalExpr_eq_lowerTotal fixCount)

/-! # Behavioral Equivalence via CEK Machine

This module defines the semantic foundation for proving MIR-level optimizations
correct. Everything is built on top of the total `step : State → State` function
from `CEK.Machine`, which makes every definition admissible in Lean's logic
(no `partial`, no `sorry`).

The key ideas:
- `steps n s` iterates `step` exactly `n` times.
- `Reaches s s'` witnesses that some number of steps connects `s` to `s'`.
- `ValueEq k v w` is a step-indexed logical relation that says two CEK values
  "look the same" up to observation depth `k`.
- `BehEqClosed m1 m2` ties it all together: two closed MIR expressions are
  behaviorally equivalent when their lowered UPLC terms agree on error
  reachability and produce `ValueEq`-related results at every depth.
-/

/-- Iterate `step` exactly `n` times starting from state `s`.
    This is the "clock" used throughout the semantic development:
    `steps 0 s = s` and `steps (n+1) s = steps n (step s)`. -/
def steps : Nat → State → State
  | 0, s => s
  | n + 1, s => steps n (step s)

/-- Existential reachability: `Reaches s s'` holds when there exists some
    step count `n` such that `steps n s = s'`. This is the central notion
    connecting concrete CEK execution to logical propositions. -/
def Reaches (s s' : State) : Prop :=
  ∃ n : Nat, steps n s = s'

/-- A state halts when it reaches some `halt v`. -/
def Halts (s : State) : Prop := ∃ v : CekValue, Reaches s (.halt v)

/-! ## Determinism

The CEK machine is deterministic: `step` is a pure function, terminal
states (`halt`, `error`) are fixed points of `step`, and therefore any
two step sequences from the same starting state that both reach `halt`
must agree on the halted value. -/

/-- `halt` is a fixed point of `step`. -/
theorem step_halt (v : CekValue) : step (.halt v) = .halt v := rfl
/-- `error` is a fixed point of `step`. -/
theorem step_error : step .error = .error := rfl

/-- `error` is absorbing: once reached, stepping any further stays at `error`. -/
theorem steps_error (n : Nat) : steps n .error = .error := by
  induction n with | zero => rfl | succ n ih => simp [steps, step_error, ih]

/-- Step counts compose: running `m + n` steps is the same as running `m`
    then `n`. Proved by induction on `m`. -/
theorem steps_trans (m n : Nat) (s : State) : steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (step s)

/-- `halt` is absorbing: once halted, stepping any further stays at `halt v`. -/
theorem steps_halt (v : CekValue) (n : Nat) : steps n (.halt v) = .halt v := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [steps, step_halt, ih]

/-- Auxiliary lemma for `reaches_unique`. If two different step counts both
    reach `halt` from the same state, the halted values must be identical.
    Proceeds by strong induction: at each step, if one side has already
    halted the other must agree (by `steps_halt`); otherwise both sides
    take one step and the induction hypothesis applies. -/
private theorem reaches_unique_aux : ∀ (m n : Nat) (s : State) (v w : CekValue),
    steps m s = .halt v → steps n s = .halt w → v = w := by
  intro m
  induction m with
  | zero =>
    intro n s v w hm hn
    dsimp [steps] at hm; subst hm
    rw [steps_halt] at hn; exact State.halt.inj hn
  | succ m ih =>
    intro n s v w hm hn
    dsimp [steps] at hm
    cases n with
    | zero =>
      dsimp [steps] at hn; subst hn
      simp only [step_halt] at hm; rw [steps_halt] at hm
      exact (State.halt.inj hm).symm
    | succ n =>
      dsimp [steps] at hn
      exact ih n (step s) v w hm hn

/-- **Determinism of halting**: if a state reaches `halt v` and also
    reaches `halt w`, then `v = w`. This is the key uniqueness property
    that makes `BehEqClosed` well-defined. -/
theorem reaches_unique {s : State} {v w : CekValue}
    (hv : Reaches s (.halt v)) (hw : Reaches s (.halt w)) : v = w :=
  let ⟨m, hm⟩ := hv; let ⟨n, hn⟩ := hw; reaches_unique_aux m n s v w hm hn

/-- **Consistency of outcomes**: a state cannot reach both `halt` and `error`.
    Proof: extend both step sequences to the same total length using
    `steps_halt`/`steps_error`, then observe the contradiction
    `.halt v = .error`. -/
theorem reaches_halt_not_error {s : State} {v : CekValue}
    (hv : Reaches s (.halt v)) (he : Reaches s .error) : False := by
  obtain ⟨m, hm⟩ := hv; obtain ⟨n, hn⟩ := he
  have h1 : steps (m + n) s = .halt v := by rw [steps_trans, hm, steps_halt]
  have h2 : steps (n + m) s = .error := by rw [steps_trans, hn, steps_error]
  rw [show m + n = n + m from Nat.add_comm m n] at h1; rw [h1] at h2; exact absurd h2 (by simp)

/-! ## Step-Indexed Value Equivalence

`ValueEq k v w` is a step-indexed logical relation on CEK values. The index
`k` bounds how deeply we are allowed to observe the values:

- At `k = 0`, all values are considered equal (no observation budget left).
- At `k + 1`, constants must be literally equal, constructors must match on
  tag and fields (recursively at depth `k`), and closures (lambdas/delays)
  must produce `ValueEq k`-related results when applied to (or forced with)
  any argument — provided both sides halt.

This is the standard technique from step-indexed logical relations
(Appel & McAllester, 2001): the successor index "pays" for one level of
observation, ensuring the definition is well-founded without needing
a metric on values.

`ListValueEq` extends this pointwise to lists of values. -/

mutual
  /-- Step-indexed equivalence of CEK values. At depth 0 everything is
      equivalent. At depth `k+1`, values must match structurally: constants
      must be equal, closures must produce equivalent results when run, and
      constructors must agree on tag with pointwise-equivalent fields. -/
  def ValueEq : Nat → CekValue → CekValue → Prop
    | 0, _, _ => True
    | _ + 1, .VCon c1, .VCon c2 => c1 = c2
    | k + 1, .VLam body1 env1, .VLam body2 env2 =>
      ∀ (arg1 arg2 : CekValue), ValueEq k arg1 arg2 →
        ∀ n, n ≤ k →
          (steps n (.compute [] (env1.extend arg1) body1) = .error ↔
           steps n (.compute [] (env2.extend arg2) body2) = .error) ∧
          (∀ v1, steps n (.compute [] (env1.extend arg1) body1) = .halt v1 →
            ∃ v2, steps n (.compute [] (env2.extend arg2) body2) = .halt v2 ∧
              ValueEq k v1 v2) ∧
          (∀ v2, steps n (.compute [] (env2.extend arg2) body2) = .halt v2 →
            ∃ v1, steps n (.compute [] (env1.extend arg1) body1) = .halt v1 ∧
              ValueEq k v1 v2)
    | k + 1, .VConstr tag1 fields1, .VConstr tag2 fields2 =>
      tag1 = tag2 ∧ ListValueEq k fields1 fields2
    | k + 1, .VDelay body1 env1, .VDelay body2 env2 =>
      ∀ n, n ≤ k →
        (steps n (.compute [] env1 body1) = .error ↔
         steps n (.compute [] env2 body2) = .error) ∧
        (∀ v1, steps n (.compute [] env1 body1) = .halt v1 →
          ∃ v2, steps n (.compute [] env2 body2) = .halt v2 ∧
            ValueEq k v1 v2) ∧
        (∀ v2, steps n (.compute [] env2 body2) = .halt v2 →
          ∃ v1, steps n (.compute [] env1 body1) = .halt v1 ∧
            ValueEq k v1 v2)
    | k + 1, .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2 =>
      b1 = b2 ∧ ListValueEq k args1 args2 ∧ ea1 = ea2 ∧
      (Moist.CEK.evalBuiltin b1 args1 = none ↔
       Moist.CEK.evalBuiltin b2 args2 = none) ∧
      (∀ (r1 r2 : CekValue),
        Moist.CEK.evalBuiltin b1 args1 = some r1 →
        Moist.CEK.evalBuiltin b2 args2 = some r2 →
        ValueEq k r1 r2)
    | _, _, _ => False

  /-- Pointwise `ValueEq` lifted to lists. Both lists must have the same
      length, with corresponding elements equivalent at depth `k`. -/
  def ListValueEq : Nat → List CekValue → List CekValue → Prop
    | _, [], [] => True
    | k, a :: as, b :: bs => ValueEq k a b ∧ ListValueEq k as bs
    | _, _, _ => False
end

/-! ## Behavioral Equivalence -/

/-- Lower a closed MIR expression to UPLC via `lowerTotal` with an empty
    variable environment. Returns `none` if the expression contains
    constructs that `lowerTotal` does not support (e.g. `Fix`). -/
def lowerMIR (m : Expr) : Option Term := lowerTotalExpr ([] : List MIR.VarId) m

/-- **Behavioral equivalence of closed MIR expressions.**

    Two closed MIR expressions `m1` and `m2` are behaviorally equivalent
    (`BehEqClosed m1 m2`) when, after lowering to UPLC via `lowerTotal`:

    1. **Error agreement**: one reaches `error` if and only if the other does.
    2. **Value agreement**: whenever both halt with values `v1` and `v2`,
       those values are `ValueEq k`-related for every step index `k`.

    If either expression fails to lower (returns `none`), the proposition
    holds vacuously (`True`). This is intentional: we only claim correctness
    for the fragment that `lowerTotal` handles.

    The entire definition is built from total functions (`steps`, `lowerTotal`),
    so it lives in `Prop` and can be used in Lean proofs without `sorry`. -/
def BehEqClosed (m1 m2 : Expr) : Prop :=
  match lowerTotalExpr ([] : List MIR.VarId) m1, lowerTotalExpr ([] : List MIR.VarId) m2 with
  | some t1, some t2 =>
    (Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧
    (Halts (.compute [] .nil t1) ↔ Halts (.compute [] .nil t2)) ∧
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) (.halt v1) →
      Reaches (.compute [] .nil t2) (.halt v2) →
      ValueEq k v1 v2
  | _, _ => True

scoped infix:50 " ≋ᶜ " => BehEqClosed

/-! ## Well-Sized Environments -/

/-- A CEK environment is well-sized at depth `d` when every variable index
    in `1..d` resolves to a value. This is the runtime counterpart of
    `closedAt d t`: a `closedAt d` term evaluated in a `WellSizedEnv d`
    environment will never fail a variable lookup. -/
def WellSizedEnv (d : Nat) (ρ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v

/-- The nil environment is well-sized at depth 0 (vacuously). -/
theorem wellSizedEnv_nil : WellSizedEnv 0 .nil :=
  fun _ hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0)

/-- Extending a well-sized environment increases the depth by 1. -/
theorem wellSizedEnv_extend {d : Nat} {ρ : CekEnv} (h : WellSizedEnv d ρ) (v : CekValue) :
    WellSizedEnv (d + 1) (ρ.extend v) := by
  intro n hn hle
  match n with
  | 1 => exact ⟨v, rfl⟩
  | n + 2 =>
    have ⟨w, hw⟩ := h (n + 1) (by omega) (by omega)
    exact ⟨w, by simp [CekEnv.extend, CekEnv.lookup, hw]⟩

/-- Well-sizedness is monotone: a larger environment is also well-sized
    at any smaller depth. -/
theorem wellSizedEnv_mono {d d' : Nat} {ρ : CekEnv} (h : WellSizedEnv d ρ) (hle : d' ≤ d) :
    WellSizedEnv d' ρ :=
  fun n hn hn' => h n hn (Nat.le_trans hn' hle)

/-- **Behavioral equivalence of MIR expressions under all environments.**

    Two MIR expressions `m1` and `m2` are behaviorally equivalent when,
    for every MIR lowering environment `env` and every well-sized CEK
    runtime environment `ρ`, the lowered terms agree on error reachability
    and produce `ValueEq k`-related results for every step index `k`.

    The `WellSizedEnv` guard restricts `ρ` to environments where every
    in-scope variable resolves — matching the invariant maintained by
    actual CEK execution. This enables proving correctness of
    optimizations that eliminate value-form bindings (including `Var`).

    Quantifying over all `env` makes `BehEq` composable: an optimization
    proved correct at any nesting depth can be applied inside lambdas,
    let-bindings, or case branches. -/
def BehEq (m1 m2 : Expr) : Prop :=
  ∀ (env : List MIR.VarId),
  match lowerTotalExpr env m1, lowerTotalExpr env m2 with
  | some t1, some t2 =>
    ∀ ρ : CekEnv, WellSizedEnv env.length ρ →
      (Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
      (Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
      ∀ (k : Nat) (v1 v2 : CekValue),
        Reaches (.compute [] ρ t1) (.halt v1) →
        Reaches (.compute [] ρ t2) (.halt v2) →
        ValueEq k v1 v2
  | _, _ => True

scoped infix:50 " ≋ " => BehEq

/-- **Refinement**: `m2` refines `m1` when `m2` compiles wherever `m1` does,
    and they are behaviorally equivalent. This is the appropriate notion for
    optimizations that may remove free variables (like dead-let elimination). -/
def Refines (m1 m2 : Expr) : Prop :=
  (∀ env, (lowerTotalExpr env m1).isSome → (lowerTotalExpr env m2).isSome) ∧
  BehEq m1 m2

scoped infix:50 " ⊑ " => Refines

/-! ## Executable observation (for conformance testing only)

`Obs` and `obsOf` provide a decidable observation type used in executable
test harnesses. They are not used in any proofs — only for `#eval`-based
conformance tests that compare the CEK machine's output against expected
results. -/

/-- Observable outcome of CEK evaluation: either a successfully
    read-back UPLC term, or a failure (error / out-of-budget). -/
inductive Obs where
  | success : Term → Obs
  | failure : Obs

instance : BEq Obs where
  beq
    | .success t1, .success t2 => termEq t1 t2
    | .failure, .failure => true
    | _, _ => false

def obsOf : CekResult → Obs
  | .success v => .success (readbackValue v)
  | .failure => .failure
  | .outOfBudget => .failure

instance : ToString Obs where
  toString
    | .success t => s!"success({repr t})"
    | .failure => "failure"

end Moist.Verified.Semantics
