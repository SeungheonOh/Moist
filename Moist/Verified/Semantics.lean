import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.MIR.Lower
import Moist.MIR.LowerTotal
import Moist.Verified.Definitions

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)

/-! # CEK execution facts

Determinism of halting, well-sized environments, and the executable
observation used by conformance tests. `steps` / `Reaches` come from
`Moist.Verified.Definitions`.
-/

-- `steps` and `Reaches` are the shared definitions from `Definitions.lean`.
export Moist.Verified.Equivalence (steps Reaches steps_error)

/-! ## Determinism

The CEK machine is deterministic: `step` is a pure function, terminal
states (`halt`, `error`) are fixed points of `step`, and therefore any
two step sequences from the same starting state that both reach `halt`
must agree on the halted value. -/

/-- `halt` is a fixed point of `step`. -/
theorem step_halt (v : CekValue) : step (.halt v) = .halt v := rfl
/-- `error` is a fixed point of `step`. -/
theorem step_error : step .error = .error := rfl

/-- Step counts compose: running `m + n` steps is the same as running `m`
    then `n`. -/
theorem steps_trans (m n : Nat) (s : State) : steps (m + n) s = steps n (steps m s) :=
  Equivalence.steps_trans m n s

/-- `halt` is absorbing: once halted, stepping any further stays at `halt v`. -/
theorem steps_halt (v : CekValue) (n : Nat) : steps n (.halt v) = .halt v :=
  Equivalence.steps_halt n v

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

/-! ## Well-Sized Environments -/

/-- A CEK environment is well-sized at depth `d` when every variable index
    in `1..d` resolves to a value. This is the runtime counterpart of
    `closedAt d t`: a `closedAt d` term evaluated in a `WellSizedEnv d`
    environment will never fail a variable lookup. -/
def WellSizedEnv (d : Nat) (ρ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v

/-- Extending a well-sized environment increases the depth by 1. -/
theorem wellSizedEnv_extend {d : Nat} {ρ : CekEnv} (h : WellSizedEnv d ρ) (v : CekValue) :
    WellSizedEnv (d + 1) (ρ.extend v) := by
  intro n hn hle
  match n with
  | 1 => exact ⟨v, rfl⟩
  | n + 2 =>
    have ⟨w, hw⟩ := h (n + 1) (by omega) (by omega)
    exact ⟨w, by simp [CekEnv.extend, CekEnv.lookup, hw]⟩

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

def obsOf : CekResult → Obs
  | .success v => .success (readbackValue v)
  | .failure => .failure
  | .outOfBudget => .failure

end Moist.Verified.Semantics
