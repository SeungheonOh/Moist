import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.MIR.Lower
import Moist.MIR.LowerTotal

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)
open Moist.MIR (Expr lowerTotal)

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
      ∀ (arg : CekValue),
        (Halts (.compute [] (env1.extend arg) body1) ↔
         Halts (.compute [] (env2.extend arg) body2)) ∧
        ∀ (v1 v2 : CekValue),
          Reaches (.compute [] (env1.extend arg) body1) (.halt v1) →
          Reaches (.compute [] (env2.extend arg) body2) (.halt v2) →
          ValueEq k v1 v2
    | k + 1, .VConstr tag1 fields1, .VConstr tag2 fields2 =>
      tag1 = tag2 ∧ ListValueEq k fields1 fields2
    | k + 1, .VDelay body1 env1, .VDelay body2 env2 =>
      (Halts (.compute [] env1 body1) ↔ Halts (.compute [] env2 body2)) ∧
      ∀ (v1 v2 : CekValue),
        Reaches (.compute [] env1 body1) (.halt v1) →
        Reaches (.compute [] env2 body2) (.halt v2) →
        ValueEq k v1 v2
    | k + 1, .VBuiltin b1 args1 ea1, .VBuiltin b2 args2 ea2 =>
      b1 = b2 ∧ ListValueEq k args1 args2 ∧ ea1 = ea2
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
def lowerMIR (m : Expr) : Option Term := lowerTotal [] m

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
  match lowerTotal [] m1, lowerTotal [] m2 with
  | some t1, some t2 =>
    (Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧
    (Halts (.compute [] .nil t1) ↔ Halts (.compute [] .nil t2)) ∧
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) (.halt v1) →
      Reaches (.compute [] .nil t2) (.halt v2) →
      ValueEq k v1 v2
  | _, _ => True

scoped infix:50 " ≋ᶜ " => BehEqClosed

/-- **Behavioral equivalence of MIR expressions under all environments.**

    Two MIR expressions `m1` and `m2` are behaviorally equivalent when,
    for every MIR lowering environment `env` and every CEK runtime
    environment `ρ`, the lowered terms agree on error reachability and
    produce `ValueEq k`-related results for every step index `k`.

    Quantifying over all `env` makes `BehEq` composable: an optimization
    proved correct at any nesting depth can be applied inside lambdas,
    let-bindings, or case branches. -/
def BehEq (m1 m2 : Expr) : Prop :=
  ∀ (env : List MIR.VarId),
  match lowerTotal env m1, lowerTotal env m2 with
  | some t1, some t2 =>
    (∀ ρ : CekEnv, Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
    (∀ ρ : CekEnv, Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
    ∀ (k : Nat) (ρ : CekEnv) (v1 v2 : CekValue),
      Reaches (.compute [] ρ t1) (.halt v1) →
      Reaches (.compute [] ρ t2) (.halt v2) →
      ValueEq k v1 v2
  | _, _ => True

scoped infix:50 " ≋ " => BehEq

/-- **Refinement**: `m2` refines `m1` when `m2` compiles wherever `m1` does,
    and they are behaviorally equivalent. This is the appropriate notion for
    optimizations that may remove free variables (like dead-let elimination). -/
def Refines (m1 m2 : Expr) : Prop :=
  (∀ env, (lowerTotal env m1).isSome → (lowerTotal env m2).isSome) ∧
  BehEq m1 m2

scoped infix:50 " ⊑ " => Refines

/-! ## ValueEq properties -/

mutual
  /-- `ValueEq` is reflexive at every step index. Proved by mutual induction
      on `k`, case-splitting on the value constructor. The `VLam`/`VDelay`
      cases use `reaches_unique` to collapse the two halting witnesses. -/
  theorem valueEq_refl : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | k + 1, .VLam _ _ => by
      unfold ValueEq; intro arg; exact ⟨Iff.rfl, fun v₁ v₂ h₁ h₂ =>
        reaches_unique h₁ h₂ ▸ valueEq_refl k v₁⟩
    | k + 1, .VDelay _ _ => by
      unfold ValueEq; exact ⟨Iff.rfl, fun v₁ v₂ h₁ h₂ =>
        reaches_unique h₁ h₂ ▸ valueEq_refl k v₁⟩
    | _ + 1, .VConstr _ fields => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl _ fields⟩
    | k + 1, .VBuiltin b args ea => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl k args, rfl⟩
  theorem listValueEq_refl : ∀ (k : Nat) (vs : List CekValue), ListValueEq k vs vs
    | _, [] => by simp [ListValueEq]
    | k, v :: vs => by simp only [ListValueEq]; exact ⟨valueEq_refl k v, listValueEq_refl k vs⟩
  theorem valueEq_symm : ∀ (k : Nat) (v₁ v₂ : CekValue), ValueEq k v₁ v₂ → ValueEq k v₂ v₁
    | 0, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, h => by simp only [ValueEq] at h ⊢; exact h.symm
    | k + 1, .VLam _ _, .VLam _ _, h => by
      unfold ValueEq at h ⊢; intro arg
      have ⟨hh, hv⟩ := h arg
      exact ⟨hh.symm, fun v₁ v₂ h₁ h₂ => valueEq_symm k _ _ (hv v₂ v₁ h₂ h₁)⟩
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1.symm, fun v₁ v₂ h₁ h₂ => valueEq_symm k _ _ (h.2 v₂ v₁ h₂ h₁)⟩
    | _ + 1, .VConstr _ _, .VConstr _ _, h => by
      unfold ValueEq at h ⊢; exact ⟨h.1.symm, listValueEq_symm _ _ _ h.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, h => by
      unfold ValueEq at h ⊢; exact ⟨h.1.symm, listValueEq_symm k _ _ h.2.1, h.2.2.symm⟩
    | _ + 1, .VCon _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValueEq] at h
  theorem listValueEq_symm : ∀ (k : Nat) (vs₁ vs₂ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₁
    | _, [], [], _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, h => by
      simp only [ListValueEq] at h ⊢
      exact ⟨valueEq_symm k _ _ h.1, listValueEq_symm k _ _ h.2⟩
    | _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
    | _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])
  theorem valueEq_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      ValueEq k v₁ v₂ → ValueEq k v₂ v₃ → ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    -- Matching constructors
    | _ + 1, .VCon _, .VCon _, .VCon _, h12, h23 => by
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam _ _, .VLam _ _, .VLam _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢; intro arg
      have ⟨hh12, hv12⟩ := h12 arg; have ⟨hh23, hv23⟩ := h23 arg
      refine ⟨hh12.trans hh23, fun w₁ w₃ hw₁ hw₃ => ?_⟩
      obtain ⟨_, hw₂⟩ := hh12.mp ⟨_, hw₁⟩
      exact valueEq_trans k _ _ _ (hv12 _ _ hw₁ hw₂) (hv23 _ _ hw₂ hw₃)
    | k + 1, .VDelay _ _, .VDelay _ _, .VDelay _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      refine ⟨h12.1.trans h23.1, fun w₁ w₃ hw₁ hw₃ => ?_⟩
      obtain ⟨_, hw₂⟩ := h12.1.mp ⟨_, hw₁⟩
      exact valueEq_trans k _ _ _ (h12.2 _ _ hw₁ hw₂) (h23.2 _ _ hw₂ hw₃)
    | _ + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans _ _ _ _ h12.2 h23.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans k _ _ _ h12.2.1 h23.2.1, h12.2.2.trans h23.2.2⟩
    -- h12 is False (v₁ and v₂ have different constructors)
    | _ + 1, .VCon _, .VLam _ _, _, h, _ | _ + 1, .VCon _, .VDelay _ _, _, h, _
    | _ + 1, .VCon _, .VConstr _ _, _, h, _ | _ + 1, .VCon _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VLam _ _, .VCon _, _, h, _ | _ + 1, .VLam _ _, .VDelay _ _, _, h, _
    | _ + 1, .VLam _ _, .VConstr _ _, _, h, _ | _ + 1, .VLam _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VDelay _ _, .VCon _, _, h, _ | _ + 1, .VDelay _ _, .VLam _ _, _, h, _
    | _ + 1, .VDelay _ _, .VConstr _ _, _, h, _ | _ + 1, .VDelay _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VConstr _ _, .VCon _, _, h, _ | _ + 1, .VConstr _ _, .VLam _ _, _, h, _
    | _ + 1, .VConstr _ _, .VDelay _ _, _, h, _ | _ + 1, .VConstr _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VCon _, _, h, _ | _ + 1, .VBuiltin _ _ _, .VLam _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, _, h, _ => by simp [ValueEq] at h
    -- h23 is False (v₂ and v₃ have different constructors, v₁ matches v₂)
    | _ + 1, .VCon _, .VCon _, .VLam _ _, _, h | _ + 1, .VCon _, .VCon _, .VDelay _ _, _, h
    | _ + 1, .VCon _, .VCon _, .VConstr _ _, _, h | _ + 1, .VCon _, .VCon _, .VBuiltin _ _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VCon _, _, h | _ + 1, .VLam _ _, .VLam _ _, .VDelay _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VConstr _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VCon _, _, h | _ + 1, .VDelay _ _, .VDelay _ _, .VLam _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VConstr _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VCon _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VLam _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VDelay _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VCon _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VLam _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VDelay _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VConstr _ _, _, h => by simp [ValueEq] at h
  theorem listValueEq_trans : ∀ (k : Nat) (vs₁ vs₂ vs₃ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₃ → ListValueEq k vs₁ vs₃
    | _, [], [], [], _, _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, _ :: _, h12, h23 => by
      simp only [ListValueEq] at h12 h23 ⊢
      exact ⟨valueEq_trans k _ _ _ h12.1 h23.1, listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | _, [], _ :: _, _, h, _ | _, _ :: _, [], _, h, _ => by simp [ListValueEq] at h
    | _, [], [], _ :: _, _, h => by simp [ListValueEq] at h
    | _, _ :: _, _ :: _, [], _, h => by simp [ListValueEq] at h
end

/-! ## Transitivity of behavioral equivalence -/

/-- Extract the content of `BehEqClosed` when both sides lower successfully. -/
private theorem behEqClosed_extract {m1 m2 : Expr} {t1 t2 : Term}
    (h1 : lowerTotal [] m1 = some t1) (h2 : lowerTotal [] m2 = some t2)
    (h : BehEqClosed m1 m2) :
    (Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧
    (Halts (.compute [] .nil t1) ↔ Halts (.compute [] .nil t2)) ∧
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) (.halt v1) →
      Reaches (.compute [] .nil t2) (.halt v2) →
      ValueEq k v1 v2 := by
  unfold BehEqClosed at h; rw [h1, h2] at h; exact h

/-- **Transitivity of closed behavioral equivalence.** -/
theorem behEqClosed_trans {a b c : Expr}
    {tb : Term} (hb : lowerTotal [] b = some tb)
    (h12 : a ≋ᶜ b) (h23 : b ≋ᶜ c) : a ≋ᶜ c := by
  unfold BehEqClosed
  cases ha : lowerTotal [] a with
  | none => split <;> trivial
  | some ta =>
    cases hc : lowerTotal [] c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have ⟨herr12, hh12, hv12⟩ := behEqClosed_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEqClosed_extract hb (show lowerTotal [] c = some tc from hc) h23
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

/-- Extract the content of `BehEq` at a specific environment when both sides lower. -/
private theorem behEq_extract {m1 m2 : Expr} {env : List MIR.VarId} {t1 t2 : Term}
    (h1 : lowerTotal env m1 = some t1) (h2 : lowerTotal env m2 = some t2)
    (h : BehEq m1 m2) :
    (∀ ρ : CekEnv, Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
    (∀ ρ : CekEnv, Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
    ∀ (k : Nat) (ρ : CekEnv) (v1 v2 : CekValue),
      Reaches (.compute [] ρ t1) (.halt v1) →
      Reaches (.compute [] ρ t2) (.halt v2) →
      ValueEq k v1 v2 := by
  have := h env; rw [h1, h2] at this; exact this

/-- **Transitivity of behavioral equivalence for open terms.**
    Requires `b` to lower wherever `a` does, so the chain is informative. -/
theorem behEq_trans {a b c : Expr}
    (hlb : ∀ env, (lowerTotal env a).isSome → (lowerTotal env b).isSome)
    (h12 : a ≋ b) (h23 : b ≋ c) : a ≋ c := by
  unfold BehEq; intro env
  cases ha : lowerTotal env a with
  | none => split <;> trivial
  | some ta =>
    obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp (hlb env (by simp [ha]))
    cases hc : lowerTotal env c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have ⟨herr12, hh12, hv12⟩ := behEq_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEq_extract hb hc h23
      refine ⟨fun ρ => (herr12 ρ).trans (herr23 ρ),
             fun ρ => (hh12 ρ).trans (hh23 ρ), ?_⟩
      intro k ρ v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := (hh12 ρ).mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k ρ v₁ v₂ hv₁ hv₂) (hv23 k ρ v₂ v₃ hv₂ hv₃)

/-- **Unconditional transitivity of refinement.**
    The compilation clause of `Refines a b` provides the lowering guarantee
    that `behEq_trans` needs, so no extra hypothesis is required. -/
theorem refines_trans {a b c : Expr}
    (h12 : Refines a b) (h23 : Refines b c) : Refines a c :=
  ⟨fun env ha => h23.1 env (h12.1 env ha),
   behEq_trans h12.1 h12.2 h23.2⟩

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
