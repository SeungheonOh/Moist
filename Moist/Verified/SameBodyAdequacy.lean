import Moist.Verified.Semantics
import Moist.Verified.StepLift

set_option linter.unusedSimpArgs false
set_option maxErrors 500

namespace Moist.Verified.SameBodyDecay

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.Verified.Semantics
open Moist.Verified.StepLift (liftState isActive step_liftState_active
  steps_liftState liftState_ne_halt liftState_eq_error)

/-! # Same-Body Adequacy via Step-Indexed Decay (CIU-style)

This module proves **same-body adequacy** — the theorem that a single closed
UPLC term evaluated under two observationally indistinguishable CEK environments
produces observationally indistinguishable results. The proof proceeds via a
CIU-style step-indexed logical relation with computation-step decay.

The key innovation is the `ValueEqD` relation, whose VLam/VDelay clauses build
a termination budget directly into the observation index:

* Standard `ValueEq` lets closure bodies run for arbitrary step counts, decoupling
  the observation budget from execution cost. This creates a dual recursion
  (over `k` and over `n`) that no lexicographic measure can tame.
* `ValueEqD` lets closure bodies run for at most `j ≤ k` steps, and the returned
  result has budget `j - n` where `n` is the actual step count. Execution
  literally consumes the budget.

With this design the fundamental lemma `stateEq_stepCompat` terminates under a
single lexicographic measure `(k, n)`, which `omega` discharges cleanly.

## File layout

* **§1 Parameterized relation types** — generic wrappers `EnvEqR`, `ListR`,
  `FrameEqR`, `StackEqR` that turn any value relation `R` into relations on
  environments, lists, frames, and stacks.

* **§2 The step-indexed value relation** — `ValueEqD` and `ListValueEqD`,
  their degenerate case (`valueEqD_zero`), and their monotonicity
  (`valueEqD_mono`, `listValueEqD_mono`).

* **§3 Structural state relations** — inductive wrappers `EnvEq`, `FrameEq`,
  `StackEq`, `StateEq` built on `ValueEqD`, with basic elimination
  (`envEq_lookup`) and extension (`envEq_extend`, `envEq_refl`) lemmas.

* **§4 Conversions to the parameterized form** — bridges between the local
  inductives and the parametric `*EqR` wrappers.

* **§5 Compatibility predicates** — `StepCompat` and `AsymCompat`, the
  semantic obligations that the fundamental lemma discharges, plus
  `stepCompat_error`, `stepCompat_halt`, and `asymCompat_step_lower`.

* **§6 Monotonicity of structural relations** — lowering the step index on
  `FrameEq`, `StackEq`, `EnvEq`, and `StateEq`.

* **§7 Value and list helpers** — `listValueEqD_length`, VCon detection
  (`vcon_eq_of_valueEqD_succ`), `applyArg` stack construction, list
  append / reverse / cons-reverse, etc.

* **§8 Builtin congruence** — `extractConsts_eq_of_listValueEqD`, per-builtin
  pass-through helpers (IfThenElse, ChooseUnit, Trace, ChooseList,
  ChooseData, MkCons), and the combined `evalBuiltin_cong_same_level`.

* **§9 The fundamental lemma** — `stateEq_stepCompat` by double induction on
  `(k, n)`, and its closure-body specialization `gen_fundamental_lemma`.

* **§10 Reflexivity** — standalone `valueEqD_refl` and `listValueEqD_refl`
  (breaking the `veq_refl` parameter), plus parameter-free wrappers
  `stateEq_stepCompat'`, `envEq_refl'`, `fundamental_lemma_proved'`.

* **§11 Equivalence with standard `ValueEq`** — the forward direction
  `(∀ k, ValueEqD k) → (∀ k, ValueEq k)` is the bridge to the project-wide
  observational relation. The backward direction is not provable and not
  needed.

* **§12 Same-body adequacy** — the main theorem.
-/

/-! ## §1 Parameterized relation types

These are generic wrappers that turn a value relation `R : CekValue → CekValue → Prop`
into relations on environments, lists, frames, and stacks. The instantiation
we use is `R = ValueEqD k` for a specific step index `k`. -/

/-- Environment relation parameterized by value relation `R`. -/
def EnvEqR (R : CekValue → CekValue → Prop) : CekEnv → CekEnv → Prop
  | .nil, .nil => True
  | .cons v1 e1, .cons v2 e2 => R v1 v2 ∧ EnvEqR R e1 e2
  | _, _ => False

/-- List relation parameterized by value relation `R`. -/
def ListR (R : CekValue → CekValue → Prop) : List CekValue → List CekValue → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListR R as bs
  | _, _ => False

/-- Frame relation parameterized by value relation `R`. -/
def FrameEqR (R : CekValue → CekValue → Prop) : Frame → Frame → Prop
  | .force, .force => True
  | .arg t1 env1, .arg t2 env2 => t1 = t2 ∧ EnvEqR R env1 env2
  | .funV v1, .funV v2 => R v1 v2
  | .applyArg v1, .applyArg v2 => R v1 v2
  | .constrField tag1 done1 todo1 env1, .constrField tag2 done2 todo2 env2 =>
      tag1 = tag2 ∧ todo1 = todo2 ∧ ListR R done1 done2 ∧ EnvEqR R env1 env2
  | .caseScrutinee alts1 env1, .caseScrutinee alts2 env2 =>
      alts1 = alts2 ∧ EnvEqR R env1 env2
  | _, _ => False

/-- Stack relation parameterized by value relation `R`. -/
def StackEqR (R : CekValue → CekValue → Prop) : Stack → Stack → Prop
  | [], [] => True
  | f1 :: s1, f2 :: s2 => FrameEqR R f1 f2 ∧ StackEqR R s1 s2
  | _, _ => False

/-! ## §2 The step-indexed value relation

`ValueEqD k v₁ v₂` is a CIU-style step-indexed relation. The VLam and VDelay
clauses quantify over arbitrary related arguments (VLam) and arbitrary related
stacks (both). The relation is bidirectional — each clause includes both
forward (side 1 → side 2) and backward (side 2 → side 1) transfer obligations.

**Step-count decay.** When a closure body runs for `n ≤ j` steps, the result has
budget `j - n`, strictly less than `j` for `n > 0`. This is the mechanism that
turns CEK steps into a termination witness.

**Why CIU.** The stack quantification (`StackEqR (ValueEqD j) stk₁ stk₂`) is what
makes the fundamental lemma provable without a separate stack-lifting argument.
When we need to apply a closure in a non-empty stack context, the clause already
covers it. -/

mutual
/-- Step-indexed value equivalence with CIU-style quantification.
    `ValueEqD k v₁ v₂` means v₁ and v₂ are equivalent for k remaining
    computation steps, tested in all stack contexts with related arguments. -/
def ValueEqD : Nat → CekValue → CekValue → Prop
  | 0, _, _ => True
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam body₁ env₁, .VLam body₂ env₂ =>
    ∀ j, j ≤ k →
      ∀ (arg₁ arg₂ : CekValue), ValueEqD j arg₁ arg₂ →
        ∀ (stk₁ stk₂ : Stack), StackEqR (ValueEqD j) stk₁ stk₂ →
          -- Forward: side 1 bounded at step n, side 2 bounded within j
          (∀ n, n ≤ j →
            steps n (.compute stk₁ (env₁.extend arg₁) body₁) = .error →
            ∃ m, m ≤ j ∧
              steps m (.compute stk₂ (env₂.extend arg₂) body₂) = .error) ∧
          (∀ v₁ n, n ≤ j →
            steps n (.compute stk₁ (env₁.extend arg₁) body₁) = .halt v₁ →
            ∃ v₂ m, m ≤ j ∧
              steps m (.compute stk₂ (env₂.extend arg₂) body₂) = .halt v₂ ∧
              ValueEqD (j - n) v₁ v₂) ∧
          -- Backward: side 2 bounded at step n, side 1 bounded within j
          (∀ n, n ≤ j →
            steps n (.compute stk₂ (env₂.extend arg₂) body₂) = .error →
            ∃ m, m ≤ j ∧
              steps m (.compute stk₁ (env₁.extend arg₁) body₁) = .error) ∧
          (∀ v₂ n, n ≤ j →
            steps n (.compute stk₂ (env₂.extend arg₂) body₂) = .halt v₂ →
            ∃ v₁ m, m ≤ j ∧
              steps m (.compute stk₁ (env₁.extend arg₁) body₁) = .halt v₁ ∧
              ValueEqD (j - n) v₁ v₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
    tag₁ = tag₂ ∧ ListValueEqD k fields₁ fields₂
  | k + 1, .VDelay body₁ env₁, .VDelay body₂ env₂ =>
    ∀ j, j ≤ k →
      ∀ (stk₁ stk₂ : Stack), StackEqR (ValueEqD j) stk₁ stk₂ →
        -- Forward
        (∀ n, n ≤ j →
          steps n (.compute stk₁ env₁ body₁) = .error →
          ∃ m, m ≤ j ∧
            steps m (.compute stk₂ env₂ body₂) = .error) ∧
        (∀ v₁ n, n ≤ j →
          steps n (.compute stk₁ env₁ body₁) = .halt v₁ →
          ∃ v₂ m, m ≤ j ∧
            steps m (.compute stk₂ env₂ body₂) = .halt v₂ ∧
            ValueEqD (j - n) v₁ v₂) ∧
        -- Backward
        (∀ n, n ≤ j →
          steps n (.compute stk₂ env₂ body₂) = .error →
          ∃ m, m ≤ j ∧
            steps m (.compute stk₁ env₁ body₁) = .error) ∧
        (∀ v₂ n, n ≤ j →
          steps n (.compute stk₂ env₂ body₂) = .halt v₂ →
          ∃ v₁ m, m ≤ j ∧
            steps m (.compute stk₁ env₁ body₁) = .halt v₁ ∧
            ValueEqD (j - n) v₁ v₂)
  | k + 1, .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
    b₁ = b₂ ∧ ListValueEqD (k + 1) args₁ args₂ ∧ ea₁ = ea₂
  | _, _, _ => False
termination_by k v₁ _ => (k, sizeOf v₁)

def ListValueEqD : Nat → List CekValue → List CekValue → Prop
  | _, [], [] => True
  | k, a :: as, b :: bs => ValueEqD k a b ∧ ListValueEqD k as bs
  | _, _, _ => False
termination_by k vs₁ _ => (k, sizeOf vs₁)
end

/-! ### Degenerate case and monotonicity -/

/-- ValueEqD 0 is trivially true. -/
theorem valueEqD_zero (v₁ v₂ : CekValue) : ValueEqD 0 v₁ v₂ := by
  simp [ValueEqD]

mutual
/-- ValueEqD is monotone: larger k is harder to satisfy.
    If equivalent for k steps, also equivalent for j ≤ k steps. -/
def valueEqD_mono : ∀ (k j : Nat), j ≤ k → ∀ v₁ v₂, ValueEqD k v₁ v₂ → ValueEqD j v₁ v₂
  | 0, 0, _, _, _, h => h
  | _ + 1, 0, _, _, _, _ => by simp [ValueEqD]
  | k + 1, j + 1, hjk, .VCon c₁, .VCon c₂, h => by
    simp only [ValueEqD] at h ⊢; exact h
  | k + 1, j + 1, hjk, .VLam body₁ env₁, .VLam body₂ env₂, h => by
    unfold ValueEqD at h ⊢
    intro j' hj' arg₁ arg₂ harg stk₁ stk₂ hstk
    exact h j' (by omega) arg₁ arg₂ harg stk₁ stk₂ hstk
  | k + 1, j + 1, hjk, .VDelay body₁ env₁, .VDelay body₂ env₂, h => by
    unfold ValueEqD at h ⊢
    intro j' hj' stk₁ stk₂ hstk
    exact h j' (by omega) stk₁ stk₂ hstk
  | k + 1, j + 1, hjk, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂, h => by
    unfold ValueEqD at h ⊢
    exact ⟨h.1, listValueEqD_mono k j (by omega) fields₁ fields₂ h.2⟩
  | k + 1, j + 1, hjk, .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂, h => by
    unfold ValueEqD at h ⊢
    exact ⟨h.1, listValueEqD_mono (k + 1) (j + 1) (by omega) args₁ args₂ h.2.1, h.2.2⟩
  -- Cross-constructor cases: False at k+1 implies False at j+1
  | _ + 1, _ + 1, _, .VCon _, .VLam _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VCon _, .VDelay _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VCon _, .VConstr _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VCon _, .VBuiltin _ _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VLam _ _, .VCon _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VLam _ _, .VDelay _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VLam _ _, .VConstr _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VLam _ _, .VBuiltin _ _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VDelay _ _, .VCon _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VDelay _ _, .VLam _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VDelay _ _, .VConstr _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VConstr _ _, .VCon _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VConstr _ _, .VLam _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VConstr _ _, .VDelay _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VCon _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VLam _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValueEqD] at h
  | _ + 1, _ + 1, _, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValueEqD] at h

def listValueEqD_mono : ∀ (k j : Nat), j ≤ k → ∀ (vs₁ vs₂ : List CekValue),
    ListValueEqD k vs₁ vs₂ → ListValueEqD j vs₁ vs₂
  | _, _, _, [], [], _ => by simp [ListValueEqD]
  | k, j, hle, a :: as, b :: bs, h => by
    simp only [ListValueEqD] at h ⊢
    exact ⟨valueEqD_mono k j hle a b h.1, listValueEqD_mono k j hle as bs h.2⟩
  | _, _, _, [], _ :: _, h => by simp [ListValueEqD] at h
  | _, _, _, _ :: _, [], h => by simp [ListValueEqD] at h
end

/-! ## §3 Structural state relations

The inductive relations `EnvEq k`, `FrameEq k`, `StackEq k`, `StateEq k`
package `ValueEqD k`-related CEK components into states. They are the
"concrete" relations on which `stateEq_stepCompat` is proved — the
`StepCompat` obligation is discharged on every such pair.

These relations mirror the parametric `*EqR` wrappers at the specific
instantiation `R = ValueEqD k`; §5 establishes the conversion. -/

/-! ### Environments -/

/-- Pointwise `ValueEqD k` on environments. -/
inductive EnvEq : Nat → CekEnv → CekEnv → Prop where
  | nil : EnvEq k .nil .nil
  | cons : ValueEqD k v1 v2 → EnvEq k e1 e2 →
      EnvEq k (.cons v1 e1) (.cons v2 e2)

theorem envEq_lookup {k : Nat} {env1 env2 : CekEnv} (h : EnvEq k env1 env2)
    (n : Nat) :
    match env1.lookup n, env2.lookup n with
    | some v1, some v2 => ValueEqD k v1 v2
    | none, none => True
    | _, _ => False := by
  induction h generalizing n with
  | nil => cases n <;> simp [CekEnv.lookup]
  | cons hv _ ih =>
    match n with
    | 0 => simp [CekEnv.lookup]
    | 1 => simp [CekEnv.lookup]; exact hv
    | n + 2 => simp only [CekEnv.lookup]; exact ih (n + 1)

theorem envEq_extend {k : Nat} {env1 env2 : CekEnv} (henv : EnvEq k env1 env2)
    {v1 v2 : CekValue} (hv : ValueEqD k v1 v2) :
    EnvEq k (env1.extend v1) (env2.extend v2) :=
  .cons hv henv

theorem envEq_refl {k : Nat} (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEqD j v v)
    (env : CekEnv) : EnvEq k env env := by
  cases env with
  | nil => exact .nil
  | cons v rest =>
    exact .cons (veq_refl k (Nat.le_refl k) v) (envEq_refl veq_refl rest)

/-! ### Frames, stacks, and states -/

/-- Same-term frame relation: frames share the same terms but have
    `ValueEqD k`-related values and `EnvEq k`-related environments. -/
inductive FrameEq (k : Nat) : Frame → Frame → Prop where
  | force : FrameEq k .force .force
  | arg : EnvEq k env1 env2 → FrameEq k (.arg t env1) (.arg t env2)
  | funV : ValueEqD k v1 v2 → FrameEq k (.funV v1) (.funV v2)
  | applyArg : ValueEqD k v1 v2 → FrameEq k (.applyArg v1) (.applyArg v2)
  | constrField : ListValueEqD k done1 done2 → EnvEq k env1 env2 →
      FrameEq k (.constrField tag done1 todo env1) (.constrField tag done2 todo env2)
  | caseScrutinee : EnvEq k env1 env2 →
      FrameEq k (.caseScrutinee alts env1) (.caseScrutinee alts env2)

/-- Pointwise frame relation on stacks. -/
inductive StackEq (k : Nat) : Stack → Stack → Prop where
  | nil : StackEq k [] []
  | cons : FrameEq k f1 f2 → StackEq k s1 s2 → StackEq k (f1 :: s1) (f2 :: s2)

/-- Same-term state relation with `ValueEqD k`-related values. -/
inductive StateEq (k : Nat) : State → State → Prop where
  | compute : StackEq k s1 s2 → EnvEq k env1 env2 →
      StateEq k (.compute s1 env1 t) (.compute s2 env2 t)
  | ret : StackEq k s1 s2 → ValueEqD k v1 v2 →
      StateEq k (.ret s1 v1) (.ret s2 v2)
  | error : StateEq k .error .error
  | halt : ValueEqD k v1 v2 →
      StateEq k (.halt v1) (.halt v2)

/-! ## §4 Conversions to the parameterized form

The structural inductives (`EnvEq`, `FrameEq`, `StackEq`) and the parametric
wrappers (`EnvEqR`, `FrameEqR`, `StackEqR`) describe the same relation at the
instantiation `R = ValueEqD k`. The conversions below let us switch between
the two forms as proof obligations demand. -/

/-- Convert local inductive `EnvEq k` to parametric `EnvEqR (ValueEqD k)`. -/
private theorem envEq_to_envEqR {k : Nat} {e1 e2 : CekEnv}
    (h : EnvEq k e1 e2) : EnvEqR (ValueEqD k) e1 e2 := by
  induction h with
  | nil => exact trivial
  | cons hv _ ih => exact ⟨hv, ih⟩

/-- Convert parametric `EnvEqR (ValueEqD k)` to local inductive `EnvEq k`. -/
private theorem envEqR_to_envEq : ∀ {k : Nat} {e1 e2 : CekEnv},
    EnvEqR (ValueEqD k) e1 e2 → EnvEq k e1 e2
  | _, .nil, .nil, _ => .nil
  | _, .cons _ _, .cons _ _, ⟨hv, he⟩ => .cons hv (envEqR_to_envEq he)
  | _, .nil, .cons _ _, h => absurd h (by simp [EnvEqR])
  | _, .cons _ _, .nil, h => absurd h (by simp [EnvEqR])

/-- Convert `ListValueEqD k` to `ListR (ValueEqD k)`. -/
private theorem listValueEqD_to_listR {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListValueEqD k vs1 vs2) : ListR (ValueEqD k) vs1 vs2 := by
  induction vs1 generalizing vs2 with
  | nil => cases vs2 with | nil => exact trivial | cons _ _ => simp [ListValueEqD] at h
  | cons a as ih =>
    cases vs2 with
    | nil => simp [ListValueEqD] at h
    | cons b bs =>
      simp only [ListValueEqD] at h
      exact ⟨h.1, ih h.2⟩

/-- Convert `ListR (ValueEqD k)` to `ListValueEqD k`. -/
private theorem listR_to_listValueEqD {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListR (ValueEqD k) vs1 vs2) : ListValueEqD k vs1 vs2 := by
  induction vs1 generalizing vs2 with
  | nil => cases vs2 with | nil => simp [ListValueEqD] | cons _ _ => simp [ListR] at h
  | cons a as ih =>
    cases vs2 with
    | nil => simp [ListR] at h
    | cons b bs =>
      simp only [ListR] at h
      simp only [ListValueEqD]
      exact ⟨h.1, ih h.2⟩

/-- Convert local inductive `FrameEq k` to parametric `FrameEqR (ValueEqD k)`. -/
private theorem frameEq_to_frameEqR {k : Nat} {f1 f2 : Frame}
    (h : FrameEq k f1 f2) : FrameEqR (ValueEqD k) f1 f2 := by
  cases h with
  | force => exact trivial
  | arg henv => exact ⟨rfl, envEq_to_envEqR henv⟩
  | funV hv => exact hv
  | applyArg hv => exact hv
  | constrField hdone henv =>
    exact ⟨rfl, rfl, listValueEqD_to_listR hdone, envEq_to_envEqR henv⟩
  | caseScrutinee henv => exact ⟨rfl, envEq_to_envEqR henv⟩

/-- Convert parametric `FrameEqR (ValueEqD k)` to local inductive `FrameEq k`. -/
private theorem frameEqR_to_frameEq {k : Nat} {f1 f2 : Frame}
    (h : FrameEqR (ValueEqD k) f1 f2) : FrameEq k f1 f2 := by
  cases f1 <;> cases f2 <;> simp [FrameEqR] at h
  case force.force => exact .force
  case arg.arg t1 e1 t2 e2 => exact h.1 ▸ .arg (envEqR_to_envEq h.2)
  case funV.funV => exact .funV h
  case applyArg.applyArg => exact .applyArg h
  case constrField.constrField tag1 d1 todo1 env1 tag2 d2 todo2 env2 =>
    exact h.1 ▸ h.2.1 ▸ .constrField (listR_to_listValueEqD h.2.2.1) (envEqR_to_envEq h.2.2.2)
  case caseScrutinee.caseScrutinee alts1 env1 alts2 env2 =>
    exact h.1 ▸ .caseScrutinee (envEqR_to_envEq h.2)

/-- Convert local inductive `StackEq k` to parametric `StackEqR (ValueEqD k)`. -/
private theorem stackEq_to_stackEqR {k : Nat} {s1 s2 : Stack}
    (h : StackEq k s1 s2) : StackEqR (ValueEqD k) s1 s2 := by
  induction h with
  | nil => exact trivial
  | cons hf _ ih => exact ⟨frameEq_to_frameEqR hf, ih⟩

/-- Convert parametric `StackEqR (ValueEqD k)` to local inductive `StackEq k`. -/
private theorem stackEqR_to_stackEq : ∀ {k : Nat} {s1 s2 : Stack},
    StackEqR (ValueEqD k) s1 s2 → StackEq k s1 s2
  | _, [], [], _ => .nil
  | _, _ :: _, _ :: _, ⟨hf, hs⟩ => .cons (frameEqR_to_frameEq hf) (stackEqR_to_stackEq hs)
  | _, [], _ :: _, h => absurd h (by simp [StackEqR])
  | _, _ :: _, [], h => absurd h (by simp [StackEqR])

/-! ## §5 Compatibility predicates

`StepCompat k n s₁ s₂` is the semantic obligation the fundamental lemma
discharges: after `n` steps of execution, side 1 and side 2 have produced
compatible results, where "compatible" means

* both error,
* both halt with `ValueEqD (k-n)`-related values, or
* both remain in compatible `compute`/`ret` states.

`AsymCompat k n s₁ s₂` is the bidirectional version that ships both
forward (side 1 errors/halts → side 2 follows) and backward transfer.
It is the form `stateEq_stepCompat` is proved about. -/

/-- Two states are `n`-step `k`-compatible when they agree on error/halt
    after exactly `n` steps, with `ValueEqD (k - n)` for halted values. -/
def StepCompat (k n : Nat) (s1 s2 : State) : Prop :=
  (steps n s1 = .error ↔ steps n s2 = .error) ∧
  (∀ v1, steps n s1 = .halt v1 →
    ∃ v2, steps n s2 = .halt v2 ∧ ValueEqD (k - n) v1 v2) ∧
  (∀ v2, steps n s2 = .halt v2 →
    ∃ v1, steps n s1 = .halt v1 ∧ ValueEqD (k - n) v1 v2)

/-- Asymmetric compatibility: each side's outcome at step `n` is matched
    by the other side within `k` steps (possibly at a different step count). -/
def AsymCompat (k n : Nat) (s1 s2 : State) : Prop :=
  (steps n s1 = .error → ∃ m, m ≤ k ∧ steps m s2 = .error) ∧
  (∀ v1, steps n s1 = .halt v1 →
    ∃ v2 m, m ≤ k ∧ steps m s2 = .halt v2 ∧ ValueEqD (k - n) v1 v2) ∧
  (steps n s2 = .error → ∃ m, m ≤ k ∧ steps m s1 = .error) ∧
  (∀ v2, steps n s2 = .halt v2 →
    ∃ v1 m, m ≤ k ∧ steps m s1 = .halt v1 ∧ ValueEqD (k - n) v1 v2)

theorem stepCompat_to_asymCompat {k n : Nat} (hn : n ≤ k) {s1 s2 : State}
    (h : StepCompat k n s1 s2) : AsymCompat k n s1 s2 :=
  ⟨fun he => ⟨n, hn, h.1.mp he⟩,
   fun v1 hv1 => let ⟨v2, hv2, hve⟩ := h.2.1 v1 hv1; ⟨v2, n, hn, hv2, hve⟩,
   fun he => ⟨n, hn, h.1.mpr he⟩,
   fun v2 hv2 => let ⟨v1, hv1, hve⟩ := h.2.2 v2 hv2; ⟨v1, n, hn, hv1, hve⟩⟩

/-- Level-dropping step for AsymCompat. -/
private theorem asymCompat_step_lower {k n : Nat} {s1 s2 : State}
    (h : AsymCompat k n (step s1) (step s2)) :
    AsymCompat (k + 1) (n + 1) s1 s2 := by
  have hlevel : k + 1 - (n + 1) = k - n := by omega
  constructor
  · intro he
    rw [show steps (n + 1) s1 = steps n (step s1) from rfl] at he
    obtain ⟨m, hm, hme⟩ := h.1 he
    exact ⟨m + 1, by omega, show steps (m + 1) s2 = .error from hme⟩
  constructor
  · intro v1 hv1
    rw [show steps (n + 1) s1 = steps n (step s1) from rfl] at hv1
    obtain ⟨v2, m, hm, hme, hve⟩ := h.2.1 v1 hv1
    exact ⟨v2, m + 1, by omega, show steps (m + 1) s2 = .halt v2 from hme, by rw [hlevel]; exact hve⟩
  constructor
  · intro he
    rw [show steps (n + 1) s2 = steps n (step s2) from rfl] at he
    obtain ⟨m, hm, hme⟩ := h.2.2.1 he
    exact ⟨m + 1, by omega, show steps (m + 1) s1 = .error from hme⟩
  · intro v2 hv2
    rw [show steps (n + 1) s2 = steps n (step s2) from rfl] at hv2
    obtain ⟨v1, m, hm, hme, hve⟩ := h.2.2.2 v2 hv2
    exact ⟨v1, m + 1, by omega, show steps (m + 1) s1 = .halt v1 from hme, by rw [hlevel]; exact hve⟩

theorem stepCompat_error (k n : Nat) :
    StepCompat k n .error .error := by
  refine ⟨Iff.rfl, fun v1 h => ?_, fun v2 h => ?_⟩
  · rw [steps_error] at h; exact absurd h (by simp)
  · rw [steps_error] at h; exact absurd h (by simp)

theorem stepCompat_halt (k n : Nat) (v1 v2 : CekValue) (hv : ValueEqD (k - n) v1 v2) :
    StepCompat k n (.halt v1) (.halt v2) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun w1 h => ?_, fun w2 h => ?_⟩
  · rw [steps_halt] at h; simp at h
  · rw [steps_halt] at h; simp at h
  · rw [steps_halt] at h; injection h with h; subst h; exact ⟨v2, steps_halt v2 n, hv⟩
  · rw [steps_halt] at h; injection h with h; subst h; exact ⟨v1, steps_halt v1 n, hv⟩

/-! ## §6 Monotonicity of structural relations

Lowering the step index of an `EnvEq` / `FrameEq` / `StackEq` / `StateEq`
relation: if `j ≤ k`, then anything true at level `k` is also true at
level `j`. These mirror `valueEqD_mono`. They appear after the
compatibility predicates because the fundamental lemma's compatibility
form does not itself need them — only the downstream reflexivity and
equivalence proofs do. -/

/-- Downgrade `FrameEq` from level `k` to any `j ≤ k`. -/
private theorem frameEq_mono {j k : Nat} (hjk : j ≤ k)
    {f1 f2 : Frame} (h : FrameEq k f1 f2) : FrameEq j f1 f2 := by
  cases h with
  | force => exact .force
  | arg henv =>
    exact .arg (by induction henv with
      | nil => exact .nil
      | cons hv _ ih => exact .cons (valueEqD_mono k j hjk _ _ hv) ih)
  | funV hv => exact .funV (valueEqD_mono k j hjk _ _ hv)
  | applyArg hv => exact .applyArg (valueEqD_mono k j hjk _ _ hv)
  | constrField hdone henv =>
    exact .constrField (listValueEqD_mono k j hjk _ _ hdone)
      (by induction henv with
        | nil => exact .nil
        | cons hv _ ih => exact .cons (valueEqD_mono k j hjk _ _ hv) ih)
  | caseScrutinee henv =>
    exact .caseScrutinee (by induction henv with
      | nil => exact .nil
      | cons hv _ ih => exact .cons (valueEqD_mono k j hjk _ _ hv) ih)

/-- Downgrade `StackEq` from level `k` to any `j ≤ k`. -/
private theorem stackEq_mono {j k : Nat} (hjk : j ≤ k)
    {s1 s2 : Stack} (h : StackEq k s1 s2) : StackEq j s1 s2 := by
  induction h with
  | nil => exact .nil
  | cons hf _ ih => exact .cons (frameEq_mono hjk hf) ih

/-- Downgrade `EnvEq` from level `k` to any `j ≤ k`. -/
private theorem envEq_mono {j k : Nat} (hjk : j ≤ k)
    {env1 env2 : CekEnv} (h : EnvEq k env1 env2) : EnvEq j env1 env2 := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons (valueEqD_mono k j hjk _ _ hv) ih

/-- Downgrade `StateEq` from level `k` to any `j ≤ k`. -/
private theorem stateEq_mono {j k : Nat} (hjk : j ≤ k)
    {s1 s2 : State} (h : StateEq k s1 s2) : StateEq j s1 s2 := by
  cases h with
  | compute hstk henv => exact .compute (stackEq_mono hjk hstk) (envEq_mono hjk henv)
  | ret hstk hv => exact .ret (stackEq_mono hjk hstk) (valueEqD_mono k j hjk _ _ hv)
  | error => exact .error
  | halt hv => exact .halt (valueEqD_mono k j hjk _ _ hv)

/-! ## §7 Value and list helpers

Small lemmas about `ValueEqD` on specific constructors, list lengths and
VCon detection, and manipulation lemmas for `ListValueEqD` (append,
reverse, cons-reverse). These are used throughout the fundamental lemma
proof to manipulate accumulated field lists and applyArg stacks. -/

/-- Helper: `ListValueEqD k` implies the lists have the same length. -/
private theorem listValueEqD_length {k : Nat} {vs1 vs2 : List CekValue}
    (h : ListValueEqD k vs1 vs2) : vs1.length = vs2.length := by
  induction vs1 generalizing vs2 with
  | nil => cases vs2 with | nil => rfl | cons _ _ => simp [ListValueEqD] at h
  | cons v1 rest1 ih =>
    cases vs2 with
    | nil => simp [ListValueEqD] at h
    | cons v2 rest2 => simp [ListValueEqD] at h; simp [List.length_cons, ih h.2]

/-- If `ValueEqD (k+1) (.VCon c) v`, then `v = .VCon c`. -/
private theorem vcon_eq_of_valueEqD_succ {k : Nat} {c : Const} {v : CekValue}
    (h : ValueEqD (k + 1) (.VCon c) v) : v = .VCon c := by
  cases v with
  | VCon c' => simp only [ValueEqD] at h; exact congrArg CekValue.VCon h.symm
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEqD] at h

/-- If `ValueEqD (k+1) v (.VCon c)`, then `v = .VCon c`. -/
private theorem vcon_eq_of_valueEqD_succ_right {k : Nat} {c : Const} {v : CekValue}
    (h : ValueEqD (k + 1) v (.VCon c)) : v = .VCon c := by
  cases v with
  | VCon c' => simp only [ValueEqD] at h; exact congrArg CekValue.VCon h
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEqD] at h

/-- For `ValueEqD (k+1) v₁ v₂`: either both are the same `VCon`, or neither is `VCon`. -/
private theorem valueEqD_succ_vcon_or_not {k : Nat} {v₁ v₂ : CekValue}
    (h : ValueEqD (k + 1) v₁ v₂) :
    (∃ c, v₁ = .VCon c ∧ v₂ = .VCon c) ∨
    ((∀ c, v₁ ≠ .VCon c) ∧ (∀ c, v₂ ≠ .VCon c)) := by
  cases v₁ with
  | VCon c =>
    have := vcon_eq_of_valueEqD_succ h
    exact .inl ⟨c, rfl, this⟩
  | VLam body env =>
    right
    refine ⟨?_, ?_⟩
    · intro c hh; cases hh
    · intro c hc
      subst hc
      exact absurd h (by simp [ValueEqD])
  | VDelay body env =>
    right
    refine ⟨?_, ?_⟩
    · intro c hh; cases hh
    · intro c hc
      subst hc
      exact absurd h (by simp [ValueEqD])
  | VConstr tag fields =>
    right
    refine ⟨?_, ?_⟩
    · intro c hh; cases hh
    · intro c hc
      subst hc
      exact absurd h (by simp [ValueEqD])
  | VBuiltin b args ea =>
    right
    refine ⟨?_, ?_⟩
    · intro c hh; cases hh
    · intro c hc
      subst hc
      exact absurd h (by simp [ValueEqD])

/-- Helper: mapping `Frame.applyArg` over `ListValueEqD k` gives `StackEq k`. -/
private theorem listValueEqD_map_applyArg_stackEq {k : Nat}
    {fs1 fs2 : List CekValue} (h : ListValueEqD k fs1 fs2) :
    StackEq k (fs1.map Frame.applyArg) (fs2.map Frame.applyArg) := by
  induction fs1 generalizing fs2 with
  | nil =>
    cases fs2 with | nil => exact .nil | cons _ _ => simp [ListValueEqD] at h
  | cons v1 rest1 ih =>
    cases fs2 with
    | nil => simp [ListValueEqD] at h
    | cons v2 rest2 =>
      simp [ListValueEqD] at h
      exact .cons (.applyArg h.1) (ih h.2)

/-- Helper: append two `StackEq k` stacks. -/
private theorem stackEq_append {k : Nat} {s1 s2 t1 t2 : Stack}
    (hs : StackEq k s1 s2) (ht : StackEq k t1 t2) :
    StackEq k (s1 ++ t1) (s2 ++ t2) := by
  induction hs with
  | nil => exact ht
  | cons hf _ ih => exact .cons hf ih

/-- Helper: reverse preserves `ListValueEqD k`. -/
private theorem listValueEqD_append {k : Nat} {a1 a2 b1 b2 : List CekValue}
    (ha : ListValueEqD k a1 a2) (hb : ListValueEqD k b1 b2) :
    ListValueEqD k (a1 ++ b1) (a2 ++ b2) := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simpa using hb
    | cons _ _ => simp [ListValueEqD] at ha
  | cons v1 rest1 ih =>
    cases a2 with
    | nil => simp [ListValueEqD] at ha
    | cons v2 rest2 =>
      simp only [ListValueEqD] at ha
      simp only [List.cons_append, ListValueEqD]
      exact ⟨ha.1, ih ha.2⟩

private theorem listValueEqD_reverse {k : Nat} {a1 a2 : List CekValue}
    (h : ListValueEqD k a1 a2) :
    ListValueEqD k a1.reverse a2.reverse := by
  induction a1 generalizing a2 with
  | nil =>
    cases a2 with
    | nil => simp [ListValueEqD]
    | cons _ _ => simp [ListValueEqD] at h
  | cons v1 rest1 ih =>
    cases a2 with
    | nil => simp [ListValueEqD] at h
    | cons v2 rest2 =>
      simp only [ListValueEqD] at h
      simp only [List.reverse_cons]
      exact listValueEqD_append (ih h.2) (by simp [ListValueEqD]; exact h.1)

/-- Helper: `ListValueEqD k` for cons-then-reverse. -/
private theorem listValueEqD_cons_rev {k : Nat} {v1 v2 : CekValue}
    {done1 done2 : List CekValue}
    (hv : ValueEqD k v1 v2) (hd : ListValueEqD k done1 done2) :
    ListValueEqD k ((v1 :: done1).reverse) ((v2 :: done2).reverse) := by
  simp only [List.reverse_cons]
  exact listValueEqD_append (listValueEqD_reverse hd) (by simp [ListValueEqD]; exact hv)

/-- `extractConsts` agreement from `ListValueEqD (k+1)`. -/
private theorem extractConsts_eq_of_listValueEqD {k : Nat} {args1 args2 : List CekValue}
    (h : ListValueEqD (k + 1) args1 args2) :
    Moist.CEK.extractConsts args1 = Moist.CEK.extractConsts args2 := by
  induction args1 generalizing args2 with
  | nil =>
    cases args2 with | nil => rfl | cons _ _ => simp [ListValueEqD] at h
  | cons a1 rest1 ih =>
    cases args2 with
    | nil => simp [ListValueEqD] at h
    | cons a2 rest2 =>
      simp only [ListValueEqD] at h
      have hv := h.1
      have ht := h.2
      cases a1 with
      | VCon c1 =>
        cases a2 with
        | VCon c2 =>
          simp only [ValueEqD] at hv; subst hv
          simp only [Moist.CEK.extractConsts]; rw [ih ht]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEqD])
      | VLam _ _ =>
        cases a2 with
        | VLam _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEqD])
      | VDelay _ _ =>
        cases a2 with
        | VDelay _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEqD])
      | VConstr _ _ =>
        cases a2 with
        | VConstr _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
          exact absurd hv (by simp [ValueEqD])
      | VBuiltin _ _ _ =>
        cases a2 with
        | VBuiltin _ _ _ => simp only [Moist.CEK.extractConsts]
        | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
          exact absurd hv (by simp [ValueEqD])

/-! ## §8 Builtin congruence

Pass-through builtins (IfThenElse, ChooseUnit, Trace, ChooseList, ChooseData,
MkCons) return a subset of their arguments unchanged based on a discriminant
argument that must be a specific `VCon`. They need a direct congruence
argument because the returned value is not itself a `VCon` and so is not
captured by the constant-extraction stage of `evalBuiltin`.

The per-builtin lemmas (`ifThenElse_cong_same_level`, etc.) each handle
one builtin by pattern matching on the argument shape. They use
`passThroughMatchK` as a uniform output type. `evalBuiltinPassThrough_cong_same_level`
dispatches on the builtin, and `evalBuiltin_cong_same_level` combines
the pass-through case with the constant-extraction case via
`extractConsts_eq_of_listValueEqD`. -/

/-! ### Per-builtin pass-through helpers -/

/-- Combined isNone agreement + value agreement, packaged as a single match
    to make per-builtin proofs easier to write. -/
private def passThroughMatchK (k : Nat) (r1 r2 : Option CekValue) : Prop :=
  match r1, r2 with
  | some v₁, some v₂ => ValueEqD (k + 1) v₁ v₂
  | none, none => True
  | _, _ => False

private theorem passThroughMatchK_to_pair {k : Nat} {b : BuiltinFun}
    {args1 args2 : List CekValue}
    (h : passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough b args1)
                              (Moist.CEK.evalBuiltinPassThrough b args2)) :
    (Moist.CEK.evalBuiltinPassThrough b args1).isNone =
    (Moist.CEK.evalBuiltinPassThrough b args2).isNone ∧
    (∀ r1 r2, Moist.CEK.evalBuiltinPassThrough b args1 = some r1 →
              Moist.CEK.evalBuiltinPassThrough b args2 = some r2 →
              ValueEqD (k + 1) r1 r2) := by
  refine ⟨?_, ?_⟩
  · cases h1 : Moist.CEK.evalBuiltinPassThrough b args1 with
    | some _ =>
      cases h2 : Moist.CEK.evalBuiltinPassThrough b args2 with
      | some _ => simp
      | none => simp [passThroughMatchK, h1, h2] at h
    | none =>
      cases h2 : Moist.CEK.evalBuiltinPassThrough b args2 with
      | some _ => simp [passThroughMatchK, h1, h2] at h
      | none => simp
  · intro r1 r2 hr1 hr2
    rw [hr1, hr2] at h
    exact h

private theorem ifThenElse_cong_same_level (k : Nat) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2) :
    passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough .IfThenElse args1)
                        (Moist.CEK.evalBuiltinPassThrough .IfThenElse args2) := by
  -- args1, args2 might be of any shape; only [_, _, .VCon (.Bool _)] matches.
  match args1, args2, hargs with
  | [], [], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [], _ :: _, h => simp [ListValueEqD] at h
  | _ :: _, [], h => simp [ListValueEqD] at h
  | [_], [_], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_], _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _, [_], h => simp [ListValueEqD] at h
  | [_, _], [_, _], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _], _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, [_, _], h => simp [ListValueEqD] at h
  | [e1, t1, c1], [e2, t2, c2], h =>
    simp only [ListValueEqD] at h
    obtain ⟨he, ht, hc, _⟩ := h
    rcases valueEqD_succ_vcon_or_not hc with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
    · cases c <;>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
        rename_i b <;> cases b <;>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
        first | exact he | exact ht
    · have h1 : Moist.CEK.evalBuiltinPassThrough .IfThenElse [e1, t1, c1] = none := by
        cases c1 with
        | VCon c => exact absurd rfl (hne1 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      have h2 : Moist.CEK.evalBuiltinPassThrough .IfThenElse [e2, t2, c2] = none := by
        cases c2 with
        | VCon c => exact absurd rfl (hne2 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      simp [passThroughMatchK, h1, h2]
  | [_, _, _], _ :: _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _, [_, _, _], h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _, _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]

private theorem chooseUnit_cong_same_level (k : Nat) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2) :
    passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough .ChooseUnit args1)
                        (Moist.CEK.evalBuiltinPassThrough .ChooseUnit args2) := by
  match args1, args2, hargs with
  | [], [], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [], _ :: _, h => simp [ListValueEqD] at h
  | _ :: _, [], h => simp [ListValueEqD] at h
  | [_], [_], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_], _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _, [_], h => simp [ListValueEqD] at h
  | [r1, c1], [r2, c2], h =>
    simp only [ListValueEqD] at h
    obtain ⟨hr, hc, _⟩ := h
    rcases valueEqD_succ_vcon_or_not hc with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
    · cases c <;>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
        exact hr
    · have h1 : Moist.CEK.evalBuiltinPassThrough .ChooseUnit [r1, c1] = none := by
        cases c1 with
        | VCon c => exact absurd rfl (hne1 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      have h2 : Moist.CEK.evalBuiltinPassThrough .ChooseUnit [r2, c2] = none := by
        cases c2 with
        | VCon c => exact absurd rfl (hne2 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      simp [passThroughMatchK, h1, h2]
  | [_, _], _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, [_, _], h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]

private theorem trace_cong_same_level (k : Nat) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2) :
    passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough .Trace args1)
                        (Moist.CEK.evalBuiltinPassThrough .Trace args2) := by
  match args1, args2, hargs with
  | [], [], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [], _ :: _, h => simp [ListValueEqD] at h
  | _ :: _, [], h => simp [ListValueEqD] at h
  | [_], [_], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_], _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _, [_], h => simp [ListValueEqD] at h
  | [r1, c1], [r2, c2], h =>
    simp only [ListValueEqD] at h
    obtain ⟨hr, hc, _⟩ := h
    rcases valueEqD_succ_vcon_or_not hc with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
    · cases c <;>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
        exact hr
    · have h1 : Moist.CEK.evalBuiltinPassThrough .Trace [r1, c1] = none := by
        cases c1 with
        | VCon c => exact absurd rfl (hne1 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      have h2 : Moist.CEK.evalBuiltinPassThrough .Trace [r2, c2] = none := by
        cases c2 with
        | VCon c => exact absurd rfl (hne2 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      simp [passThroughMatchK, h1, h2]
  | [_, _], _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, [_, _], h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]

private theorem chooseList_cong_same_level (k : Nat) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2) :
    passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough .ChooseList args1)
                        (Moist.CEK.evalBuiltinPassThrough .ChooseList args2) := by
  match args1, args2, hargs with
  | [], [], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [], _ :: _, h => simp [ListValueEqD] at h
  | _ :: _, [], h => simp [ListValueEqD] at h
  | [_], [_], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_], _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _, [_], h => simp [ListValueEqD] at h
  | [_, _], [_, _], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _], _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, [_, _], h => simp [ListValueEqD] at h
  | [cs1, n1, c1], [cs2, n2, c2], h =>
    simp only [ListValueEqD] at h
    obtain ⟨hcs, hn, hc, _⟩ := h
    rcases valueEqD_succ_vcon_or_not hc with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
    · cases c <;>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
        (try (rename_i l; cases hl : l.isEmpty <;>
              simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough, hl] <;>
              first | exact hcs | exact hn))
    · have h1 : Moist.CEK.evalBuiltinPassThrough .ChooseList [cs1, n1, c1] = none := by
        cases c1 with
        | VCon c => exact absurd rfl (hne1 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      have h2 : Moist.CEK.evalBuiltinPassThrough .ChooseList [cs2, n2, c2] = none := by
        cases c2 with
        | VCon c => exact absurd rfl (hne2 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      simp [passThroughMatchK, h1, h2]
  | [_, _, _], _ :: _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _, [_, _, _], h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _, _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]

private theorem chooseData_cong_same_level (k : Nat) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2) :
    passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough .ChooseData args1)
                        (Moist.CEK.evalBuiltinPassThrough .ChooseData args2) := by
  match args1, args2, hargs with
  | [], [], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [], _ :: _, h => simp [ListValueEqD] at h
  | _ :: _, [], h => simp [ListValueEqD] at h
  | [_], [_], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_], _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _, [_], h => simp [ListValueEqD] at h
  | [_, _], [_, _], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _], _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, [_, _], h => simp [ListValueEqD] at h
  | [_, _, _], [_, _, _], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _, _], _ :: _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _, [_, _, _], h => simp [ListValueEqD] at h
  | [_, _, _, _], [_, _, _, _], _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _, _, _], _ :: _ :: _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _], h => simp [ListValueEqD] at h
  | [_, _, _, _, _], [_, _, _, _, _], _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _, _, _, _], _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _], h => simp [ListValueEqD] at h
  | [b1, i1, l1, m1, cn1, c1], [b2, i2, l2, m2, cn2, c2], h =>
    simp only [ListValueEqD] at h
    obtain ⟨hb, hi, hl, hm, hcn, hc, _⟩ := h
    rcases valueEqD_succ_vcon_or_not hc with ⟨c, rfl, rfl⟩ | ⟨hne1, hne2⟩
    · cases c <;>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
        (try (rename_i d; cases d <;>
              simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough] <;>
              first | exact hb | exact hi | exact hl | exact hm | exact hcn))
    · have h1 : Moist.CEK.evalBuiltinPassThrough .ChooseData [b1, i1, l1, m1, cn1, c1] = none := by
        cases c1 with
        | VCon c => exact absurd rfl (hne1 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      have h2 : Moist.CEK.evalBuiltinPassThrough .ChooseData [b2, i2, l2, m2, cn2, c2] = none := by
        cases c2 with
        | VCon c => exact absurd rfl (hne2 c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl
      simp [passThroughMatchK, h1, h2]
  | [_, _, _, _, _, _], _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _, _], h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]

private theorem mkCons_cong_same_level (k : Nat) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2) :
    passThroughMatchK k (Moist.CEK.evalBuiltinPassThrough .MkCons args1)
                        (Moist.CEK.evalBuiltinPassThrough .MkCons args2) := by
  match args1, args2, hargs with
  | [], [], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [], _ :: _, h => simp [ListValueEqD] at h
  | _ :: _, [], h => simp [ListValueEqD] at h
  | [_], [_], _ => simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_], _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _, [_], h => simp [ListValueEqD] at h
  | [tail1, elem1], [tail2, elem2], h =>
    simp only [ListValueEqD] at h
    obtain ⟨ht, he, _⟩ := h
    -- tail must be VCon (.ConstList _) on both sides, else passThrough = none.
    cases tail1 with
    | VCon c1 =>
      have htail2 := vcon_eq_of_valueEqD_succ ht
      subst htail2
      cases c1 with
      | ConstList l =>
        -- elem must be VCon for both sides to give some
        cases elem1 with
        | VCon ec1 =>
          have helem2 := vcon_eq_of_valueEqD_succ he
          subst helem2
          simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough, ValueEqD]
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          cases elem2 with
          | VCon ec2 => exact absurd he (by simp [ValueEqD])
          | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
            simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
      | Integer _ | ByteString _ | String _ | Unit | Bool _ | ConstDataList _
      | ConstPairDataList _ | Pair _ | PairData _ | Data _ | ConstArray _
      | Bls12_381_G1_element | Bls12_381_G2_element | Bls12_381_MlResult =>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
    | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
      cases tail2 with
      | VCon c2 => exact absurd ht (by simp [ValueEqD])
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]
  | [_, _], _ :: _ :: _ :: _, h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, [_, _], h => simp [ListValueEqD] at h
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ =>
    simp [passThroughMatchK, Moist.CEK.evalBuiltinPassThrough]

/-- evalBuiltinPassThrough isNone agreement and same-level value agreement
    from ListValueEqD (k+1). -/
private theorem evalBuiltinPassThrough_cong_same_level {k : Nat}
    (b : BuiltinFun) {args1 args2 : List CekValue}
    (hargs : ListValueEqD (k + 1) args1 args2)
    (_veq_refl_k : ∀ v : CekValue, ValueEqD (k + 1) v v) :
    (Moist.CEK.evalBuiltinPassThrough b args1).isNone =
    (Moist.CEK.evalBuiltinPassThrough b args2).isNone ∧
    (∀ r1 r2, Moist.CEK.evalBuiltinPassThrough b args1 = some r1 →
              Moist.CEK.evalBuiltinPassThrough b args2 = some r2 →
              ValueEqD (k + 1) r1 r2) := by
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                 b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact passThroughMatchK_to_pair (ifThenElse_cong_same_level k hargs)
    · exact passThroughMatchK_to_pair (chooseUnit_cong_same_level k hargs)
    · exact passThroughMatchK_to_pair (trace_cong_same_level k hargs)
    · exact passThroughMatchK_to_pair (chooseData_cong_same_level k hargs)
    · exact passThroughMatchK_to_pair (chooseList_cong_same_level k hargs)
    · exact passThroughMatchK_to_pair (mkCons_cong_same_level k hargs)
  · have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                   b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
      ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
       fun h => hb (h ▸ .inr (.inr (.inl rfl))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
    rw [Moist.CEK.evalBuiltinPassThrough_none_of_not_passthrough b args1 hb_not,
        Moist.CEK.evalBuiltinPassThrough_none_of_not_passthrough b args2 hb_not]
    exact ⟨rfl, fun _ _ h => by simp at h⟩

private theorem evalBuiltin_cong_same_level (k : Nat) (b : BuiltinFun)
    (args1 args2 : List CekValue)
    (hargs : ListValueEqD (k + 1) args1 args2)
    (veq_refl_k : ∀ v : CekValue, ValueEqD (k + 1) v v) :
    (Moist.CEK.evalBuiltin b args1 = none ↔
     Moist.CEK.evalBuiltin b args2 = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b args1 = some r1 →
              Moist.CEK.evalBuiltin b args2 = some r2 →
              ValueEqD (k + 1) r1 r2) := by
  have ⟨hpt_isNone, hpt_val⟩ := evalBuiltinPassThrough_cong_same_level b hargs veq_refl_k
  have hec := extractConsts_eq_of_listValueEqD hargs
  constructor
  · -- none ↔ none: derive from passThrough agreement + extractConsts agreement
    cases hp1 : Moist.CEK.evalBuiltinPassThrough b args1 with
    | some v1 =>
      have hp2_some : ∃ v2, Moist.CEK.evalBuiltinPassThrough b args2 = some v2 := by
        rw [show (Moist.CEK.evalBuiltinPassThrough b args1).isNone = false from by simp [hp1]] at hpt_isNone
        cases hp2 : Moist.CEK.evalBuiltinPassThrough b args2 with
        | some v2 => exact ⟨v2, rfl⟩
        | none => simp [hp2] at hpt_isNone
      obtain ⟨v2, hp2⟩ := hp2_some
      simp [Moist.CEK.evalBuiltin, hp1, hp2]
    | none =>
      have hp2_none : Moist.CEK.evalBuiltinPassThrough b args2 = none := by
        rw [show (Moist.CEK.evalBuiltinPassThrough b args1).isNone = true from by simp [hp1]] at hpt_isNone
        cases hp2 : Moist.CEK.evalBuiltinPassThrough b args2 with
        | none => rfl
        | some _ => simp [hp2] at hpt_isNone
      simp [Moist.CEK.evalBuiltin, hp1, hp2_none, hec]
  · -- Value agreement at level k+1
    intro r1 r2 hr1 hr2
    simp only [Moist.CEK.evalBuiltin] at hr1 hr2
    cases hp1 : Moist.CEK.evalBuiltinPassThrough b args1 with
    | some v1 =>
      rw [show (Moist.CEK.evalBuiltinPassThrough b args1).isNone = false from by simp [hp1]] at hpt_isNone
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b args2 with
      | none => simp [hp2] at hpt_isNone
      | some v2 =>
        rw [hp1] at hr1; rw [hp2] at hr2
        injection hr1 with hr1; injection hr2 with hr2
        subst hr1; subst hr2
        exact hpt_val v1 v2 hp1 hp2
    | none =>
      rw [hp1] at hr1
      rw [show (Moist.CEK.evalBuiltinPassThrough b args1).isNone = true from by simp [hp1]] at hpt_isNone
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b args2 with
      | some v2 => simp [hp2] at hpt_isNone
      | none =>
        rw [hp2] at hr2
        rw [hec] at hr1
        cases hc : Moist.CEK.extractConsts args2 with
        | none => simp [hc] at hr1
        | some cs =>
          simp only [hc] at hr1 hr2
          cases hbc : Moist.CEK.evalBuiltinConst b cs with
          | none => simp [hbc] at hr1
          | some c =>
            simp only [hbc] at hr1 hr2
            injection hr1 with hr1; injection hr2 with hr2
            subst hr1; subst hr2
            exact veq_refl_k _

/-! ## §9 The fundamental lemma

`stateEq_stepCompat` is the core of this module. Given a `StateEq k`
relating two CEK states and a step budget `n ≤ k`, it shows that running
both states for `n` steps produces compatible outcomes with `ValueEqD (k-n)`
on any halt values.

The proof is a large case analysis on the head frame of the state, using:

* **Decreasing `n`** for every non-closure CEK step (load Var, push frame,
  enter Force, etc.).
* **Decreasing `k`** only at VLam/VDelay body entry, where the relation's
  own clause supplies a bound `j ≤ k-1` for the body.
* **Step-count decay `k - n`** in the halt case, so the returned `ValueEqD`
  has a budget that reflects how much of the fuel was consumed.

Termination is by the lexicographic measure `(k, n)`, and Lean discharges
every decreasing obligation with `omega`.

`gen_fundamental_lemma` is the specialization to closure-body execution
that downstream code consumes. -/

/-- **Generalized fundamental lemma**: if two states are `StateEq k`-related,
    they are `AsymCompat k n` for `n ≤ k`.

    Proved by well-founded induction on `(k, n)` lexicographically. -/
theorem stateEq_stepCompat
    (k n : Nat) (hn : n ≤ k)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEqD j v v)
    {s1 s2 : State} (hrel : StateEq k s1 s2) :
    AsymCompat k n s1 s2 := by
  have sc_to_ac : ∀ {k' n' : Nat} {s1' s2' : State}, n' ≤ k' →
      StepCompat k' n' s1' s2' → AsymCompat k' n' s1' s2' :=
    fun hn' h => stepCompat_to_asymCompat hn' h
  match n with
  | 0 =>
    simp only [AsymCompat, steps]
    cases hrel with
    | error =>
      exact ⟨fun _ => ⟨0, hn, rfl⟩, fun v h => by simp at h,
             fun _ => ⟨0, hn, rfl⟩, fun v h => by simp at h⟩
    | halt hv =>
      exact ⟨fun h => by simp at h,
             fun v1 h => by injection h with h; subst h; exact ⟨_, 0, hn, rfl, hv⟩,
             fun h => by simp at h,
             fun v2 h => by injection h with h; subst h; exact ⟨_, 0, hn, rfl, hv⟩⟩
    | compute _ _ =>
      exact ⟨fun h => by simp at h, fun v h => by simp at h,
             fun h => by simp at h, fun v h => by simp at h⟩
    | ret _ _ =>
      exact ⟨fun h => by simp at h, fun v h => by simp at h,
             fun h => by simp at h, fun v h => by simp at h⟩
  | n + 1 =>
    obtain ⟨km, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hn' : n ≤ km := by omega
    apply asymCompat_step_lower
    have call_n : ∀ {s1' s2' : State}, StateEq km s1' s2' → AsymCompat km n s1' s2' :=
      fun hrel' => stateEq_stepCompat km n hn' (fun j hj v => veq_refl j (by omega) v) hrel'
    have call_n' : ∀ {s1' s2' : State}, StateEq (km + 1) s1' s2' → AsymCompat km n s1' s2' :=
      fun hrel' => call_n (stateEq_mono (by omega) hrel')
    -- Helper: build ValueEqD (km+1) for same-body VLam
    have vlam_valueEqD : ∀ {body : Term} {env1 env2 : CekEnv},
        EnvEq (km + 1) env1 env2 → ValueEqD (km + 1) (.VLam body env1) (.VLam body env2) := by
      intro body env1 env2 henv
      unfold ValueEqD
      intro j hj arg1 arg2 harg stk1 stk2 hstk
      have henv_j : EnvEq j env1 env2 := envEq_mono (by omega) henv
      have henv1_j : EnvEq j (env1.extend arg1) (env2.extend arg2) := envEq_extend henv_j harg
      have hstk_j : StackEq j stk1 stk2 := stackEqR_to_stackEq hstk
      have hrel_j : StateEq j (.compute stk1 (env1.extend arg1) body)
          (.compute stk2 (env2.extend arg2) body) :=
        .compute hstk_j henv1_j
      exact ⟨fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).1 he,
             fun v1 n' hn' hv1 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.1 v1 hv1,
             fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.1 he,
             fun v2 n' hn' hv2 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.2 v2 hv2⟩
    -- Helper: build ValueEqD (km+1) for same-body VDelay
    have vdelay_valueEqD : ∀ {body : Term} {env1 env2 : CekEnv},
        EnvEq (km + 1) env1 env2 → ValueEqD (km + 1) (.VDelay body env1) (.VDelay body env2) := by
      intro body env1 env2 henv
      unfold ValueEqD
      intro j hj stk1 stk2 hstk
      have henv_j : EnvEq j env1 env2 := envEq_mono (by omega) henv
      have hstk_j : StackEq j stk1 stk2 := stackEqR_to_stackEq hstk
      have hrel_j : StateEq j (.compute stk1 env1 body)
          (.compute stk2 env2 body) :=
        .compute hstk_j henv_j
      exact ⟨fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).1 he,
             fun v1 n' hn' hv1 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.1 v1 hv1,
             fun n' hn' he => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.1 he,
             fun v2 n' hn' hv2 => (stateEq_stepCompat j n' hn' (fun i hi v => veq_refl i (by omega) v) hrel_j).2.2.2 v2 hv2⟩
    -- Helper: build ValueEqD (km+1) for same-constructor VConstr from ListValueEqD km
    have vconstr_valueEqD : ∀ {tag : Nat} {fs1 fs2 : List CekValue},
        ListValueEqD km fs1 fs2 → ValueEqD (km + 1) (.VConstr tag fs1) (.VConstr tag fs2) := by
      intro tag fs1 fs2 hfs
      unfold ValueEqD
      exact ⟨rfl, hfs⟩
    -- Helper: ListValueEqD reflexivity using veq_refl
    have listValueEqD_refl_local : ∀ (j : Nat) (_ : j ≤ km + 1) (vs : List CekValue), ListValueEqD j vs vs := by
      intro j hj vs
      induction vs with
      | nil => simp [ListValueEqD]
      | cons v rest ih => simp only [ListValueEqD]; exact ⟨veq_refl j (by omega) v, ih⟩
    -- Now case split on hrel
    cases hrel with
    | error =>
      simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
    | halt hv =>
      simp only [step]
      exact sc_to_ac hn' (stepCompat_halt km n _ _ (valueEqD_mono (km + 1) (km - n) (by omega) _ _ hv))
    | compute hstk henv =>
      rename_i s1' s2' env1 env2 t
      cases t with
      | Var idx =>
        have hlookup := envEq_lookup henv idx
        simp only [step]
        generalize h1 : env1.lookup idx = r1
        generalize h2 : env2.lookup idx = r2
        rw [h1, h2] at hlookup
        match r1, r2, hlookup with
        | some v1, some v2, hveq => exact call_n' (.ret hstk hveq)
        | none, none, _ => exact sc_to_ac hn' (stepCompat_error km n)
        | some _, none, hf => exact hf.elim
        | none, some _, hf => exact hf.elim
      | Constant pair =>
        obtain ⟨c, _⟩ := pair
        simp only [step]
        exact call_n' (.ret hstk (veq_refl (km + 1) (Nat.le_refl _) (.VCon c)))
      | Builtin b =>
        simp only [step]
        exact call_n' (.ret hstk (veq_refl (km + 1) (Nat.le_refl _) (.VBuiltin b [] _)))
      | Lam _ body =>
        simp only [step]
        exact call_n' (.ret hstk (vlam_valueEqD henv))
      | Delay body =>
        simp only [step]
        exact call_n' (.ret hstk (vdelay_valueEqD henv))
      | Force e =>
        simp only [step]
        exact call_n' (.compute (.cons .force hstk) henv)
      | Apply f x =>
        simp only [step]
        exact call_n' (.compute (.cons (.arg henv) hstk) henv)
      | Error =>
        simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
      | Constr tag args =>
        cases args with
        | nil =>
          simp only [step]
          exact call_n' (.ret hstk (veq_refl (km + 1) (Nat.le_refl _) (.VConstr tag [])))
        | cons m ms =>
          simp only [step]
          exact call_n' (.compute
            (.cons (.constrField (by simp [ListValueEqD]) henv) hstk) henv)
      | Case scrut alts =>
        simp only [step]
        exact call_n' (.compute (.cons (.caseScrutinee henv) hstk) henv)
    | ret hstk hv =>
      rename_i s1' s2' v1 v2
      cases hstk with
      | nil =>
        simp only [step]
        exact sc_to_ac hn' (stepCompat_halt km n v1 v2 (valueEqD_mono (km + 1) (km - n) (by omega) _ _ hv))
      | cons hframe hrest =>
        rename_i f1 f2 rest1 rest2
        cases hframe with
        | force =>
          cases v1 with
          | VDelay body1 env1 =>
            cases v2 with
            | VDelay body2 env2 =>
              simp only [step]
              unfold ValueEqD at hv
              have hrest_km : StackEq km rest1 rest2 := stackEq_mono (by omega) hrest
              have hclause := hv km (by omega) rest1 rest2 (stackEq_to_stackEqR hrest_km)
              exact ⟨hclause.1 n hn',
                     fun v1' hv1' => hclause.2.1 v1' n hn' hv1',
                     hclause.2.2.1 n hn',
                     fun v2' hv2' => hclause.2.2.2 v2' n hn' hv2'⟩
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEqD at hv
              obtain ⟨hb, hargs, hea⟩ := hv
              subst hb; subst hea
              simp only [step]
              cases h_head : ea1.head with
              | argQ =>
                simp only [h_head]
                cases h_tail : ea1.tail with
                | none =>
                  simp only [h_tail]
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level km b1 args1 args2 hargs
                      (veq_refl (km + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 args1 with
                  | none =>
                    simp only [h_eval1, heval_none.mp h_eval1]
                    exact sc_to_ac hn' (stepCompat_error km n)
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 args2 with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only [h_eval1, h_eval2]
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_n' (.ret hrest hveq)
                | some ea_rest =>
                  simp only [h_tail]
                  have hvb : ValueEqD (km + 1) (.VBuiltin b1 args1 ea_rest) (.VBuiltin b1 args2 ea_rest) := by
                    unfold ValueEqD; exact ⟨rfl, hargs, rfl⟩
                  exact call_n' (.ret hrest hvb)
              | argV =>
                simp only [h_head]
                exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VCon _ =>
            cases v2 with
            | VCon _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
        | arg henv_arg =>
          simp only [step]
          exact call_n' (.compute (.cons (.funV hv) hrest) henv_arg)
        | funV hfv =>
          rename_i vf1 vf2
          cases vf1 with
          | VLam body1 env1 =>
            cases vf2 with
            | VLam body2 env2 =>
              simp only [step]
              unfold ValueEqD at hfv
              have hv_km : ValueEqD km v1 v2 := valueEqD_mono (km + 1) km (by omega) v1 v2 hv
              have hrest_km : StackEq km rest1 rest2 := stackEq_mono (by omega) hrest
              have hclause := hfv km (by omega) v1 v2 hv_km rest1 rest2 (stackEq_to_stackEqR hrest_km)
              exact ⟨hclause.1 n hn',
                     fun v1' hv1' => hclause.2.1 v1' n hn' hv1',
                     hclause.2.2.1 n hn',
                     fun v2' hv2' => hclause.2.2.2 v2' n hn' hv2'⟩
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hfv; exact hfv.elim
          | VBuiltin b1 args1 ea1 =>
            cases vf2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEqD at hfv
              obtain ⟨hb, hargs, hea⟩ := hfv
              subst hb; subst hea
              simp only [step]
              cases h_head : ea1.head with
              | argV =>
                simp only [h_head]
                cases h_tail : ea1.tail with
                | none =>
                  simp only [h_tail]
                  have hargs_new : ListValueEqD (km + 1) (v1 :: args1) (v2 :: args2) := by
                    simp only [ListValueEqD]; exact ⟨hv, hargs⟩
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level km b1 (v1 :: args1) (v2 :: args2)
                      hargs_new (veq_refl (km + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 (v1 :: args1) with
                  | none =>
                    simp only [h_eval1, heval_none.mp h_eval1]
                    exact sc_to_ac hn' (stepCompat_error km n)
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 (v2 :: args2) with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only [h_eval1, h_eval2]
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_n' (.ret hrest hveq)
                | some ea_rest =>
                  simp only [h_tail]
                  have hargs_new : ListValueEqD (km + 1) (v1 :: args1) (v2 :: args2) := by
                    simp only [ListValueEqD]; exact ⟨hv, hargs⟩
                  have hvb : ValueEqD (km + 1) (.VBuiltin b1 (v1 :: args1) ea_rest)
                      (.VBuiltin b1 (v2 :: args2) ea_rest) := by
                    unfold ValueEqD; exact ⟨rfl, hargs_new, rfl⟩
                  exact call_n' (.ret hrest hvb)
              | argQ =>
                simp only [h_head]
                exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEqD at hfv; exact hfv.elim
          | VCon _ =>
            cases vf2 with
            | VCon _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hfv; exact hfv.elim
          | VDelay _ _ =>
            cases vf2 with
            | VDelay _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hfv; exact hfv.elim
          | VConstr _ _ =>
            cases vf2 with
            | VConstr _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hfv; exact hfv.elim
        | applyArg hvx =>
          rename_i vx1 vx2
          cases v1 with
          | VLam body1 env1 =>
            cases v2 with
            | VLam body2 env2 =>
              simp only [step]
              unfold ValueEqD at hv
              have hvx_km : ValueEqD km vx1 vx2 := valueEqD_mono (km + 1) km (by omega) vx1 vx2 hvx
              have hrest_km : StackEq km rest1 rest2 := stackEq_mono (by omega) hrest
              have hclause := hv km (by omega) vx1 vx2 hvx_km rest1 rest2 (stackEq_to_stackEqR hrest_km)
              exact ⟨hclause.1 n hn',
                     fun v1' hv1' => hclause.2.1 v1' n hn' hv1',
                     hclause.2.2.1 n hn',
                     fun v2' hv2' => hclause.2.2.2 v2' n hn' hv2'⟩
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VBuiltin b1 args1 ea1 =>
            cases v2 with
            | VBuiltin b2 args2 ea2 =>
              unfold ValueEqD at hv
              obtain ⟨hb, hargs, hea⟩ := hv
              subst hb; subst hea
              simp only [step]
              cases h_head : ea1.head with
              | argV =>
                simp only [h_head]
                cases h_tail : ea1.tail with
                | none =>
                  simp only [h_tail]
                  have hargs_new : ListValueEqD (km + 1) (vx1 :: args1) (vx2 :: args2) := by
                    simp only [ListValueEqD]; exact ⟨hvx, hargs⟩
                  have ⟨heval_none, heval_some⟩ :=
                    evalBuiltin_cong_same_level km b1 (vx1 :: args1) (vx2 :: args2)
                      hargs_new (veq_refl (km + 1) (by omega))
                  cases h_eval1 : Moist.CEK.evalBuiltin b1 (vx1 :: args1) with
                  | none =>
                    simp only [h_eval1, heval_none.mp h_eval1]
                    exact sc_to_ac hn' (stepCompat_error km n)
                  | some r1 =>
                    cases h_eval2 : Moist.CEK.evalBuiltin b1 (vx2 :: args2) with
                    | none => exact absurd (heval_none.mpr h_eval2) (by simp [h_eval1])
                    | some r2 =>
                      simp only [h_eval1, h_eval2]
                      have hveq := heval_some r1 r2 h_eval1 h_eval2
                      exact call_n' (.ret hrest hveq)
                | some ea_rest =>
                  simp only [h_tail]
                  have hargs_new : ListValueEqD (km + 1) (vx1 :: args1) (vx2 :: args2) := by
                    simp only [ListValueEqD]; exact ⟨hvx, hargs⟩
                  have hvb : ValueEqD (km + 1) (.VBuiltin b1 (vx1 :: args1) ea_rest)
                      (.VBuiltin b1 (vx2 :: args2) ea_rest) := by
                    unfold ValueEqD; exact ⟨rfl, hargs_new, rfl⟩
                  exact call_n' (.ret hrest hvb)
              | argQ =>
                simp only [h_head]
                exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VCon _ =>
            cases v2 with
            | VCon _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VConstr _ _ =>
            cases v2 with
            | VConstr _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
        | constrField hdone henv_cf =>
          rename_i done1 done2 env1_cf env2_cf tag todo
          cases todo with
          | nil =>
            simp only [step]
            have hv_km : ValueEqD km v1 v2 := valueEqD_mono (km + 1) km (by omega) v1 v2 hv
            have hdone_km : ListValueEqD km done1 done2 := listValueEqD_mono (km + 1) km (by omega) done1 done2 hdone
            have hfields : ListValueEqD km (v1 :: done1).reverse (v2 :: done2).reverse :=
              listValueEqD_cons_rev hv_km hdone_km
            exact call_n' (.ret hrest (vconstr_valueEqD hfields))
          | cons m ms =>
            simp only [step]
            have hdone' : ListValueEqD (km + 1) (v1 :: done1) (v2 :: done2) := by
              simp only [ListValueEqD]; exact ⟨hv, hdone⟩
            exact call_n' (.compute (.cons (.constrField hdone' henv_cf) hrest) henv_cf)
        | caseScrutinee henv_cs =>
          rename_i alts
          cases v1 with
          | VConstr tag1 fields1 =>
            cases v2 with
            | VConstr tag2 fields2 =>
              unfold ValueEqD at hv
              obtain ⟨htag, hfields⟩ := hv
              subst htag
              simp only [step]
              cases h_alt : alts[tag1]? with
              | none => exact sc_to_ac hn' (stepCompat_error km n)
              | some alt =>
                have hstk_km : StackEq km
                    (fields1.map Frame.applyArg ++ rest1)
                    (fields2.map Frame.applyArg ++ rest2) :=
                  stackEq_append (listValueEqD_map_applyArg_stackEq hfields) (stackEq_mono (by omega) hrest)
                exact stateEq_stepCompat km n hn' (fun j hj v => veq_refl j (by omega) v)
                  (.compute hstk_km (envEq_mono (by omega) henv_cs))
            | VCon _ | VLam _ _ | VDelay _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VCon c1 =>
            cases v2 with
            | VCon c2 =>
              unfold ValueEqD at hv
              subst hv
              simp only [step]
              cases h_ctf : Moist.CEK.constToTagAndFields c1 with
              | none => exact sc_to_ac hn' (stepCompat_error km n)
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple
                by_cases hcond : numCtors > 0 && alts.length > numCtors
                · simp only [hcond, if_true]
                  exact sc_to_ac hn' (stepCompat_error km n)
                · simp only [Bool.not_eq_true] at hcond
                  simp only [hcond, if_false]
                  cases h_alt : alts[tag]? with
                  | none => exact sc_to_ac hn' (stepCompat_error km n)
                  | some alt =>
                    have hfields_refl : ListValueEqD (km + 1) fields fields :=
                      listValueEqD_refl_local (km + 1) (by omega) fields
                    exact call_n' (.compute
                      (stackEq_append (listValueEqD_map_applyArg_stackEq hfields_refl) hrest)
                      henv_cs)
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VLam _ _ =>
            cases v2 with
            | VLam _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VDelay _ _ =>
            cases v2 with
            | VDelay _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              unfold ValueEqD at hv; exact hv.elim
          | VBuiltin _ _ _ =>
            cases v2 with
            | VBuiltin _ _ _ => simp only [step]; exact sc_to_ac hn' (stepCompat_error km n)
            | VCon _ | VLam _ _ | VDelay _ _ | VConstr _ _ =>
              unfold ValueEqD at hv; exact hv.elim
termination_by (k, n)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Empty-stack version for the original interface. -/
theorem gen_fundamental_lemma
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEqD j v v) :
    ∀ (body : Term) (env1 env2 : CekEnv),
    EnvEq k env1 env2 → ∀ n, n ≤ k →
    AsymCompat k n (.compute [] env1 body) (.compute [] env2 body) := by
  intro body env1 env2 henv n hn
  exact stateEq_stepCompat k n hn veq_refl (.compute .nil henv)

/-! ## §10 Reflexivity

`stateEq_stepCompat` is stated with a `veq_refl` parameter — a local
assumption that every value is `ValueEqD j`-related to itself for
`j ≤ k`. We now discharge this assumption by proving `valueEqD_refl`
and `listValueEqD_refl` directly by well-founded recursion on
`(k, sizeOf v)`.

The proof is mutually recursive. At each successor step it builds a
`StateEq` witnessing closure self-relatedness and feeds it to
`stateEq_stepCompat`. This is the dependency cycle that
`stateEq_stepCompat`'s `veq_refl` parameter breaks. -/

mutual
  theorem valueEqD_refl : ∀ (k : Nat) (v : CekValue), ValueEqD k v v
    | 0, _ => by simp [ValueEqD]
    | _ + 1, .VCon _ => by simp [ValueEqD]
    | k + 1, .VLam body env => by
      unfold ValueEqD; intro j hj arg1 arg2 hargs stk1 stk2 hstk
      have veq : ∀ i, i ≤ j → ∀ w : CekValue, ValueEqD i w w :=
        fun i hi w => valueEqD_refl i w
      have hrel : StateEq j (.compute stk1 (env.extend arg1) body)
          (.compute stk2 (env.extend arg2) body) :=
        .compute (stackEqR_to_stackEq hstk) (envEq_extend (envEq_refl veq env) hargs)
      exact ⟨fun n hn he => (stateEq_stepCompat j n hn veq hrel).1 he,
             fun v1 n hn hv1 => (stateEq_stepCompat j n hn veq hrel).2.1 v1 hv1,
             fun n hn he => (stateEq_stepCompat j n hn veq hrel).2.2.1 he,
             fun v2 n hn hv2 => (stateEq_stepCompat j n hn veq hrel).2.2.2 v2 hv2⟩
    | k + 1, .VDelay body env => by
      unfold ValueEqD; intro j hj stk1 stk2 hstk
      have veq : ∀ i, i ≤ j → ∀ w : CekValue, ValueEqD i w w :=
        fun i hi w => valueEqD_refl i w
      have hrel : StateEq j (.compute stk1 env body)
          (.compute stk2 env body) :=
        .compute (stackEqR_to_stackEq hstk) (envEq_refl veq env)
      exact ⟨fun n hn he => (stateEq_stepCompat j n hn veq hrel).1 he,
             fun v1 n hn hv1 => (stateEq_stepCompat j n hn veq hrel).2.1 v1 hv1,
             fun n hn he => (stateEq_stepCompat j n hn veq hrel).2.2.1 he,
             fun v2 n hn hv2 => (stateEq_stepCompat j n hn veq hrel).2.2.2 v2 hv2⟩
    | _ + 1, .VConstr _ fields => by
      unfold ValueEqD; exact ⟨rfl, listValueEqD_refl _ fields⟩
    | _ + 1, .VBuiltin b args ea => by
      unfold ValueEqD; exact ⟨rfl, listValueEqD_refl _ args, rfl⟩
  termination_by k v => (k, sizeOf v)
  theorem listValueEqD_refl : ∀ (k : Nat) (vs : List CekValue), ListValueEqD k vs vs
    | _, [] => by simp [ListValueEqD]
    | k, v :: vs => by simp only [ListValueEqD]; exact ⟨valueEqD_refl k v, listValueEqD_refl k vs⟩
  termination_by k vs => (k, sizeOf vs)
end

/-! ### Parameter-free wrappers

With `valueEqD_refl` in hand, we can supply the `veq_refl` parameter
automatically. The primed versions (`stateEq_stepCompat'`, `envEq_refl'`,
`fundamental_lemma_proved'`) are the forms downstream code actually uses. -/

private def veq_refl_of (k : Nat) : ∀ j, j ≤ k → ∀ v : CekValue, ValueEqD j v v :=
  fun j _ v => valueEqD_refl j v

/-- `stateEq_stepCompat` without the `veq_refl` parameter. -/
theorem stateEq_stepCompat' (k n : Nat) (hn : n ≤ k)
    {s1 s2 : State} (hrel : StateEq k s1 s2) :
    AsymCompat k n s1 s2 :=
  stateEq_stepCompat k n hn (veq_refl_of k) hrel

/-- `envEq_refl` without the `veq_refl` parameter. -/
theorem envEq_refl' {k : Nat} (env : CekEnv) : EnvEq k env env :=
  envEq_refl (veq_refl_of k) env

/-- The fundamental lemma without `veq_refl` parameter. -/
theorem fundamental_lemma_proved' (k : Nat)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEqD k arg1 arg2)
    (n : Nat) (hn : n ≤ k) :
    (steps n (.compute [] (env.extend arg1) body) = .error →
      ∃ m, m ≤ k ∧ steps m (.compute [] (env.extend arg2) body) = .error) ∧
    (∀ v1, steps n (.compute [] (env.extend arg1) body) = .halt v1 →
      ∃ v2 m, m ≤ k ∧ steps m (.compute [] (env.extend arg2) body) = .halt v2 ∧
        ValueEqD (k - n) v1 v2) ∧
    (steps n (.compute [] (env.extend arg2) body) = .error →
      ∃ m, m ≤ k ∧ steps m (.compute [] (env.extend arg1) body) = .error) ∧
    (∀ v2, steps n (.compute [] (env.extend arg2) body) = .halt v2 →
      ∃ v1 m, m ≤ k ∧ steps m (.compute [] (env.extend arg1) body) = .halt v1 ∧
        ValueEqD (k - n) v1 v2) := by
  have henv : EnvEq k (env.extend arg1) (env.extend arg2) :=
    envEq_extend (envEq_refl' env) hargs
  exact gen_fundamental_lemma (veq_refl_of k) body _ _ henv n hn

/-! ## §11 Equivalence with standard `ValueEq`

The CIU-style `ValueEqD` and the project-wide `ValueEq` (from
`Moist.Verified.Semantics`) are not definitionally equal: `ValueEq`'s VLam
clause quantifies over empty stacks and identical arguments, while
`ValueEqD`'s quantifies over arbitrary related stacks and arguments with
step-bounded witnesses.

They **do agree** under universal quantification over the step index:

```
(∀ k, ValueEqD k v₁ v₂) → (∀ k, ValueEq k v₁ v₂)
```

The forward direction is the one needed for `sameBody_adequacy`: we prove
`∀ k, ValueEqD k` via the fundamental lemma, then transport to `∀ k, ValueEq k`.
Instantiating `ValueEqD k`'s stack quantifier at `[]` and its argument
quantifier at a `valueEqD_refl`-witnessed pair recovers exactly the data
`ValueEq k`'s VLam clause wants.

The backward direction (`ValueEq → ValueEqD` for VLam/VDelay) is **not**
provable — standard `ValueEq` lacks the stack-quantification data that
`ValueEqD` demands — and is not needed. -/

mutual
def valueEqD_to_valueEq_all : ∀ (v₁ v₂ : CekValue),
    (∀ k, ValueEqD k v₁ v₂) → ∀ k, ValueEq k v₁ v₂
  | _, _, _, 0 => by simp [ValueEq]
  | .VCon c₁, .VCon c₂, hfwd, k + 1 => by
    simp only [ValueEq]
    have h := hfwd 1; simp only [ValueEqD] at h; exact h
  | .VLam body₁ env₁, .VLam body₂ env₂, hfwd, k + 1 => by
    unfold ValueEq; intro arg
    constructor
    · -- error ↔
      constructor
      · intro ⟨n, herr⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        -- Instantiate with same arg, empty stacks
        have hclause := hd n (by omega) arg arg (valueEqD_refl n arg) [] [] trivial
        obtain ⟨m, _, hm⟩ := hclause.1 n (by omega) herr
        exact ⟨m, hm⟩
      · intro ⟨n, herr⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) arg arg (valueEqD_refl n arg) [] [] trivial
        obtain ⟨m, _, hm⟩ := hclause.2.2.1 n (by omega) herr
        exact ⟨m, hm⟩
    constructor
    · -- halts ↔
      constructor
      · intro ⟨r₁, n, hhalt⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) arg arg (valueEqD_refl n arg) [] [] trivial
        obtain ⟨r₂, m, _, hhalt₂, _⟩ := hclause.2.1 r₁ n (by omega) hhalt
        exact ⟨r₂, m, hhalt₂⟩
      · intro ⟨r₂, n, hhalt⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) arg arg (valueEqD_refl n arg) [] [] trivial
        obtain ⟨r₁, m, _, hhalt₁, _⟩ := hclause.2.2.2 r₂ n (by omega) hhalt
        exact ⟨r₁, m, hhalt₁⟩
    · -- value equivalence on results
      intro r₁ r₂ ⟨n₁, hhalt₁⟩ ⟨n₂, hhalt₂⟩
      apply valueEqD_to_valueEq_all r₁ r₂
      intro k'
      have hd := hfwd (n₁ + k' + 1); unfold ValueEqD at hd
      have hclause := hd (n₁ + k') (by omega) arg arg (valueEqD_refl (n₁ + k') arg) [] [] trivial
      obtain ⟨r₂', m, _, hhalt₂', hvd⟩ := hclause.2.1 r₁ n₁ (by omega) hhalt₁
      have : r₂' = r₂ := reaches_unique ⟨m, hhalt₂'⟩ ⟨n₂, hhalt₂⟩
      subst this; simpa using hvd
  | .VDelay body₁ env₁, .VDelay body₂ env₂, hfwd, k + 1 => by
    unfold ValueEq
    constructor
    · constructor
      · intro ⟨n, herr⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) [] [] trivial
        obtain ⟨m, _, hm⟩ := hclause.1 n (by omega) herr
        exact ⟨m, hm⟩
      · intro ⟨n, herr⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) [] [] trivial
        obtain ⟨m, _, hm⟩ := hclause.2.2.1 n (by omega) herr
        exact ⟨m, hm⟩
    constructor
    · constructor
      · intro ⟨r₁, n, hhalt⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) [] [] trivial
        obtain ⟨r₂, m, _, hhalt₂, _⟩ := hclause.2.1 r₁ n (by omega) hhalt
        exact ⟨r₂, m, hhalt₂⟩
      · intro ⟨r₂, n, hhalt⟩
        have hd := hfwd (n + 1); unfold ValueEqD at hd
        have hclause := hd n (by omega) [] [] trivial
        obtain ⟨r₁, m, _, hhalt₁, _⟩ := hclause.2.2.2 r₂ n (by omega) hhalt
        exact ⟨r₁, m, hhalt₁⟩
    · intro r₁ r₂ ⟨n₁, hhalt₁⟩ ⟨n₂, hhalt₂⟩
      apply valueEqD_to_valueEq_all r₁ r₂
      intro k'
      have hd := hfwd (n₁ + k' + 1); unfold ValueEqD at hd
      have hclause := hd (n₁ + k') (by omega) [] [] trivial
      obtain ⟨r₂', m, _, hhalt₂', hvd⟩ := hclause.2.1 r₁ n₁ (by omega) hhalt₁
      have : r₂' = r₂ := reaches_unique ⟨m, hhalt₂'⟩ ⟨n₂, hhalt₂⟩
      subst this; simpa using hvd
  | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂, hfwd, k + 1 => by
    unfold ValueEq
    have hd := hfwd 1; unfold ValueEqD at hd
    exact ⟨hd.1, listValueEqD_to_listValueEq_all fields₁ fields₂
      (fun k' => by have h := hfwd (k' + 1); unfold ValueEqD at h; exact h.2) k⟩
  | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂, hfwd, k + 1 => by
    unfold ValueEq
    have hd := hfwd (k + 1); unfold ValueEqD at hd
    have hargs_all : ∀ k', ListValueEqD k' args₁ args₂ :=
      fun k' => by
        -- ListValueEqD (k'+1) from hfwd at k'+1, then mono down
        have h := hfwd (k' + 1); unfold ValueEqD at h
        exact listValueEqD_mono (k' + 1) k' (by omega) args₁ args₂ h.2.1
    have hb : b₁ = b₂ := hd.1
    refine ⟨hd.1, listValueEqD_to_listValueEq_all args₁ args₂ hargs_all k,
      hd.2.2, ?_, ?_⟩
    · -- evalBuiltin none ↔ none
      have hargs_k1 : ListValueEqD (k + 1) args₁ args₂ := hargs_all (k + 1)
      have hcong := evalBuiltin_cong_same_level k b₁ args₁ args₂ hargs_k1
        (fun v => valueEqD_refl (k + 1) v)
      have := hcong.1
      -- Convert from b₁ to b₂ using hb
      subst hb
      exact this
    · -- ∀ r1 r2, evalBuiltin some → ValueEq k r1 r2
      intro r1 r2 hr1 hr2
      -- Build ∀ k', ValueEqD k' r1 r2 then convert via valueEqD_to_valueEq_all
      apply valueEqD_to_valueEq_all r1 r2
      intro k''
      cases k'' with
      | zero => simp [ValueEqD]
      | succ k' =>
        have hargs_k1 : ListValueEqD (k' + 1) args₁ args₂ := hargs_all (k' + 1)
        have hcong := evalBuiltin_cong_same_level k' b₁ args₁ args₂ hargs_k1
          (fun v => valueEqD_refl (k' + 1) v)
        -- Need evalBuiltin b₁ args₂ = some r2; we have evalBuiltin b₂ args₂ = some r2
        have hr2' : Moist.CEK.evalBuiltin b₁ args₂ = some r2 := by rw [hb]; exact hr2
        exact hcong.2 r1 r2 hr1 hr2'
  -- Cross-constructor cases
  | .VCon _, .VLam _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VCon _, .VDelay _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VCon _, .VConstr _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VCon _, .VBuiltin _ _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VLam _ _, .VCon _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VLam _ _, .VDelay _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VLam _ _, .VConstr _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VLam _ _, .VBuiltin _ _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VDelay _ _, .VCon _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VDelay _ _, .VLam _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VDelay _ _, .VConstr _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VDelay _ _, .VBuiltin _ _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VConstr _ _, .VCon _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VConstr _ _, .VLam _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VConstr _ _, .VDelay _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VConstr _ _, .VBuiltin _ _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VBuiltin _ _ _, .VCon _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VBuiltin _ _ _, .VLam _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VBuiltin _ _ _, .VDelay _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this
  | .VBuiltin _ _ _, .VConstr _ _, hfwd, _ + 1 => by have := hfwd 1; simp [ValueEqD] at this

def listValueEqD_to_listValueEq_all : ∀ (vs₁ vs₂ : List CekValue),
    (∀ k, ListValueEqD k vs₁ vs₂) → ∀ k, ListValueEq k vs₁ vs₂
  | [], [], _, _ => by simp [ListValueEq]
  | a :: as, b :: bs, hfwd, k => by
    simp only [ListValueEq]
    exact ⟨valueEqD_to_valueEq_all a b
             (fun k' => by have := hfwd k'; simp only [ListValueEqD] at this; exact this.1) k,
           listValueEqD_to_listValueEq_all as bs
             (fun k' => by have := hfwd k'; simp only [ListValueEqD] at this; exact this.2) k⟩
  | [], _ :: _, hfwd, _ => by have := hfwd 0; simp [ListValueEqD] at this
  | _ :: _, [], hfwd, _ => by have := hfwd 0; simp [ListValueEqD] at this
end

-- Note: The backward direction `ValueEq → ValueEqD` for VLam/VDelay is not
-- provable without additional structure and is not needed for `sameBody_adequacy`.
-- Only the forward direction (`ValueEqD → ValueEq`) is used.

/-! ## §12 Same-body adequacy

The main theorem of this module. Given a closed UPLC term `t` and two
environments `env₁ env₂` related at every step index by `EnvEq k`, the
two computations agree on

1. erroring (both or neither),
2. halting (both or neither), and
3. value equivalence at every step index `k` on any halted results.

The proof reduces to the fundamental lemma `stateEq_stepCompat'` applied
to `StateEq.compute .nil (henv n)` at a budget chosen to leave enough
remaining after execution. The `valueEqD_to_valueEq_all` bridge converts
the `ValueEqD` result to `ValueEq`. -/

/-- Same-body adequacy: same closed term under equivalent environments
    gives equivalent results. Uses the fundamental lemma with ValueEqD,
    then bridges to ValueEq via the equivalence. -/
theorem sameBody_adequacy (t : Term) (env₁ env₂ : CekEnv)
    (henv : ∀ k, EnvEq k env₁ env₂) :
    (Reaches (.compute [] env₁ t) .error ↔ Reaches (.compute [] env₂ t) .error) ∧
    (Halts (.compute [] env₁ t) ↔ Halts (.compute [] env₂ t)) ∧
    ∀ (k : Nat) (v₁ v₂ : CekValue),
      Reaches (.compute [] env₁ t) (.halt v₁) →
      Reaches (.compute [] env₂ t) (.halt v₂) →
      ValueEq k v₁ v₂ := by
  constructor
  · -- error ↔
    constructor
    · intro ⟨n, herr⟩
      have hrel : StateEq n (.compute [] env₁ t) (.compute [] env₂ t) :=
        .compute .nil (henv n)
      have hac := stateEq_stepCompat' n n (by omega) hrel
      obtain ⟨m, _, hm⟩ := hac.1 herr
      exact ⟨m, hm⟩
    · intro ⟨n, herr⟩
      have hrel : StateEq n (.compute [] env₁ t) (.compute [] env₂ t) :=
        .compute .nil (henv n)
      have hac := stateEq_stepCompat' n n (by omega) hrel
      obtain ⟨m, _, hm⟩ := hac.2.2.1 herr
      exact ⟨m, hm⟩
  constructor
  · -- halts ↔
    constructor
    · intro ⟨v₁, n, hhalt⟩
      have hrel : StateEq n (.compute [] env₁ t) (.compute [] env₂ t) :=
        .compute .nil (henv n)
      have hac := stateEq_stepCompat' n n (by omega) hrel
      obtain ⟨v₂, m, _, hhalt₂, _⟩ := hac.2.1 v₁ hhalt
      exact ⟨v₂, m, hhalt₂⟩
    · intro ⟨v₂, n, hhalt⟩
      have hrel : StateEq n (.compute [] env₁ t) (.compute [] env₂ t) :=
        .compute .nil (henv n)
      have hac := stateEq_stepCompat' n n (by omega) hrel
      obtain ⟨v₁, m, _, hhalt₁, _⟩ := hac.2.2.2 v₂ hhalt
      exact ⟨v₁, m, hhalt₁⟩
  · -- value equivalence
    intro k v₁ v₂ ⟨n₁, hhalt₁⟩ ⟨n₂, hhalt₂⟩
    apply valueEqD_to_valueEq_all v₁ v₂
    intro k'
    -- Use budget n₁ + k' at step n₁, so result has ValueEqD (n₁ + k' - n₁) = ValueEqD k'
    have hrel : StateEq (n₁ + k') (.compute [] env₁ t) (.compute [] env₂ t) :=
      .compute .nil (henv (n₁ + k'))
    have hac := stateEq_stepCompat' (n₁ + k') n₁ (by omega) hrel
    obtain ⟨v₂', m, _, hhalt₂', hvd⟩ := hac.2.1 v₁ hhalt₁
    have : v₂' = v₂ := reaches_unique ⟨m, hhalt₂'⟩ ⟨n₂, hhalt₂⟩
    subst this; simpa using hvd

end Moist.Verified.SameBodyDecay
