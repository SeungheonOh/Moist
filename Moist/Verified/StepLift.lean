import Moist.Verified.Semantics

set_option linter.unusedSimpArgs false

namespace Moist.Verified.StepLift

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Semantics

/-! # Stack Lifting and Beta Decomposition for CEK States

This module provides the **beta decomposition** lemmas that let us
reason about `Apply (Lam n body) e'` by splitting it into two
independent reachability claims: one for the argument `e'` and one
for the body `body`.

The core technique is **stack lifting**: `liftState base s` prepends
a fixed continuation `base` to every stack inside state `s`. We prove
that `step` commutes with `liftState` as long as the inner state is
"active" (i.e. not `halt`, `error`, or `ret []`). This lets us embed
a sub-computation (evaluating `e'` with an empty stack) into a larger
context (evaluating it with `[funV (VLam body env)]` on the stack).

**Main results:**

- `beta_reaches` (analysis direction): if `Apply (Lam n body) e'`
  halts with `v`, then `e'` halts with some `ve` and `body` under
  `env.extend ve` halts with `v`.

- `beta_reaches_error` (analysis direction for errors): if
  `Apply (Lam n body) e'` errors, then either `e'` errors or `e'`
  halts with `ve` and the body errors.

- `beta_apply_from_inner` (synthesis direction): given that `e'`
  halts with `ve` and `body` under `env.extend ve` reaches `s`,
  compose them to show `Apply (Lam n body) e'` reaches `s`.
-/

/-! ## CekEnv helpers -/

@[simp] theorem CekEnv.lookup_zero (env : CekEnv) : env.lookup 0 = none := by
  cases env <;> rfl

/-! ## liftState -/

/-- Prepend a base continuation stack to every stack inside a state.
    This embeds a sub-computation into a larger evaluation context.
    `compute s env t` becomes `compute (s ++ base) env t`;
    `halt v` becomes `ret base v` (the sub-computation finished, so
    control returns to the outer context). -/
def liftState (base : Stack) : State → State
  | .compute s env t => .compute (s ++ base) env t
  | .ret s v => .ret (s ++ base) v
  | .halt v => .ret base v
  | .error => .error

/-- A state is "active" when it has pending computation — i.e. it is
    not a terminal state (`halt`, `error`) and not a `ret` with an empty
    stack (which would transition to `halt` on the next step). The
    `step`/`liftState` commutation only holds for active states. -/
def isActive : State → Bool
  | .compute _ _ _ => true
  | .ret (_ :: _) _ => true
  | _ => false

/-! ## step commutes with liftState -/

/-- **Single-step commutation**: for an active state `s`,
    `step (liftState base s) = liftState base (step s)`.
    Proved by exhaustive case analysis on every `State`/`Term`/`Frame`
    combination that `step` can encounter. The proof is large but
    mechanical — each case reduces to `simp [step, liftState]` with
    occasional list-append lemmas. -/
theorem step_liftState_active (base : Stack) (s : State) (h : isActive s = true) :
    step (liftState base s) = liftState base (step s) := by
  match s with
  | .compute stk env t =>
    simp only [liftState]
    cases t with
    | Var n => simp [step]; cases env.lookup n <;> simp [liftState]
    | Constant p => obtain ⟨c, ty⟩ := p; simp [step, liftState]
    | Builtin b => simp [step, liftState]
    | Lam n body => simp [step, liftState]
    | Delay body => simp [step, liftState]
    | Force e => simp [step, liftState, List.cons_append]
    | Apply f x => simp [step, liftState, List.cons_append]
    | Constr tag args => cases args with
      | nil => simp [step, liftState]
      | cons m ms => simp [step, liftState, List.cons_append]
    | Case scrut alts => simp [step, liftState, List.cons_append]
    | Error => simp [step, liftState]
  | .ret (f :: stk) v =>
    simp only [liftState, List.cons_append]
    cases f with
    | force => cases v with
      | VDelay body env => simp [step, liftState]
      | VBuiltin b args ea =>
        simp only [step]; cases ea.head <;> (try simp [liftState]) <;>
        cases ea.tail <;> (try simp [liftState]) <;>
        cases evalBuiltin b args <;> simp [liftState]
      | _ => simp [step, liftState]
    | arg m env => simp [step, liftState, List.cons_append]
    | funV vf => cases vf with
      | VLam body env => simp [step, liftState]
      | VBuiltin b args ea =>
        simp only [step]; cases ea.head <;> (try simp [liftState]) <;>
        cases ea.tail <;> (try simp [liftState]) <;>
        cases evalBuiltin b (_ :: args) <;> simp [liftState]
      | _ => simp [step, liftState]
    | constrField tag done todo env => cases todo with
      | nil => simp [step, liftState]
      | cons m ms => simp [step, liftState, List.cons_append]
    | applyArg vx => cases v with
      | VLam body env => simp [step, liftState]
      | VBuiltin b args ea =>
        simp only [step]; cases ea.head <;> (try simp [liftState]) <;>
        cases ea.tail <;> (try simp [liftState]) <;>
        cases evalBuiltin b (_ :: args) <;> simp [liftState]
      | _ => simp [step, liftState]
    | caseScrutinee alts env => cases v with
      | VConstr tag fields =>
        simp only [step]; cases alts[tag]? <;> simp [liftState, List.append_assoc]
      | VCon c =>
        simp only [step, constToTagAndFields, liftState, List.cons_append]
        split <;> try rfl
        · split <;> try rfl
          split <;> simp [liftState, List.append_assoc]
      | _ => simp [step, liftState]
  | .ret [] _ => simp [isActive] at h
  | .halt _ => simp [isActive] at h
  | .error => simp [isActive] at h

/-- **Multi-step commutation**: if every intermediate state `steps j s`
    (for `j < n`) is active, then `steps n (liftState base s) =
    liftState base (steps n s)`. Follows from `step_liftState_active`
    by induction on `n`. -/
theorem steps_liftState (base : Stack) :
    ∀ (n : Nat) (s : State),
    (∀ j, j < n → isActive (steps j s) = true) →
    steps n (liftState base s) = liftState base (steps n s)
  | 0, _, _ => by simp [steps]
  | n + 1, s, hact => by
    simp only [steps]
    rw [step_liftState_active base s (hact 0 (Nat.zero_lt_succ n))]
    exact steps_liftState base n (step s) (fun j hj => by
      have := hact (j + 1) (by omega); simp only [steps] at this; exact this)

/-! ## Beta decomposition via liftState -/

/-- Find the first step index `K ≤ bound` where the state becomes inactive,
    and certify that all earlier steps were active. This is a well-founded
    search used by the beta decomposition lemmas to locate the point where
    the inner sub-computation finishes (halts or returns with empty stack). -/
private theorem firstInactive (s : State) (bound : Nat)
    (hex : ∃ k, k ≤ bound ∧ isActive (steps k s) = false) :
    ∃ K, K ≤ bound ∧ isActive (steps K s) = false ∧
         (∀ j, j < K → isActive (steps j s) = true) := by
  induction bound with
  | zero =>
    obtain ⟨k, hk, hinact⟩ := hex
    have : k = 0 := by omega
    subst this
    exact ⟨0, Nat.le_refl _, hinact, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ bound ih =>
    -- Either some k ≤ bound satisfies, or bound+1 is the first
    by_cases h : ∃ k, k ≤ bound ∧ isActive (steps k s) = false
    · obtain ⟨K, hK_le, hK_inact, hK_min⟩ := ih h
      exact ⟨K, by omega, hK_inact, hK_min⟩
    · -- No k ≤ bound is inactive, so all k ≤ bound are active
      have hall : ∀ j, j ≤ bound → isActive (steps j s) = true := by
        intro j hj
        by_cases heq : isActive (steps j s) = true
        · exact heq
        · exfalso; apply h; exact ⟨j, hj, by cases isActive (steps j s) <;> simp_all⟩
      obtain ⟨k, hk, hinact⟩ := hex
      have hk_eq : k = bound + 1 := by
        by_cases heq : k = bound + 1
        · exact heq
        · exfalso; have hle : k ≤ bound := by omega
          have := hall k hle; simp [hinact] at this
      subst hk_eq
      exact ⟨bound + 1, Nat.le_refl _, hinact, fun j hj => hall j (by omega)⟩

/-- `liftState base s` is never `halt`. A lifted state is either `compute`
    (stack extended), `ret` (stack extended or base for halt), or `error`.
    This fact drives the contradiction in `beta_reaches`: the inner
    computation must eventually become inactive, otherwise `liftState` of
    the final state would need to be `halt`, which is impossible. -/
theorem liftState_ne_halt (base : Stack) (s : State) (v : CekValue) :
    liftState base s ≠ .halt v := by
  cases s <;> simp [liftState]

/-- **Beta decomposition (halt case)**: if `Apply (Lam n body) e'` halts
    with value `v`, then the argument `e'` halts with some intermediate
    value `ve`, and the body `body` evaluated in `env.extend ve` also
    halts with `v`.

    **Proof sketch:**
    1. The first 3 steps are mechanical: `compute [] env (Apply (Lam n body) e')`
       → `compute [funV (VLam body env)] env e'`.
    2. Rewrite the latter as `liftState [funV ...] (compute [] env e')`.
    3. Use `firstInactive` + `liftState_ne_halt` to find the step `K` where
       the inner computation finishes.
    4. At step `K`, the inner state is either `halt ve` or `ret [] ve`.
       Extract `ve` and show `Reaches (.compute [] env e') (.halt ve)`.
    5. The remaining `(N-3)-K` steps evaluate the body from
       `ret [funV (VLam body env)] ve`, which takes one step to
       `compute [] (env.extend ve) body`, yielding the second `Reaches`. -/
theorem beta_reaches (env : CekEnv) (body e' : Term) (n : Nat) (v : CekValue)
    (hreach : Reaches (.compute [] env (.Apply (.Lam n body) e')) (.halt v)) :
    ∃ ve, Reaches (.compute [] env e') (.halt ve) ∧
          Reaches (.compute [] (env.extend ve) body) (.halt v) := by
  obtain ⟨N, hN⟩ := hreach
  -- After 3 mechanical steps: compute [funV (VLam body env)] env e'
  have hge3 : N ≥ 3 := by
    match N, hN with
    | 0, hN | 1, hN | 2, hN => simp [steps, step] at hN
    | _ + 3, _ => omega
  have h3 : steps 3 (.compute [] env (.Apply (.Lam n body) e')) =
      .compute [.funV (.VLam body env)] env e' := by simp [steps, step]
  have hrest : steps (N - 3) (.compute [.funV (.VLam body env)] env e') = .halt v := by
    have : N = 3 + (N - 3) := by omega
    rw [this, steps_trans, h3] at hN; exact hN
  -- Identify as liftState
  have hlift : State.compute [.funV (.VLam body env)] env e' =
      liftState [.funV (.VLam body env)] (.compute [] env e') := by simp [liftState]
  rw [hlift] at hrest
  -- hrest : steps (N-3) (liftState [...] (compute [] env e')) = halt v
  -- Not all inner states can be active (liftState of anything is never halt)
  have h_has_inactive : ∃ k, k ≤ (N - 3) ∧ isActive (steps k (.compute [] env e')) = false := by
    -- Proof by contradiction: if all j ≤ N-3 are active, steps_liftState gives
    -- halt v = liftState ... (steps (N-3) ...) which is impossible.
    -- We use Classical.byContradiction since by_contra isn't available.
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ (N - 3) → isActive (steps j (.compute [] env e')) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] env e')) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] env e')) <;> simp_all⟩
      have h_comm := steps_liftState [.funV (.VLam body env)] (N - 3) (.compute [] env e')
        (fun j hj => hall' j (by omega))
      rw [hrest] at h_comm
      exact absurd h_comm.symm (liftState_ne_halt _ _ v)
  -- Find the first non-active step
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] env e') (N - 3) h_has_inactive
  -- steps_liftState applies for the first K steps
  have h_comm : steps K (liftState [.funV (.VLam body env)] (.compute [] env e')) =
      liftState [.funV (.VLam body env)] (steps K (.compute [] env e')) :=
    steps_liftState [.funV (.VLam body env)] K (.compute [] env e') hK_min
  -- The inner state at K is not error (would prevent reaching halt)
  have h_not_error : steps K (.compute [] env e') ≠ .error := by
    intro herr
    have : steps ((N - 3) - K) (liftState [.funV (.VLam body env)] .error) = .halt v := by
      have : N - 3 = K + ((N - 3) - K) := by omega
      rw [this, steps_trans, h_comm, herr] at hrest; exact hrest
    simp [liftState, steps_error] at this
  -- Extract ve: non-active, non-error => ret [] ve or halt ve
  have ⟨ve, h_inner_eq, h_lifted_eq⟩ :
      ∃ ve, (steps K (.compute [] env e') = .halt ve ∨
             steps K (.compute [] env e') = .ret [] ve) ∧
            liftState [.funV (.VLam body env)] (steps K (.compute [] env e')) =
              .ret [.funV (.VLam body env)] ve := by
    generalize h_sK : steps K (.compute [] env e') = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] ve => exact ⟨ve, .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt ve => exact ⟨ve, .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  -- Reaches for e'
  have h_reaches_e : Reaches (.compute [] env e') (.halt ve) := by
    cases h_inner_eq with
    | inl h => exact ⟨K, h⟩
    | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
  -- Remaining steps after K: steps ((N-3) - K) (ret [...] ve) = halt v
  have h_apply : steps ((N - 3) - K) (.ret [.funV (.VLam body env)] ve) = .halt v := by
    have : N - 3 = K + ((N - 3) - K) := by omega
    rw [this, steps_trans, h_comm, h_lifted_eq] at hrest; exact hrest
  -- ret [funV (VLam body env)] ve -> compute [] (env.extend ve) body in 1 step
  have hge1 : (N - 3) - K ≥ 1 := by
    by_cases hlt : (N - 3) - K ≥ 1
    · exact hlt
    · exfalso; have : (N - 3) - K = 0 := by omega
      rw [this] at h_apply; simp [steps] at h_apply
  have h_body : steps ((N - 3) - K - 1) (.compute [] (env.extend ve) body) = .halt v := by
    have : (N - 3) - K = 1 + ((N - 3) - K - 1) := by omega
    rw [this, steps_trans] at h_apply
    simp [steps, step] at h_apply
    exact h_apply
  exact ⟨ve, h_reaches_e, (N - 3) - K - 1, h_body⟩

/-- `liftState` reflects errors: if the lifted state is `error`, the
    original state must also be `error` (since all other constructors
    produce `compute` or `ret` under `liftState`). -/
theorem liftState_eq_error (base : Stack) (s : State)
    (h : liftState base s = .error) : s = .error := by
  cases s <;> simp [liftState] at h ⊢ <;> exact h

/-- **Beta decomposition (error case)**: if `Apply (Lam n body) e'` reaches
    `error`, then either `e'` itself errors, or `e'` halts with some `ve`
    and the body errors under `env.extend ve`. Same proof structure as
    `beta_reaches`, with an additional case split on whether the inner
    computation at step `K` is `.error`. -/
theorem beta_reaches_error (env : CekEnv) (body e' : Term) (n : Nat)
    (hreach : Reaches (.compute [] env (.Apply (.Lam n body) e')) .error) :
    Reaches (.compute [] env e') .error ∨
    ∃ ve, Reaches (.compute [] env e') (.halt ve) ∧
          Reaches (.compute [] (env.extend ve) body) .error := by
  obtain ⟨N, hN⟩ := hreach
  -- After 3 mechanical steps: compute [funV (VLam body env)] env e'
  have hge3 : N ≥ 3 := by
    match N, hN with
    | 0, hN | 1, hN | 2, hN => simp [steps, step] at hN
    | _ + 3, _ => omega
  have h3 : steps 3 (.compute [] env (.Apply (.Lam n body) e')) =
      .compute [.funV (.VLam body env)] env e' := by simp [steps, step]
  have hrest : steps (N - 3) (.compute [.funV (.VLam body env)] env e') = .error := by
    have : N = 3 + (N - 3) := by omega
    rw [this, steps_trans, h3] at hN; exact hN
  -- Identify as liftState
  have hlift : State.compute [.funV (.VLam body env)] env e' =
      liftState [.funV (.VLam body env)] (.compute [] env e') := by simp [liftState]
  rw [hlift] at hrest
  -- Not all inner states can be active (liftState of active is never error by liftState_eq_error)
  have h_has_inactive : ∃ k, k ≤ (N - 3) ∧ isActive (steps k (.compute [] env e')) = false := by
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ j, j ≤ (N - 3) → isActive (steps j (.compute [] env e')) = true := by
        intro j hj
        by_cases hact : isActive (steps j (.compute [] env e')) = true
        · exact hact
        · exfalso; apply hall; exact ⟨j, hj, by cases isActive (steps j (.compute [] env e')) <;> simp_all⟩
      have h_comm := steps_liftState [.funV (.VLam body env)] (N - 3) (.compute [] env e')
        (fun j hj => hall' j (by omega))
      rw [hrest] at h_comm
      -- h_comm : .error = liftState [...] (steps (N-3) (compute [] env e'))
      -- liftState of anything is never .error unless inner is .error
      -- But if inner is .error, it's not active — contradiction with hall'
      have h_inner_err := liftState_eq_error _ _ h_comm.symm
      have := hall' (N - 3) (Nat.le_refl _)
      rw [h_inner_err] at this; simp [isActive] at this
  -- Find the first non-active step
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] env e') (N - 3) h_has_inactive
  -- steps_liftState applies for the first K steps
  have h_comm : steps K (liftState [.funV (.VLam body env)] (.compute [] env e')) =
      liftState [.funV (.VLam body env)] (steps K (.compute [] env e')) :=
    steps_liftState [.funV (.VLam body env)] K (.compute [] env e') hK_min
  -- Case split: is the inner state at K .error or not?
  by_cases h_is_error : steps K (.compute [] env e') = .error
  · -- Inner computation errors: e' reaches error
    left
    exact ⟨K, h_is_error⟩
  · -- Inner computation does not error: extract ve
    right
    have ⟨ve, h_inner_eq, h_lifted_eq⟩ :
        ∃ ve, (steps K (.compute [] env e') = .halt ve ∨
               steps K (.compute [] env e') = .ret [] ve) ∧
              liftState [.funV (.VLam body env)] (steps K (.compute [] env e')) =
                .ret [.funV (.VLam body env)] ve := by
      generalize h_sK : steps K (.compute [] env e') = sK at hK_inact h_is_error
      match sK with
      | .compute .. => simp [isActive] at hK_inact
      | .ret [] ve => exact ⟨ve, .inr rfl, by simp [liftState]⟩
      | .ret (_ :: _) _ => simp [isActive] at hK_inact
      | .halt ve => exact ⟨ve, .inl rfl, by simp [liftState]⟩
      | .error => exact absurd rfl h_is_error
    -- Reaches for e'
    have h_reaches_e : Reaches (.compute [] env e') (.halt ve) := by
      cases h_inner_eq with
      | inl h => exact ⟨K, h⟩
      | inr h => exact ⟨K + 1, by rw [steps_trans, h]; rfl⟩
    -- Remaining steps after K
    have h_apply : steps ((N - 3) - K) (.ret [.funV (.VLam body env)] ve) = .error := by
      have : N - 3 = K + ((N - 3) - K) := by omega
      rw [this, steps_trans, h_comm, h_lifted_eq] at hrest; exact hrest
    -- ret [funV (VLam body env)] ve -> compute [] (env.extend ve) body in 1 step
    have hge1 : (N - 3) - K ≥ 1 := by
      by_cases hlt : (N - 3) - K ≥ 1
      · exact hlt
      · exfalso; have : (N - 3) - K = 0 := by omega
        rw [this] at h_apply; simp [steps] at h_apply
    have h_body : steps ((N - 3) - K - 1) (.compute [] (env.extend ve) body) = .error := by
      have : (N - 3) - K = 1 + ((N - 3) - K - 1) := by omega
      rw [this, steps_trans] at h_apply
      simp [steps, step] at h_apply
      exact h_apply
    exact ⟨ve, h_reaches_e, (N - 3) - K - 1, h_body⟩

/-- **Beta composition (synthesis direction)**: given that `e'` halts with
    `ve` and `body` in the extended environment `env.extend ve` reaches
    state `s`, compose the two to show `Apply (Lam n body) e'` reaches `s`.

    This is the converse of `beta_reaches` and is used in the dead-let
    error-equivalence proof: we know the RHS errors, so we construct the
    LHS error by composing `e'` halting (from atomic purity) with the
    body erroring (from `closedAt_zero_error_env_irrel`). -/
theorem beta_apply_from_inner (env : CekEnv) (body e' : Term) (n : Nat)
    (ve : CekValue) (s : State)
    (he : Reaches (.compute [] env e') (.halt ve))
    (hb : Reaches (.compute [] (env.extend ve) body) s) :
    Reaches (.compute [] env (.Apply (.Lam n body) e')) s := by
  obtain ⟨Ke, hKe⟩ := he
  obtain ⟨Kb, hKb⟩ := hb
  -- 3 mechanical steps: compute [] env (Apply ...) → compute [funV ...] env e'
  have h3 : steps 3 (.compute [] env (.Apply (.Lam n body) e')) =
      .compute [.funV (.VLam body env)] env e' := by simp [steps, step]
  -- Identify as liftState
  have hlift : State.compute [.funV (.VLam body env)] env e' =
      liftState [.funV (.VLam body env)] (.compute [] env e') := by simp [liftState]
  -- We need all inner steps < some bound to be active, then use steps_liftState
  -- Find the first non-active step in e' computation (bounded by Ke)
  have h_not_active_Ke : isActive (steps Ke (.compute [] env e')) = false := by
    rw [hKe]; rfl
  have h_has_inactive : ∃ k, k ≤ Ke ∧ isActive (steps k (.compute [] env e')) = false :=
    ⟨Ke, Nat.le_refl _, h_not_active_Ke⟩
  obtain ⟨K, hK_le, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] env e') Ke h_has_inactive
  -- steps_liftState applies for the first K steps
  have h_comm : steps K (liftState [.funV (.VLam body env)] (.compute [] env e')) =
      liftState [.funV (.VLam body env)] (steps K (.compute [] env e')) :=
    steps_liftState [.funV (.VLam body env)] K (.compute [] env e') hK_min
  -- Inner state at K is not error (since e' eventually halts)
  have h_not_error : steps K (.compute [] env e') ≠ .error := by
    intro herr
    -- If inner reaches error at K, it stays error forever
    have : steps Ke (.compute [] env e') = .error := by
      have : Ke = K + (Ke - K) := by omega
      rw [this, steps_trans, herr, steps_error]
    rw [hKe] at this; exact absurd this (by simp)
  -- Extract ve': non-active, non-error => ret [] ve' or halt ve'
  have ⟨ve', h_inner_eq, h_lifted_eq⟩ :
      ∃ ve', (steps K (.compute [] env e') = .halt ve' ∨
              steps K (.compute [] env e') = .ret [] ve') ∧
             liftState [.funV (.VLam body env)] (steps K (.compute [] env e')) =
               .ret [.funV (.VLam body env)] ve' := by
    generalize h_sK : steps K (.compute [] env e') = sK at hK_inact h_not_error
    match sK with
    | .compute .. => simp [isActive] at hK_inact
    | .ret [] ve' => exact ⟨ve', .inr rfl, by simp [liftState]⟩
    | .ret (_ :: _) _ => simp [isActive] at hK_inact
    | .halt ve' => exact ⟨ve', .inl rfl, by simp [liftState]⟩
    | .error => exact absurd rfl h_not_error
  -- Show ve' = ve by determinism
  have h_ve_eq : ve' = ve := by
    -- steps (K+1) inner = halt ve'
    have h_halt_ve' : steps (K + 1) (.compute [] env e') = .halt ve' := by
      cases h_inner_eq with
      | inl h => rw [steps_trans, h, steps_halt]
      | inr h => rw [steps_trans, h]; rfl
    -- steps Ke inner = halt ve, and K+1 ≤ Ke (or K = Ke)
    by_cases hle : K + 1 ≤ Ke
    · have h_Ke_eq : steps Ke (.compute [] env e') = .halt ve' := by
        have : Ke = (K + 1) + (Ke - (K + 1)) := by omega
        rw [this, steps_trans, h_halt_ve', steps_halt]
      rw [hKe] at h_Ke_eq; exact (State.halt.inj h_Ke_eq).symm
    · -- K+1 > Ke, so K = Ke
      have hKeq : K = Ke := by omega
      rw [← hKeq] at hKe
      -- steps K = halt ve and steps (K+1) = halt ve'
      -- step (halt ve) = halt ve, so halt ve' = halt ve
      have : steps (K + 1) (.compute [] env e') = .halt ve := by
        rw [steps_trans, hKe]; rfl
      rw [h_halt_ve'] at this; exact State.halt.inj this
  subst h_ve_eq
  -- Now: steps K (liftState base inner) = ret [funV ...] ve
  -- One more step: ret [funV (VLam body env)] ve → compute [] (env.extend ve) body
  -- Then Kb more steps reach s.
  -- Total: 3 + K + 1 + Kb steps
  -- Compose everything
  have h_total : steps (3 + K + 1 + Kb) (.compute [] env (.Apply (.Lam n body) e')) = s := by
    have : 3 + K + 1 + Kb = 3 + (K + (1 + Kb)) := by omega
    rw [this, steps_trans, h3, hlift, steps_trans, h_comm, h_lifted_eq]
    rw [show 1 + Kb = 1 + Kb from rfl, steps_trans]
    simp [steps, step, hKb]
  exact ⟨3 + K + 1 + Kb, h_total⟩

end Moist.Verified.StepLift
