# Proposal: Generalizing `dead_let_sound_closed` to Open Terms

> **Status**: Phase 1 complete — the bisimulation framework is generalized with σ. All files compile. Phase 2 (BehEq + dead_let_sound + lowerTotal_prepend_unused) is next.

## Motivation

`dead_let_sound_closed` currently proves:

```lean
BehEqClosed (.Let [(x, e, false)] body) body
```

where `BehEqClosed` requires both sides to be **closed MIR expressions** — lowered with `lowerTotal []` and evaluated from `.nil` env. This means the theorem can only be applied at the top level of a program. It cannot be composed with other optimizations or applied inside a lambda body where free variables are in scope.

We want to generalize to:

```lean
BehEq env (.Let [(x, e, false)] body) body
```

where `body` may contain free variables from `env`, and the equivalence holds under **any** compatible CEK environment.

---

## Current Architecture

### File Layout (`Moist/Verified/`)

| File | Role |
|------|------|
| `Semantics.lean` | `steps`, `Reaches`, `ValueEq`, `ListValueEq`, `BehEqClosed` |
| `ClosedAt.lean` | `closedAt`, `ValueRelV`, `EnvRelV`, `StateRel`, `FrameRel`, `StackRel` |
| `Bisim.lean` | `step_preserves`, `bisim_reaches`, `bisim_reaches_error` |
| `StepLift.lean` | `liftState`, `beta_reaches`, `beta_reaches_error`, `beta_apply_from_inner` |
| `DeadLet.lean` | `lowerTotal_closedAt`, `closedAt_envRelV_valueEq`, `dead_let_sound_closed` |
| `Example.lean` | Manual CEK-stepping proof + `dead_let_sound_closed` applications |

### Current Proof Strategy

The proof at `DeadLet.lean:449` uses three main components:

**1. Beta decomposition** (`StepLift.lean`): `beta_reaches` decomposes `Apply (Lam n body) e'` via `liftState` + `firstInactive` — works for **any** argument term and **any** CEK environment `env`. No step-counting or `IsValueTerm` restriction.

```lean
theorem beta_reaches (env : CekEnv) (body e' : Term) (n : Nat) (v : CekValue)
    (hreach : Reaches (.compute [] env (.Apply (.Lam n body) e')) (.halt v)) :
    ∃ ve, Reaches (.compute [] env e') (.halt ve) ∧
          Reaches (.compute [] (env.extend ve) body) (.halt v)
```

**2. Environment irrelevance** (`DeadLet.lean:458`): the critical trick:
```lean
lowerTotal_closed_env_irrel x body hsc.unused
-- rewrites: lowerTotal [x] body = lowerTotal [] body
```

Since `x ∉ freeVars body`, both sides produce the **same UPLC term** `body'`.

**3. Bridge** (`DeadLet.lean:486`): `closedAt_envRelV_valueEq` (same term, two `EnvRelV`-related envs → `ValueEq k`).

**4. Error equivalence** (`DeadLet.lean:470-480`): `BehEqClosed` now includes error agreement:
```lean
(Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧ ...
```
Handled via `beta_reaches_error` + `atomicPure_never_error` + `closedAt_zero_error_env_irrel`.

---

## The Shift Problem

For a non-empty `env = [a, b, c]`, lowering produces **different UPLC terms**:

| Side | MIR Lowering Env | Variable `a` Index | Variable `b` Index | Variable `c` Index |
|------|------------------|--------------------|--------------------|--------------------|
| LHS body | `x :: env` = `[x, a, b, c]` | 2 | 3 | 4 |
| RHS body | `env` = `[a, b, c]` | 1 | 2 | 3 |

Prepending `x` shifts all env-variable de Bruijn indices by +1. The trick `lowerTotal (x :: env) body = lowerTotal env body` does **not** hold — these are structurally different UPLC terms.

### What each side evaluates to

Given CEK environment `ρ`:

- **LHS**: `Apply (Lam 0 body_x) e'` in `ρ` → via `beta_reaches` → `body_x` in `ρ.extend ve`
  - Position 1 → `ve` (the dead binding — never accessed)
  - Position 2 → `ρ.lookup 1` (value of `a`)
  - Position 3 → `ρ.lookup 2` (value of `b`)
  - Position 4 → `ρ.lookup 3` (value of `c`)

- **RHS**: `body_env` in `ρ`
  - Position 1 → `ρ.lookup 1` (value of `a`)
  - Position 2 → `ρ.lookup 2` (value of `b`)
  - Position 3 → `ρ.lookup 3` (value of `c`)

The accessed values are **identical** — offset by 1. This is a **renaming**: the LHS term is the RHS term with all free variable indices incremented by 1, evaluated in a correspondingly shifted environment.

---

## Key Insight: Shift Weakening IS Bisimulation

The existing bisimulation (`StateRel` + `step_preserves`) proves:

> Same term, different environments → related results

Shift weakening needs:

> Renamed term, correspondingly renamed environment → related results

These are the same thing — a bisimulation — just with a more general notion of "related states." Rather than proving shift weakening as a standalone lemma (duplicating the ~200-line `step_preserves` case analysis), we **generalize `StateRel` to carry a renaming** so that the existing bisim handles both cases.

The identity renaming recovers the current behavior. A shift-by-1 renaming gives us the weakening property.

---

## Proposed Changes

### 1. Define Renaming Infrastructure

New file `Moist/Verified/Rename.lean` (or extend `ClosedAt.lean`):

```lean
/-- A renaming maps de Bruijn indices to de Bruijn indices.
    `shiftRename c` inserts a gap at position `c`:
    indices < c are unchanged, indices ≥ c are incremented by 1. -/
def shiftRename (c : Nat) (n : Nat) : Nat :=
  if n ≥ c then n + 1 else n

/-- Lift a renaming under a binder. Position 1 (the new binding) is
    kept fixed; all other positions are shifted through σ. -/
def liftRename (σ : Nat → Nat) : Nat → Nat
  | 0 => 0          -- position 0 is always unused
  | 1 => 1          -- the new lambda binding
  | n + 2 => σ (n + 1) + 1  -- existing vars shifted

/-- Lifting shiftRename c yields shiftRename (c + 1). -/
theorem liftRename_shift (c : Nat) :
    liftRename (shiftRename c) = shiftRename (c + 1)

/-- Apply renaming to a UPLC term. -/
mutual
  def renameTerm (σ : Nat → Nat) : Term → Term
    | .Var n => .Var (σ n)
    | .Lam name body => .Lam name (renameTerm (liftRename σ) body)
    | .Apply f x => .Apply (renameTerm σ f) (renameTerm σ x)
    | .Force e => .Force (renameTerm σ e)
    | .Delay e => .Delay (renameTerm σ e)
    | .Constr tag args => .Constr tag (renameTermList σ args)
    | .Case scrut alts => .Case (renameTerm σ scrut) (renameTermList σ alts)
    | t => t  -- Constant, Builtin, Error
  def renameTermList (σ : Nat → Nat) : List Term → List Term
    | [] => []
    | t :: ts => renameTerm σ t :: renameTermList σ ts
end

/-- renameTerm id = id -/
theorem renameTerm_id : renameTerm id t = t
```

### 2. Generalize `EnvRelV`

Currently (`ClosedAt.lean:269`):
```lean
inductive EnvRelV : Nat → CekEnv → CekEnv → Prop where
  | mk : (∀ n, 0 < n → n ≤ d →
            LookupRelV (env1.lookup n) (env2.lookup n)) →
          EnvRelV d env1 env2
```

Generalized to carry a renaming:
```lean
inductive EnvRelV : (Nat → Nat) → Nat → CekEnv → CekEnv → Prop where
  | mk : (∀ n, 0 < n → n ≤ d →
            LookupRelV (env1.lookup (σ n)) (env2.lookup n)) →
          EnvRelV σ d env1 env2
```

The current behavior is recovered with `σ = id`. For dead-let weakening, `σ = shiftRename 1` and `env1 = ρ.extend ve`, `env2 = ρ`:
- `(ρ.extend ve).lookup (n + 1) = ρ.lookup n` for `n ≥ 1` ✓

Key lemma — extension preserves the relation with lifted renaming:
```lean
theorem envRelV_extend (σ : Nat → Nat) (d : Nat) (env1 env2 : CekEnv)
    (v1 v2 : CekValue) (henv : EnvRelV σ d env1 env2) (hv : ValueRelV v1 v2) :
    EnvRelV (liftRename σ) (d + 1) (env1.extend v1) (env2.extend v2)
```

### 3. Generalize `FrameRel`, `StackRel`, `StateRel`

**`FrameRel`** — frames that carry terms get the renaming applied:
```lean
inductive FrameRel : (Nat → Nat) → Frame → Frame → Prop where
  | force : FrameRel σ .force .force
  | arg (d : Nat) (t : Term) (henv : EnvRelV σ d env1 env2)
        (hclosed : closedAt d t = true) :
      FrameRel σ (.arg (renameTerm σ t) env1) (.arg t env2)
  | funV (hv : ValueRelV v1 v2) : FrameRel σ (.funV v1) (.funV v2)
  | applyArg (hv : ValueRelV v1 v2) : FrameRel σ (.applyArg v1) (.applyArg v2)
  | constrField (d : Nat) (tag : Nat) (hdone : ListValueRelV done1 done2)
      (todo : List Term) (htodo : closedAtList d todo = true)
      (henv : EnvRelV σ d env1 env2) :
      FrameRel σ (.constrField tag done1 (renameTermList σ todo) env1)
                  (.constrField tag done2 todo env2)
  | caseScrutinee (d : Nat) (alts : List Term) (halts : closedAtList d alts = true)
      (henv : EnvRelV σ d env1 env2) :
      FrameRel σ (.caseScrutinee (renameTermList σ alts) env1)
                  (.caseScrutinee alts env2)
```

**`StackRel`** — each frame can carry its own renaming (different closures may have different rename contexts):
```lean
inductive FrameRelAny : Frame → Frame → Prop where
  | mk (σ : Nat → Nat) (h : FrameRel σ f1 f2) : FrameRelAny f1 f2

inductive StackRel : Stack → Stack → Prop where
  | nil : StackRel [] []
  | cons (hf : FrameRelAny f1 f2) (hrs : StackRel s1 s2) :
      StackRel (f1 :: s1) (f2 :: s2)
```

Note: `StackRel` is renaming-independent — each frame bundles its own `σ`. This mirrors how the current `FrameRel` bundles its own depth `d`. The `force`, `funV`, and `applyArg` frames don't carry terms, so their renaming is irrelevant.

**`StateRel`** — the compute constructor carries the renaming:
```lean
inductive StateRel : State → State → Prop where
  | compute (hs : StackRel s1 s2) (σ : Nat → Nat) (d : Nat)
      (henv : EnvRelV σ d env1 env2) (ht : closedAt d t = true) :
      StateRel (.compute s1 env1 (renameTerm σ t)) (.compute s2 env2 t)
  | ret (hs : StackRel s1 s2) (hv : ValueRelV v1 v2) :
      StateRel (.ret s1 v1) (.ret s2 v2)
  | error : StateRel .error .error
  | halt (hv : ValueRelV v1 v2) :
      StateRel (.halt v1) (.halt v2)
```

The current behavior (same term both sides) is recovered by `σ = id` and `renameTerm id t = t`.

### 4. Update `step_preserves`

The proof structure is **identical** to the current one. `renameTerm σ` distributes over every term constructor, so each case just pushes the rename inward:

```lean
theorem step_preserves {s₁ s₂ : State} (h : StateRel s₁ s₂) :
    StateRel (step s₁) (step s₂) := by
  cases h with
  | error => exact .error
  | halt hv => exact .halt hv
  | compute hs σ d henv ht =>
    cases ‹Term› with   -- case split on t (the RHS/unrenamed term)
    | Var n =>
      -- LHS has renameTerm σ (.Var n) = .Var (σ n)
      -- step looks up env1.lookup (σ n) and env2.lookup n
      -- EnvRelV σ d env1 env2 gives LookupRelV between them
      ...
    | Apply f x =>
      -- renameTerm σ (.Apply f x) = .Apply (renameTerm σ f) (renameTerm σ x)
      -- Both sides push an arg frame and evaluate the function
      -- arg frame carries σ, env relation, closedAt witness
      simp [renameTerm, step]
      have ⟨hf, hx⟩ := closedAt_apply ht
      exact .compute (.cons (.mk σ (.arg d x henv hx)) hs) σ d henv hf
    | Lam n body =>
      -- renameTerm σ (.Lam n body) = .Lam n (renameTerm (liftRename σ) body)
      -- Both sides return VLam with their respective envs
      -- ValueRelV.vlam carries liftRename σ ... but wait.
      ...
    ...
  | ret hs hv => ...  -- unchanged from current proof
```

**The Var case** is the only materially different case. Currently it looks up `env1.lookup n` and `env2.lookup n` — now it looks up `env1.lookup (σ n)` and `env2.lookup n`. The generalized `EnvRelV σ` gives exactly this.

**The Lam/Delay cases** produce `ValueRelV` closures. Currently `ValueRelV.vlam` bundles the same body on both sides. Now one side has `renameTerm (liftRename σ) body` and the other has `body`. This requires generalizing `ValueRelV.vlam`:

```lean
| vlam (σ : Nat → Nat) (d : Nat)
    (hclosed : closedAt (d + 1) body = true)
    (henv : EnvRelV σ d env1 env2) :
    ValueRelV (.VLam (renameTerm (liftRename σ) body) env1) (.VLam body env2)
```

Current behavior recovered with `σ = id` + `renameTerm (liftRename id) body = body`.

**The ret cases** (`funV`, `applyArg`, `caseScrutinee`, `constrField`) are the same as current — they pattern-match on `ValueRelV` constructors and extract the carried `σ`/env relation. The generalized `ValueRelV.vlam` carries the renaming, so when a lambda closure is applied, the body is evaluated with `EnvRelV (liftRename σ)`.

**The refl cases** (`step_force_refl`, `step_funV_refl`, etc.) work unchanged because `ValueRelV.refl` implies both sides are identical — renaming is `id`, envs are the same.

### 5. Impact on `ValueRelV`

Generalize to carry a renaming for closures:

```lean
inductive ValueRelV : CekValue → CekValue → Prop where
  | vcon : ValueRelV (.VCon c) (.VCon c)
  | vlam (σ : Nat → Nat) (d : Nat)
      (hclosed : closedAt (d + 1) body = true)
      (henv : EnvRelV σ d env1 env2) :
      ValueRelV (.VLam (renameTerm (liftRename σ) body) env1) (.VLam body env2)
  | vdelay (σ : Nat → Nat) (d : Nat)
      (hclosed : closedAt d body = true)
      (henv : EnvRelV σ d env1 env2) :
      ValueRelV (.VDelay (renameTerm σ body) env1) (.VDelay body env2)
  | vconstr (htag : tag1 = tag2) (hfs : ListValueRelV fs1 fs2) :
      ValueRelV (.VConstr tag1 fs1) (.VConstr tag2 fs2)
  | vbuiltin (hb : b1 = b2) (hargs : ListValueRelV args1 args2) (hea : ea1 = ea2) :
      ValueRelV (.VBuiltin b1 args1 ea1) (.VBuiltin b2 args2 ea2)
  | refl : ValueRelV v v
```

### 6. Syntactic Shift Lemma

In `MIR/LowerTotal.lean`:

```lean
theorem lowerTotal_prepend_unused (env : List VarId) (x : VarId)
    (body : Expr) (t : Term)
    (hunused : (freeVars body).contains x = false)
    (hlower : lowerTotal env body = some t) :
    lowerTotal (x :: env) body = some (renameTerm (shiftRename 1) t)
```

### 7. Define `BehEq` and Prove `dead_let_sound`

In `Verified/Semantics.lean`:
```lean
def BehEq (env : List VarId) (m1 m2 : Expr) : Prop :=
  match lowerTotal env m1, lowerTotal env m2 with
  | some t1, some t2 =>
    (∀ ρ, Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
    ∀ (k : Nat) (ρ : CekEnv) (v1 v2 : CekValue),
      Reaches (.compute [] ρ t1) (.halt v1) →
      Reaches (.compute [] ρ t2) (.halt v2) →
      ValueEq k v1 v2
  | _, _ => True
```

In `Verified/DeadLet.lean`:
```lean
theorem dead_let_sound (env : List VarId) (x : VarId) (e body : Expr)
    (hsc : MIRDeadLetCond x e body) :
    BehEq env (.Let [(x, e, false)] body) body
```

Proof outline:
1. Lower both sides. LHS becomes `Apply (Lam 0 body_x) e'` where `body_x = renameTerm (shiftRename 1) body_env` (by `lowerTotal_prepend_unused`)
2. **Value case**: `beta_reaches` gives `body_x` in `ρ.extend ve`. Construct `StateRel` with `σ = shiftRename 1`, `EnvRelV (shiftRename 1) d (ρ.extend ve) ρ`. Apply `bisim_reaches` → `ValueRelV` → `ValueRelV.toValueEq` → `ValueEq k`.
3. **Error case**: same structure with `bisim_reaches_error`.

---

## What Already Works Unchanged

| Component | Why it's ready |
|-----------|---------------|
| `beta_reaches` / `beta_reaches_error` / `beta_apply_from_inner` | Already env-parametric |
| `lowerTotal_closedAt` | Works for any `env : List VarId` |
| `closedAt_envRelV_valueEq` + `env_rel_bundle_aux` | Already handles general `EnvRelV` — just needs to accept the new `σ`-parameterized version |
| `evalBuiltin_relV` | Only touches `ValueRelV` values (VCon/refl cases) — renaming is irrelevant |
| `StepLift.lean` | Entirely about single-environment computation — no changes needed |

---

## Work Breakdown

| Component | File | Change Type | Complexity |
|-----------|------|-------------|-----------|
| `renameTerm`, `liftRename`, `shiftRename` | New `Rename.lean` or `ClosedAt.lean` | New definitions + lemmas | Low |
| `renameTerm_id`, `renameTerm` distributes over constructors | Same | New proofs | Low |
| `liftRename_shift`, `closedAt` of renamed terms | Same | New proofs | Low-Medium |
| `EnvRelV` generalized with `σ` | `ClosedAt.lean` | Modify definition | Low |
| `envRelV_extend` with `liftRename` | `ClosedAt.lean` | Modify proof | Medium |
| `ValueRelV.vlam`/`vdelay` with `σ` | `ClosedAt.lean` | Modify definition | Low |
| `FrameRel` with `σ` on term-carrying frames | `ClosedAt.lean` | Modify definition | Low |
| `StateRel.compute` with `σ` | `ClosedAt.lean` | Modify definition | Low |
| `step_preserves` generalized | `Bisim.lean` | Modify proof (~200 lines) | **Medium-High** |
| `refl` case helpers generalized | `Bisim.lean` | Modify proofs | Medium |
| `env_rel_bundle_aux` / `closedAt_envRelV_valueEq` | `DeadLet.lean` | Modify to accept `σ`-parameterized `EnvRelV` | Medium |
| `lowerTotal_prepend_unused` | `LowerTotal.lean` | New proof | Medium |
| `BehEq` + `dead_let_sound` | `Semantics.lean` + `DeadLet.lean` | New | Medium |

### Key Observation on `step_preserves`

The proof's case analysis structure is **identical** to the current one. For every non-Var term constructor, `renameTerm σ` distributes through:
```
renameTerm σ (.Apply f x) = .Apply (renameTerm σ f) (renameTerm σ x)
```
So the step function produces the same structure on both sides. The only new reasoning is in the **Var case** (lookup through `σ`) and the **Lam/Delay cases** (produce `ValueRelV` with `liftRename σ`). The `ret` cases are essentially the same because they just destructure `ValueRelV` and `FrameRel`.

The `evalBuiltin_relV` proof needs **no changes** — it works on `ValueRelV` for builtins/constants, which are renaming-independent (VCon, VBuiltin carry no terms).

The `refl` case helpers (`step_force_refl`, `step_funV_refl`, `step_applyArg_refl`, `step_case_refl`) can remain specialized for `refl` since `ValueRelV.refl` means identical values with trivially identity renaming.

---

## Open Questions

1. **Should the renaming be a general `σ : Nat → Nat` or restricted to `shiftRename c`?** General is cleaner conceptually and future-proofs for other transformations (e.g., substitution). Restricted is simpler to reason about (e.g., `liftRename` has a closed form). Recommend: use general `σ` in definitions, prove specialized lemmas for `shiftRename`.

2. **Should `renameTerm_id` be a `@[simp]` lemma or handled by definitional equality?** If `σ = id` and we rely on `renameTerm id t = t` being `rfl`, we need the termination checker to cooperate. More likely, it's a proof by structural induction that should be `@[simp]`.

3. **Should `StackRel` carry a single `σ` or per-frame `σ`?** Per-frame (via `FrameRelAny`) is more general and matches the current per-frame depth. A single `σ` would be simpler but less compositional — closures from different scopes may carry different renamings.

4. **Should `atomicPure_halts` be generalized to non-empty lowering envs?** Currently it only handles `lowerTotal [] e`. For the open case, we need `lowerTotal env e` — but since `e` is atomic pure (Lit/Builtin/Lam/Delay), the lowered term structure is the same regardless of env. Need a small generalization.
