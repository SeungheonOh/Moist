# Feasibility Analysis: `refines_app_arg_behEq`

## Target Theorem

```lean
theorem refines_app_arg_behEq (f a a' : Expr) (ha : a ⊑ a') :
    Expr.App f a ⊑ Expr.App f a'
```

This says: if `a` refines `a'` (same compilation + behavioral equivalence),
then `App f a` refines `App f a'` for any `f`.

## Definitions Involved

### `Refines` (Semantics.lean:278-280)

```lean
def Refines (m1 m2 : Expr) : Prop :=
  (∀ env, (lowerTotalExpr env m1).isSome → (lowerTotalExpr env m2).isSome) ∧
  BehEq m1 m2
```

Two components: (1) compilation preservation, (2) behavioral equivalence.

### `BehEq` (Semantics.lean:260-271)

```lean
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
```

For every lowering environment and well-sized runtime environment:
error agreement, halting agreement, and step-indexed value equivalence.

### `ValueEq` for VLam (Semantics.lean:143-152)

```lean
| k + 1, .VLam body1 env1, .VLam body2 env2 =>
    ∀ (arg : CekValue),
      (Reaches (.compute [] (env1.extend arg) body1) .error ↔
       Reaches (.compute [] (env2.extend arg) body2) .error) ∧
      (Halts (.compute [] (env1.extend arg) body1) ↔
       Halts (.compute [] (env2.extend arg) body2)) ∧
      ∀ (v1 v2 : CekValue),
        Reaches (.compute [] (env1.extend arg) body1) (.halt v1) →
        Reaches (.compute [] (env2.extend arg) body2) (.halt v2) →
        ValueEq k v1 v2
```

Both closures receive the **same** `arg`. This is the critical design choice
that drives the entire feasibility analysis.

### CEK step for `Apply` (Machine.lean:107,128-139)

```
compute s ρ (Apply f x) → compute (arg x ρ :: s) ρ f
ret (arg m ρ :: s) vf   → compute (funV vf :: s) ρ m
ret (funV (VLam body ρ) :: s) vx → compute s (ρ.extend vx) body
ret (funV (VBuiltin b args ea) :: s) vx → [builtin saturation logic]
ret (funV _ :: _) _      → error
```

### CekEnv (Value.lean:79-96)

```lean
inductive CekEnv where
  | nil : CekEnv
  | cons : CekValue → CekEnv → CekEnv

def lookup : CekEnv → Nat → Option CekValue
  | .nil, _ => none
  | .cons _ _, 0 => none
  | .cons v _, 1 => some v
  | .cons _ rest, n + 1 => lookup rest n

def extend (env : CekEnv) (v : CekValue) : CekEnv := .cons v env
```

1-based de Bruijn. `extend` prepends. `lookup 0 = none` always.

---

## Phase-by-Phase Analysis

### Phase 1: `compute_to_error_from_error`

**Statement:**

```lean
theorem compute_to_error_from_error (ρ : CekEnv) (t : Term) (extra : Stack)
    (h : Reaches (.compute [] ρ t) .error) :
    Reaches (.compute extra ρ t) .error
```

**Status:** Does not exist yet. Needed by Phase 2d.

**Proof logic:**

1. Unpack `h` to `⟨N, hN⟩` where `steps N (compute [] ρ t) = error`.
2. `compute extra ρ t = liftState extra (compute [] ρ t)` by definition.
3. At step N, inner state is `.error`, which is inactive.
4. By `firstInactive`, get minimal `K ≤ N` where inner is inactive.
5. By `steps_liftState`, commutation holds for K steps.
6. Case-split on `steps K (compute [] ρ t)`:
   - `.compute` or `.ret (_ :: _)`: contradicts inactivity.
   - `.error`: `liftState extra .error = .error`. Return `⟨K, ...⟩`.
   - `.halt v`: `steps N inner = .halt v` by `steps_halt`.
     But `steps N inner = .error`. Contradiction (`.halt v ≠ .error`).
   - `.ret [] v`: `steps (K+1) inner = .halt v`.
     Then `steps N inner = .halt v` by `steps_halt`. Same contradiction.

**Verdict: Provable.** Mirrors `compute_to_ret_from_halt` (Purity.lean:156)
and `force_sub_error` (Congruence.lean:1043). All infrastructure exists:
`firstInactive`, `steps_liftState`, `liftState_eq_error`, `steps_error`,
`steps_halt`.

**Estimated size:** ~40 lines.

---

### Phase 2: Application Decomposition

Three lemmas that decompose `Apply tf ta` evaluation into function phase,
argument phase, and frame application phase.

#### Phase 2a: `app_reaches` (halt decomposition)

**Statement:**

```lean
theorem app_reaches (ρ : CekEnv) (tf ta : Term) (w : CekValue)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) (.halt w)) :
    ∃ vf vx,
      Reaches (.compute [] ρ tf) (.halt vf) ∧
      Reaches (.compute [] ρ ta) (.halt vx) ∧
      Reaches (.ret [.funV vf] vx) (.halt w)
```

**Proof logic:**

Step A (initial mechanical step):
- `steps 1 (compute [] ρ (Apply tf ta)) = compute [arg ta ρ] ρ tf`.
  By the `step` definition for `Apply`.
- Remaining: `steps (N-1) (compute [arg ta ρ] ρ tf) = halt w`.

Step B (first liftState phase, function evaluation):
- `compute [arg ta ρ] ρ tf = liftState [arg ta ρ] (compute [] ρ tf)`.
- Apply `firstInactive` to inner computation `compute [] ρ tf` bounded by N-1.
- `steps_liftState` gives commutation for the first K1 steps.
- Case-split inner state at K1:
  - `.error`: liftState gives `.error`, but remaining steps reach `.halt w`.
    `steps_error` gives error forever. Contradiction.
  - `.halt vf` or `.ret [] vf`: liftState gives `.ret [arg ta ρ] vf`.
    Extract `Reaches (compute [] ρ tf) (.halt vf)`.
  - `.compute` or `.ret (_ :: _)`: contradicts inactivity.

Step C (mechanical step through arg frame):
- After K1 lifted steps: at `ret [arg ta ρ] vf`.
- `step (ret [arg ta ρ] vf) = compute [funV vf] ρ ta`.
  This is **unconditional** (Machine.lean:128).

Step D (second liftState phase, argument evaluation):
- `compute [funV vf] ρ ta = liftState [funV vf] (compute [] ρ ta)`.
- Apply `firstInactive` again to `compute [] ρ ta` bounded by remaining steps.
- Same case analysis. Extract `vx` where argument halts.

Step E (remaining steps):
- After function and argument phases: at `ret [funV vf] vx`.
- Remaining steps give `Reaches (ret [funV vf] vx) (.halt w)`.
- Return `⟨vf, vx, hf_reaches, ha_reaches, hframe_reaches⟩`.

**Verification of step count arithmetic:**
- Total N steps. 1 initial step. K1 for function phase. 1 for arg-to-funV transition.
  K2 for argument phase. Remaining = N - 1 - K1 - 1 - K2.
- Each bound is non-negative: from K1 ≤ N-1, K2 ≤ (remaining after K1 and transition).
- `omega` handles all arithmetic.

**Verdict: Provable.** Same pattern as `force_reaches` (Congruence.lean:638)
but with two liftState phases instead of one.

**Estimated size:** ~80 lines.

#### Phase 2b: `app_reaches_error` (error decomposition)

**Statement:**

```lean
theorem app_reaches_error (ρ : CekEnv) (tf ta : Term)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) .error) :
    Reaches (.compute [] ρ tf) .error ∨
    ∃ vf, Reaches (.compute [] ρ tf) (.halt vf) ∧
      (Reaches (.compute [] ρ ta) .error ∨
       ∃ vx, Reaches (.compute [] ρ ta) (.halt vx) ∧
             Reaches (.ret [.funV vf] vx) .error)
```

**Proof logic:**

Same decomposition as Phase 2a but targeting `.error`. At each liftState phase,
case-split: did the inner computation error, or did it produce a value?

Function phase:
- Inner `.error` at K1: `Left ⟨K1, proof⟩`.
- Inner `.halt vf`: continue to argument phase.

Argument phase:
- Inner `.error` at K2: `Right ⟨vf, hf, Left ⟨K2, proof⟩⟩`.
- Inner `.halt vx`: remaining steps give frame error.
  `Right ⟨vf, hf, Right ⟨vx, ha, ⟨R, proof⟩⟩⟩`.

**Verdict: Provable.** Same pattern as `force_reaches_error` (Congruence.lean:698).

**Estimated size:** ~100 lines.

#### Phase 2c: `app_apply_from_parts` (synthesis)

**Statement:**

```lean
theorem app_apply_from_parts (ρ : CekEnv) (tf ta : Term)
    (vf vx : CekValue) (s : State)
    (hf : Reaches (.compute [] ρ tf) (.halt vf))
    (ha : Reaches (.compute [] ρ ta) (.halt vx))
    (hcont : Reaches (.ret [.funV vf] vx) s) :
    Reaches (.compute [] ρ (.Apply tf ta)) s
```

**Proof logic:**

1. `steps 1 (compute [] ρ (Apply tf ta)) = compute [arg ta ρ] ρ tf`.
2. `compute_to_ret_from_halt ρ tf vf [arg ta ρ] hf`
   gives `Reaches (compute [arg ta ρ] ρ tf) (ret [arg ta ρ] vf)` in Kf steps.
3. `step (ret [arg ta ρ] vf) = compute [funV vf] ρ ta` (1 step).
4. `compute_to_ret_from_halt ρ ta vx [funV vf] ha`
   gives `Reaches (compute [funV vf] ρ ta) (ret [funV vf] vx)` in Ka steps.
5. `hcont` gives `Reaches (ret [funV vf] vx) s` in Kc steps.
6. Total: `1 + Kf + 1 + Ka + Kc` steps. Compose via `steps_trans`.

**Verdict: Provable.** Same pattern as `beta_apply_from_inner` (StepLift.lean:399)
but without assuming `Lam` form for the function.

**Estimated size:** ~30 lines.

#### Phase 2d: Error synthesis helpers

```lean
theorem app_error_from_fun_error (ρ : CekEnv) (tf ta : Term)
    (h : Reaches (.compute [] ρ tf) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error

theorem app_error_from_arg_error (ρ : CekEnv) (tf ta : Term) (vf : CekValue)
    (hf : Reaches (.compute [] ρ tf) (.halt vf))
    (ha : Reaches (.compute [] ρ ta) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error
```

**Proof logic for `app_error_from_fun_error`:**

1. 1 step: `compute [] ρ (Apply tf ta) → compute [arg ta ρ] ρ tf`.
2. `compute_to_error_from_error ρ tf [arg ta ρ] h`
   gives `Reaches (compute [arg ta ρ] ρ tf) .error`.
3. Compose: total = 1 + error steps.

**Proof logic for `app_error_from_arg_error`:**

1. 1 step + `compute_to_ret_from_halt` for function → `ret [arg ta ρ] vf`.
2. 1 step → `compute [funV vf] ρ ta`.
3. `compute_to_error_from_error ρ ta [funV vf] ha`
   gives `Reaches (compute [funV vf] ρ ta) .error`.
4. Compose.

**Verdict: Provable.** Thin wrappers around Phase 1 and `compute_to_ret_from_halt`.

**Estimated size:** ~30 lines total.

---

### Phase 3: `EnvValueEq` and Its Lemmas

**Definition:**

```lean
def EnvValueEq (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False
```

#### Phase 3a: `envValueEq_refl`

```lean
theorem envValueEq_refl (k d : Nat) (ρ : CekEnv) : EnvValueEq k d ρ ρ
```

Logic: `intro n hn hle`. `ρ.lookup n` matches itself.
If `some v`: `ValueEq k v v` from `valueEq_refl`. If `none`: `True`.

**Verdict: Trivially provable.**

#### Phase 3b: `envValueEq_extend`

```lean
theorem envValueEq_extend (k d : Nat) {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hρ : EnvValueEq k d ρ₁ ρ₂) (hv : ValueEq k v₁ v₂) :
    EnvValueEq k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂)
```

Logic by case-split on n:
- `n = 0`: excluded by `0 < n`.
- `n = 1`: `(ρ.extend v).lookup 1 = some v`. Both sides give `some v₁`, `some v₂`.
  Need `ValueEq k v₁ v₂`. Have `hv`.
- `n = m + 2`: `(ρ.extend v).lookup (m+2) = ρ.lookup (m+1)`.
  Both sides reduce to `ρ₁.lookup (m+1)`, `ρ₂.lookup (m+1)`.
  From `hρ (m+1) (by omega) (by omega)`.

Verified against CekEnv definitions:
- `extend env v = cons v env`
- `lookup (cons v env) 1 = some v`
- `lookup (cons v env) (n+1) = lookup env n` for all n

**Verdict: Provable.** Clean case split.

#### Phase 3c: `envValueEq_lookup_left`

```lean
theorem envValueEq_lookup_left {k d : Nat} {ρ₁ ρ₂ : CekEnv} {n : Nat} {v₁ : CekValue}
    (hρ : EnvValueEq k d ρ₁ ρ₂) (hn : 0 < n) (hd : n ≤ d)
    (h₁ : ρ₁.lookup n = some v₁) :
    ∃ v₂, ρ₂.lookup n = some v₂ ∧ ValueEq k v₁ v₂
```

Logic: Specialize `hρ n hn hd`. Rewrite with `h₁`.
If `ρ₂.lookup n = none`: match gives `False`. Contradiction.
If `ρ₂.lookup n = some v₂`: match gives `ValueEq k v₁ v₂`.

**Verdict: Trivially provable.**

#### Phase 3d: `envValueEq_index_mono`

```lean
theorem envValueEq_index_mono (hρ : EnvValueEq (k+1) d ρ₁ ρ₂) :
    EnvValueEq k d ρ₁ ρ₂
```

Requires `valueEq_mono` (Phase 4). At each position, downgrade from
`ValueEq (k+1)` to `ValueEq k`.

**Verdict: Provable given Phase 4.**

**Total Phase 3 estimated size:** ~60 lines.

---

### Phase 4: `valueEq_mono` and Builtin Extensionality

#### Phase 4a: `valueEq_mono`

**Statement:**

```lean
mutual
  theorem valueEq_mono : ∀ (k : Nat) (v₁ v₂ : CekValue),
      ValueEq (k + 1) v₁ v₂ → ValueEq k v₁ v₂
  theorem listValueEq_mono : ∀ (k : Nat) (vs₁ vs₂ : List CekValue),
      ListValueEq (k + 1) vs₁ vs₂ → ListValueEq k vs₁ vs₂
end
```

**Proof logic by mutual induction on k:**

Base `k = 0`: `ValueEq 0 v₁ v₂ = True`. Trivial.

Successor `k + 1`: Need `ValueEq (k+2) v₁ v₂ → ValueEq (k+1) v₁ v₂`.
Case-split on value constructors:

- `VCon, VCon`: `c₁ = c₂` at both levels. Same.
- `VLam body₁ env₁, VLam body₂ env₂`:
  At `k+2`: `∀ arg, error↔ ∧ halts↔ ∧ (∀ w₁ w₂, ... → ValueEq (k+1) w₁ w₂)`.
  At `k+1`: need `∀ arg, error↔ ∧ halts↔ ∧ (∀ w₁ w₂, ... → ValueEq k w₁ w₂)`.
  Error↔ and halts↔ are identical (not indexed). For value clause:
  `ValueEq (k+1) w₁ w₂ → ValueEq k w₁ w₂` by IH.
- `VDelay body₁ env₁, VDelay body₂ env₂`: Same structure as VLam.
- `VConstr tag₁ fs₁, VConstr tag₂ fs₂`: Tag equal. `ListValueEq (k+1) → ListValueEq k` by `listValueEq_mono` IH.
- `VBuiltin b₁ args₁ ea₁, VBuiltin b₂ args₂ ea₂`:
  `b₁ = b₂`, `ListValueEq (k+1) → ListValueEq k`, `ea₁ = ea₂`,
  evalBuiltin none↔ (same), evalBuiltin result `ValueEq (k+1) → ValueEq k` by IH.
- Cross-constructor cases (20 pairs): `ValueEq (k+2) = False`. Contradiction.

**Key verification:** The VLam case uses the IH `valueEq_mono k` on `w₁, w₂`
which are universally quantified, not structurally smaller. This is fine
because induction is on `k`, not on values.

**Verdict: Provable.** Same exhaustive case-split pattern as `valueEq_trans`
(Semantics.lean:351-428) and `valueEq_symm` (Semantics.lean:307-350).

**Estimated size:** ~80 lines.

#### Phase 4b: `evalBuiltin_listValueEq`

**Statement:**

```lean
theorem evalBuiltin_listValueEq (k : Nat) (b : BuiltinFun)
    (args₁ args₂ : List CekValue)
    (hargs : ListValueEq (k + 1) args₁ args₂) :
    (evalBuiltin b args₁ = none ↔ evalBuiltin b args₂ = none) ∧
    (∀ r₁ r₂,
      evalBuiltin b args₁ = some r₁ →
      evalBuiltin b args₂ = some r₂ →
      ValueEq k r₁ r₂)
```

**Proof logic (two-stage, mirroring Bisim.lean):**

**Stage 1: VCon skeleton preservation.**

```lean
private theorem valueEq_vconProj (k : Nat) (v₁ v₂ : CekValue)
    (h : ValueEq (k + 1) v₁ v₂) : vconProj v₁ = vconProj v₂
```

Case-split on `v₁, v₂`:
- `VCon c₁, VCon c₂`: `ValueEq (k+1)` gives `c₁ = c₂`. `vconProj` agrees.
- `VCon, non-VCon`: `ValueEq (k+1) = False`. Contradiction.
- `non-VCon, non-VCon`: both `vconProj` return `none`.

Then `listValueEq_vconSkel`: by induction on `ListValueEq`.

**Stage 2: `extractConsts` agreement.**

If both argument lists have the same VCon skeleton, `extractConsts` produces
identical constant lists (or both fail). Proof by structural induction on
`ListValueEq`, same as `Bisim.extractConsts_relV` (Bisim.lean:166-199).

**Stage 3: evalBuiltin case split.**

- Constant builtins: `extractConsts` agrees on both sides. `evalBuiltinConst` is
  a pure function on constants. Identical inputs produce identical `VCon` output.
  `ValueEq k (VCon c) (VCon c)` by `valueEq_refl`.
- Pass-through builtins (IfThenElse, ChooseUnit, Trace, ChooseData, ChooseList, MkCons):
  Condition value is `VCon` (same on both sides by `ValueEq`). Same argument selected.
  Result is `ValueEq (k+1)`-related (from `ListValueEq (k+1)`).
  Downgrade to `ValueEq k` via `valueEq_mono`.
- Non-pass-through, non-constant builtins: `evalBuiltinPassThrough` returns `none`.
  Both `none`. Trivial.

**Verdict: Provable.** Mirrors `Bisim.evalBuiltin_passThrough_relV` (Builtin.lean:259)
with `ListValueEq` replacing `ListValueRelV` and `valueEq_mono` handling the index shift.

**Estimated size:** ~100 lines.

---

### Phase 5: Same-Body Adequacy

This is the critical phase. We need to show that the **same** closed term
evaluated under two environments that differ only at one variable position
produces equivalent results.

#### What is needed

For `funV_frame_beh` in the VLam case, both sides evaluate the same `body`
under `ρ_closure.extend vx` vs `ρ_closure.extend vx'` where `ρ_closure` is
identical and `ValueEq (k+1) vx vx'`. We need:

1. **Error↔**: `Reaches (compute [] (ρ.extend vx) body) .error ↔ Reaches (compute [] (ρ.extend vx') body) .error`
2. **Halts↔**: Same for halting.
3. **ValueEq k**: When both halt, results are `ValueEq k`-related.

#### The core difficulty

The `ValueEq` definition for VLam applies both closures to the **same** `arg`:

```lean
∀ (arg : CekValue),
  Reaches (.compute [] (env1.extend arg) body1) ...
  Reaches (.compute [] (env2.extend arg) body2) ...
```

During execution of `body`, if a variable lookup produces `vx` (left) vs `vx'` (right),
and `vx` is a `VLam` closure that gets applied, the two sides enter **different**
closure bodies with **different** closure environments. At this point we cannot
use `ValueEq` on the closures because it only handles same-argument application,
and subsequent values diverge structurally.

#### Why existing shortcuts fail

**Bisimulation shortcut (DeadLet.lean:358):**
The existing proof for `closedAt_envRelV_valueEq` handles compound terms
(`Apply`, `Force`, `Constr`, `Case`) by delegating to `bisim_reaches`, which
provides `ValueRelV` (structural relation). This requires `StateRel`, which
requires `EnvRelV` (structural environment relation).

We cannot build `EnvRelV` from `EnvValueEq` because:
- `EnvRelV σ d env₁ env₂` requires `ValueRelV` at each position.
- `EnvValueEq k d ρ₁ ρ₂` gives `ValueEq k` at each position.
- `ValueEq k → ValueRelV` is **not provable** in general.
  (`ValueRelV` is structural; `ValueEq` is observational.)

**Error↔ at k = 0:**
`EnvValueEq 0 d ρ₁ ρ₂` says `ValueEq 0` (= `True`) at each position.
The values could be structurally unrelated (e.g., `VLam` vs `VCon`
at index `k+1` would give `False`, but at index 0 gives `True`).
Error behavior can genuinely differ under `EnvValueEq 0`.

Counterexample: `body = Apply (Var 1) (Var 1)`.
`ρ₁: lookup 1 = VLam ... (self-application halts)`.
`ρ₂: lookup 1 = VCon 42 (application errors)`.
`ValueEq 0 (VLam ...) (VCon 42) = True`.
But `compute [] ρ₁ body` halts while `compute [] ρ₂ body` errors.

Therefore error↔ under `EnvValueEq 0` is **false**.

#### The fundamental blocker

The `ValueEq` definition for VLam quantifies over a **single** argument
applied to both closures, not over two `ValueEq`-related arguments.
This means:

1. Same-body adequacy for compound terms cannot recurse through the
   `ValueEq` clause on intermediate closures, because intermediate
   closures on the two sides may have different bodies/environments,
   and we'd need to apply them to different arguments.

2. Error↔ cannot be derived from `EnvValueEq k` for general `k`
   because the step-indexed nature means at `k = 0` all values
   are trivially related regardless of actual behavior.

3. No combination of induction on `k`, structural induction on
   terms, or induction on execution steps resolves this without
   additional infrastructure.

#### What would make it provable

**Option A: Modify `ValueEq` for VLam to quantify over related arguments (recommended).**

Change the VLam clause from:
```lean
| k + 1, .VLam body1 env1, .VLam body2 env2 =>
    ∀ (arg : CekValue), ...
```

To:
```lean
| k + 1, .VLam body1 env1, .VLam body2 env2 =>
    ∀ (arg1 arg2 : CekValue), ValueEq (k + 1) arg1 arg2 →
      (Reaches (.compute [] (env1.extend arg1) body1) .error ↔
       Reaches (.compute [] (env2.extend arg2) body2) .error) ∧
      (Halts (.compute [] (env1.extend arg1) body1) ↔
       Halts (.compute [] (env2.extend arg2) body2)) ∧
      ∀ (v1 v2 : CekValue),
        Reaches (.compute [] (env1.extend arg1) body1) (.halt v1) →
        Reaches (.compute [] (env2.extend arg2) body2) (.halt v2) →
        ValueEq k v1 v2
```

And similarly for VDelay (if applicable).

This is the standard step-indexed logical relation formulation.
It makes same-body adequacy directly provable because the Apply case
can use the VLam clause with `ValueEq`-related arguments on both sides.

**Impact on existing proofs:**
- `valueEq_refl`: VLam case currently uses `reaches_unique` on `h₁, h₂`
  (same arg → same result). With two args, need `arg1 = arg2` (from
  `ValueEq (k+1) arg arg` by reflexivity), then same proof works.
  Requires instantiating with `arg, arg, valueEq_refl (k+1) arg`.
- `valueEq_symm`: VLam case swaps sides. With two args, swap `arg1, arg2`
  and use `valueEq_symm` on the arg relation. Minor change.
- `valueEq_trans`: VLam case chains through a middle value. With two args,
  need a middle `arg₂` where `ValueEq arg₁ arg₂` and `ValueEq arg₂ arg₃`.
  Use `arg₂ = arg₁` (by reflexivity) for the first half and `arg₂ = arg₃`
  for the second. Needs care but is provable.
- `valueEq_mono`: VLam case strips one index level. Minor adaptation.
- `refines_delay_behEq`, `refines_lam_behEq`, `refines_force_behEq`:
  These use `refines_behEq_at` which provides `BehEq` between sub-terms.
  `BehEq` evaluates both under the **same** `ρ`, so both closures receive
  the same argument via `ρ.extend arg`. The proofs instantiate the new
  VLam clause with `arg, arg, valueEq_refl`. Minor syntactic changes.
- `closedAt_envRelV_valueEq` (DeadLet.lean): The `relV_implies_valueEq_succ`
  VLam case currently applies both closures to the same `arg`. With the new
  definition, apply to `arg, arg` with `ValueRelV.toValueEq` for the arg
  relation. Requires `ValueRelV arg arg = .refl` → `valueEq_refl`.
- `Bisim` machinery: Not affected (uses `ValueRelV`/`StateRel`, not `ValueEq`).

**Estimated rework:** ~50-100 lines of changes across Semantics.lean,
Trans.lean, Congruence.lean, and DeadLet.lean. Most changes are syntactic
(adding `arg, arg, valueEq_refl` where previously just `arg`).

**Option B: Define `ValueEqStrong` separately and prove `BehEq` gives it.**

Define a stronger relation with the two-argument VLam clause. Prove:
- `ValueEq k v₁ v₂ → ValueEqStrong k v₁ v₂` (requires same-body adequacy).
- Use `ValueEqStrong` in `funV_frame_beh`.

This avoids changing existing definitions but duplicates the relation hierarchy.
Higher total cost, more maintenance burden.

**Option C: Custom bisimulation for same-body execution.**

Define `SameBodyStateRel k` that tracks `ValueEq`-related values through
the CEK execution. Prove `step_preserves_sameBody`. This is essentially
re-implementing Bisim.lean with `ValueEq` instead of `ValueRelV`.

Estimated size: ~500-800 lines. Very high effort for a one-off result.

**Option D: Direct CEK trace argument.**

Prove `funV_frame_beh` directly by induction on execution length, tracking
the relationship between the two executions through every step.

Similar effort to Option C but less reusable.

---

### Phase 6: `funV_frame_beh`

**Statement:**

```lean
private theorem funV_frame_beh (k : Nat) (vf vx vx' : CekValue)
    (hx : ValueEq (k + 1) vx vx') :
    (Reaches (.ret [.funV vf] vx) .error ↔
     Reaches (.ret [.funV vf] vx') .error) ∧
    (Halts (.ret [.funV vf] vx) ↔ Halts (.ret [.funV vf] vx')) ∧
    ∀ w₁ w₂,
      Reaches (.ret [.funV vf] vx) (.halt w₁) →
      Reaches (.ret [.funV vf] vx') (.halt w₂) →
      ValueEq k w₁ w₂
```

**Proof by case-split on vf:**

- **VCon c**: `step (ret [funV (VCon c)] vx) = error`. Both sides error in 1 step.
  Error↔: `Iff.rfl`. Halts↔: both false. ValueEq: vacuous (can't halt).

- **VDelay body env**: Same as VCon. `ret (funV (VDelay ..) :: _) _ → error`.

- **VConstr tag fields**: Same. `ret (funV (VConstr ..) :: _) _ → error`.

- **VLam body ρ_closure**:
  - Left: `step → compute [] (ρ_closure.extend vx) body`.
  - Right: `step → compute [] (ρ_closure.extend vx') body`.
  - Same body, same closure environment. Only argument differs.
  - **Requires same-body adequacy (Phase 5).**
  - With Option A (`ValueEq` quantifies over related args):
    We have `ValueEq (k+1) (VLam body ρ_closure) (VLam body ρ_closure)` (by `valueEq_refl`).
    Instantiate with `arg1 = vx, arg2 = vx', harg = hx`. Directly obtain
    error↔, halts↔, and `ValueEq k` for the body.

- **VBuiltin b args ea**: Case-split on `ea.head` and `ea.tail`.
  - `ea.head = argQ`: error. Both sides.
  - `ea.head = argV, ea.tail = some rest` (partial application):
    Result is `VBuiltin b (vx :: args) rest` vs `VBuiltin b (vx' :: args) rest`.
    Need `ValueEq k`. Build component-wise:
    - `b = b`: rfl.
    - `ListValueEq (k-1) (vx :: args) (vx' :: args)`: from `valueEq_mono` on `hx`
      and `listValueEq_refl` on `args`.
    - `ea-related`: rfl.
    - `evalBuiltin none↔`: from `evalBuiltin_listValueEq`.
    - `evalBuiltin result ValueEq`: from `evalBuiltin_listValueEq`.
  - `ea.head = argV, ea.tail = none` (saturated):
    `evalBuiltin b (vx :: args)` vs `evalBuiltin b (vx' :: args)`.
    Use `evalBuiltin_listValueEq` with `ListValueEq (k+1) (vx :: args) (vx' :: args)`.
    Error case: both produce `none` → both reach `.error`.
    Success case: `ValueEq k r₁ r₂` from the theorem.

**Verdict: Provable given Phase 5 (or Option A).** ~100 lines.

---

### Phase 7: The Final Theorem

**Statement:**

```lean
theorem refines_app_arg_behEq (f a a' : Expr) (ha : a ⊑ a') :
    Expr.App f a ⊑ Expr.App f a'
```

**Proof structure:**

```lean
refine ⟨?comp, ?beh⟩
```

#### Compilation clause

Goal: `∀ env, (lowerTotalExpr env (.App f a)).isSome → (lowerTotalExpr env (.App f a')).isSome`

1. `rw [lowerTotalExpr_app] at hs ⊢`.
2. `lowerTotalExpr env f` is shared. If `none`, `hs` gives `False`.
3. If `some tf`: need `(lowerTotalExpr env a').isSome`.
   From `hs`: `(lowerTotalExpr env a).isSome`.
   From `ha.1 env`: get `(lowerTotalExpr env a').isSome`.
4. Rewrite and `simp [Option.bind]`.

**Verdict: Straightforward.** ~15 lines.

#### BehEq clause

Goal: for every `env, ρ, hwf`:
- Error↔ for `Apply tf ta` vs `Apply tf ta'`.
- Halts↔.
- ValueEq k.

Setup:
1. Case-split on lowering of `f`, `a`, `a'`.
2. Extract `tf, ta, ta'`.
3. Get `⟨herr_a, hhalt_a, hval_a⟩ := refines_behEq_at ha ...`.
4. Key fact: `tf` is the same on both sides.

**Error↔ (→ direction):**

1. Decompose left error with `app_reaches_error ρ tf ta herr`.
2. Three sub-cases:
   - Function errors: `app_error_from_fun_error ρ tf ta'` (same function).
   - Function halts with `vf`, argument errors:
     `herr_a.mp` transfers error from `ta` to `ta'`.
     `app_error_from_arg_error ρ tf ta' vf hf ha'_err`.
   - Function halts with `vf`, argument halts with `vx`, frame errors:
     Get `vx'` from `hhalt_a.mp ⟨vx, hvx⟩`.
     Get `funV_frame_beh` error transfer.
     `app_apply_from_parts ρ tf ta' vf vx' .error hf' hvx' hframe_err`.
3. Reverse direction symmetric.

**Halts↔:**

1. Decompose halting with `app_reaches ρ tf ta w hw`.
2. Get `vf, vx` with function halting, argument halting, frame halting.
3. Get `vx'` from `hhalt_a.mp ⟨vx, hvx⟩`.
4. Get frame halting from `funV_frame_beh` halts transfer.
5. Compose with `app_apply_from_parts`.

**ValueEq k:**

1. Decompose both sides with `app_reaches`.
2. Function determinism: both evaluate `tf` under same `ρ`.
   By `reaches_unique`: `vf₁ = vf₂ = vf`.
3. Get `hval_a (k+1) vx vx' hvx hvx'` for `ValueEq (k+1) vx vx'`.
4. Apply `funV_frame_beh k vf vx vx'` third component.
5. Return `ValueEq k w₁ w₂`.

**Verdict: Provable given all prerequisites.** ~80 lines.

---

## Summary

```
Phase                          Provable?   Difficulty   Lines   Blocker
---------------------------    ---------   ----------   -----   -------
1. compute_to_error_from_error Yes         Easy         ~40     None
2. App decomposition           Yes         Medium       ~240    Phase 1
3. EnvValueEq + lemmas         Yes         Easy         ~60     None
4. valueEq_mono + builtins     Yes         Medium       ~180    None
5. Same-body adequacy          BLOCKED     Hard         ~500+   ValueEq def
6. funV_frame_beh              Given P5    Medium       ~100    Phase 5
7. Final theorem               Given P6    Easy         ~80     Phase 6
```

**Total if unblocked:** ~1200 lines.

## Recommended Path Forward

**Modify the `ValueEq` definition for VLam (and VDelay) to quantify over
two `ValueEq`-related arguments.** This is the standard step-indexed logical
relation formulation and resolves Phase 5 entirely.

With this change:
- Phase 5 becomes unnecessary as a standalone theorem.
- Phase 6 (`funV_frame_beh`) directly uses `valueEq_refl` on `vf` and `hx`
  on the arguments to invoke the VLam clause.
- Existing proofs need minor syntactic updates (~50-100 lines).
- The modification enables all future congruence theorems (not just App arg).

The same change to VDelay is needed for consistency:
```lean
| k + 1, .VDelay body1 env1, .VDelay body2 env2 =>
    -- Currently: just error↔ ∧ halts↔ ∧ ValueEq k on results.
    -- No change needed: VDelay has no argument.
```

VDelay is fine as-is since forcing doesn't take an argument.
