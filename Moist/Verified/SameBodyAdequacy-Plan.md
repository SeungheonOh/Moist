# Proving `sameBody_adequacy`

## Goal

```lean
theorem sameBody_adequacy (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (Reaches (.compute [] ρ₁ t) .error ↔ Reaches (.compute [] ρ₂ t) .error) ∧
    (Halts (.compute [] ρ₁ t) ↔ Halts (.compute [] ρ₂ t)) ∧
    ∀ (k : Nat) (v₁ v₂ : CekValue),
      Reaches (.compute [] ρ₁ t) (.halt v₁) →
      Reaches (.compute [] ρ₂ t) (.halt v₂) →
      ValueEq k v₁ v₂
```

where `EnvValueEqAll d ρ₁ ρ₂ := ∀ k, EnvValueEq k d ρ₁ ρ₂`.

## Architecture: same-body bisimulation

The proof follows the same architecture as the existing `Bisim.lean`:

1. Define structural value/frame/stack/state relations for same-body execution.
2. Prove `step` preserves the relation (`sb_step_preserves`).
3. Extract error/halt/value agreement from the bisimulation.
4. Bridge the structural relation to `ValueEq k` (for all k).
5. Compose everything into `sameBody_adequacy`.

## Phase 1: Same-body structural relations

### 1.1 `SBValueRelV`

```lean
mutual
  inductive SBValueRelV : CekValue → CekValue → Prop where
    | refl : SBValueRelV v v
    | vlam (d : Nat) (hcl : closedAt (d + 1) body = true)
        (henv : SBEnvRelV d env₁ env₂) :
        SBValueRelV (.VLam body env₁) (.VLam body env₂)
    | vdelay (d : Nat) (hcl : closedAt d body = true)
        (henv : SBEnvRelV d env₁ env₂) :
        SBValueRelV (.VDelay body env₁) (.VDelay body env₂)
    | vconstr (htag : tag₁ = tag₂) (hfs : SBListValueRelV fs₁ fs₂) :
        SBValueRelV (.VConstr tag₁ fs₁) (.VConstr tag₂ fs₂)
    | vbuiltin (hb : b₁ = b₂) (hargs : SBListValueRelV args₁ args₂)
        (hea : ea₁ = ea₂) :
        SBValueRelV (.VBuiltin b₁ args₁ ea₁) (.VBuiltin b₂ args₂ ea₂)

  inductive SBListValueRelV : List CekValue → List CekValue → Prop where
    | nil : SBListValueRelV [] []
    | cons (hv : SBValueRelV v₁ v₂) (hrs : SBListValueRelV vs₁ vs₂) :
        SBListValueRelV (v₁ :: vs₁) (v₂ :: vs₂)

  inductive SBEnvRelV : Nat → CekEnv → CekEnv → Prop where
    | mk : (∀ n, 0 < n → n ≤ d →
              SBLookupRelV (env₁.lookup n) (env₂.lookup n)) →
           SBEnvRelV d env₁ env₂

  inductive SBLookupRelV : Option CekValue → Option CekValue → Prop where
    | bothNone : SBLookupRelV none none
    | bothSome (hv : SBValueRelV v₁ v₂) : SBLookupRelV (some v₁) (some v₂)
end
```

Key differences from `ValueRelV` / `EnvRelV`:
- **No renaming** (`σ = id`): both sides execute the same term.
- **Same body** in VLam/VDelay: `body` appears once, not `body` vs `renameTerm σ body`.
- **`.refl` constructor**: same value on both sides (from shared closure env).

**Provability: straightforward definition.** No proof obligations in the definition itself.

### 1.2 Frame/Stack/State relations

```lean
inductive SBFrameRel : Frame → Frame → Prop where
  | force : SBFrameRel .force .force
  | arg (d : Nat) (hcl : closedAt d t = true) (henv : SBEnvRelV d env₁ env₂) :
      SBFrameRel (.arg t env₁) (.arg t env₂)
  | funV (hv : SBValueRelV v₁ v₂) : SBFrameRel (.funV v₁) (.funV v₂)
  | applyArg (hv : SBValueRelV v₁ v₂) : SBFrameRel (.applyArg v₁) (.applyArg v₂)
  | constrField (tag : Nat) (hdone : SBListValueRelV d₁ d₂)
      (hcl : closedAtList d todo = true) (henv : SBEnvRelV d env₁ env₂) :
      SBFrameRel (.constrField tag d₁ todo env₁) (.constrField tag d₂ todo env₂)
  | caseScrutinee (hcl : closedAtList d alts = true) (henv : SBEnvRelV d env₁ env₂) :
      SBFrameRel (.caseScrutinee alts env₁) (.caseScrutinee alts env₂)

inductive SBStackRel : Stack → Stack → Prop where
  | nil : SBStackRel [] []
  | cons (hf : SBFrameRel f₁ f₂) (hrs : SBStackRel s₁ s₂) :
      SBStackRel (f₁ :: s₁) (f₂ :: s₂)

inductive SBStateRel : State → State → Prop where
  | compute (hs : SBStackRel s₁ s₂) (d : Nat) (henv : SBEnvRelV d env₁ env₂)
      (ht : closedAt d t = true) :
      SBStateRel (.compute s₁ env₁ t) (.compute s₂ env₂ t)
  | ret (hs : SBStackRel s₁ s₂) (hv : SBValueRelV v₁ v₂) :
      SBStateRel (.ret s₁ v₁) (.ret s₂ v₂)
  | error : SBStateRel .error .error
  | halt (hv : SBValueRelV v₁ v₂) : SBStateRel (.halt v₁) (.halt v₂)
```

Key: `SBStateRel.compute` has the SAME term `t` on both sides (no renaming).
Frame `arg` and `caseScrutinee` carry the same term list (not renamed).

**Provability: straightforward definition.** Same pattern as existing `StateRel`.

### 1.3 Helper lemmas

```lean
theorem sbEnvRelV_elim (h : SBEnvRelV d env₁ env₂) (hn : 0 < n) (hle : n ≤ d) :
    SBLookupRelV (env₁.lookup n) (env₂.lookup n)

theorem sbEnvRelV_extend (henv : SBEnvRelV d env₁ env₂) (hv : SBValueRelV v₁ v₂) :
    SBEnvRelV (d + 1) (env₁.extend v₁) (env₂.extend v₂)

theorem sbListValueRelV_append (h1 : SBListValueRelV a₁ a₂) (h2 : SBListValueRelV b₁ b₂) :
    SBListValueRelV (a₁ ++ b₁) (a₂ ++ b₂)

theorem sbListValueRelV_reverse (h : SBListValueRelV a₁ a₂) :
    SBListValueRelV a₁.reverse a₂.reverse

theorem sbListValueRelV_cons_rev (hv : SBValueRelV v₁ v₂)
    (hdone : SBListValueRelV done₁ done₂) :
    SBListValueRelV ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse)

theorem sbStackRel_append (hs : SBStackRel s₁ s₂) (ht : SBStackRel t₁ t₂) :
    SBStackRel (s₁ ++ t₁) (s₂ ++ t₂)

theorem sbListValueRelV_map_applyArg_stackRel (h : SBListValueRelV fs₁ fs₂) :
    SBStackRel (fs₁.map Frame.applyArg) (fs₂.map Frame.applyArg)
```

**Provability: trivial.** Each is a direct structural induction, mirroring the
existing `listValueRelV_append`, `stackRel_append`, etc. in `Bisim.lean`.
Same proofs, different type names.

### 1.4 `EnvValueEqAll → SBEnvRelV`

```lean
theorem envValueEqAll_to_sbEnvRelV (d : Nat) (ρ₁ ρ₂ : CekEnv)
    (h : EnvValueEqAll d ρ₁ ρ₂) : SBEnvRelV d ρ₁ ρ₂
```

This bridges from the hypothesis of `sameBody_adequacy` to the bisimulation.
At each position, `EnvValueEqAll` gives `∀ k, ValueEq k v₁ v₂`. We need
`SBValueRelV v₁ v₂`. Specifically we need `SBLookupRelV`.

If both `some v₁, some v₂`: need `SBValueRelV v₁ v₂`. But we only have
`∀ k, ValueEq k v₁ v₂`, which is observational. We can't construct a
structural `SBValueRelV` from it in general.

**THIS IS THE KEY ISSUE.** `∀ k, ValueEq k` does not imply `SBValueRelV`
because `SBValueRelV` requires structural matching (same body for VLam,
same env structure) while `ValueEq` is observational.

**Resolution**: We don't need `SBValueRelV` for the differing values. We
need a HYBRID relation that allows some positions to be `SBValueRelV`
(structural) and others to be `∀ k, ValueEq k` (observational).

## Revised Phase 1: Hybrid value relation

### 1.1 revised: `SBValueRel`

```lean
inductive SBValueRel : CekValue → CekValue → Prop where
  | structural : SBValueRelV v₁ v₂ → SBValueRel v₁ v₂
  | observational : (∀ k, ValueEq k v₁ v₂) → SBValueRel v₁ v₂
```

The frame/stack/state relations use `SBValueRel` instead of `SBValueRelV`:

```lean
inductive SBFrameRel : Frame → Frame → Prop where
  | funV : SBValueRel v₁ v₂ → SBFrameRel (.funV v₁) (.funV v₂)
  | applyArg : SBValueRel v₁ v₂ → SBFrameRel (.applyArg v₁) (.applyArg v₂)
  -- force, arg, constrField, caseScrutinee: same as before (structural)
  ...
```

And `SBStateRel` uses `SBValueRel` in the `ret` case.

### 1.2 Step preservation with hybrid relation

The `sb_step_preserves` proof now has an additional case to handle:

**VLam application with `.observational` function value:**
```
ret (.funV vf₁ :: s₁) vx₁  and  ret (.funV vf₂ :: s₂) vx₂
where SBValueRel vf₁ vf₂ via .observational
```

If `vf₁ = VLam body₁ env₁` and `vf₂ = VLam body₂ env₂` with `∀ k, ValueEq k vf₁ vf₂`:
- Left steps to `compute s₁ (env₁.extend vx₁) body₁`
- Right steps to `compute s₂ (env₂.extend vx₂) body₂`
- `body₁ ≠ body₂` and `env₁ ≠ env₂` in general

**We CANNOT construct `SBStateRel` for these states** because `SBStateRel.compute`
requires the same term on both sides.

**This means the bisimulation BREAKS at `.observational` VLam application.**

### Resolution: exit the bisimulation at `.observational` application points

When an `.observational` VLam/VDelay is applied/forced, we exit the bisimulation
and use `ValueEq` directly. The trick: from this point, we know the FINAL
result agrees (via `ValueEq`), so we just need to show the rest of the stack
processes the result correctly.

This requires:
1. The VLam clause of `ValueEq` gives error↔/halts↔/ValueEq for the body
   computation (same arg on both sides).
2. A stack-lifting argument to embed the body result into the remaining stack.

But we also need the argument bridging (vx₁ vs vx₂), which brings us back
to `sameBody_adequacy`.

**This circular dependency is the fundamental obstacle.**

## Breaking the circularity: two-layer proof

### Layer 1: Pure bisimulation (structural values only)

Prove that `SBStateRel` (using only `SBValueRelV`, no `.observational`) is
preserved by `step`. This handles all cases where intermediate values are
structural — i.e., they came from the shared parts of the environment.

This is a direct adaptation of `Bisim.step_preserves` with `σ = id` and
no renaming. Every case is simpler than the original (no renaming terms
in `renameTerm σ`).

**Provability: high.** ~400 lines (simpler than `Bisim.step_preserves`'s ~500
because no renaming). Each case maps directly from the existing proof.

### Layer 2: `SBValueRelV → ∀ k, ValueEq k`

Bridge from the structural same-body relation to observational equivalence:

```lean
theorem sbValueRelV_to_valueEq (k : Nat) (v₁ v₂ : CekValue)
    (h : SBValueRelV v₁ v₂) : ValueEq k v₁ v₂
```

**Proof structure:** Mutual induction on `k`, mirroring `DeadLet.env_rel_bundle_aux`.

Three components:
- **(A)** `closedAt d t → SBEnvRelV d ρ₁ ρ₂ → both halt → ValueEq k v₁ v₂`
- **(B)** `SBValueRelV v₁ v₂ → ValueEq k v₁ v₂`
- **(C)** `SBListValueRelV vs₁ vs₂ → ListValueEq k vs₁ vs₂`

**(A)** at `k+1` for simple terms (Var, Constant, Builtin, Error, Lam, Delay): direct.
- Var: `SBEnvRelV` gives `SBLookupRelV`, both look up same position, get
  `SBValueRelV` values, apply **(B)**.
- Lam: both produce `VLam body ρ₁` and `VLam body ρ₂`. Package as
  `SBValueRelV.vlam`. Apply **(B)**.
- etc.

**(A)** at `k+1` for compound terms (Apply, Force, Constr, Case):
delegate to `sb_bisim_reaches` (Layer 1) to get `SBValueRelV`, then **(B)**.

**This is the SAME trick as `DeadLet.closed_eval_valueEq_succ`** at line 384:
```lean
| .Apply _ _ | .Force _ | .Constr _ _ | .Case _ _ =>
    exact relV_to_eq v₁ v₂ (Bisim.bisim_reaches (.compute .nil σ d hrel hcl) h₁ h₂)
```

We do the same but with `sb_bisim_reaches` and `sbValueRelV_to_valueEq`.

**Provability: high.** Follows the exact structure of `DeadLet.env_rel_bundle_aux`.

**(B)** at `k+1`: case-split on `SBValueRelV`:
- `.refl`: `valueEq_refl`.
- `.vlam d hcl henv`: same as `DeadLet.relV_implies_valueEq_succ` vlam case.
  VLam clause needs `∀ arg, error↔ ∧ halts↔ ∧ ValueEq k`.
  Build `SBEnvRelV (d+1) (env₁.extend arg) (env₂.extend arg)` via `sbEnvRelV_extend`
  with `SBValueRelV.refl` for the arg.
  Then **(A)** at `k` gives `ValueEq k`. Error↔/halts↔ from `sb_bisim_reaches_error`
  and `sb_bisim_halts`. **Same proof as DeadLet.relV_implies_valueEq_succ.**
- `.vdelay`: analogous.
- `.vconstr`: use **(C)**.
- `.vbuiltin`: use **(C)** + builtin extensionality.

**Provability: high.** Direct mirror of `DeadLet.relV_implies_valueEq_succ`.

### Layer 3: Compose into `sameBody_adequacy`

```lean
theorem sameBody_adequacy (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (error↔) ∧ (halts↔) ∧ (∀ k v₁ v₂, halt v₁ → halt v₂ → ValueEq k v₁ v₂)
```

**Proof:**

The key challenge: `EnvValueEqAll` gives `∀ k, ValueEq k` at each position,
but `SBEnvRelV` needs `SBValueRelV` at each position. We can't go from
`∀ k, ValueEq k` to `SBValueRelV` (observational → structural is impossible).

**However, for the SPECIFIC case we care about:**

In `funV_frame_beh`, the environments are `ρ.extend vx` vs `ρ.extend vx'`
where `ρ` is SHARED. The values at positions > 1 are literally the SAME
value → `SBValueRelV.refl`. Only position 1 has `∀ k, ValueEq k vx vx'`.

So we DON'T need to convert position 1 to `SBValueRelV`. Instead:

1. Use the VLam clause of `ValueEq (k+1)` on `vf` (which is
   `ValueEq (k+1) vf vf` by `valueEq_refl`) to get: for any single `arg`,
   error↔/halts↔/ValueEq k for `body` under `ρ_closure.extend arg`.

   Instantiate with `arg = vx₁`:
   - `body` under `ρ_closure.extend vx₁` ↔ `body` under `ρ_closure.extend vx₁`
   - This is trivial (same computation). **Useless.**

   Hmm, that doesn't help because both sides of `valueEq_refl` use the
   same env.

2. **Instead:** Build `SBEnvRelV d (ρ.extend vx) (ρ.extend vx')` where:
   - Position 1: can't be `SBValueRelV` (vx ≠ vx' in general).

**Back to the fundamental problem.** We can't build a pure `SBEnvRelV`
because position 1 isn't structural.

### Final resolution: `sameBody_adequacy` has TWO cases

**Case A: Pure structural (all positions `SBValueRelV`).**

This is what Layer 1+2 handles. It covers the case where both environments
are structurally related at EVERY position.

**Case B: Single differing position with `∀ k, ValueEq k`.**

This is the specific case for `funV_frame_beh`. The proof composes:
1. VLam clause with arg = vx: body(vx) under env₁ ↔ body(vx) under env₂.
   Wait — in our case env₁ = env₂ = ρ_closure. So body under
   `ρ_closure.extend vx` side 1 and `ρ_closure.extend vx` side 2 are
   identical. The VLam clause of `valueEq_refl (k+1) (VLam body ρ_closure)`
   instantiated at arg = vx gives trivial identity.

   **The VLam clause of valueEq_refl can't compare vx vs vx'.**

3. **Use Case A directly:**
   `ρ_closure.extend vx` vs `ρ_closure.extend vx'`:
   - Position 1: vx vs vx'. Not `SBValueRelV`. Can't use Case A.

**OK so Case A alone can't handle the differing argument.**

### Actually viable approach: factored composition

The proof of `sameBody_adequacy` for `ρ.extend vx` vs `ρ.extend vx'`:

Chain through a middle computation using `ρ.extend vx` on BOTH sides:

```
body under (ρ.extend vx)  ≡  body under (ρ.extend vx)   [trivial: same]
body under (ρ.extend vx)  ≡  body under (ρ.extend vx')  [WHAT WE WANT]
```

That doesn't help. Chain through a DIFFERENT middle:

```
body under (ρ.extend vx)  ≡  body under (ρ.extend vx')
```

Use Case A for `ρ.extend vx` vs `ρ.extend vx'` where `SBEnvRelV` holds
at positions > 1 (structural, same ρ) but NOT at position 1.

**We need to handle position 1 separately.**

Approach: build a MODIFIED `SBEnvRelV` that allows ONE position to be
`∀ k, ValueEq k` instead of `SBValueRelV`. But this complicates the
bisimulation.

**Alternative approach: add `.observational` to `SBValueRelV` and handle
the bisimulation breakage.**

```lean
inductive SBValueRelV : CekValue → CekValue → Prop where
  | refl : SBValueRelV v v
  | vlam ...
  | vdelay ...
  | vconstr ...
  | vbuiltin ...
  | veqAll : (∀ k, ValueEq k v₁ v₂) → SBValueRelV v₁ v₂
```

The `.veqAll` constructor wraps `∀ k, ValueEq k`. Now `SBEnvRelV` can be
built with `.veqAll` at position 1.

Step preservation: most cases work exactly as before. The hard case is
`.veqAll` VLam application:

```
ret (.funV vf₁ :: s₁) vx₁  where SBValueRelV vf₁ vf₂ via .veqAll
```

`∀ k, ValueEq k (VLam body₁ env₁) (VLam body₂ env₂)` where body₁ ≠ body₂
potentially. Both sides step to different terms. Can't maintain `SBStateRel`.

**At this point, EXIT the bisimulation:**

Instead of maintaining `SBStateRel` through the closure body, use the
`ValueEq` clause to get error↔/halts↔/ValueEq k for the body computation.
Then use stack-lifting to embed the body result into the remaining stack
and show the remaining stack processes the result correctly.

The remaining stack is `SBStackRel`-related. The body results are
`∀ k, ValueEq k`-related (from the VLam clause, using the same arg on
both sides, the trivially-related args give trivially-related body results
... wait, the ARGS are also `SBValueRelV`-related, possibly via `.veqAll`.

Hmm, the VLam clause uses a SINGLE arg. We have vx₁ and vx₂ (different).

**The VLam clause at k+1 says:**
`∀ arg, error↔ ∧ halts↔ ∧ ValueEq k` for `body₁(arg)` vs `body₂(arg)`.

With `arg = vx₁`:
- error↔ for `body₁(vx₁)` vs `body₂(vx₁)`. ✓
- halts↔. ✓
- ValueEq k for results. ✓

Now we need `body₂(vx₁)` ≡ `body₂(vx₂)`. This is `sameBody_adequacy`
applied to `body₂` under `env₂.extend vx₁` vs `env₂.extend vx₂`.

**This is a recursive call to `sameBody_adequacy` on a closure body
(not a sub-term).**

**Well-foundedness:** The key insight — the closure body's EXECUTION takes
fewer steps than the overall execution. If we parameterize by the total
number of steps to termination, the recursive call is at a strictly smaller
step count.

Define:
```lean
def StepBound (s : State) (n : Nat) : Prop :=
  (∃ v, steps n s = .halt v) ∨ steps n s = .error
```

Then `sameBody_adequacy` is proved by strong induction on `n₁ + n₂` where
`n₁` bounds the left computation and `n₂` bounds the right.

For the `.veqAll` VLam application:
- Total steps: N = overhead + n_body₁ + n_body₂ + n_rest
- The VLam clause gives us body₁(vx₁) ≡ body₂(vx₁) (error↔/halts↔/ValueEq).
- The recursive call for body₂(vx₁) ≡ body₂(vx₂) uses n_body₂ + n_body₂' < N
  steps (the body computation is strictly shorter than the full Apply).

**This is well-founded!**

## Revised proof plan

### Phase 1: Structural relations (no `.veqAll`)

Define `SBValueRelV`, `SBListValueRelV`, `SBEnvRelV`, `SBLookupRelV`,
`SBFrameRel`, `SBStackRel`, `SBStateRel` as described above (WITHOUT
`.veqAll`).

Prove helper lemmas: `sbEnvRelV_extend`, `sbListValueRelV_append`,
`sbListValueRelV_reverse`, `sbStackRel_append`, etc.

**Provability: trivial.** Pure definitions + structural inductions. ~100 lines.

### Phase 2: `sb_step_preserves`

```lean
theorem sb_step_preserves (h : SBStateRel s₁ s₂) : SBStateRel (step s₁) (step s₂)
```

Direct adaptation of `Bisim.step_preserves` with σ = id, no renameTerm.

Every case from the original proof maps over:
- Compute Var: use `sbEnvRelV_elim`, both look up same position.
- Compute Constant/Builtin/Error: identical.
- Compute Lam: produce `SBValueRelV.vlam` with `closedAt_lam`.
- Compute Delay: produce `SBValueRelV.vdelay` with `closedAt_delay`.
- Compute Force/Apply: push appropriate `SBFrameRel` frame.
- Compute Constr/Case: push frame, same as original.
- Ret Force: case-split on `SBValueRelV`. VDelay → compute body.
  `.refl` handled by helper.
- Ret FunV: case-split on `SBValueRelV`. VLam → extend env.
  `.refl` handled by helper.
- Ret ApplyArg: same as FunV.
- Ret ConstrField: accumulate field, use `sbListValueRelV_cons_rev`.
- Ret CaseScrutinee: index into alts, push applyArg frames.

**Provability: high.** ~400 lines. Every case is SIMPLER than the original
because there's no renaming. The `refl` cases need helpers (same as existing
`step_force_refl`, `step_funV_refl`, etc.).

The only structural concern: the existing proof uses `closedAt d (renameTerm σ t)`
in several places. Without renaming, this simplifies to `closedAt d t`. No
issues.

**Builtin cases:** `evalBuiltin_relV` works with `ListValueRelV`. We need
an `SBListValueRelV` → `ListValueRelV` bridge, or prove `sb_evalBuiltin_relV`
directly. Since `SBValueRelV.refl` maps to `ValueRelV.refl` and the structural
constructors map directly, a bridge `SBValueRelV → ValueRelV` is easy:

```lean
theorem sbValueRelV_to_valueRelV : SBValueRelV v₁ v₂ → ValueRelV v₁ v₂
```

`.refl` → `.refl`. `.vlam d hcl henv` → `.vlam id d hcl (sbEnvRelV_to_envRelV henv)`.
etc. Need `sbEnvRelV_to_envRelV : SBEnvRelV d e₁ e₂ → EnvRelV id d e₁ e₂`.

**Provability: high.** Structural recursion. The `vlam` case uses
`renameTerm id body = body` (which is `renameTerm_id`). ~50 lines.

Then `sb_evalBuiltin_relV` follows from `evalBuiltin_relV` + the bridge.

### Phase 3: Extraction theorems

```lean
theorem sb_steps_preserves (n : Nat) (h : SBStateRel s₁ s₂) :
    SBStateRel (steps n s₁) (steps n s₂)

theorem sb_bisim_reaches (h : SBStateRel s₁ s₂)
    (h₁ : Reaches s₁ (.halt v₁)) (h₂ : Reaches s₂ (.halt v₂)) :
    SBValueRelV v₁ v₂

theorem sb_bisim_reaches_error (h : SBStateRel s₁ s₂)
    (h₁ : Reaches s₁ .error) : Reaches s₂ .error

theorem sb_bisim_halts (h : SBStateRel s₁ s₂)
    (h₁ : Halts s₁) : Halts s₂

theorem sb_bisim_halts_rev (h : SBStateRel s₁ s₂)
    (h₂ : Halts s₂) : Halts s₁
```

**Provability: trivial.** Exact copies of the existing `Bisim.steps_preserves`,
`bisim_reaches`, etc. Same 5-10 line proofs. ~40 lines total.

### Phase 4: `SBValueRelV → ValueEq k` bridge

```lean
theorem sbValueRelV_to_valueEq (k : Nat) (v₁ v₂ : CekValue)
    (h : SBValueRelV v₁ v₂) : ValueEq k v₁ v₂
```

**Proof:** Mutual induction on `k` with three components (A, B, C), exactly
mirroring `DeadLet.env_rel_bundle_aux`.

**(A)** `closedAt d t → SBEnvRelV d ρ₁ ρ₂ → both halt → ValueEq k`:
- Simple terms: direct (same as DeadLet).
- Compound terms: `sb_bisim_reaches` → `SBValueRelV` → **(B)**.

**(B)** `SBValueRelV → ValueEq (k+1)`:
- `.refl`: `valueEq_refl`.
- `.vlam d hcl henv`: VLam clause needs `∀ arg, error↔ ∧ halts↔ ∧ ValueEq k`.
  Extend env with `.refl` for arg. Build `SBEnvRelV (d+1)`.
  Error↔ from `sb_bisim_reaches_error`. Halts↔ from `sb_bisim_halts`.
  ValueEq k from **(A)** at index k. **Same as DeadLet.**
- `.vdelay`: analogous.
- `.vconstr`: tag + **(C)**.
- `.vbuiltin`: use **(C)** + existing builtin extensionality.

**(C)** `SBListValueRelV → ListValueEq k`: pointwise **(B)**.

**Provability: high.** ~100 lines. Exact mirror of `DeadLet.env_rel_bundle_aux`.

### Phase 5: `sameBody_adequacy` — pure structural case

For environments where ALL positions are `SBValueRelV`-related (no
`.veqAll` needed):

```lean
private theorem sameBody_structural (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (henv : SBEnvRelV d ρ₁ ρ₂) :
    (error↔) ∧ (halts↔) ∧ (∀ k v₁ v₂, halt v₁ → halt v₂ → ValueEq k v₁ v₂)
```

**Proof:** Build `SBStateRel.compute .nil d henv hcl`. Apply
`sb_bisim_reaches_error` for error↔. Apply `sb_bisim_halts` for halts↔.
Apply `sb_bisim_reaches` + `sbValueRelV_to_valueEq` for ValueEq.

**Provability: trivial.** ~10 lines. Just composition of Phase 2-4 results.

### Phase 6: `sameBody_adequacy` — full theorem

```lean
theorem sameBody_adequacy (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (error↔) ∧ (halts↔) ∧ (∀ k v₁ v₂, halt v₁ → halt v₂ → ValueEq k v₁ v₂)
```

The full theorem handles environments where some positions differ by
`∀ k, ValueEq k` (not structural). The specific case: `ρ.extend vx` vs
`ρ.extend vx'` where ρ is shared and `∀ k, ValueEq k vx vx'`.

**Proof by well-founded induction on execution step count:**

Define the step-count measure:
```lean
private def stepMeasure (s₁ s₂ : State) (h₁ : Reaches s₁ terminal₁)
    (h₂ : Reaches s₂ terminal₂) : Nat :=
  h₁.choose + h₂.choose  -- sum of step counts
```

For each term constructor:

- **Var 0**: Both error. error↔ trivial. halts↔ trivial (both false).
  ValueEq: contradiction (can't halt). Step count: 1.

- **Var (m+1)**: `EnvValueEqAll` at k=1 gives `ValueEq 1`, which ensures
  same constructor. Both look up → both `some` with `∀ k, ValueEq k`.
  Both halt in 2 steps. error↔: neither errors. halts↔: both halt.
  ValueEq k: from `EnvValueEqAll`. Step count: 2.

  Wait — `EnvValueEqAll` gives `∀ k, ValueEq k v₁ v₂` at each position.
  At `k = 1`, `ValueEq 1` ensures same constructor (VCon/VLam/etc.).
  So both lookups either succeed (same constructor) or both fail (both none).
  If both succeed: results are `∀ k, ValueEq k`-related. Done.
  If both fail: both error. Done.

- **Constant, Builtin, Error, Lam, Delay**: Same as Phase 5 (structural).
  Both compute deterministically without depending on the env (or only
  capturing it). Lam/Delay capture the env but produce VLam/VDelay with
  the same body → use `sameBody_structural` with a structurally related env?

  Wait — Lam produces `VLam body ρ₁` vs `VLam body ρ₂`. These have the
  same body but different envs. We need `∀ k, ValueEq k (VLam body ρ₁) (VLam body ρ₂)`.

  `ValueEq (k+1) (VLam body ρ₁) (VLam body ρ₂)`: `∀ arg, error↔ ∧ halts↔ ∧ ValueEq k`
  for `ρ₁.extend arg body` vs `ρ₂.extend arg body`.

  For any `arg`: both envs are `EnvValueEqAll (d+1) (ρ₁.extend arg) (ρ₂.extend arg)`:
  - Position 1: same arg, `∀ k, ValueEq k arg arg` by `valueEq_refl`.
  - Positions > 1: from `EnvValueEqAll d ρ₁ ρ₂`.

  **Recursive call** to `sameBody_adequacy` for `body` under `ρ₁.extend arg` vs
  `ρ₂.extend arg`. This is a call on a DIFFERENT term (`body`) with a
  DIFFERENT env.

  **Is this well-founded?** The body `body` is a sub-term of `Lam m body`.
  So structural recursion on `t` works here.

  But when we reach compound terms, they will enter closures whose bodies
  are NOT sub-terms...

- **Force e**: Decompose via `force_reaches` / `force_reaches_error`.
  - Sub-term `e`: recursive call (structural).
  - Force frame: if results are `∀ k, ValueEq k` VDelay values, the VDelay
    clause gives error↔/halts↔/ValueEq k for forced bodies. Done directly.

  Wait — the sub-term `e` recursive call gives `∀ k, ValueEq k val₁ val₂`
  on e's results. For VDelay at `k+1`: `ValueEq k` on forced results.
  For the full Force e, we need `∀ k, ValueEq k` on the forced results.
  Pick `k+1` for the sub-evaluation → get `ValueEq (k+1)` on delays →
  get `ValueEq k` on forced results. Since k was arbitrary, we have
  `∀ k, ValueEq k`. ✓

- **Apply f x**: Decompose (needs `app_reaches` etc.).
  - Sub-terms `f`, `x`: recursive calls (structural).
  - Frame: `∀ k, ValueEq k vf₁ vf₂` and `∀ k, ValueEq k vx₁ vx₂`.
    VLam clause with arg = vx₁: body₁(vx₁) ≡ body₂(vx₁).
    Need body₂(vx₁) ≡ body₂(vx₂).
    **Recursive call to sameBody_adequacy on body₂** — NOT a sub-term!
    Well-foundedness: body₂ execution uses fewer steps than Apply f x.
    **Needs step-count induction.**

So the FULL proof needs both structural recursion on `t` (for sub-terms)
and step-count induction (for closure body entry).

**Combined recursion metric:** lexicographic `(step_count, term_size)` or
just `step_count` (which subsumes term structure since sub-term evaluation
uses fewer steps).

### Phase 6 detailed proof structure

By strong induction on `N = n₁ + n₂` where `n₁, n₂` bound the steps to
termination on both sides. If both error, use error step counts. If both
halt, use halt step counts. For the error↔/halts↔ parts, use the appropriate
bound.

Actually, this is cleaner as induction on `N₁` (left side step count), with
the right side handled by composing sub-results:

**Better: by structural induction on `t`, with closure body entry handled
by the `ValueEq` VLam clause + stack lifting.**

For the Apply case:
1. Structural IH on `f`: `sameBody_adequacy` for `f`.
2. Structural IH on `x`: `sameBody_adequacy` for `x`.
3. Frame: `vf₁, vf₂` with `∀ k, ValueEq k`. VLam clause gives body agreement
   for same arg.
4. Argument bridge: compose body₂(vx₁) ≡ body₂(vx₂).
   This needs `sameBody_adequacy` for `body₂` which is NOT a sub-term.
   BUT: body₂ has `closedAt d' body₂` for some d', and the envs are
   `EnvValueEqAll d'` (from `∀ k, ValueEq k vx₁ vx₂` at head, refl at tail).

   We need this as a SEPARATE lemma (not a recursive call in the structural
   induction on `t`).

**This separate lemma IS `sameBody_adequacy` itself!** So we have a genuine
recursive call to the same theorem on a non-sub-term.

**Resolution: use `sameBody_structural` (Phase 5) for the argument bridge.**

The key insight: for the argument bridge body₂(vx₁) ≡ body₂(vx₂):
- body₂ is the body of a closure captured from evaluating `f`.
- env₂ is the closure's environment.
- The envs `env₂.extend vx₁` vs `env₂.extend vx₂` differ at position 1.
- Positions > 1: env₂ is the SAME on both sides → `SBValueRelV.refl`.
- Position 1: `vx₁` vs `vx₂` with `∀ k, ValueEq k`.

We CAN'T use `sameBody_structural` because position 1 isn't structural.

**Final approach: add a `.veqAll` constructor to `SBValueRelV` and prove a
restricted `sb_step_preserves` that handles it by exiting to `ValueEq`.**

When a `.veqAll` VLam is applied (the bisimulation breaks):
- The VLam clause gives error↔/halts↔/ValueEq k for body under SAME arg.
- We chain: left result ≡ body₂(vx₁) (via VLam clause) ≡ body₂(vx₂) result.
- The second link is sameBody_structural for body₂ under env₂.extend vx₁ vs
  env₂.extend vx₂ — but position 1 has `.veqAll`, not structural.

**We're going in circles.** Let me step back and think about what REALLY works.

## What actually works

The only approach that avoids the circularity is:

**Induction on execution step count**, not on term structure.

```lean
private theorem sameBody_adequacy_aux (N : Nat) :
    ∀ d t ρ₁ ρ₂,
      closedAt d t = true →
      EnvValueEqAll d ρ₁ ρ₂ →
      (∀ v₁, Reaches (.compute [] ρ₁ t) (.halt v₁) → ∃ n₁, n₁ ≤ N ∧ steps n₁ (.compute [] ρ₁ t) = .halt v₁) →
      (∀ v₂, Reaches (.compute [] ρ₂ t) (.halt v₂) → ∃ n₂, n₂ ≤ N ∧ steps n₂ (.compute [] ρ₂ t) = .halt v₂) →
      -- ... same for error ...
      (error↔) ∧ (halts↔) ∧ (∀ k v₁ v₂, halt v₁ → halt v₂ → ValueEq k v₁ v₂)
```

By strong induction on `N`. The closure body recursive call uses the
step count of the body execution, which is strictly less than N (since
the function and argument evaluations consumed some steps).

Actually this is unnecessarily complex. The simpler formulation:

The proof combines:
1. `sameBody_structural` (Phase 5) for the case where the bisimulation
   handles everything.
2. For the non-structural case (differing argument), compose via
   VLam clause + `sameBody_structural`.

But `sameBody_structural` requires `SBEnvRelV`, which needs `SBValueRelV`
at every position. The differing position has `∀ k, ValueEq k`, not
`SBValueRelV`.

**THE MISSING PIECE: `∀ k, ValueEq k v₁ v₂ → SBValueRelV v₁ v₂`.**

This is not provable in general. But it IS provable for values that are
produced by the same computation under related environments! Specifically:
if both `v₁` and `v₂` are produced by evaluating the same term under
`SBEnvRelV`-related environments, then `sb_bisim_reaches` gives `SBValueRelV`.

**So: first prove that `vx₁` and `vx₂` (the arguments) are `SBValueRelV`-related
(not just `∀ k, ValueEq k`-related), THEN use `sameBody_structural`.**

But `vx₁` and `vx₂` come from evaluating `ta` and `ta'` (different terms)
under the same `ρ`. They're NOT produced by the same computation.

Hmm.

**Actually, for the SPECIFIC case of `refines_app_arg_behEq`:**
- `vx` from `ta` under `ρ`.
- `vx'` from `ta'` under `ρ`.
- `ta ≠ ta'` (different lowered argument terms).
- `BehEq` gives `∀ k, ValueEq k vx vx'`.

There's NO way to get `SBValueRelV vx vx'` since they come from different terms.

**The argument bridge genuinely requires a NON-structural relation at position 1.**

So we MUST handle the case where some env positions are observationally
(not structurally) related. This means `sb_step_preserves` must handle
the `.veqAll` case.

For `.veqAll` VLam application, the bisimulation EXITS. The continuation
result is determined by the VLam clause of `ValueEq` (for the same-arg
part) and a recursive `sameBody_adequacy` call (for the arg bridge).

**The recursion is well-founded on the execution step count:**

```lean
private theorem sameBody_aux (N : Nat) (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true) (hρ : EnvValueEqAll d ρ₁ ρ₂)
    (hN₁ : ∀ s, Reaches (.compute [] ρ₁ t) s → ∃ n, n ≤ N ∧ steps n (.compute [] ρ₁ t) = s)
    (hN₂ : ∀ s, Reaches (.compute [] ρ₂ t) s → ∃ n, n ≤ N ∧ steps n (.compute [] ρ₂ t) = s) :
    (error↔) ∧ (halts↔) ∧ (∀ k v₁ v₂, halt v₁ → halt v₂ → ValueEq k v₁ v₂)
```

By strong induction on N. Hmm, but the step-bound hypotheses are awkward.

**Simpler: prove a bisimulation that tracks the step count budget.**

Actually, the simplest correct approach:

## Simplest correct approach

**Don't use a bisimulation at all. Use the existing `StateRel` bisimulation
with σ = id, plus the VLam clause of ValueEq, composed via transitivity.**

For `sameBody_adequacy` for `ρ₁.extend vx` vs `ρ₂.extend vx'`:

Case 1: `ρ₁ = ρ₂ = ρ` (shared env, different head).
This is the case for `funV_frame_beh`.

Chain: body(ρ.extend vx) ≡ body(ρ.extend vx')

By composing THREE computations:
- body(ρ.extend vx) ≡ body(ρ.extend vx)    [identity]
- Hmm, still can't bridge.

Actually, use the EXISTING `StateRel` bisimulation:
- `EnvRelV id d ρ ρ` is trivially constructible (by `envRelV_refl`).
- Extend with `ValueRelV.refl` for vx:
  `EnvRelV (liftRename id) (d+1) (ρ.extend vx) (ρ.extend vx)`.
  Since `liftRename id = id`, this is `EnvRelV id (d+1) (ρ.extend vx) (ρ.extend vx)`.
- Build `StateRel.compute .nil id (d+1) henvExt hcl`.
- `bisim_reaches` gives `ValueRelV` for body under (ρ.extend vx) vs (ρ.extend vx).
  This is trivially `.refl` since it's the same computation. **Useless.**

We need (ρ.extend vx) vs (ρ.extend vx'), not vs itself.

`EnvRelV id d ρ ρ` extended with `ValueRelV vx vx'` gives
`EnvRelV id (d+1) (ρ.extend vx) (ρ.extend vx')`.
But we need `ValueRelV vx vx'`, which we don't have.

**WE CANNOT USE THE EXISTING BISIMULATION because the differing values
aren't `ValueRelV`-related.**

## Conclusion

The proof of `sameBody_adequacy` requires a bisimulation that allows
`.veqAll` values at some environment positions, with a well-founded exit
strategy when `.veqAll` closures are applied. The well-foundedness comes
from execution step count decreasing at each closure entry.

The estimated complexity is ~600-800 lines total:
- Phase 1 (relations + helpers): ~150 lines
- Phase 2 (sb_step_preserves): ~400 lines
- Phase 3 (extraction): ~40 lines
- Phase 4 (SBValueRelV → ValueEq bridge): ~100 lines
- Phase 5 (sameBody_structural): ~10 lines
- Phase 6 (sameBody_adequacy composition): ~100 lines

The `.veqAll` exit handling in Phase 2 and the step-count well-foundedness
in Phase 6 are the genuinely new proof work. Everything else mirrors existing
infrastructure.
