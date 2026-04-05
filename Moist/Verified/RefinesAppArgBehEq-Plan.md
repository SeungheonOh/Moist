# Plan for `refines_app_arg_behEq`

## Goal

Prove:

```lean
theorem refines_app_arg_behEq (f a a' : Expr) (ha : a ⊑ a') :
    Expr.App f a ⊑ Expr.App f a' := by
  sorry
```

Target file for the final theorem:

- `Moist/Verified/Congruence.lean`

The theorem is not blocked by the outer `App` syntax. It is blocked by the semantic fact that the same function value must be applied to two arguments that are only `ValueEq`-related.

The critical missing ingredient is:

- same-body adequacy under environments related pointwise by `ValueEq`

Without that, the lambda case of application cannot be closed.

## Recommended file split

Minimal clean split:

1. `Moist/Verified/StepLift.lean`
   - add generic stack-lifting lemmas that are not purity-specific
2. `Moist/Verified/SameBody.lean`
   - new file
   - put `EnvValueEq`, builtin extensionality under `ListValueEq`, and same-body adequacy here
3. `Moist/Verified/Congruence.lean`
   - add the `funV`-frame transfer lemmas
   - add application decomposition lemmas
   - prove `refines_app_arg_behEq`

If you want the smallest patch count instead of the cleanest layering, all new lemmas can temporarily live in `Congruence.lean`, but the generic same-body machinery does not belong there long-term.

## What not to do

- Do not try to finish `refines_app_arg_behEq` directly from `refines_behEq_at`.
  - The proof will get stuck at the lambda case of `.ret [.funV vf] vx`.
- Do not rely on `Moist/Verified/FTLR.lean` as-is.
  - It still has `sorry`s.
  - It is phrased in terms of `FullValueEq` / `EnvFullEq`, which is stronger than what `ha : a ⊑ a'` gives.
- Do not import `DeadLet.lean` into `Congruence.lean` hoping `ValueRelV.toValueEq` will solve the problem.
  - `ValueRelV -> ValueEq` is only one-way.
  - the application proof needs adequacy for environments related by `ValueEq`, not `ValueRelV`.

## Dependency graph

```text
compute_to_error_from_error
        \
         +--> app decomposition lemmas -----------------------------\
                                                                 \
EnvValueEq + lookup/extend + evalBuiltin_listValueEq + same-body  +--> funV_frame_beh
                                                                 /
refines_behEq_at -----------------------------------------------/
                                                                \
                                                                 +--> refines_app_arg_behEq
```

## Phase 1: Generic lift lemmas

These are used to move between evaluating a term with an empty stack and evaluating it under an inert stack suffix.

### Lemma 1.1

File:

- move or duplicate next to `liftState` in `Moist/Verified/StepLift.lean`

Statement:

```lean
theorem compute_to_ret_from_halt (ρ : CekEnv) (t : Term) (v : CekValue)
    (extra : Stack)
    (h : Reaches (.compute [] ρ t) (.halt v)) :
    Reaches (.compute extra ρ t) (.ret extra v)
```

Status:

- already proved in `Moist/Verified/Purity.lean`

Plan:

- move it out of `Purity.lean` or duplicate it locally
- no proof changes needed

### Lemma 1.2

File:

- `Moist/Verified/StepLift.lean`

Statement:

```lean
theorem compute_to_error_from_error (ρ : CekEnv) (t : Term)
    (extra : Stack)
    (h : Reaches (.compute [] ρ t) .error) :
    Reaches (.compute extra ρ t) .error
```

Proof idea:

- prove by the same `firstInactive` + `steps_liftState` pattern as `compute_to_ret_from_halt`
- use `liftState_eq_error` instead of `liftState_ne_halt`

Exact tactic shape:

1. `obtain ⟨N, hN⟩ := h`
2. show some step `K <= N` is inactive
   - use `steps N ... = .error`
3. obtain first inactive `K` via `firstInactive`
4. commute `steps K` through `liftState extra`
5. show the inner state at `K` cannot be `.halt _`
   - contradiction with later error using `steps_halt`
6. split on the inner state at `K`
   - `.error` gives the result directly
   - `.ret [] v` and `.halt v` are impossible because they would force later halting
   - active states contradict minimality

This lemma will be used only as a reconstruction tool when the function or argument subcomputation errors.

## Phase 2: Environment relation by `ValueEq`

This is the actual missing abstraction.

### Lemma 2.1

File:

- new `Moist/Verified/SameBody.lean`

Definition:

```lean
def EnvValueEq (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n -> n ≤ d ->
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEq k v₁ v₂
    | none, none => True
    | _, _ => False
```

Reason:

- `ValueEq` for lambdas quantifies over applying closures to related arguments
- after one beta step, the two environments differ only in the head binding
- that relation must be stable under further lambdas

### Lemma 2.2

Statement:

```lean
theorem envValueEq_refl (k d : Nat) (ρ : CekEnv) : EnvValueEq k d ρ ρ
```

Tactics:

1. `intro n hn hle`
2. `cases h : ρ.lookup n`
3. `simp [EnvValueEq, h, valueEq_refl]`

### Lemma 2.3

Statement:

```lean
theorem envValueEq_extend (k d : Nat) {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hρ : EnvValueEq k d ρ₁ ρ₂) (hv : ValueEq k v₁ v₂) :
    EnvValueEq k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂)
```

Tactics:

1. `intro n hn hle`
2. `cases n with`
3. `case zero => omega`
4. `case succ m => cases m with`
5. `case zero`
   - this is lookup position `1`
   - `simp [CekEnv.extend, EnvValueEq, hv]`
6. `case succ m'`
   - reduce both lookups to tail lookups
   - `simpa [CekEnv.extend] using hρ (m' + 1) (by omega) (by omega)`

### Lemma 2.4

Statement:

```lean
theorem envValueEq_lookup_left {k d : Nat} {ρ₁ ρ₂ : CekEnv} {n : Nat} {v₁ : CekValue}
    (hρ : EnvValueEq k d ρ₁ ρ₂) (hn : 0 < n) (hd : n ≤ d)
    (h₁ : ρ₁.lookup n = some v₁) :
    ∃ v₂, ρ₂.lookup n = some v₂ ∧ ValueEq k v₁ v₂
```

Tactics:

1. specialize `hρ n hn hd`
2. rewrite `h₁` into `hρ`
3. `cases h₂ : ρ₂.lookup n`
4. `simp [h₂] at hρ`
5. extract `⟨_, h₂, hρ⟩`

Also add the symmetric version:

```lean
theorem envValueEq_lookup_right ...
```

This is needed for the variable cases in same-body adequacy.

## Phase 3: Builtins under `ListValueEq`

The builtin case must not depend on `ValueRelV`; it must work directly from `ListValueEq`.

### Lemma 3.1

File:

- `Moist/Verified/SameBody.lean`

Statement:

```lean
theorem evalBuiltin_listValueEq (k : Nat) (b : BuiltinFun)
    (args₁ args₂ : List CekValue)
    (hargs : ListValueEq (k + 1) args₁ args₂) :
    (Moist.CEK.evalBuiltin b args₁ = none ↔
     Moist.CEK.evalBuiltin b args₂ = none) ∧
    (∀ r₁ r₂,
      Moist.CEK.evalBuiltin b args₁ = some r₁ →
      Moist.CEK.evalBuiltin b args₂ = some r₂ →
      ValueEq k r₁ r₂)
```

Proof idea:

- mirror the two-stage proof already used in `Bisim.evalBuiltin_relV`
- but replace `ListValueRelV` with `ListValueEq (k+1)`

Sublemmas to prove first:

```lean
private theorem valueEq_vconProj ...
private theorem listValueEq_vconSkel ...
private theorem extractConsts_listValueEq ...
```

Tactics:

1. define the same `vconProj` helper used in `Bisim`
2. prove skeleton preservation by induction on `ListValueEq`
3. for `ValueEq (k+1)` on heads:
   - `VCon` case gives literal equality
   - mismatched `VCon` / non-`VCon` is impossible by `simp [ValueEq]`
4. then copy the `evalBuiltin` case split from `Bisim.evalBuiltin_relV`
   - `simp [evalBuiltin]`
   - `generalize` pass-through results
   - `generalize` `extractConsts` results
   - use skeleton equality to show success/failure agreement

This lemma is used in:

- same-body adequacy for builtin values
- `funV` frame transfer for saturated builtins

## Phase 4: Same-body adequacy under `EnvValueEq`

This is the core logical-relation proof. The right model is the existing bundle in `DeadLet.lean`, but with `EnvRelV` replaced by `EnvValueEq`.

### Lemma 4.1

File:

- `Moist/Verified/SameBody.lean`

Private bundle:

```lean
private theorem same_body_bundle_aux (k : Nat) :
    (∀ d t ρ₁ ρ₂ v₁ v₂,
      closedAt d t = true ->
      EnvValueEq k d ρ₁ ρ₂ ->
      Reaches (.compute [] ρ₁ t) (.halt v₁) ->
      Reaches (.compute [] ρ₂ t) (.halt v₂) ->
      ValueEq k v₁ v₂) ∧
    (∀ v₁ v₂, SameBodyValueEq k v₁ v₂ -> ValueEq k v₁ v₂) ∧
    (∀ vs₁ vs₂, SameBodyListValueEq k vs₁ vs₂ -> ListValueEq k vs₁ vs₂)
```

Recommended auxiliary inductives:

```lean
inductive SameBodyValueEq (k : Nat) : CekValue -> CekValue -> Prop where
  | vcon ...
  | vlam ...
  | vdelay ...
  | vconstr ...
  | vbuiltin ...

inductive SameBodyListValueEq (k : Nat) : List CekValue -> List CekValue -> Prop where
  | nil
  | cons ...
```

Why this extra layer is worth it:

- it makes the closure cases match the shape of `ValueEq`
- it avoids trying to prove `ValueEq` directly by raw case analysis on CEK values
- it is the same role that `ValueRelV -> ValueEq` plays in `DeadLet.lean`

### Lemma 4.2

Successor bridge:

```lean
private theorem sameBodyValue_to_valueEq_succ (k : Nat)
    (ihA : ...)
    (ihB : ...)
    (ihC : ...)
    (v₁ v₂ : CekValue) :
    SameBodyValueEq (k + 1) v₁ v₂ -> ValueEq (k + 1) v₁ v₂
```

Tactics by constructor:

- `vcon`
  - `simp [ValueEq]`
- `vlam`
  - `unfold ValueEq`
  - `intro arg`
  - use `envValueEq_extend` with `valueEq_refl _ arg`
  - recurse with `ihA`
- `vdelay`
  - same pattern, but no fresh binder shift
- `vconstr`
  - `unfold ValueEq`
  - `refine ⟨rfl, ?_⟩`
  - discharge with `ihC`
- `vbuiltin`
  - `unfold ValueEq`
  - use `evalBuiltin_listValueEq`

### Lemma 4.3

Evaluation theorem at successor index:

```lean
private theorem closed_eval_envValueEq_succ (k : Nat)
    (ihA : ...)
    (value_to_eq : ∀ v₁ v₂, SameBodyValueEq (k + 1) v₁ v₂ -> ValueEq (k + 1) v₁ v₂)
    (d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv) (v₁ v₂ : CekValue)
    (hcl : closedAt d t = true)
    (hρ : EnvValueEq (k + 1) d ρ₁ ρ₂)
    (h₁ : Reaches (.compute [] ρ₁ t) (.halt v₁))
    (h₂ : Reaches (.compute [] ρ₂ t) (.halt v₂)) :
    ValueEq (k + 1) v₁ v₂
```

Proof strategy:

- `match t with`

Cases:

1. `Var 0`
   - impossible
   - `cases` on the reachability witness and `simp [steps, step]`
2. `Var (m+1)`
   - use `envValueEq_lookup_left` and `envValueEq_lookup_right`
   - obtain the looked-up values
   - use `reaches_unique` to rewrite `v₁` and `v₂`
3. `Constant`
   - both halt in 2 steps
   - `reaches_unique`
   - `simp [ValueEq]`
4. `Builtin`
   - both halt in 2 steps with identical `VBuiltin`
   - `unfold ValueEq`
   - use `valueEq_refl` on the builtin result clause
5. `Error`
   - impossible
6. `Lam`
   - both halt in 2 steps as closures with the same body
   - package a `SameBodyValueEq.vlam`
   - apply `value_to_eq`
7. `Delay`
   - same as `Lam`
8. `Force`
   - use `force_reaches` from `Congruence.lean`
   - recurse on the inner term
   - transfer the outer force-frame behavior with existing:
     - `force_frame_error_transfer`
     - `force_frame_halts_transfer`
   - for final value clause, match on the forced value exactly as in `refines_force_behEq`
9. `Apply`
   - this is where the new application decomposition lemmas from Phase 6 are used
10. `Constr`
   - prove fieldwise decomposition
   - recurse on each field and use list assembly
11. `Case`
   - decompose the scrutinee
   - then transfer through the pushed `applyArg` frames
   - this may require an `applyArg_frame_beh` theorem analogous to `funV_frame_beh`

Note:

- `Apply` and `Case` are the two largest cases
- do not start them before Phase 5 and Phase 6 are in place

### Lemma 4.4

Public corollary:

```lean
theorem closedAt_envValueEq_valueEq (k d : Nat) (t : Term) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t = true)
    (hρ : EnvValueEq k d ρ₁ ρ₂)
    (v₁ v₂ : CekValue)
    (h₁ : Reaches (.compute [] ρ₁ t) (.halt v₁))
    (h₂ : Reaches (.compute [] ρ₂ t) (.halt v₂)) :
    ValueEq k v₁ v₂
```

Proof:

- direct projection from `same_body_bundle_aux`

This is the theorem the lambda branch of application actually needs.

## Phase 5: Transfer through the `.funV` frame

This is the immediate local lemma that `refines_app_arg_behEq` will consume.

### Lemma 5.1

File:

- `Moist/Verified/Congruence.lean`

Statement:

```lean
private theorem funV_frame_beh (k : Nat)
    (vf vx vx' : CekValue)
    (hx : ValueEq (k + 1) vx vx') :
    (Reaches (.ret [.funV vf] vx) .error ↔ Reaches (.ret [.funV vf] vx') .error) ∧
    (Halts (.ret [.funV vf] vx) ↔ Halts (.ret [.funV vf] vx')) ∧
    ∀ w₁ w₂,
      Reaches (.ret [.funV vf] vx) (.halt w₁) ->
      Reaches (.ret [.funV vf] vx') (.halt w₂) ->
      ValueEq k w₁ w₂
```

Proof by `cases vf with`:

1. `VCon`
   - both sides step to `.error`
   - `simp [steps, step]`
2. `VDelay`
   - both sides step to `.error`
3. `VConstr`
   - both sides step to `.error`
4. `VLam body ρ`
   - both sides step in one step to:
     - `.compute [] (ρ.extend vx) body`
     - `.compute [] (ρ.extend vx') body`
   - get `hclosed` from `closedAt_exists body`
   - build `EnvValueEq (k + 1) (d' + 1) (ρ.extend vx) (ρ.extend vx')`
     - tail positions by `envValueEq_refl`
     - head position by `hx`
   - use `closedAt_envValueEq_valueEq` for the value clause
   - error/halt clauses are obtained by the same theorem specialized to reachability
5. `VBuiltin b args ea`
   - `cases hhead : ea.head`
   - `cases htail : ea.tail`
   - partial case:
     - result is `.VBuiltin b (vx :: args) rest`
     - use `unfold ValueEq`
     - combine `hx` with `listValueEq_refl`
   - saturated case:
     - use `evalBuiltin_listValueEq`

Tactic notes:

- for impossible halting/error branches, use:
  - `cases n with`
  - `simp [steps, step, steps_error, steps_halt]`
- for the lambda case, do not unfold all of `closedAt_envValueEq_valueEq`
  - use it as a black-box theorem

### Optional Lemma 5.2

If the `Case` branch of Phase 4 becomes awkward, add the sibling theorem:

```lean
private theorem applyArg_frame_beh ...
```

It is the same proof as `funV_frame_beh`, but for `.ret [.applyArg vx] vf`.

## Phase 6: Application decomposition lemmas

These are the application analogues of:

- `force_reaches`
- `force_reaches_error`
- `beta_apply_from_inner`

### Lemma 6.1

File:

- `Moist/Verified/Congruence.lean`

Statement:

```lean
private theorem app_reaches (ρ : CekEnv) (tf ta : Term) (w : CekValue)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) (.halt w)) :
    ∃ vf vx,
      Reaches (.compute [] ρ tf) (.halt vf) ∧
      Reaches (.compute [] ρ ta) (.halt vx) ∧
      Reaches (.ret [.funV vf] vx) (.halt w)
```

Proof sketch:

1. step once:
   - `compute [] ρ (Apply tf ta)` to `compute [.arg ta ρ] ρ tf`
2. use the same `firstInactive` + `liftState` pattern as `force_reaches`
   - base stack is `[.arg ta ρ]`
3. extract `vf` where function evaluation finishes
4. after one mechanical step from `.ret [.arg ta ρ] vf`
   - obtain `compute [.funV vf] ρ ta`
5. repeat the same pattern with base stack `[.funV vf]`
6. extract `vx`

This is the longest single helper after Phase 4.

### Lemma 6.2

Statement:

```lean
private theorem app_reaches_error (ρ : CekEnv) (tf ta : Term)
    (h : Reaches (.compute [] ρ (.Apply tf ta)) .error) :
    Reaches (.compute [] ρ tf) .error ∨
    ∃ vf, Reaches (.compute [] ρ tf) (.halt vf) ∧
      (Reaches (.compute [] ρ ta) .error ∨
       ∃ vx, Reaches (.compute [] ρ ta) (.halt vx) ∧
             Reaches (.ret [.funV vf] vx) .error)
```

Proof sketch:

- same structure as `app_reaches`
- split depending on whether the function phase already errors
- if not, split again depending on whether the argument phase errors

### Lemma 6.3

Statement:

```lean
private theorem app_apply_from_parts (ρ : CekEnv) (tf ta : Term)
    (vf vx : CekValue) (s : State)
    (hf : Reaches (.compute [] ρ tf) (.halt vf))
    (ha : Reaches (.compute [] ρ ta) (.halt vx))
    (hcont : Reaches (.ret [.funV vf] vx) s) :
    Reaches (.compute [] ρ (.Apply tf ta)) s
```

Tactics:

1. use the initial mechanical step for `Apply`
2. use `compute_to_ret_from_halt` to embed the function computation under `[.arg ta ρ]`
3. one mechanical step from `.ret [.arg ta ρ] vf` to `.compute [.funV vf] ρ ta`
4. use `compute_to_ret_from_halt` again to embed the argument computation under `[.funV vf]`
5. compose with `hcont` using `steps_trans`

### Lemma 6.4

Optional reconstruction helpers if needed:

```lean
private theorem app_error_from_fun_error ...
private theorem app_error_from_arg_error ...
```

These are thin wrappers around `compute_to_error_from_error` plus the mechanical CEK steps.

## Phase 7: The final theorem

### Lemma 7.1

File:

- `Moist/Verified/Congruence.lean`

Statement:

```lean
theorem refines_app_arg_behEq (f a a' : Expr) (ha : a ⊑ a') :
    Expr.App f a ⊑ Expr.App f a' := by
```

Proof skeleton:

```lean
refine ⟨?comp, ?beh⟩
```

#### Compilation clause

Goal:

```lean
∀ env, (lowerTotalExpr env (.App f a)).isSome ->
       (lowerTotalExpr env (.App f a')).isSome
```

Tactics:

1. `intro env hs`
2. `rw [lowerTotalExpr_app] at hs ⊢`
3. `cases hf : lowerTotalExpr env f <;> simp [Option.bind, hf] at hs`
4. in the `some tf` case:
   - `cases ha0 : lowerTotalExpr env a <;> simp [Option.bind, ha0] at hs`
   - get `hs_arg : (lowerTotalExpr env a).isSome`
   - use `ha.1 env hs_arg`
   - `obtain ⟨ta', hta'⟩ := Option.isSome_iff_exists.mp ...`
   - `rw [hf, hta']`
   - `simp [Option.bind]`

#### BehEq clause

Goal:

```lean
intro env
```

Tactics:

1. `simp only [lowerTotalExpr_app]`
2. `cases hf : lowerTotalExpr env f`
   - `none => simp [Option.bind_none]`
3. `case some tf =>`
   - `cases ha0 : lowerTotalExpr env a`
   - `cases ha1 : lowerTotalExpr env a'`
   - reduce to the `some ta`, `some ta'` case
4. `intro ρ hwf`
5. obtain the argument refinement at this environment:

```lean
have ⟨herr_a, hhalt_a, hval_a⟩ := refines_behEq_at ha ha0 ha1 ρ hwf
```

6. prove error equivalence
   - `constructor`
   - decompose the left error with `app_reaches_error`
   - function-error branch:
     - reconstruct right error with same function error
   - function-halt branch:
     - if argument errors, transfer using `herr_a`
     - if argument halts with `vx` and frame errors, obtain `vx'` from `hhalt_a`
     - use `funV_frame_beh 0 vf vx vx'`
     - reconstruct with `app_apply_from_parts`
7. prove halting equivalence
   - use `app_reaches` on the halting side
   - get `vf`, `vx`
   - obtain `vx'` from `hhalt_a`
   - use `funV_frame_beh 0 vf vx vx'`
   - reconstruct with `app_apply_from_parts`
8. prove the final `ValueEq k`
   - decompose both halting apps with `app_reaches`
   - use determinism of the function phase to identify the same `vf`
     - both function evaluations are from the same term `tf` and same env `ρ`
     - use `reaches_unique`
   - get `harg : ValueEq (k + 1) vx vx'` from `hval_a (k + 1) ...`
   - apply the third component of `funV_frame_beh k vf vx vx' harg`

Important detail:

- the function-phase determinism argument is essential
- the theorem only changes the argument expression, so the function value is literally the same on both sides

## Expected proof order

This order avoids circular work:

1. `compute_to_error_from_error`
2. `EnvValueEq` and its lookup/extend lemmas
3. `evalBuiltin_listValueEq`
4. same-body adequacy bundle in `SameBody.lean`
5. `funV_frame_beh`
6. `app_reaches`, `app_reaches_error`, `app_apply_from_parts`
7. `refines_app_arg_behEq`

## Sanity check before editing Lean

Before implementing, confirm these two design choices:

1. Put same-body adequacy in a shared file, not inside `DeadLet.lean`
2. Keep the application proof centered on a single `funV_frame_beh` theorem

If either choice changes mid-implementation, the proof will sprawl.
