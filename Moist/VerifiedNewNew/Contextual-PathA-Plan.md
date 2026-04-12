# Path A — Open-Context CtxEq via CEK Trace Bisimulation

> **Status:** in progress (started 2026-04-12).
> **Owner:** Claude.
> **Read this top-to-bottom before resuming work.** Follow biblically.

---

## 0. Goal

Replace the closed-context `CtxEq`/`CtxRefines` with the open-context versions and prove

```lean
theorem soundness (t₁ t₂ : Term) :
    OpenEq 0 t₁ t₂ → ∀ C : Context,
      ObsEq (.compute [] .nil (fill C t₁))
            (.compute [] .nil (fill C t₂))
```

without using `openEq_contextual_closure` (which fundamentally needs `C.closedAt 0`).

---

## 1. Architectural picture

Two CEK traces starting from `compute [] .nil (fill C t₁)` and `compute [] .nil (fill C t₂)` evolve in lockstep modulo a syntactic substitution congruence, until one of them is about to *directly* compute `t₁` while the other is about to directly compute `t₂` — at which point `OpenEq 0 t₁ t₂` takes over the rest of the trace.

To formalise this we need:

1. **`Subst`** — a syntactic congruence relation parameterised by `(t₁, t₂)` saying "these two terms / values / envs / frames / stacks / states differ only by zero or more `t₁ ↔ t₂` swaps".
2. **Lockstep step lemma** — `step` preserves `Subst` *unless* the step is about to "expose" the hole content as the active term being computed, in which case it leaves a residual obligation that `OpenEq 0` discharges.
3. **Lifting `Subst`-on-stacks to `StackRelK`** — at the moment the hole becomes active, we need to convert "the two stacks are syntactically `Subst`-related" into "the two stacks are biorthogonally `StackRelK`-related", so that `OpenEq 0 t₁ t₂` can be instantiated against them. **This is the deepest part of the proof.**
4. **Soundness assembly** — strong induction on the number of steps to halt, using the lockstep lemma at each step and discharging via `OpenEq 0` at every transition.

---

## 2. File layout

```
Moist/VerifiedNewNew/Contextual/Subst.lean      -- Phases 1-3
Moist/VerifiedNewNew/Contextual/Soundness.lean  -- Phases 4-6
```

`Contextual.lean` itself will eventually:
- Drop `C.closedAt 0` from the body of `CtxEq` and `CtxRefines`.
- Lose the closedness preconditions on every congruence theorem.
- Re-export `soundness` from `Contextual/Soundness.lean`.

> **N.B.** Lean 4 allows both `Contextual.lean` (module file) and `Contextual/` (directory of submodules) to coexist. The submodule files have namespace `Moist.VerifiedNewNew.Contextual.Subst` etc.

---

## 3. Phases (in execution order)

### Phase 1 — `Subst` definitions (Subst.lean, ~250 lines)

Mutually inductive substitution congruences over the entire CEK universe, parameterised by `t₁ t₂ : Term`. See architectural picture for the full inductive shapes.

Five inductive families:
- `TermSubst` (mutual with `TermListSubst`)
- `ValueSubst` (mutual with `ValueListSubst` and `EnvSubst`)
- `FrameSubst`
- `StackSubst`
- `StateSubst`

Plus reflexivity and symmetry lemmas for each.

**Estimated effort:** 1.5 days.

### Phase 2 — Initial state lemma (Subst.lean, ~50 lines)

```lean
theorem fill_termSubst (C : Context) (t₁ t₂ : Term) :
    TermSubst t₁ t₂ (fill C t₁) (fill C t₂)

theorem initial_stateSubst (C : Context) (t₁ t₂ : Term) :
    StateSubst t₁ t₂ (.compute [] .nil (fill C t₁))
                     (.compute [] .nil (fill C t₂))
```

By induction on `C`, using `swap` at the hole.

**Estimated effort:** 0.5 days.

### Phase 3 — Step preservation (Subst.lean, ~600–800 lines)

The core lockstep lemma:

```lean
theorem stateSubst_step_or_obsEq (h_open : OpenEq 0 t₁ t₂) :
    ∀ {s_l s_r : State}, StateSubst t₁ t₂ s_l s_r →
      (∀ v_l, s_l ≠ .halt v_l) → (∀ v_r, s_r ≠ .halt v_r) →
      (StateSubst t₁ t₂ (step s_l) (step s_r))
      ∨ (∀ k, ObsEqK k s_l s_r)
```

The disjunction handles:
- Left: structural step preservation (via the `TermSubst`/`ValueSubst` constructor at the active position).
- Right: at a `swap`/`swapInv` position the rest of the trace is governed by `OpenEq 0`, giving `ObsEqK` for any `k`. Right-disjunct existence is proved by instantiating `h_open` against the bridge from Phase 4.

Case-split on the constructor at the active position:
- `varRefl`, `constRefl`, `builtinRefl`, `errorRefl`, `lam`, `apply`, `force`, `delay`, `constr`, `case`: structural; left disjunct.
- `swap`/`swapInv`: right disjunct.

The CEK has ~25 step rules across `compute` and `ret`; each needs a case.

**Estimated effort:** 4–6 days.

### Phase 4 — `Subst → EnvEqK / StackRelK` bridge (Subst.lean, ~300 lines)

The hardest single lemma:

```lean
theorem stackSubst_to_stackRelK {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ {π_l π_r : Stack}, StackSubst t₁ t₂ π_l π_r →
      ∀ k, StackRelK ValueEqK k π_l π_r

theorem envSubst_to_envEqK {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ {ρ_l ρ_r : CekEnv}, EnvSubst t₁ t₂ ρ_l ρ_r →
      ∀ k d, EnvEqK k d ρ_l ρ_r

theorem valueSubst_to_valueEqK {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ {v_l v_r : CekValue}, ValueSubst t₁ t₂ v_l v_r →
      ∀ k, ValueEqK k v_l v_r
```

These three are mutually recursive *with each other and with Phase 3*. The standard trick: do the proof by strong induction on `k`. At `k = 0` everything is vacuous; at `k + 1` use the IH at level `k` plus one extra `step_or_obsEq` to bridge.

**Estimated effort:** 4–5 days. **This is the design bottleneck.**

### Phase 5 — Trace soundness (Soundness.lean, ~200 lines)

```lean
theorem stateSubst_obsEq {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
    ∀ {s_l s_r : State}, StateSubst t₁ t₂ s_l s_r →
      ObsEq s_l s_r

theorem soundness (t₁ t₂ : Term) (h_open : OpenEq 0 t₁ t₂) :
    ∀ C, ObsEq (.compute [] .nil (fill C t₁))
              (.compute [] .nil (fill C t₂)) :=
  fun C => stateSubst_obsEq h_open (initial_stateSubst C t₁ t₂)
```

Strong induction on the number of steps to halt; case-split on `stateSubst_step_or_obsEq`'s disjunction.

**Estimated effort:** 1–2 days.

### Phase 6 — Drop closedness preconditions everywhere (Contextual.lean, ~30 minutes)

- Remove `C.closedAt 0 = true` from the body of `CtxEq` and `CtxRefines`.
- Remove `hC` arg from `ctxEq_trans`, `ctxRefines_trans`, `ctxEq_symm`, `ctxRefines_antisymm`.
- Strip `h_inner_closed` from `ctxEq_extend` and `ctxRefines_extend`.
- Strip closedness preconditions from `ctxEq_app`, `ctxRefines_app`, `ctxEq_constr*`, `ctxRefines_constr*`, `ctxEq_case*`, `ctxRefines_case*`.
- Then `MIR.lean`: drop `C.closedAt 0` from closed-context call sites; `mirCtxEq_iff_refines_bidir` proof shrinks.

**Estimated effort:** 0.5 days.

### Phase 7 — Tear down or migrate the old soundness chain

Keep the old `openEq_contextual_closure` and `soundness_closed` as alternative (more efficient) routes for closed-context use cases. Add a comment marking which is which.

**Estimated effort:** 1 day.

---

## 4. Risks

| Risk | Likelihood | Mitigation |
|---|---|---|
| Mutual recursion in Phase 4 doesn't terminate / Lean can't see termination | High | `termination_by` with explicit `(k, …)` lex ordering. Worst case: rewrite as `Nat.rec` on `k`. |
| `stateSubst_step_or_obsEq` has more dispatch cases than expected | Medium | Factor out `compat_*` style helpers paralleling `Equivalence.lean`'s structure. |
| Phase 4's bridge needs more invariants than just `Subst` | Medium | Add a side hypothesis (e.g. closedness of t₁ and t₂ but **not** of C) — much weaker than current. |
| Builtin step rules complex | Medium | Reuse `evalBuiltin_compat` from `Equivalence.lean`. |
| `Equivalence.lean` proofs end up duplicated | Low | Cite, don't re-prove. |
| Total file growth painful | Low | Splitting into `Subst.lean` + `Soundness.lean`. |

---

## 5. Effort

| Phase | Description | Effort |
|---|---|---|
| 1 | `Subst` definitions + reflexivity/symmetry | 1.5 days |
| 2 | `fill_termSubst`, `initial_stateSubst` | 0.5 days |
| 3 | `stateSubst_step_or_obsEq` | 4–6 days |
| 4 | `stackSubst_to_stackRelK` and friends | 4–5 days |
| 5 | `soundness` via strong induction | 1–2 days |
| 6 | Drop closedness preconditions | 0.5 days |
| 7 | Migrate old soundness | 1 day |
| **Total** | | **12.5–16.5 days** |

---

## 6. Verification milestones

1. **End of Phase 1**: All `Subst` definitions compile, reflexivity/symmetry closed without `sorry`.
2. **End of Phase 2**: `fill_termSubst` and `initial_stateSubst` compile.
3. **End of Phase 3, ~halfway**: `stateSubst_step_or_obsEq` proved for `compute` rules. Right disjunct still `sorry`.
4. **End of Phase 3**: same lemma for `ret` rules.
5. **End of Phase 4**: bridge lemmas close, retiring all the Phase 3 `sorry`s.
6. **End of Phase 5**: `soundness` closes.
7. **End of Phase 6**: full build of `Moist.VerifiedNewNew.Contextual` and `Moist.VerifiedNewNew.MIR` with no closedness preconditions on congruences.

---

## 7. Resume protocol

When resuming work:
1. Re-read this file top to bottom.
2. Check current phase status (which milestones have been hit) by inspecting `Subst.lean` / `Soundness.lean` and counting `sorry`s.
3. Identify the next sub-task in the current phase.
4. Continue execution. **Do not skip phases.** **Do not modify the architecture without updating this file first.**

If you hit a blocker:
1. Stop execution.
2. Write the blocker description in section 8 below.
3. Report to the user with the specific phase and line.

---

## 8. Blockers encountered

### B1 (RESOLVED, 2026-04-12) — see §9 progress log for the breakthrough.

The `term_obsEq` reformulation in `Soundness.lean` bypasses the bridges
entirely. Original analysis preserved below for context.

---

### B1 — Phase 4 mixed-state problem (architectural, 2026-04-12)

**Where:** `Moist/VerifiedNewNew/Contextual/Soundness.lean`, the `succ m` branch
of `all_bridges`. The base case (`zero`) is fully proved.

**Symptom.** The four bridges at level `m+1` are mutually entangled in a way
the naïve `subst_valueEqK` strategy cannot resolve.

**Concretely.**

1. The `vLam`/`vDelay` cases of `subst_valueEqK` at level `m+1` need to show
   that applying two `ValueSubst`-related closures produces `ObsEqK`-related
   compute states. The resulting compute states have envs of the form
   `(ρ_l.extend arg₁)` / `(ρ_r.extend arg₂)` where:
     * `ρ_l`/`ρ_r` are `EnvSubst`-related (syntactic, from `vLam`),
     * `arg₁`/`arg₂` are `ValueEqK`-related (semantic, from the application
       property in the definition of `ValueEqK` for `VLam`).
   The extended envs are *neither* `EnvSubst`-related (the args are not
   `ValueSubst`-related) *nor* pure `EnvEqK`-related (the original tail is
   only `EnvSubst`-related at this point).

2. The same problem appears in `subst_stackRelK` at level `m+1`: stepping a
   `.ret` state through a `.arg` (or `.applyArg`) frame produces a compute
   state with a `.funV` (or `.applyArg`) at the top of the stack whose
   contained value is `ValueEqK`-related (from the `.ret`'s value), not
   `ValueSubst`-related. The rest of the stack remains `StackSubst`-related.
   This "mixed" stack cannot be expressed in terms of `StateSubst`, so the
   inner IH `ih_state` cannot be applied directly.

**Resolution path (refactor).** Generalise the relations to a "weak/mixed"
family that allows the top of the stack/env to carry `ValueEqK`-related
values rather than `ValueSubst`-related ones. Concretely:

```
inductive WkFrame (t₁ t₂ : Term) (k : Nat) : Frame → Frame → Prop
  | subst : FrameSubst t₁ t₂ f_l f_r → WkFrame t₁ t₂ k f_l f_r
  | funVEqK : ValueEqK k v_l v_r →
      WkFrame t₁ t₂ k (.funV v_l) (.funV v_r)
  | applyArgEqK : ValueEqK k v_l v_r →
      WkFrame t₁ t₂ k (.applyArg v_l) (.applyArg v_r)
inductive WkStack ... | ...
inductive WkState ... | compute (StackRelK + EnvSubst-with-EqK-ext + TermSubst)
                       | ret (StackRelK + ValueEqK)
                       ...
```

Then prove the bridge for `WkState` and observe that `StateSubst → WkState`,
recovering `subst_obsEq` as a corollary. The cost is roughly **doubling the
size of `Subst.lean`** because the entire `stateSubst_step_or_obsEq` step
lemma needs to be re-proved against `WkState`.

**Estimated effort to resolve B1:** 5–7 days (matches the original Phase 4
estimate plus the refactor overhead).

**Status as of stopping point.** Base case `k = 0` of `all_bridges` is fully
proven. The successor case `k = m+1` carries one `sorry` annotated with the
above analysis. The four projections (`subst_obsEq`, `subst_stackRelK`,
`subst_valueEqK`, `subst_envEqK`) are wired up and will inherit the proof
once `all_bridges` is closed.

---

## 9. Progress log

- **2026-04-12 — Phase 6 COMPLETE. Closedness preconditions dropped.**

  `Contextual.lean` and `MIR.lean` have been rewritten to operate on
  unrestricted open contexts:

    * `def CtxEq` and `def CtxRefines` no longer carry `C.closedAt 0 = true →`.
      Both quantify over every `Context` unconditionally.
    * `ctxEq_trans / _refl / _symm`, `ctxRefines_trans / _refl / _antisymm`,
      `CtxEq.toCtxRefines(_symm)` all drop their `hC` arg and compose
      trivially via `Iff.trans` / `Function` composition.
    * `ctxEq_extend` / `ctxRefines_extend` no longer take the
      `h_inner_closed` closedness obligation — they just compose contexts
      and apply `fill_compose`.
    * All `ctxEq_*` and `ctxRefines_*` congruence theorems
      (`lam`, `delay`, `force`, `app`, `constr_one`, `constr_swap_prefix`,
      `constr`, `case_scrut`, `case_one_alt`, `case_swap_prefix`, `case`)
      drop their closedness sidecars.
    * The `closedAt_mono` / `closedAtList_mono` mutual block, the
      `closedAtList_append` helper, and the entire old-`soundness` chain
      (`openEq_listRel_refl`, `openEq_listRel_around`, `openEq_constr`,
      `openEq_contextual_closure`, `envEqK_zero`, `stackRelK_nil`,
      `openEq_weaken_zero`, `soundness`) have been deleted — the new
      open-context soundness lives in `Contextual/Soundness.lean` and is
      referenced via a pointer doc-comment at the bottom of
      `Contextual.lean`.
    * `MIR.lean`: `mirCtxEq_refl` drops its second lambda arg; `mirCtxEq_symm`
      and `mirCtxEq_trans` drop their `hC` and invoke `hctx C` directly.
      `MIRCtxEq`/`MIRCtxRefines` definitions needed no edits — they inherit
      the new open-context `CtxEq`/`CtxRefines` through the `open`.

  **Build status:**
  ```
  ✔ [60/63] Built Moist.VerifiedNewNew.Contextual.Subst (425ms)
  ✔ [63/63] Built Moist.VerifiedNewNew.Contextual.Soundness (763ms)
  ✔ Built Moist.VerifiedNewNew.Contextual + MIR
  ```

  No sorries in `Contextual.lean`, `Contextual/Subst.lean`,
  `Contextual/Soundness.lean`, or `MIR.lean` itself. The only remaining
  warning in the chain is the pre-existing `Moist.MIR.Analysis:514` sorry
  (`Inhabited ANFExpr` via `default := ⟨.Error, sorry⟩`) that `MIR.lean`
  picks up through its `Moist.MIR.LowerTotal` import — unchanged from
  before Phase 6 and outside its scope.

  Path A of the plan is now end-to-end green: open-context `CtxEq`,
  open-context congruences, and open-context soundness via the
  `term_obsEq` semantic bridge.

- **2026-04-12 — 🎉 ALL SORRIES CLOSED. Phase 4 + 5 COMPLETE.**

  Final status:
    * `Moist/VerifiedNewNew/Contextual/Soundness.lean` (592 lines): zero
      sorries. Contains `term_obsEq` (the main bridge), `constrField_helper`
      (for the constr non-empty case), `soundness` (the open-context
      soundness theorem), plus all supporting helpers.
    * `Moist/VerifiedNewNew/Contextual/Subst.lean` (442 lines): zero sorries.
      Removed the obsolete `evalBuiltin_subst` and `stateSubst_step_or_obsEq`
      (which belonged to the old direct-bridge approach that hit B1).
    * `Moist/VerifiedNewNew/Equivalence.lean`: removed unused `import
      Moist.MIR.Lower` and `import Moist.MIR.LowerTotal` to prune the
      transitive sorry from `Moist.MIR.Analysis` (which had a sorry'd
      `Inhabited ANFExpr` instance).

  **Cases proven in `term_obsEq`:**
    * `swap` / `swapInv`: instantiate `OpenEq 0 t₁ t₂` directly.
    * `varRefl`: env lookup via `AtLeastEnvEqK`, dispatch via stack relation.
    * `constRefl` / `builtinRefl` / `errorRefl`: trivial structural cases.
    * `lam` / `delay`: construct `ValueEqK` of `VLam`/`VDelay` closure inline
      using `ih` at smaller levels with extended env.
    * `force`: pushes `.force` frame; constructs new `StackRelK` inline by
      dispatching on `vf` via `ValueEqK` (`VDelay` uses application property,
      `VBuiltin` uses `evalBuiltin_compat` from `Equivalence.lean`).
    * `apply`: pushes `.arg` frame; constructs new `StackRelK` inline, which
      itself triggers a nested `.funV` frame `StackRelK` construction
      (`VLam` uses application property, `VBuiltin` uses `evalBuiltin_compat`).
    * `constr` empty: directly retVConstr.
    * `constr` non-empty: uses `constrField_helper`, which is parameterized
      over `term_obsEq`'s IH and recurses on the field list, mirroring
      `Equivalence.lean`'s `constrField_stackRelK` proof.
    * `case`: constructs `.caseScrutinee` `StackRelK` inline. Dispatches on
      `vf` between `VConstr` (uses `termListSubst_getElem?` +
      `applyArgFrames_stackRelK`) and `VCon` (uses `constToTagAndFields` +
      length-equality alignment + `listRel_refl_vcon` for the constant's
      auto-generated fields).

  **Soundness theorem signature** (the headline):
  ```lean
  theorem soundness {t₁ t₂ : Term} (h_open : OpenEq 0 t₁ t₂) :
      ∀ (C : Context),
        ObsEq (.compute [] .nil (fill C t₁)) (.compute [] .nil (fill C t₂))
  ```

  **Build status:**
  ```
  ✔ [50/50] Built Moist.VerifiedNewNew.Contextual.Soundness
  Build completed successfully (50 jobs).
  ```

  No sorries anywhere on the dependency chain (Subst → Equivalence →
  Rename, CEK.Machine, CEK.Readback, CEK.DecidableEq, Plutus.Term).

  **What this unblocks:** Phase 6 — drop closedness preconditions from
  `CtxEq` and the congruence theorems in `Contextual.lean` and `MIR.lean`.
  The `soundness` theorem from `Soundness.lean` is the bridge.



- **2026-04-12 — Phases 1+2 done.** `Subst.lean` compiles cleanly: all five
  inductive families, reflexivity (mutual on terms/lists/values/envs/frames/
  stacks/states), symmetry (within the same `t₁`/`t₂` parameters), and
  `fill_termSubst` / `initial_stateSubst`. Lean 4 panics on docstrings inside
  `where` clauses — workaround was to use a regular comment for the splice
  helper.

  Lines: ~322. Build green: `Moist.VerifiedNewNew.Contextual.Subst (376ms)`.

- **2026-04-12 — Phase 3 lockstep lemma done modulo Phase 4.** All structural
  cases of `stateSubst_step_or_obsEq` are proven:
    * `error`, `halt` (trivial)
    * Compute side: `varRefl` (via `envSubst_lookup`), `constRefl`,
      `builtinRefl`, `errorRefl`, `lam`, `apply`, `force`, `delay`, `constr`
      (both empty and head-cons), `case`.
    * Ret side: `nil` stack, `force` frame (`vCon`/`vLam`/`vConstr`/`vDelay`/
      `vBuiltin`), `arg` frame, `funV` frame (all 5 value variants),
      `applyArg` frame (all 5 value variants), `constrField` frame (both
      `nil` and `cons` of remaining list, with `valueListSubst_reverse` for
      the `nil` case), `caseScrutinee` frame (`vConstr` via
      `termListSubst_getElem?` + `valueListSubst_map_applyArg` +
      `stackSubst_append`, `vCon` via length-equality alignment + the same
      lookup helper, `vLam`/`vDelay`/`vBuiltin` errors).

  **Helpers added (~100 lines):** `envSubst_lookup`, `envSubst_extend`,
  `stackSubst_cons`, `valueListSubst_append`, `valueListSubst_reverse`,
  `stackSubst_append`, `valueListSubst_map_applyArg`, `termListSubst_getElem?`,
  `termListSubst_length_eq`.

  **Builtin cases:** `force`/`vBuiltin`, `funV`/`vBuiltin`, `applyArg`/`vBuiltin`
  all dispatch via `evalBuiltin_subst` (currently `sorry`d, deferred to Phase 4
  along with the two `swap`/`swapInv` cases on the compute side).

  **Sorry inventory after Phase 3:**
    1. `evalBuiltin_subst` (one sorry, factored as a named helper).
    2. Compute `swap` case (right disjunct via Phase 4 bridge).
    3. Compute `swapInv` case (right disjunct via Phase 4 bridge).

  Lines: ~755. Build green: `Moist.VerifiedNewNew.Contextual.Subst (653ms)`.

  **Stopping point.** Phase 4 is the design bottleneck and was estimated at
  4–5 days. Resuming Phase 4 should start by reading section 3.4 of this plan
  and the existing `compat_*_k` proofs in `Equivalence.lean` for inspiration
  on the mutual recursion + step-index strong induction structure.

- **2026-04-12 — Phase 4 architectural breakthrough; B1 RESOLVED via the
  `term_obsEq` reformulation.**

  After analysing B1, I refactored `Soundness.lean` to bypass the
  `Subst → Eq*` bridges entirely. The new approach defines a single big
  theorem `term_obsEq` that takes:

    * a *semantic* env relation `AtLeastEnvEqK k ρ_l ρ_r` (= `EnvEqK k ∞`)
    * a *semantic* stack relation `StackRelK ValueEqK k π_l π_r`
    * a *syntactic* term relation `TermSubst t₁ t₂ tm_l tm_r`

  and concludes `ObsEqK k (compute π_l ρ_l tm_l) (compute π_r ρ_r tm_r)`.

  Crucially, the *initial state* `compute [] .nil (fill C t)` trivially
  satisfies all three premises (empty stack/env are trivially related, and
  `fill_termSubst` provides `TermSubst`). So `term_obsEq` directly closes the
  open-context soundness theorem **without any `Subst → Eq*` bridge** — the
  mixed-state problem from B1 simply never arises because we never construct
  `ValueSubst` for runtime values.

  Proof structure: strong induction on `k` (encoded as `∀ i ≤ k, …`), with
  per-`TermSubst`-constructor case analysis. Cases proven so far:

    * `swap`/`swapInv`: instantiate `OpenEq 0 t₁ t₂` directly.
    * `varRefl`: lookup via `AtLeastEnvEqK`, dispatch via `hπ` at level `m`.
    * `constRefl`/`builtinRefl`/`errorRefl`: trivial structural cases.
    * `lam`: **The critical case.** Steps to `ret` with a `VLam` closure;
      uses `hπ` to ask for `ValueEqK m` of the closure; constructs the
      application property of `VLam` inline by recursively calling `ih` at
      smaller levels with the EXTENDED env `(ρ_l.extend arg_l)` (which is
      `AtLeastEnvEqK i` because the original env was via `mono` and the new
      arg is `ValueEqK i` from the application property's args).
    * `delay`: analogous to `lam` for `VDelay`.
    * `force`: pushes `.force` frame onto stack; constructs the new
      `StackRelK` inline by dispatching on `vf` via `ValueEqK` (with
      `VDelay` using its own application property).
    * `apply`: pushes `.arg` frame; constructs new `StackRelK` inline,
      which itself triggers a nested `.funV` frame `StackRelK` construction
      using `ValueEqK` of `VLam`/`VBuiltin`.

  The two `VBuiltin` sub-cases inside `force` and `apply`, plus the
  non-empty `constr` and `case` cases, remain `sorry`'d. They follow the
  same pattern (mechanical extensions of `force`/`apply`).

  **Soundness theorem now compiles.** The `soundness` theorem at the bottom
  of `Soundness.lean` is fully wired up: it takes `OpenEq 0 t₁ t₂` and
  produces `ObsEq` for the empty-state runs of `fill C t₁` / `fill C t₂`,
  using `term_obsEq` directly. No bridges required.

  **Sorry inventory in `Soundness.lean` after this turn:**
    1. Inside `term_obsEq` `force` case, `VBuiltin` sub-case (line ~330).
    2. Inside `term_obsEq` `apply` case, `VBuiltin` sub-case (line ~292).
    3. `term_obsEq` `constr` non-empty case (line ~368).
    4. `term_obsEq` `case` case (line ~373).

  All four are mechanical extensions of the working `force`/`apply`
  patterns. None of them are architectural blockers.

  Build green: `Moist.VerifiedNewNew.Contextual.Soundness (546ms)`.
  Lines: ~430.

  **What this unblocks (Phase 6):** The closedness preconditions on the
  congruence theorems in `Contextual.lean` and `MIR.lean` can now be
  dropped. `CtxEq` can be redefined to quantify over *all* contexts, not
  just closed ones, with the open-context soundness theorem from this file
  filling the bridge to `OpenEq 0`.

- **2026-04-12 — Phase 4 partial: lam/apply done, leaving B1.**
  (DEPRECATED — superseded by the breakthrough above.) See file history.
  Original Phase 4 attempt with the four-bridges `all_bridges` theorem
  hit B1 in the `succ m` case. The refactor to `term_obsEq` rendered this
  obsolete.

- **2026-04-12 — Phase 4 base case done; inductive step blocked on B1.**
  (DEPRECATED — superseded by the breakthrough above.)
  Created `Moist/VerifiedNewNew/Contextual/Soundness.lean` (~140 lines).
  Bundled the four bridges as a single `all_bridges` theorem for unified
  induction on `k`. The `k = 0` base case closes cleanly for all four:

    * `subst_obsEq @ 0`: dispatch on `StateSubst` constructor; `error`/
      `compute`/`ret` are non-halt (`obsEqK_zero_nonhalt`); `halt` constructs
      explicit witnesses for both `Iff` directions (n forced to 0 by `n ≤ 0`).
    * `subst_stackRelK @ 0`: `j ≤ 0` forces `j = 0`; ObsEqK 0 of `.ret` non-
      halt states is vacuous.
    * `subst_valueEqK @ 0`: `ValueEqK 0` is `True` by definition.
    * `subst_envEqK @ 0`: dispatch on `envSubst_lookup`; `none/none` is
      `trivial`; `some/some` reduces to `ValueEqK 0` which is `True`.

  Four projection theorems (`subst_obsEq`, `subst_stackRelK`, `subst_valueEqK`,
  `subst_envEqK`) are wired up and will inherit the proof once the inductive
  step is closed.

  **`succ m` case** is `sorry` with an extensive comment documenting the
  blocker B1 (see section 8). The blocker is the architectural bottleneck
  flagged at the planning stage. Resolving it requires introducing a "weak/
  mixed" family of relations (`WkFrame`/`WkStack`/`WkState`) that allow
  the top stack frame to carry `ValueEqK`-related values rather than
  `ValueSubst`-related ones, then re-proving the Phase 3 step lemma against
  the new relation.

  Build green: `Moist.VerifiedNewNew.Contextual.Soundness (227ms)`.

  **Sorry inventory across the whole project after this turn:**
    1. `Subst.lean:452` — `evalBuiltin_subst` (Phase 4 helper)
    2. `Subst.lean:480` — `stateSubst_step_or_obsEq` (2 inner sorries on
       `swap`/`swapInv`, both Phase 4 dependencies)
    3. `Soundness.lean:46` — `all_bridges` `succ m` case (B1 — see §8)

  Stopping per "stop when you hit a blocker". Resuming requires the B1
  refactor.
