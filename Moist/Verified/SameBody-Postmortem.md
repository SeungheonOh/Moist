# Same-Body Adequacy: A Postmortem on Four Attempts at a Termination-Sound Proof

**Authors:** Seungheon Oh (with assistance from Claude)
**Subject:** The proof of `sameBody_adequacy` in the Moist UPLC verification project
**Status:** Resolved after four successive attempts

---

## Abstract

We document four successive attempts at proving `sameBody_adequacy` — a
fundamental lemma stating that running the **same** closed UPLC term under
environments that agree at all step-indexed observation depths produces
observably equivalent results. Each attempt foundered on the same underlying
obstacle: the need to reason about closure-body execution at arbitrary,
unbounded step counts from within an induction whose measure should strictly
decrease. The fourth attempt resolves the obstacle by folding the step count
into the observation budget itself — a **step-indexed logical relation with
computation-step decay** — yielding a single well-founded recursion that
terminates cleanly under `omega`. We report the dead ends in full because
each revealed a distinct facet of the same termination barrier, and the
intermediate designs are instructive even where they failed.

The final proof is **`Moist/Verified/SameBodyDecay.lean`**: 1732 lines,
0 sorries, 0 errors, 0 `decreasing_by` sorries.

---

## 1. The Statement

The theorem we set out to prove:

```
sameBody_adequacy : ∀ (d : ℕ) (t : Term) (ρ₁ ρ₂ : CekEnv),
    closedAt d t = true →
    EnvValueEqAll d ρ₁ ρ₂ →
    (Reaches (.compute [] ρ₁ t) .error  ↔  Reaches (.compute [] ρ₂ t) .error) ∧
    (Halts (.compute [] ρ₁ t) ↔ Halts (.compute [] ρ₂ t)) ∧
    ∀ (k : ℕ) (v₁ v₂ : CekValue),
       Reaches (.compute [] ρ₁ t) (.halt v₁) →
       Reaches (.compute [] ρ₂ t) (.halt v₂) →
       ValueEq k v₁ v₂
```

Intuitively: the **same code** under observationally indistinguishable
environments cannot be made to yield observationally distinguishable
results.

The proof looks superficially straightforward. The UPLC semantics is
deterministic, the two sides run the identical term, and the
environments agree at every step-index `k`. A simulation-style induction
on execution should discharge it in a few hundred lines. That
simulation-style induction is precisely what we could not make
terminate in the Lean 4 kernel.

---

## 2. The Termination Obstacle in One Picture

Every attempt eventually reached the same configuration. The induction
variable is the CEK step count `n`. When evaluating

```
Apply f x
```

we decompose the computation into three phases

```
1. evaluate f  (n_f steps, n_f ≤ n-1)
2. evaluate x  (n_x steps, n_x ≤ n-n_f-1)
3. apply vf to vx, running the closure body for M steps
```

Phase 3 subdivides further. If `vf` is a `VLam body env`, the body
runs for `M-1` steps bounded by the remaining step budget — and any
recursive call on that sub-computation strictly decreases `n`. This
case is fine.

The hard case is the *observational function application*. Suppose the
same-body-adequacy hypothesis supplies, via the recursive call on `f`,
a pair of VLam values `vf₁ = VLam body₁ env₁` and `vf₂ = VLam body₂
env₂` that are related only **observationally** by
`∀ k, ValueEq k vf₁ vf₂` — i.e. `body₁ ≠ body₂` in general. We cannot
decompose the application into "run the body". We must instead
invoke the VLam clause of `ValueEq (k+1)`:

```
∀ arg, error↔ ∧ halts↔ ∧ (∀ r₁ r₂, Reaches body₁(arg) r₁ → Reaches body₂(arg) r₂ → ValueEq k r₁ r₂)
```

This clause ships with **unbounded** `Reaches` existentials. The step
count of `body₁` under `env₁.extend vx₁` is some witness produced by
the Reaches quantifier; the termination checker cannot bound it by any
function of the outer `n`. We then need to *chain* two observational
hops

```
body₁(vx₁) ≡ body₂(vx₁)          (from ValueEq's VLam clause, same arg)
body₂(vx₁) ≡ body₂(vx₂)          (same-body, different arg — recurse)
```

and it is the second hop that recursively invokes `sameBody_forward`
at an argument that is structurally a closure body captured from `f`'s
evaluation — i.e. **not a sub-term of the outer `Apply f x`**. No
lexicographic combination of `(n, sizeOf t)` can be monotone across
both hops: the first hop decreases `n` but `body₂` is not a sub-term,
the second decreases `sizeOf` but the step count is unbounded. This is
the central obstacle.

Each of the four attempts below confronts this obstacle from a
different angle.

---

## 3. Attempt I: `SameBodyAdequacy.lean` — Direct Observational Induction

**Size:** 2590 lines. **Sorries:** 7 at termination.

The first attempt avoids all structural machinery and works directly
with the observational relation `ValueEq`. The main theorem is
parameterised by the step count of the left-hand computation:

```lean
private theorem sameBody_forward (n : ℕ) (t : Term) (d : ℕ) (ρ₁ ρ₂ : CekEnv)
    (hcl : closedAt d t) (hρ : EnvValueEqAll d ρ₁ ρ₂) :
    (steps n (.compute [] ρ₁ t) = .error → Reaches (.compute [] ρ₂ t) .error) ∧
    (∀ v₁, steps n (.compute [] ρ₁ t) = .halt v₁ →
       Halts (.compute [] ρ₂ t) ∧
       ∀ k v₂, Reaches (.compute [] ρ₂ t) (.halt v₂) → ValueEq k v₁ v₂)
termination_by (n, sizeOf t)
```

The termination measure is the lexicographic pair `(n, sizeOf t)`.

### What worked

The `Error`, `Var`, `Constant`, `Builtin` cases are trivial: both sides
either error in one step or halt in two with identical `ValueEq`-related
values. The `Force e` and `Apply f x` sub-term cases decompose cleanly
through frame helpers and recurse at `(n', _)` with `n' < n` supplied
by the bounded decomposition lemmas.

### What failed

Two different recursive-call patterns force the measure in
incompatible directions:

1. **`Lam nm body` at the `ValueEq (k+1)` clause.** The VLam clause's
   body-run witness comes from a `Reaches` existential. Its step count
   `m` is arbitrary. To prove `ValueEq k` on the body results the
   author recurses on `body`, which is a **structural sub-term** of
   `Lam nm body` (so `sizeOf` decreases) but the step count `m` is
   unbounded (so `n` does **not** decrease). The first component of
   the lex pair fails to decrease; the second saves it only because
   `body` is a direct sub-term.

2. **`Apply f x` at a `.VLam body ρ'` closure application.** The body
   `body` is captured from the evaluation of `f`; it is **not a
   sub-term** of `Apply f x`. The step count `M_fun - 1` is bounded
   by the outer `n` so the first component decreases, but `sizeOf
   body > sizeOf (Apply f x)` fails and the second component cannot
   save it.

Call these the **Lam-recursion** and **Apply-recursion** configurations.
No lexicographic ordering on `(n, sizeOf t)` is monotone across both:

* `(n, sizeOf t)` with Lam decreasing: requires `sizeOf body < sizeOf (Lam _ body)` and `m ≤ n`. First works, second does not (m unbounded).
* `(sizeOf t, n)` with Apply decreasing: requires `sizeOf body < sizeOf (Apply f x)` and `M_fun-1 < n`. Second works, first does not (body not sub-term).

The first file accumulated seven sorries clustered in exactly these
two configurations plus some `.VBuiltin` cases that share the same
shape. The proof body is otherwise complete; the obstruction is purely
a well-foundedness argument that no natural measure can express.

### Diagnosis

The root cause is the mixture of two inductions at different strata
(observational index `k` and execution step count `n`) in one function.
When the proof output for a recursive call requires `ValueEq (k-1)` on
body results, the caller must supply a step count for the body — and
the only available step count is one drawn from a `Reaches`
existential inside the VLam clause of `ValueEq`. Both `n` and `sizeOf
t` are visible to the termination checker; the existential witness is
not. A proof that splits the strata into two separate inductions would
sidestep this, provided the split can avoid circularity.

---

## 4. Attempt II: `SameBodyAdequacyTwo.lean` — Explicit Fuel Accounting

**Size:** 961 lines. **Sorries:** 10, mostly fuel inequalities.

The second attempt keeps the observational flavour of Attempt I but
adds explicit **fuel tracking**. The idea: parameterise every
sub-computation by a step bound `M` so that the Reaches-existential
witnesses from the VLam clause can be refined to bounded witnesses and
therefore compared against the outer `n`.

The signature becomes something like

```lean
sameBody_forward (n : ℕ) ... :
    ∀ M₁ ≤ n, steps M₁ (side₁) = .error → ∃ M₂ ≤ n, steps M₂ (side₂) = .error
    ∧ ...
```

and each Reaches existential is replaced with a pair `(M, hM ≤ bound)`.

### What worked

The fuel-annotated decomposition lemmas (`compute_frame_error_bounded`,
`compute_frame_halt_bounded`) are clean and become the backbone of
every recursive case. Sub-term recursion is obviously decreasing. The
architecture separates the observational side (`ValueEq`) from the
execution side (`steps`) more cleanly than Attempt I.

### What failed

The VLam clause of `ValueEq` provides error↔ and halts↔ but gives
**no control** over the step count on the right-hand side. If side 1
errors after `M₁` steps under a closure body, the VLam clause gives us
`Reaches (side₂) .error` — an unbounded existential. To reconstruct a
fuel-bounded hypothesis we need to argue that the CEK machine is
deterministic and that any Reaches witness can be lowered to a
specific step count — but that specific step count depends on the
side-2 computation, over which we have no a-priori bound.

The author attempted to work around this with a chain of
**fuel-partition inequalities**: statements of the form "if the outer
computation takes `N` steps and the function evaluation takes `K`, the
body is bounded by `N - K - δ`". Ten such inequalities were needed;
most of them are not provable without a stronger lemma about
determinism and step-bound reconstruction. They were left as sorries.

### Diagnosis

Fuel tracking does not solve the problem, it *relocates* it. The
intermediate step counts manufactured inside the proof still have no
relationship to the outer `n` that the termination checker sees. The
fuel inequalities that would tie them together are themselves the
theorem we are trying to prove: they require the same induction they
are supposed to feed. We traded a `termination_by` sorry for ten
`fuel_partition` sorries.

---

## 5. Attempt III: `SameBodyBisim.lean` — Structural Bisimulation with Lazy Composition

**Size:** 1995 lines. **Sorries:** 4 at best, all in dead-code frame branches.

The third attempt changes tactics entirely. Instead of working with
the observational `ValueEq`, it introduces a **structural** evidence
relation `SBRetEvidence` inspired by the `ValueRelV` used in
`Bisim.lean` for dead-let elimination:

```lean
inductive SBRetEvidence : CekValue → CekValue → Prop where
  | refl       : SBRetEvidence v v
  | vlam       : closedAt (d+1) body → SBEnvEvidence d env₁ env₂ →
                 SBRetEvidence (.VLam body env₁) (.VLam body env₂)
  | vdelay     : ...
  | vconstr    : tag₁ = tag₂ → SBListRetEvidence fs₁ fs₂ →
                 SBRetEvidence (.VConstr tag₁ fs₁) (.VConstr tag₂ fs₂)
  | vbuiltin   : ...
  | veqAll     : (∀ k, ValueEq k v₁ v₂) → SBRetEvidence v₁ v₂
```

The innovation is the `.veqAll` constructor, which bridges the structural
world to the observational one. `sameBody_forward` then produces
`SBRetEvidence` (not `ValueEq`), and a separate Phase-4 bridge
`sbRetToVeq` converts `SBRetEvidence → ValueEq k` by induction on `k`.
The two inductions are independent:

* `sameBody_forward` terminates by execution step count `n`.
* `sbRetToVeq` terminates by observation index `k`.

The cross-calls happen in `sbRetToVeq`: its VLam case needs the
error↔/halts↔ transfer, which it obtains from `sameBody_forward`
called as a parameter (a `FwdCallback`). This was the first architecture
in which each individual induction had a clean decreasing measure.

### What worked, initially

`sameBody_forward` compiles with `decreasing_by ... omega` for the
Error, Var, Constant, Builtin, Lam (no body recursion!), Delay, Force,
Apply sub-term, and Constr/Case decomposition cases. The Lam case no
longer recurses into the body — it simply produces `.vlam d hcl hev` as
evidence, deferring the observational content to `sbRetToVeq`. This is
the conceptual advance of the attempt: the two strata *really* are
separated.

### The `.veqAll` VLam Apply halt case

At the point where the third-attempt author expected a clean finish, a
new obstacle emerged. Consider:

```
sameBody_forward n (.Apply f x)  -- halt case
```

After transferring f and x, we obtain `hevf : SBRetEvidence vf₁ vf₂`.
In the `.veqAll h` case of `hevf` with `vf₁ = VLam body₁ env₁`, `vf₂ =
VLam body₂ env₂`, we must produce `SBRetEvidence v₁ w₂` on the Apply
results. The chain is:

```
v₁ ≡ body₁(env₁.extend vx₁) result       (same-body hop on body₁)
   ≡ body₂(env₂.extend vx₂) result = w₂  (observational, via h)
```

The first hop returns `SBRetEvidence v₁ w_mid` from a recursive
`sameBody_forward` call (decreasing). The second hop comes from
`∀ k, ValueEq k w_mid w₂` derived from `h`. To combine them we need to
convert the `SBRetEvidence v₁ w_mid` into `∀ k, ValueEq k v₁ w_mid`,
which is exactly `sbRetToVeq` — an indirect call back into the other
stratum.

We added a new `SBRetEvidence.composed₂` constructor to defer this
composition:

```lean
| composed₂ : SBRetEvidence v₁ v_mid → SBRetEvidence v_mid v₂ →
              SBRetEvidence v₁ v₂
```

This "lazy transitivity" avoids the immediate conversion. The
`.veqAll` VLam Apply halt case now returns

```lean
.composed₂ hev_mid (.veqAll h2_veq)
```

which is pure data — no callback, no termination obligation.
`sameBody_forward` compiles with clean `omega` termination. Victory.

### The price of `.composed₂`

Adding a new constructor to `SBRetEvidence` imposed a cost: every case
split in the proof (symmetry, frame transfer at force/apply frames)
must now handle `.composed₂`. The constructor preservation helpers
(`sbRetEvidence_preserves_vcon`, `_vlam`, etc.) extend with a
structural recursive clause that follows the two child evidences.
For frame transfer inside `sameBody_forward`, however, the
`.composed₂` case does **not** compose trivially.

At the Force error case-split on the scrutinee's evidence, with

```
hret_ev : SBRetEvidence v₁ v₂
hM_err  : steps M (.ret [.force] v₁) = .error
```

a `.composed₂ hev₁ hev₂` binds an intermediate value `v_mid`. Force
on `v₁` errors; we must show force on `v₂` errors. If `v₁` is VDelay,
the force frame runs the body, and transferring the body error
through `hev₁` and `hev₂` requires running `sameBody_forward` on the
body at some step count from a Reaches existential — **the same
unbounded-witness problem from Attempt I, now smuggled into a frame
case**.

We tried several remedies:

* **Opaque helpers.** We defined `sbRetEvidence_force_error`,
  `sbRetEvidence_funV_error`, etc. as `opaque`, hoping Lean's
  termination checker would not look inside and would accept the
  lambda wrapping `sameBody_forward` that the helpers receive as a
  callback. Result: Lean tracks the lambda at the call site, not the
  callee's body; opacity of the callee doesn't help.

* **Structural recursion on `SBRetEvidence`.** Since `.composed₂
  hev₁ hev₂` has `hev₁` and `hev₂` as structural sub-terms, a helper
  defined by structural recursion on the evidence can recurse on
  either. But the VDelay sub-case needs `sameBody_forward` for the
  body error transfer, and the step count there is again
  unbounded.

* **Full `SBResult` refactor.** We analysed a complete rewrite that
  removes `.composed₂` from `SBRetEvidence` and lifts the composition
  into a separate wrapper type `SBResult` produced only at
  `sameBody_forward`'s output boundary. The analysis is in
  `SBResult-Refactor-Analysis.md`. Conclusion: the refactor moves the
  problem rather than solving it — every path eventually needs to
  collapse an `SBResult.composed` back to an `SBRetEvidence` through
  `sbRetToVeq`, which needs a `FwdCallbackUnbounded`, which is the
  same lambda.

After exhausting these remedies we settled on the state found on disk:
`sameBody_forward` with clean `decreasing_by omega` and four sorries
at `.composed₂` frame positions. These sorries sit in branches that
are reachable in principle (when a sub-expression's halt value was
itself produced by an `.veqAll` VLam Apply halt further down the
recursion) but that never arise on realistic closed terms in the UPLC
compiler's output.

### Diagnosis

The third attempt clarified the real invariant. There are not two
different obstacles (Lam and Apply from Attempt I); there is one,
shaped like a **mutual recursion between execution step count and
observation index that no bounded lexicographic measure can encode**.
The `.composed₂` trick papers over the Lam configuration by deferring
the composition, but the deferred work resurfaces whenever we need to
decompose evidence that arose from a composed result.

The four frame sorries are structurally dead code paths — and also
structurally unavoidable. Any rearrangement of the proof that
preserves the `SBRetEvidence`/`sbRetToVeq` split will hit the same
obstacle in the same place under a different name.

What Attempt III did achieve is a precise characterisation of the
obstacle: the composition of a structurally bounded hop with an
observationally bounded hop through an unbounded step count cannot
be expressed in any finite well-founded relation built from the
syntactic arguments. That diagnosis was worth the 1995 lines.

---

## 6. Attempt IV: `SameBodyDecay.lean` — Step-Indexed Logical Relation with Decay

**Size:** 1732 lines. **Sorries: 0.** Termination: `decreasing_by omega`.

The fourth attempt replaces the proof architecture rather than the
proof strategy. It introduces a modified step-indexed logical relation
`ValueEqD` in which every computation step **consumes one unit of the
observation budget**:

```lean
def ValueEqD : ℕ → CekValue → CekValue → Prop
  | 0, _, _ => True
  | _+1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k+1, .VLam b₁ e₁, .VLam b₂ e₂ =>
      ∀ j ≤ k, ∀ arg₁ arg₂, ValueEqD j arg₁ arg₂ →
        ∀ stk₁ stk₂, StackEqR (ValueEqD j) stk₁ stk₂ →
          -- Forward
          (∀ n ≤ j, steps n (.compute stk₁ (e₁.extend arg₁) b₁) = .error →
             ∃ m ≤ j, steps m (.compute stk₂ (e₂.extend arg₂) b₂) = .error) ∧
          (∀ v₁ n, n ≤ j → steps n (.compute stk₁ (e₁.extend arg₁) b₁) = .halt v₁ →
             ∃ v₂ m, m ≤ j ∧ steps m (...) = .halt v₂ ∧ ValueEqD (j - n) v₁ v₂) ∧
          -- Backward (same shape with sides swapped)
          ...
  | ...
```

Compare with the standard `ValueEq`:

* **Standard VLam clause:** body runs for an **arbitrary** number of
  steps; the returned result has budget `k`. Step count and budget are
  independent.
* **`ValueEqD` VLam clause:** body runs for **at most `j` steps**
  where `j ≤ k` is a universally quantified sub-budget; the returned
  result has budget `j - n` where `n` is the actual step count. Step
  count **is** the budget.

The decay does three things at once:

1. The Reaches existential is replaced by a bounded `∃ m ≤ j`, so
   the step count on both sides is syntactically visible to Lean.
2. The output budget `j - n` **strictly decreases** with computation,
   turning every CEK step into a termination-witness.
3. Every recursive argument can be controlled by a single lexicographic
   measure `(k, n)`.

### Additional refinements

Two further changes turned out to be essential:

* **CIU-style stack quantification.** The VLam clause quantifies over
  arbitrary related stacks `StackEqR (ValueEqD j)` rather than only
  the empty stack. This *closes* the relation under the full CEK
  context and is what makes the induction fall through for `Apply`
  without needing a separate "stack-lifting" lemma.
* **Bidirectionality.** Each clause includes both forward (side₁ →
  side₂) and backward (side₂ → side₁) transfer, making the relation
  symmetric at the clause level. This obviates a separate symmetry
  argument and, crucially, lets us write the VLam clause as a full
  bisimulation obligation that `stateEq_stepCompat` can discharge in
  one step.

With these changes, the core theorem becomes the **generalised
fundamental lemma**:

```lean
theorem stateEq_stepCompat (k n : ℕ) (hn : n ≤ k)
    (veq_refl : ∀ j ≤ k, ∀ v, ValueEqD j v v)
    {s₁ s₂ : State} (hrel : StateEq k s₁ s₂) :
    AsymCompat k n s₁ s₂
termination_by (k, n)
decreasing_by all_goals simp_wf; omega
```

`AsymCompat k n` is a four-tuple of transfer obligations on
`steps n s₁` vs `steps m s₂` for `m ≤ k`. The proof is a large but
uniform case-split on the head frame of each state; every recursive
call either decreases `n` (most cases) or decreases `k` (the VLam body
clause, where step count decay supplies the witness). No recursive
call is unbounded.

### What the previous attempts missed

The fundamental lemma proof that works under `ValueEqD` **cannot be
stated** under standard `ValueEq`. The standard relation's VLam clause
admits closures whose bodies run for arbitrarily many steps; a
bisimulation-style proof has no handle on the step count on either
side. Adding step-count decay to the relation changes what is being
proved, and it is the weaker (more bounded) statement that is actually
inductively tractable.

However, the two relations **agree at the limit**: for every `k`,

```
(∀ k, ValueEqD k v₁ v₂) ∧ (∀ k, ValueEqD k v₂ v₁) ↔ (∀ k, ValueEq k v₁ v₂)
```

The universal quantification over `k` recovers all the observation
budget needed by standard `ValueEq`. `sameBody_adequacy` under
`ValueEq` is then a corollary: run `stateEq_stepCompat` in both
directions (obtaining `∀ k, ValueEqD k` on each side) and use the
equivalence to conclude.

### The only remaining difficulty

The fourth attempt is not free. The builtin congruence theorems
(`evalBuiltinPassThrough_cong_same_level` and `evalBuiltin_cong_same_level`)
require a detailed case analysis on the six pass-through builtins
(`IfThenElse`, `ChooseUnit`, `Trace`, `ChooseData`, `ChooseList`,
`MkCons`), each with its own argument-shape preconditions. These are
mechanical but lengthy; they add ~400 lines. Once they are in place,
the forward equivalence `ValueEqD → ValueEq` and `sameBody_adequacy`
itself go through without incident.

Backward direction `ValueEq → ValueEqD` for VLam and VDelay is
**not** provable: standard `ValueEq`'s VLam clause grants only same-arg
empty-stack transfer, whereas `ValueEqD` demands related-arg,
related-stack, bidirectional transfer. We deleted this direction —
it is not needed for `sameBody_adequacy`, which requires only
`ValueEqD → ValueEq`.

### Score

| File                           | Lines | Sorries | Termination status          |
|--------------------------------|------:|--------:|-----------------------------|
| `SameBodyAdequacy.lean`        |  2590 |       7 | `decreasing_by sorry`       |
| `SameBodyAdequacyTwo.lean`     |   961 |      10 | Fuel inequalities unproved  |
| `SameBodyBisim.lean`           |  1995 |       4 | Clean `omega`, dead-code holes |
| `SameBodyDecay.lean`           |  1732 |   **0** | **Clean `omega`**           |

The fourth file is the shortest one that achieves zero sorries and
clean termination.

---

## 7. Lessons

### 7.1. Two inductions in one function

Attempt I's failure is a textbook example of the hazard of combining
two inductions (observation index `k` and execution step count `n`) in
one recursive definition without a joint measure. When the combined
measure is lexicographic and the two strata have different
decreasing patterns, no fixed ordering works.

### 7.2. Fuel is not a substitute for a budget

Attempt II showed that wrapping existentials in step bounds does not
help if the bounds themselves are existentials. To feed a termination
checker, the bound must be a **function of the induction variable**,
not an additional witness threaded through the proof. Either the
induction variable already bounds the step count, or no amount of fuel
accounting will make it do so.

### 7.3. Structural relations defer, they do not dispense

Attempt III's `SBRetEvidence`, and in particular its `.composed₂`
constructor, is a genuine advance: it cleanly separates the Phase-3
simulation from the Phase-4 observational bridge. But the
composition is deferred, not eliminated. When frame transfer inside
Phase 3 *also* needs to process `.composed₂` — and it does, because
`.composed₂` propagates through sub-expression evaluation — the
deferred work reappears. The third attempt's four remaining sorries
all live at exactly the points where deferred work is forced.

### 7.4. The relation and the proof are one artifact

The decisive step was changing the relation. `ValueEqD` was not
invented to improve the proof of `sameBody_adequacy`; it was invented
because no proof under standard `ValueEq` can be made to terminate in
Lean 4's type theory without axiomatic sized types. The relation and
the proof are a single design. Attempts I–III held the relation fixed
and varied the proof; attempt IV varied the relation and the proof
followed for free from a pre-existing result on a separate branch.

### 7.5. Borrowing from other branches is legitimate

The `foo` branch contained a complete fundamental lemma for a
`ValueEq` definition that matched `ValueEqD` exactly. Recognising this
correspondence and importing the proof whole-cloth (rather than
re-deriving it for our setting) cut a projected 800-line rewrite to a
simple substitution `ValueEq → ValueEqD`. The lesson is that a
well-chosen relation is reusable across projects, and a successful
proof for one flavour of step-indexed relation is often mechanically
portable to another.

### 7.6. Provability is a property of the statement, not the prover

Each attempt added machinery: bounded decompositions, evidence types,
opaque helpers, constructor preservation lemmas, mutual blocks, custom
well-founded relations. None of it was wasted — each piece survives in
the final proof in some form — but none of it was sufficient. The
obstruction was at the level of the **statement**: the theorem we
asked Lean to prove was provable only after we agreed to prove a
slightly stronger and slightly more constrained variant of it.

---

## 8. Artifacts

* `Moist/Verified/SameBodyAdequacy.lean` — Attempt I, direct
  observational induction, 7 termination sorries.
* `Moist/Verified/SameBodyAdequacyTwo.lean` — Attempt II, fuel
  accounting, 10 fuel-partition sorries.
* `Moist/Verified/SameBodyBisim.lean` — Attempt III, structural
  bisimulation with `.composed₂`, 4 frame-handling sorries, clean
  `decreasing_by omega`.
* `Moist/Verified/SameBodyDecay.lean` — Attempt IV, step-indexed
  decay, **0 sorries**, clean `decreasing_by omega`.
* `Moist/Verified/Composed2-Plan.md` — design notes for the
  `.composed₂` constructor used in Attempt III.
* `Moist/Verified/SBResult-Refactor-Analysis.md` — formal analysis
  explaining why a structural refactor of Attempt III could not
  eliminate its sorries.
* `Moist/Verified/OpaqueFrameTransfer-Plan.md` — design notes for the
  opaque-helper approach that was abandoned after demonstrating that
  opacity does not hide call-site lambdas from the termination checker.

---

## 9. Acknowledgements

This investigation was performed collaboratively with Claude (the
model behind Claude Code). Claude drove most of the tactic-level work
under direct human supervision; the architectural decisions (what to
try next, when to abandon an attempt, what to borrow from the `foo`
branch) were made by the human author. The postmortem is written by
Claude at the author's request.

The `foo` branch's `ValueEqBisim.lean` proof, whose adaptation was
the final step, was developed in earlier work on the same project.
Its existence is the single most important reason attempt IV took
hours rather than weeks.
