# Big-step vs CEK (vs small-step) under Blaster

**Date:** 2026-06-15 · **Z3:** 4.16.0 · **Lean/Blaster:** 4.24.0
**Sources:** [`PCBbigstep.lean`](./PCBbigstep.lean) (involved) · [`PCBbigstep_scale.lean`](./PCBbigstep_scale.lean) (scaling) · [`PCBbigstep_ite.lean`](./PCBbigstep_ite.lean) (control flow). Setup in [`README.md`](./README.md); CEK/small-step baselines in [`VERDICT.md`](./VERDICT.md).

## Question

Is a **big-step** (definitional-interpreter) evaluator a better Blaster substrate than the
CEK machine — and than the substitution **small-step** of [`VERDICT.md`](./VERDICT.md)?
Big-step = recursive descent straight to values: *CEK minus the defunctionalized
continuation, small-step minus the re-traversal-per-redex.*

Measured on the *same* `Term`, *same* builtins (`@[simp]` denotations from
`input-output-hk/PlutusCoreBlaster`), *same* Blaster, *same* Z3 — so the comparison
isolates the evaluation strategy. Metric is Blaster's **optimization** (symbolic-execution)
phase; in every case the generated SMT is byte-identical and Z3 solve is a flat ~0.02s.

## Verdict

**Big-step is the best substrate measured — it beats the CEK ~1.5–2.1× on *every* workload,
including the strict control flow where the small-step *lost* ~5×.**

| workload | winner | factor vs CEK |
|---|---|---|
| straight-line arithmetic | **big-step** | ~1.8–2.1× |
| involved (multi-arg, hyps, transitivity) | **big-step** | ~1.5–2.1× |
| strict control flow (`IfThenElse`) | **big-step** | ~1.5× (small-step was ~0.2×, i.e. 5× *slower*) |
| lazy control flow (`Case` on symbolic data) | neither (untested; the wall is symbolic machine-forking, independent of strategy) | — |

So unlike the small-step (whose win *flipped* to a 5× loss on control flow), big-step keeps
its edge everywhere. On `IfThenElse` it evaluates each branch exactly once and selects — it
never re-runs a fuel loop across both branches the way the small-step does.

## Evidence

All goals `✅ Valid`; SMT byte-identical across substrates; Z3 solve ~0.02s throughout.
Times are Blaster optimization seconds.

### Scaling: `λx. 0 ≤ (x*x + … n times)` (nonlinear ⇒ Z3)

| n | CEK | small-step | **big-step** | big-step vs CEK |
|--:|----:|-----------:|-------------:|----------------:|
| 1 | 0.222 | 0.110 | **0.107** | 2.07× |
| 2 | 0.223 | 0.122 | **0.108** | 2.06× |
| 4 | 0.260 | 0.154 | **0.141** | 1.84× |
| 8 | 0.274 | 0.176 | **0.154** | 1.78× |

### Involved proofs (multi-arg, nonlinear, hypotheses)

| validator (proof obligation) | CEK | small-step | **big-step** | big-step vs CEK |
|---|--:|--:|--:|--:|
| AM-GM `2xy ≤ x²+y²` | 0.255 | 0.156 | **0.126** | 2.02× |
| swap `xy<(x+dx)(y-dy) ⇒ …` (1 hyp) | 0.253 | 0.164 | **0.166** | 1.52× |
| swap composition (6 vars, 2 hyps, transitivity) | 0.282 | 0.195 | **0.170** | 1.66× |
| mono `0≤x→1≤y→x≤xy` (2 hyps) | 0.240 | — | **0.112** | 2.14× |

### Control flow (strict `IfThenElse`) — where the verdict used to flip

| validator | mechanism | CEK | small-step | **big-step** | big-step vs CEK |
|---|---|--:|--:|--:|--:|
| `0 ≤ ite(x<0, -x, x)` | strict `IfThenElse` | 0.155 | 0.757 | **0.105** | 1.48× |
| nested-ITE sign ≤ 1 | strict `IfThenElse` | 0.171 | 0.774 | **0.115** | 1.49× |

(small-step figures from [`VERDICT.md`](./VERDICT.md); there the CEK won ~5×.)

Sample SMT (AM-GM, identical for all three substrates):
```smt2
(declare-const $0 Int) (declare-const $1 Int)
(assert (not (=> (@isInt $0) (=> (@isInt $1) (not (< (+ (* $0 $0) (* $1 $1)) (* $1 (* 2 $0))))))))
```

## Why big-step wins everywhere

Blaster must symbolically unfold the evaluator until the validator's denotation falls out.
The cost is roughly *#evaluator-unfolds × per-unfold work*.

- The **CEK** reaches a value through many *administrative* transitions
  (`Eval` → push frame → `Return` → pop frame → …), each an unfold Blaster pays for.
- The **small-step** removes the frames but `seval` calls `sstep` once per redex, and each
  `sstep` re-traverses from the root to *find* the next redex — quadratic-ish on deep terms,
  and on `IfThenElse` it duplicates the remaining fuel loop into both branches (the 5× loss).
- The **big-step** descends to each subterm's value **exactly once** and combines — no frames,
  no re-traversal, and on `IfThenElse` each branch is evaluated once then one is selected.
  Fewest unfolds ⇒ fastest optimization.

This matches the design intuition: big-step is the most direct encoding of "evaluate to a
value", so Blaster's partial evaluator has the least scaffolding to chew through.

## What made big-step competitive (same three ingredients as the small-step)

1. **Tiny builtin evaluator** (`evalB2`) over the per-builtin `@[simp] …_rfl` denotations, so
   builtins rewrite to native `Int`/`Bool` ops (not a giant `evalBuiltin` match).
2. **No `reflect`/`discharge`** — values *are* `Term`s; results read off with `bresBool`.
3. **Recogniser helpers** (`lamBody?`, `spine1?`, `iteHead2?`) + explicit `termination_by n`
   (structural on fuel), so Blaster generates `beval`'s unfold theorem.

## Caveats / scope

- This `beval` is over PCB's *named* `Term` for an apples-to-apples in-repo comparison (like
  `evalB2`); it mirrors the *verified* de Bruijn `Moist.Verified.BigStep.bigEval`, which is
  proven ≡ the Moist CEK both directions but uses Moist's Blaster-hostile `evalBuiltin`/`Const`
  (`BitVec`) and so isn't run directly here.
- Both substrates need **scalar extraction** before Z3 (`resBool`/`bresBool`); the rich result
  types aren't SMT-translatable. Shared limitation.
- **Lazy `Case` on symbolic data** still forks the machine and hangs Blaster's optimizer for
  *any* evaluator (it's a symbolic-branching wall, not a strategy artifact) — not re-tested here.
- Coverage: integer builtins (Add/Sub/Mul/LessThan(Equals)), β-reduction, multi-arg validators,
  strict `IfThenElse`. Not covered: lazy `Case`, division/modulo, bytestrings/crypto.
