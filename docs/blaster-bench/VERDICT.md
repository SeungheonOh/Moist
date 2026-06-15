# Verdict: optimized small-step vs. PlutusCoreBlaster's CEK under Blaster

**Date:** 2026-06-15 · **Z3:** 4.16.0 · **Lean/Blaster:** 4.24.0
**Sources:** [`PCBcompare.lean`](./PCBcompare.lean) · setup & reproduction in [`README.md`](./README.md)

## Question

Is a substitution **small-step** evaluator a better Blaster substrate than a
purpose-built **CEK** machine for proving smart-contract properties? Compared
against the public, Blaster-optimized CEK of
[`input-output-hk/PlutusCoreBlaster`](https://github.com/input-output-hk/PlutusCoreBlaster).

## Verdict (workload-dependent)

Measured on the *same* `Term`, *same* builtins (`@[simp]` denotations), *same* Blaster,
*same* Z3 — so the comparison isolates the evaluator. The winner **depends on the
validator's shape**:

| workload | winner | factor |
|---|---|---|
| straight-line arithmetic (compute a Bool) | **small-step** | ~1.3–2× faster |
| strict control flow (`IfThenElse`) | **CEK** | ~5× faster |
| lazy control flow (`Case`/delayed branches) | **neither — both hang** | — |

So there is no blanket winner. The small-step wins when it simply does fewer
administrative reductions; the CEK wins on control flow because its `evalBuiltin` collapses
a value-`ite` in one step, whereas the small-step re-traverses and re-runs its fuel loop in
both branches. (This already *reverses* the earlier wrong-baseline "they're equivalent",
which was an artifact of Moist's Blaster-hostile `evalBuiltin`/`Const`.)

In all cases the generated SMT and z3 solve time are identical; the difference is purely
Blaster's symbolic-execution (optimization) phase.

## Evidence

All goals: byte-identical SMT for both substrates; identical z3 solve time. Only Blaster
*optimization* (symbolic-execution) time differs.

### Scaling: `λx. 0 ≤ (x*x + … n times)` (nonlinear ⇒ z3)

| n | CEK | small-step | speedup |
|--:|----:|-----------:|--------:|
| 1 | 0.214s | **0.110s** | 1.95× |
| 2 | 0.227s | **0.122s** | 1.86× |
| 4 | 0.257s | **0.154s** | 1.67× |
| 8 | 0.287s | **0.176s** | 1.63× |

### Involved proofs (multi-arg, nonlinear, hypotheses)

| validator (proof obligation) | z3? | CEK | small-step | speedup |
|---|---|--:|--:|--:|
| AM-GM `2xy ≤ x²+y²` | 0.020s | 0.218s | **0.130s** | 1.68× |
| swap strict⇒nonstrict (1 hyp) | opt-closed | 0.218s | **0.163s** | 1.34× |
| swap composition (6 vars, 2 hyps, transitivity) | 0.020s | 0.247s | **0.169s** | 1.46× |
| mono `0≤x→1≤y→x≤xy` (2 hyps) | 0.025s | 0.204s | **0.117s** | 1.74× |

### Control flow (`PCBite2_controlflow.lean`, `PCBcontrol_case.lean`)

| validator | mechanism | CEK | small-step | winner |
|---|---|--:|--:|---|
| `0 ≤ ite(x<0, -x, x)` | strict `IfThenElse` | **0.134s** | 0.757s | CEK ~5.6× |
| nested-ITE sign ≤ 1 | strict `IfThenElse` | **0.163s** | 0.774s | CEK ~4.7× |
| `0 ≤ \|x\|` via `case (x<0)` | lazy `Case` on Bool | **hang** | **hang** | neither |

**Lazy `Case`/delayed branches hang Blaster's optimizer for *both* substrates** (even at
minimal fuel/depth, optimizer-only, no z3): a branch on *symbolic* data forks the machine's
continued execution, which Blaster cannot symbolically reduce. **Strict `IfThenElse`
works** (both branches evaluated to values first, then one terminal value-`ite`), but here
the **CEK is ~5× faster**: its `evalBuiltin` collapses the value-`ite` in a single step,
whereas the small-step re-traverses and re-runs its fuel loop inside both branches of the
`ite` that flows into the outer comparison.

### Richer SMT: division / modulo (`PCBmeaningful_divmod.lean`)

These produce genuinely *different, meaningful* SMT — Blaster synthesizes floor-division
helper definitions and verifies real number-theoretic facts:

```smt2
(define-fun @Int.fdiv ((@x Int)(@y Int)) Int (ite (= 0 @y) 0 (ite (< @y 0) (div (- @x)(- @y)) (div @x @y))))
(define-fun @Int.fmod ((@x Int)(@y Int)) Int (ite (= 0 @y) @x (ite (< @y 0) (- (mod (- @x) @y)) (mod @x @y))))
(assert (not (=> (@isInt $0) (= $0 (+ (@Int.fmod $0 7) (* 7 (@Int.fdiv $0 7)))))))   ; Euclidean identity
```

| validator | SMT (CEK = small-step, byte-identical) | CEK | small-step |
|---|---|--:|--:|
| `(x/7)*7 + x%7 = x` (Euclid) | `… = (+ (fmod $0 7) (* 7 (fdiv $0 7)))` | **0.176s** | 0.768s |
| `0 ≤ x % 5` | `¬(< (fmod $0 5) 0)` | **0.136s** | 0.719s |
| `0 < d → 0 ≤ x % d` (symbolic divisor + guard) | `(< 0 $1) → ¬(< (fmod $0 $1) 0)` | **0.136s** | 0.734s |

### The robust meta-finding: SMT is substrate-independent

Across **every** validator both evaluators fully optimize — linear, nonlinear, multi-hyp,
6-variable transitivity, strict `IfThenElse`, division, modulo, and a *symbolic* divisor
with a guard — **the generated SMT is byte-identical between the CEK and the small-step.**
Blaster fully evaluates the evaluator away, leaving the validator's *denotation*, which does
not depend on how it was evaluated. So the SMT *expression* differs across **validators**
(trivial `x*x≥0` → rich Euclidean/`fdiv`/`fmod`), but never between the two **substrates**
for the same validator. The only way to make the substrates' SMT differ is to break full
optimization (an unsupported builtin → wrong answer, or under-unfolding → untranslatable
state) — a defect, not a meaningful difference. (Note: div/mod-heavy validators run slower
on the small-step here, an artifact of the `if y=0 then none` guard in `evalB2`.)

## Why the winner flips

The CEK reaches a value through many *administrative* transitions
(`Eval` → push frame → `Return` → pop frame → …) that Blaster must unfold; the small-step
takes fewer, larger redex contractions. On **straight-line** code that pure-overhead
difference makes the small-step win. But on **control flow**, a symbolic `ite` must flow
through *more* evaluation; the CEK consumes it in one `evalBuiltin` step, while the
small-step's re-traversal duplicates the remaining fuel loop across both branches — so the
CEK wins there. **z3 is never the bottleneck** (flat ~0.02s, identical both ways); the
entire difference is Blaster's symbolic-execution (optimization) phase.

## What made the small-step competitive

The naive Moist `evalF` lacked all three; adding them is what beat the CEK:

1. **Tiny builtin evaluator** (`evalB2`, only the builtins used) over the same per-builtin
   `@[simp] …_rfl : addInteger x y = Int.add x y` denotations — so Blaster rewrites
   builtins to native `Int` ops instead of unfolding a giant `evalBuiltin` match (which
   *times out* in Moist).
2. **No `reflect`/`discharge` round-trip** — builtins evaluate directly on `Const` args.
3. **Recogniser helpers** (`lamBody?`, `spine1?`) + explicit **`termination_by sizeOf`** —
   both required for Lean to generate `sstep`'s unfold theorem (deep nested patterns or a
   missing `termination_by` → Blaster error `failed to generate unfold theorem`).

## Caveats / scope

- **Both** substrates require **scalar extraction** before z3 (`resBool`/`sresBool`): the
  rich result types aren't SMT-translatable — PCB's `CekValue` hits a `Fin` error, Moist's
  `Const` a `BitVec` error. This is a shared limitation, not small-step-specific.
- Keep `unfold-depth` modest (~200–400 here); over-large depths over-unfold and blow up.
- **Symbolic lazy branching is a hard wall for the evaluator approach** (both substrates):
  any `Case`/if that branches the machine on symbolic input hangs Blaster's optimizer.
  Validators must be *straight-line to a Bool* or use *strict* `IfThenElse`. PCB's own
  `ValidatorsExamples` sidestep this entirely by modelling validators as plain Lean
  functions (Blaster handles Lean `match`/`if` natively) rather than running UPLC.
- Coverage: integer builtins (Add/Sub/Mul/LessThan(Equals)), β-reduction, multi-arg
  validators, `Force`/`Delay`, and strict `IfThenElse`. **Not covered:** lazy `Case`
  (hangs), bytestrings/crypto. The small-step here is over PCB's *named* `Term` (for a fair
  in-repo comparison), not Moist's verified de Bruijn `evalF`.
- The small-step used here is *not yet proof-backed* (it's an executable evaluator for
  benchmarking); porting these optimizations into Moist's verified `evalF` bridge is the
  natural follow-up.
