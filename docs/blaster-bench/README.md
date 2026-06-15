# Optimized small-step vs PlutusCoreBlaster's CEK (measured)

Head-to-head Blaster benchmark: an **optimized substitution small-step** evaluator
vs the purpose-built **Blaster-optimized CEK** of
[`input-output-hk/PlutusCoreBlaster`](https://github.com/input-output-hk/PlutusCoreBlaster),
run on the *same* `Term` type, *same* builtins (`@[simp] …_rfl` denotations),
*same* Blaster, *same* Z3 (4.16.0). Source: [`PCBcompare.lean`](./PCBcompare.lean).

## Result

All goals produce **byte-identical SMT** for both substrates and identical z3
solve time — the only difference is Blaster *optimization* (symbolic-execution)
time, where the small-step wins.

### Scaling sweep: `λx. 0 ≤ (x*x + … n times)` (nonlinear ⇒ z3)

| `n` | PCB CEK | optimized small-step | speedup |
|----:|--------:|---------------------:|--------:|
|   1 | 0.214s  | **0.110s**           | 1.95×   |
|   2 | 0.227s  | **0.122s**           | 1.86×   |
|   4 | 0.257s  | **0.154s**           | 1.67×   |
|   8 | 0.287s  | **0.176s**           | 1.63×   |

### Involved proofs (multi-arg, nonlinear, hypotheses)

| validator (proof obligation)                       | z3?       | PCB CEK | small-step | speedup |
|----------------------------------------------------|-----------|--------:|-----------:|--------:|
| AM-GM `2xy ≤ x²+y²` (∀ x y)                         | 0.020s    | 0.218s  | **0.130s** | 1.68×   |
| swap strict⇒nonstrict (∀, 1 hyp)                    | opt-closed| 0.218s  | **0.163s** | 1.34×   |
| swap **composition** (6 vars, 2 hyps, transitivity) | 0.020s    | 0.247s  | **0.169s** | 1.46×   |
| mono `0≤x→1≤y→x≤xy` (∀, 2 hyps)                     | 0.025s    | 0.204s  | **0.117s** | 1.74×   |

The optimized small-step is consistently **~1.3–2× faster** than the
Blaster-optimized CEK. z3 solve time (~0.02s) is identical and not the
bottleneck — symbolic execution dominates, and that is where the small-step's
lower administrative overhead pays off.

## Why the small-step wins

The CEK reaches a value through many *administrative* transitions
(`Eval` → push frame → `Return` → pop frame → …), each a `step` unfolding Blaster
must symbolically execute. The small-step takes fewer, larger transitions (locate
the redex, contract it), so Blaster unfolds less to reach the normal form.

## The optimizations that made it competitive (vs the naive Moist `evalF`)

1. **Tiny builtin evaluator** `evalB2` (only the builtins used), calling the same
   per-builtin denotations PCB exposes to Blaster via `@[simp] …_rfl = Int.add/…`
   — so Blaster rewrites builtins to native `Int` ops instead of unfolding a giant
   `evalBuiltin` match (which *times out* in Moist).
2. **No `reflect`/`discharge` round-trip** — builtins evaluate directly on `Const`
   term arguments.
3. **Recogniser helpers** (`lamBody?`, `spine1?`) instead of deep nested term
   patterns, **plus an explicit `termination_by sizeOf`** — both required for Lean
   to generate `sstep`'s unfold theorem, which Blaster needs (without them Blaster
   errors `failed to generate unfold theorem`).
4. **Scalar extraction** before z3 (`sresBool`/`resBool`) — *both* substrates need
   this; PCB's `CekValue` hits a `Fin` SMT-translation error, Moist's `Const` a
   `BitVec` one. Keep `unfold-depth` modest.

## Reproduce

```bash
git clone https://github.com/input-output-hk/PlutusCoreBlaster /tmp/PlutusCoreBlaster
cd /tmp/PlutusCoreBlaster
lake build && lake build PlutusCore.Integer.Lemmas        # also builds Blaster@main
cp <this-dir>/PCBcompare.lean .
BL=.lake/packages/Blaster/.lake/build/lib/lean
DYN=$(grep -oE 'Built Blaster[A-Za-z._]*:dynlib' build.log | sed -E 's/^Built //;s/:dynlib$//' \
      | while read m; do printf -- '--load-dynlib=%s/%s.so ' "$BL" "${m//./_}"; done)
LEAN_PATH=.lake/build/lib/lean:$BL nix-shell -p z3 --run \
  "lean $DYN --root=. PCBcompare.lean"
```
