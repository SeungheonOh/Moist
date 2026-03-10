import Moist.MIR.Expr
import Moist.MIR.ANF
import Moist.MIR.Optimize.Purity
import Moist.MIR.Optimize.FloatOut
import Moist.MIR.Optimize.Inline
import Moist.MIR.Optimize.CSE
import Moist.MIR.Optimize.DCE
import Moist.MIR.Optimize.EtaReduce
import Moist.MIR.Optimize.ForceDelay

namespace Moist.MIR

/-! # Optimization Pipeline

Drives all optimization passes in the correct order with fixed-point
iteration for the simplification loop.

## Pipeline Structure

```
ANF input
  │
  ▼
Float Out            ← maximize sharing by hoisting pure bindings
  │                    out of Lam/Fix
  ▼
ANF normalize        ← create let bindings for CSE (once)
  │
  ▼
┌─────────────────┐
│ Simplify (loop) │  repeat until no pass
│  1. CSE         │  makes progress
│  2. Inlining    │
│  3. Eta Reduce  │
│  4. Force-Delay │
│  5. DCE         │
└─────────────────┘
  │
  ▼
MIR output → PreLowerInline → Lower
```

ANF normalization runs once at the start to create let bindings that
CSE and other passes can work with. It is NOT repeated in the loop —
inlining intentionally removes let bindings, and re-normalizing would
recreate exactly the bindings that inline just eliminated, causing a
wasteful back-and-forth cycle. The PreLowerInline pass handles any
remaining cleanup (beta reduction, atom substitution, single-use
inlining) before lowering.

## Why This Order

1. **Float-out first**: Hoists pure bindings outside Lam/Fix so the
   simplifier sees them at their widest scope. A binding that was
   recomputed per-call is now shared, making it a better inlining or
   CSE candidate.

2. **CSE before inlining**: Deduplicate first so there are fewer
   bindings to analyze during inlining.

3. **Inlining before eta**: Inlining may expose eta-reducible patterns
   by substituting known lambda definitions.

4. **Eta before force-delay**: Eta reduction simplifies lambda structure
   before force-delay cancellation.

5. **Force-delay before DCE**: Cancellation makes `Delay` bindings
   dead; DCE sweeps them away.

## Fixed-Point Iteration

The simplify loop repeats up to `maxIterations` times (default 20).
It stops early when no pass in a full iteration reports a change.
This converges because each pass strictly reduces expression
complexity or count: CSE reduces binding count, inlining reduces
variable indirection, eta reduces lambda wrapping, force-delay
removes force/delay pairs, and DCE removes dead bindings.

## Examples

### Simple pipeline

```
-- Input (ANF):
Lam x →
  let a = 1
  let b = addInteger x
  let c = addInteger x   -- duplicate of b
  in App b c

-- After float-out: a floats out (pure, no x dep)
let a = 1
Lam x →
  let b = addInteger x
  let c = addInteger x
  in App b c

-- After CSE: c is duplicate of b
let a = 1
Lam x →
  let b = addInteger x
  in App b b

-- After DCE: a is unused and pure
Lam x →
  let b = addInteger x
  in App b b
```

### Force-delay pipeline

```
-- Input (ANF):
let v = Delay (Var x)
let w = Force (Var v)
in Var w

-- After force-delay: Force (Var v) → Var x
let v = Delay (Var x)
let w = Var x
in Var w

-- After inlining: w is an atom used once → inline
let v = Delay (Var x)
in Var x

-- After DCE: v is unused and pure → removed
Var x
```
-/

/-- Maximum number of simplify loop iterations before giving up.
In practice the pipeline converges in 2--4 iterations. -/
def maxOptIterations : Nat := 20

/-- Run one iteration of the simplify loop:
CSE → Inline → Eta Reduce → ForceDelay → DCE.
Returns the simplified expression and whether any sub-pass made progress. -/
partial def simplifyOnce (e : Expr) : FreshM (Expr × Bool) := do
  let (e1, c1) := cse e
  let (e2, c2) ← inlinePass e1
  let (e3, c3) := etaReduce e2
  let (e4, c4) := forceDelay e3
  let (e5, c5) := dce e4
  pure (e5, c1 || c2 || c3 || c4 || c5)

/-- Run the simplify loop to fixed point (up to `maxOptIterations`). -/
partial def simplifyLoop (e : Expr) (fuel : Nat := maxOptIterations) : FreshM Expr := do
  if fuel == 0 then return e
  let (e', changed) ← simplifyOnce e
  if changed then simplifyLoop e' (fuel - 1)
  else return e'

/-- Run the full optimization pipeline on an MIR expression.

1. Float out pure bindings past Lam/Fix boundaries.
2. ANF normalize (once) to create let bindings for CSE.
3. Simplify to fixed point (CSE, inline, eta, force-delay, DCE).

Returns the optimized MIR expression. -/
partial def optimize (e : Expr) : FreshM Expr := do
  let (e1, _) := floatOut e
  let e2 ← anfNormalize e1
  simplifyLoop e2

/-- Convenience wrapper: run the full optimization pipeline with a given
fresh variable starting index.

```
optimizeExpr input 1000
-- Runs floatOut → ANF → simplify loop
-- Fresh variables start at uid 1000
```
-/
def optimizeExpr (e : Expr) (freshStart : Nat := 1000) : Expr :=
  runFresh (optimize e) freshStart

end Moist.MIR
