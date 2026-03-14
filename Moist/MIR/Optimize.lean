import Moist.MIR.Expr
import Moist.MIR.ANF
import Moist.MIR.Optimize.Purity
import Moist.MIR.Optimize.FloatOut
import Moist.MIR.Optimize.Inline
import Moist.MIR.Optimize.CSE
import Moist.MIR.Optimize.DCE
import Moist.MIR.Optimize.EtaReduce
import Moist.MIR.Optimize.ForceDelay
import Moist.MIR.Optimize.BetaReduce
import Moist.MIR.Optimize.CaseMerge

namespace Moist.MIR

/-! # Optimization Pipeline

Drives all optimization passes in the correct order with fixed-point
iteration for the simplification loop.

## Pipeline Structure

```
ANF input
  │
  ▼
Float Out (1st)      ← hoist pure bindings out of Lam/Fix
  │
  ▼
Beta Reduce          ← eliminate (λx. body) arg redexes
  │
  ▼
ANF normalize        ← create let bindings (including inside case branches)
  │
  ▼
Float Out (2nd)      ← hoist ANF-created lets out of Case alternatives
  │                    so CSE can deduplicate across branches
  ▼
┌─────────────────┐
│ Simplify (loop) │  repeat until no pass
│  1. ANF         │  makes progress
│  2. Case Merge  │
│  3. CSE         │
│  4. Inlining    │
│  5. Eta Reduce  │
│  6. Force-Delay │
│  7. DCE         │
└─────────────────┘
  │
  ▼
MIR output → PreLowerInline → Lower
```

ANF normalization runs at the start of each simplify iteration to
re-lift sub-expressions that inlining collapsed into nested App trees.
This exposes common sub-expressions as let-binding RHS values where
CSE can detect and eliminate them.

Without re-ANF, inlining single-use chains can bury shared
computations inside expression trees where CSE cannot see them.
For example, two field accesses sharing a common prefix
(sndPair → tailList) end up duplicating the prefix inline after
the intermediate let bindings are collapsed.

ANF and inline can oscillate (ANF lifts a single-use binding, inline
removes it, ANF re-lifts it, ...) but this is bounded by
maxOptIterations. Each *productive* iteration (where CSE eliminates
a duplicate) strictly reduces the number of distinct computations,
guaranteeing convergence of the useful work.

## Why This Order

1. **Float-out first**: Hoists pure bindings outside Lam/Fix so the
   simplifier sees them at their widest scope. A binding that was
   recomputed per-call is now shared, making it a better inlining or
   CSE candidate.

2. **ANF before CSE**: Re-lifts non-atomic sub-expressions into let
   bindings so CSE can compare them as RHS values.

3. **CSE before inlining**: Deduplicate first so there are fewer
   bindings to analyze during inlining.

4. **Inlining before eta**: Inlining may expose eta-reducible patterns
   by substituting known lambda definitions.

5. **Eta before force-delay**: Eta reduction simplifies lambda structure
   before force-delay cancellation.

6. **Force-delay before DCE**: Cancellation makes `Delay` bindings
   dead; DCE sweeps them away.

## Fixed-Point Iteration

The simplify loop repeats up to `maxIterations` times (default 20).
It stops early when no pass in a full iteration reports a change.
This converges because each productive pass strictly reduces expression
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
ANF → CaseMerge → CSE → Inline → Eta Reduce → ForceDelay → DCE.
ANF re-normalization at the start re-lifts sub-expressions that inlining
collapsed, exposing them as let-binding RHS values for CSE.
CaseMerge runs before CSE to merge duplicate cases on the same scrutinee,
exposing field references as simple variable bindings for CSE and inlining. -/
partial def simplifyOnce (e : Expr) : FreshM Expr := do
  let e0 ← anfNormalize e
  let (e0b, _) := caseMergePass e0
  let (e1, _) := cse [] e0b
  let (e2, _) ← inlinePass e1
  let (e3, _) := etaReduce e2
  let (e4, _) := forceDelay e3
  let (e5, _) := dce e4
  pure e5

/-- Run the simplify loop to fixed point (up to `maxOptIterations`).
Uses alpha-equivalence to detect fixpoint despite fresh variable renaming. -/
partial def simplifyLoop (e : Expr) (fuel : Nat := maxOptIterations) : FreshM Expr := do
  if fuel == 0 then return e
  let e' ← simplifyOnce e
  if e'.alphaEq e then return e
  else simplifyLoop e' (fuel - 1)

/-- Run the full optimization pipeline on an MIR expression.

1. Float out pure bindings past Lam/Fix boundaries.
2. Beta reduce to eliminate immediately-applied lambdas.
3. ANF normalize to create let bindings.
4. Float out again — ANF creates let bindings inside case branches
   (e.g. `let anf = force headList`) that can now be floated out of
   case alternatives and deduplicated by CSE.
5. Simplify to fixed point (CSE, inline, eta, force-delay, DCE).

Returns the optimized MIR expression. -/
partial def optimize (e : Expr) : FreshM Expr := do
  let (e1, _) := floatOut e
  let (e2, _) ← betaReducePass e1
  let e3 ← anfNormalize e2
  let (e4, _) := floatOut e3
  simplifyLoop e4

/-- Debug: run pipeline up through beta reduction + ANF (before simplify loop). -/
def optimizeDebugBeta (e : Expr) (freshStart : Nat := 1000) : Expr × Bool :=
  let m : FreshM (Expr × Bool) := do
    let (e1, _) := floatOut e
    let (e2, betaChanged) ← betaReducePass e1
    let e3 ← anfNormalize e2
    pure (e3, betaChanged)
  runFresh m freshStart

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

/-! ## Optimization Trace

Step-by-step trace of the optimization pipeline for debugging.
Each step records the pass name, the resulting expression, and
whether the pass reported a change.
-/

structure OptStep where
  pass : String
  expr : Expr
  changed : Bool

/-- Run the full optimization pipeline, recording every intermediate step.
Returns the array of steps (the last entry is the final result). -/
partial def optimizeTrace (e : Expr) : FreshM (Array OptStep) := do
  let mut steps : Array OptStep := #[]
  -- Pre-loop passes
  let (e1, c1) := floatOut e
  steps := steps.push ⟨"FloatOut (1st)", e1, c1⟩
  let (e2, c2) ← betaReducePass e1
  steps := steps.push ⟨"BetaReduce", e2, c2⟩
  let e3 ← anfNormalize e2
  steps := steps.push ⟨"ANF", e3, true⟩
  let (e4, c4) := floatOut e3
  steps := steps.push ⟨"FloatOut (2nd)", e4, c4⟩
  -- Simplify loop (unrolled for tracing, fixpoint by alpha-equivalence)
  let mut current := e4
  let mut fuel := maxOptIterations
  let mut iter : Nat := 1
  repeat
    if fuel == 0 then break
    let e0 ← anfNormalize current
    let (e0b, c0b) := caseMergePass e0
    let (e1, c1) := cse [] e0b
    let (e2, c2) ← inlinePass e1
    let (e3, c3) := etaReduce e2
    let (e4, c4) := forceDelay e3
    let (e5, c5) := dce e4
    steps := steps.push ⟨s!"Simplify {iter}: ANF", e0, true⟩
    if c0b then
      steps := steps.push ⟨s!"Simplify {iter}: CaseMerge", e0b, c0b⟩
    if c1 then
      steps := steps.push ⟨s!"Simplify {iter}: CSE", e1, c1⟩
    if c2 then
      steps := steps.push ⟨s!"Simplify {iter}: Inline", e2, c2⟩
    if c3 then
      steps := steps.push ⟨s!"Simplify {iter}: EtaReduce", e3, c3⟩
    if c4 then
      steps := steps.push ⟨s!"Simplify {iter}: ForceDelay", e4, c4⟩
    if c5 then
      steps := steps.push ⟨s!"Simplify {iter}: DCE", e5, c5⟩
    if e5.alphaEq current then
      break
    current := e5
    fuel := fuel - 1
    iter := iter + 1
  return steps

/-- Run the optimization trace with a given fresh variable starting index. -/
def optimizeTraceExpr (e : Expr) (freshStart : Nat := 1000) : Array OptStep :=
  runFresh (optimizeTrace e) freshStart

end Moist.MIR
