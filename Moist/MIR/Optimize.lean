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
import Moist.MIR.Optimize.Advanced

namespace Moist.MIR

/-! # Optimization Pipeline

The public optimizer accepts lexically scoped MIR and reserves its fresh
supply above all input identifiers. Scope-moving passes freshen binders
when needed; valid Fix nodes retain their mandatory outer lambda.

Pipeline:
1. Share safe delayed values, remove nonrecursive Fix, and hygienically float out.
2. Beta reduction, ANF normalization, and another float-out.
3. Repeated ANF → known-constructor cases → checked shapes, folding, and
   destructor fusion → effect-aware CSE → DCE →
   ordered inlining → beta → safe eta → force-delay.
4. compileOptimized runs checked pre-lowering cleanup and lowering, followed
   by final packing and explicitly selected sharing/size trade-offs.

Case simplification uses concrete constructor facts, never a branch's
lambda count. CSE preserves Trace effects, including unknown aliases.
Inlining preserves the evaluation frontier, not merely strictness.

The simplification loop uses origin-aware alpha equivalence for its fixed
point and maxOptIterations as a hard bound. ANF and inlining can oscillate;
a bound is necessary and is not a proof of global optimization optimality.
Resource budgets are measured separately from value/error/trace correctness.
-/

/-- Maximum number of simplify loop iterations before giving up.
In practice the pipeline converges in 2--4 iterations. -/
def maxOptIterations : Nat := 20

/-- Run one iteration of the simplify loop:
Prepare → ANF → CaseMerge → checked simplification → CSE → DCE →
Inline → Beta Reduce → Eta Reduce → ForceDelay.
ANF re-normalization at the start re-lifts sub-expressions that inlining
collapsed, exposing them as let-binding RHS values for CSE and DCE.
CaseMerge runs before CSE to specialize concrete constructors,
exposing field applications for CSE and inlining without assuming arities.
DCE runs on ANF input so every sub-computation is a named let binding,
making pure dead code easy to identify. -/
partial def simplifyOnce (e : Expr) : FreshM Expr := do
  let prepared := Advanced.prepare e
  reserveFreshFor prepared
  let e0 ← anfNormalize (uniqueOptimizationBinders prepared)
  let (e0b, _) := caseMergePass e0
  let e0c := Advanced.simplify e0b
  reserveFreshFor e0c
  let (e1, _) := cse [] e0c
  let (e2, _) := dce e1
  let (e3, _) ← inlinePassWithCanon e2
  let (e4, _) ← betaReducePass e3
  let (e5, _) := etaReduce e4
  let (e6, _) := forceDelay e5
  pure e6

/-- Run the simplify loop to fixed point (up to `maxOptIterations`).
Uses alpha-equivalence to detect fixpoint despite fresh variable renaming. -/
partial def simplifyLoop (e : Expr) (fuel : Nat := maxOptIterations) : FreshM Expr := do
  if fuel == 0 then return e
  let e' ← simplifyOnce e
  if e'.alphaEq e then return e
  else simplifyLoop e' (fuel - 1)

/-- Run the full optimization pipeline on an MIR expression.

1. Share safe delayed values, remove nonrecursive Fix, then float out.
2. Beta reduce to eliminate immediately-applied lambdas.
3. ANF normalize to create let bindings.
4. Float out again — ANF creates let bindings inside case branches
   (e.g. `let anf = force headList`) that can now be floated out of
   case alternatives and deduplicated by CSE.
5. Simplify to fixed point (CSE, inline, beta, eta, force-delay, DCE).

Returns the optimized MIR expression. -/
partial def optimize (e : Expr) : FreshM Expr := do
  let prepared := Advanced.prepare e
  reserveFreshFor prepared
  let (e1, _) := floatOut prepared
  let (e2, _) ← betaReducePass e1
  let e3 ← anfNormalize e2
  let (e4, _) := floatOut e3
  simplifyLoop e4

/-- Debug: run pipeline up through beta reduction + ANF (before simplify loop). -/
def optimizeDebugBeta (e : Expr) (freshStart : Nat := 1000) : Expr × Bool :=
  let m : FreshM (Expr × Bool) := do
    let prepared := Advanced.prepare e
    reserveFreshFor prepared
    let (e1, _) := floatOut prepared
    let (e2, betaChanged) ← betaReducePass e1
    let e3 ← anfNormalize e2
    pure (e3, betaChanged)
  runFresh m freshStart

/-- Convenience wrapper: run the full optimization pipeline with a given
fresh variable starting index.

```
optimizeExpr input 1000
-- Runs floatOut → ANF → simplify loop
-- Fresh variables start no lower than uid 1000 or the input's maximum plus one
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
  let prepared := Advanced.prepare e
  reserveFreshFor prepared
  let mut steps : Array OptStep := #[⟨"Delayed values / nonrecursive Fix", prepared, !prepared.alphaEq e⟩]
  -- Pre-loop passes
  let (e1, c1) := floatOut prepared
  steps := steps.push ⟨"FloatOut (1st)", e1, c1⟩
  let (e2, c2) ← betaReducePass e1
  steps := steps.push ⟨"BetaReduce", e2, c2⟩
  let e3 ← anfNormalize e2
  steps := steps.push ⟨"ANF", e3, !e3.alphaEq e2⟩
  let (e4, c4) := floatOut e3
  steps := steps.push ⟨"FloatOut (2nd)", e4, c4⟩
  -- Simplify loop (unrolled for tracing, fixpoint by alpha-equivalence)
  let mut current := e4
  let mut fuel := maxOptIterations
  let mut iter : Nat := 1
  repeat
    if fuel == 0 then break
    let prepared := Advanced.prepare current
    reserveFreshFor prepared
    let e0 ← anfNormalize (uniqueOptimizationBinders prepared)
    let (e0b, c0b) := caseMergePass e0
    let e0c := Advanced.simplify e0b
    reserveFreshFor e0c
    let (e1, c1) := cse [] e0c
    let (e1b, c1b) := dce e1
    let (e2, c2) ← inlinePassWithCanon e1b
    let (e3, c3) ← betaReducePass e2
    let (e4, c4) := etaReduce e3
    let (e5, c5) := forceDelay e4
    steps := steps.push ⟨s!"Simplify {iter}: Prepare", prepared, !prepared.alphaEq current⟩
    steps := steps.push ⟨s!"Simplify {iter}: ANF", e0, !e0.alphaEq prepared⟩
    steps := steps.push ⟨s!"Simplify {iter}: CaseMerge", e0b, c0b⟩
    steps := steps.push ⟨s!"Simplify {iter}: Checked values", e0c, !e0c.alphaEq e0b⟩
    steps := steps.push ⟨s!"Simplify {iter}: CSE", e1, c1⟩
    steps := steps.push ⟨s!"Simplify {iter}: DCE", e1b, c1b⟩
    steps := steps.push ⟨s!"Simplify {iter}: Inline", e2, c2⟩
    steps := steps.push ⟨s!"Simplify {iter}: BetaReduce", e3, c3⟩
    steps := steps.push ⟨s!"Simplify {iter}: EtaReduce", e4, c4⟩
    steps := steps.push ⟨s!"Simplify {iter}: ForceDelay", e5, c5⟩
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
