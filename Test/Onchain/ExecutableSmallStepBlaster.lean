import Moist.Verified.SmallStep
import Blaster

/-! # Blaster on the executable small-step (`evalF`) vs the CEK — measured

Companion to `Test/Onchain/Demo.lean` (Blaster on the CEK `exec`). Here Blaster
symbolically executes `Moist.Verified.SmallStep.evalF` — the total, fuel-driven
small-step evaluator proven equivalent to `Step`/`Steps` and the CEK — and we
compare it head-to-head with a self-contained CEK iterator.

## How to run (NOT the pure-core `lean`-only path)

`import Blaster` shells out to a `z3` binary and loads Blaster's precompiled
dynlibs. In this repo's dev box:

```
# 1. build Blaster's oleans+dynlibs once (lake, empty deps, no zig needed):
cd .lake/packages/Blaster && lake build Blaster
# 2. run with z3 on PATH and Blaster dynlibs loaded:
BL=.lake/packages/Blaster/.lake/build/lib/lean
DYN=$(grep -oE 'Built Blaster[A-Za-z._]*:dynlib' build.log | sed -E 's/^Built //;s/:dynlib$//' \
      | while read m; do echo --load-dynlib=$BL/${m//./_}.so; done)
LEAN_PATH=.lake/build/lib:$BL nix-shell -p z3 --run \
  "lean $DYN --root=. Test/Onchain/ExecutableSmallStepBlaster.lean"
```

## What was measured (Z3 4.16.0, this file)

* **Identical SMT.** With the scalar result extracted (see `outInt`/`cekInt`),
  Blaster's optimizer symbolically executes BOTH evaluators down to the carried
  integer, leaving the *same* pure-`Int` residual. The dumped SMT query is
  byte-for-byte identical for `evalF` and the CEK; z3 solve time is identical
  (~0.02s). The choice of evaluator is erased before z3 ever runs.

* **Symbolic-execution (optimizer) cost.**

  | reduction                     | `evalF` opt | CEK opt |
  |-------------------------------|-------------|---------|
  | 1 β, no binder (`id x`)       | 0.038s      | 0.077s  |
  | 2 β, **under binder** (`K x`) | 0.117s      | 0.077s  |
  | 3 β, no binder (`id³ x`)      | 0.039s      | 0.089s  |

  `evalF` is *cheaper* than the CEK on substitution-light reductions, but pays a
  measurable penalty when β fires under a binder (`substTerm`/`renameTerm`); the
  CEK is steadier (environments, no substitution). Both are well under 0.15s.

## Two shared hard limits (NOT small-step-specific)

1. **`evalBuiltin` blows up the optimizer** for BOTH `evalF` and the CEK — a
   concrete `AddInteger` goal times out either way (Blaster unfolds the giant
   builtin match). `Demo.lean` sidesteps this by giving Blaster builtin *spec
   axioms* instead of the implementation; do the same for builtin-heavy goals.
2. **`Const`/`Term`/`State` carry `ByteArray`/`BitVec`**, which Blaster cannot
   translate to SMT. So a goal that reaches z3 while still mentioning those types
   fails translation. Extract scalars first (`outInt`/`cekInt`) so the residual
   handed to z3 is pure arithmetic.

Also: keep `unfold-depth` MODEST (~30–60). Depth 100+ over-unfolds the recursive
evaluators and blows up (a 600s timeout on a goal that closes in 0.04s at depth 40).
-/

namespace Test.ExecutableSmallStepBlaster

open Moist.Plutus.Term (Term Const BuiltinType AtomicType BuiltinFun)
open Moist.Verified.SmallStep (evalF Outcome)
open Moist.CEK (State CekValue)

abbrev int (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
abbrev lam (b : Term) : Term := .Lam 0 b
abbrev app (f x : Term) : Term := .Apply f x
abbrev idT : Term := lam (.Var 1)
abbrev kT : Term := lam (lam (.Var 2))   -- λx.λy.x

/-- Self-contained CEK iterator over Moist's own `step` (pure core). -/
def cekRun : Nat → State → State
  | 0, s => s
  | n + 1, s => cekRun n (Moist.CEK.step s)
def cekInit (t : Term) : State := .compute [] .nil t

/-- Extract the integer payload so the residual handed to z3 is pure `Int`. -/
def outInt : Outcome → Int | .value (.Constant (.Integer n, _)) => n | _ => 0
def cekInt : State → Int   | .halt (.VCon (.Integer n)) => n | _ => 0

/-! ### Head-to-head: identical SMT for both substrates.
    Residual `x = y - 1` from `x + 1 = y`; `dump-smt-lib` shows the query. -/

-- small-step
#blaster (unfold-depth: 30) (timeout: 60) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y : Int), x + 1 = y → outInt (evalF 6 (app idT (int x))) = y - 1]
-- CEK (emits the byte-for-byte same SMT query)
#blaster (unfold-depth: 50) (timeout: 60) (dump-smt-lib: 1) (verbose: 1)
  [∀ (x y : Int), x + 1 = y → cekInt (cekRun 20 (cekInit (app idT (int x)))) = y - 1]

/-! ### Scaling (optimizer cost): β under a binder is the small-step's cost. -/

-- 2 β under a binder: K combinator discards its second argument
#blaster (unfold-depth: 40) (timeout: 60) (verbose: 1)
  [∀ (x y : Int), x + 1 = y → outInt (evalF 8 (app (app kT (int x)) (int 0))) = y - 1]
#blaster (unfold-depth: 70) (timeout: 60) (verbose: 1)
  [∀ (x y : Int), x + 1 = y → cekInt (cekRun 30 (cekInit (app (app kT (int x)) (int 0)))) = y - 1]

-- 3 β, substitution-light: nested identities (evalF here beats the CEK)
#blaster (unfold-depth: 50) (timeout: 60) (verbose: 1)
  [∀ (x y : Int), x + 1 = y → outInt (evalF 10 (app idT (app idT (app idT (int x))))) = y - 1]
#blaster (unfold-depth: 90) (timeout: 60) (verbose: 1)
  [∀ (x y : Int), x + 1 = y → cekInt (cekRun 40 (cekInit (app idT (app idT (app idT (int x)))))) = y - 1]

end Test.ExecutableSmallStepBlaster
