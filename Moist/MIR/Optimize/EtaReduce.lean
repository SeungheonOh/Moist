import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Safety

namespace Moist.MIR

/-! # Eta Reduction

Simplifies `λx. f x` to `f` when `x` is not free in `f` and `f` is
guaranteed callable. Nested lambdas are checked one layer at a time;
absence of free variables alone does not justify multi-argument eta.

## CEK Safety

Reduction requires a head that is guaranteed to evaluate to a callable
value. Unknown variables, saturated applications, and delayed values do
not satisfy this condition in untyped call-by-value evaluation.
The mandatory outer lambda of a Fix body is preserved for lowering.
-/

/-- `some f` when `λx. f x` may be replaced by `f`. -/
def etaRule : Expr → Option Expr
  | .Lam parameter (.App function (.Var argument)) =>
    if parameter == argument && !(freeVars function).contains parameter && isCallableValue function then
      some function
    else none
  | _ => none

/-- Eta reduction with explicit recursion fuel. Every recursive call is on a
    strictly smaller expression (a reduction only shrinks its input), so
    `exprSize` fuel is never exhausted. The result of a reduction is revisited
    only when the rule fired: `alphaEq` is not reflexive on every literal
    (`ConstArray`), so comparing an unreduced lambda with itself could fail. -/
def etaReduceFuel : Nat → Expr → Expr × Bool
  | 0, e => (e, false)
  | fuel + 1, .Lam x body =>
    let (body', changed) := etaReduceFuel fuel body
    let full := Expr.Lam x body'
    match etaRule full with
    | none => (full, changed)
    | some reduced =>
      if alphaEq reduced full then (full, changed)
      else
        -- Recurse into the result in case it exposed more eta opportunities
        let (reduced', changed2) := etaReduceFuel fuel reduced
        (reduced', true || changed2)
  | fuel + 1, .Fix f (.Lam parameter body) =>
    let (body', changed) := etaReduceFuel fuel body
    (.Fix f (.Lam parameter body'), changed)
  | fuel + 1, .Fix f body =>
    let (body', changed) := etaReduceFuel fuel body
    (.Fix f body', changed)
  | fuel + 1, .App f x =>
    let (f', c1) := etaReduceFuel fuel f
    let (x', c2) := etaReduceFuel fuel x
    (.App f' x', c1 || c2)
  | fuel + 1, .Force e =>
    let (e', changed) := etaReduceFuel fuel e
    (.Force e', changed)
  | fuel + 1, .Delay e =>
    let (e', changed) := etaReduceFuel fuel e
    (.Delay e', changed)
  | fuel + 1, .Constr tag args =>
    let results := args.map (etaReduceFuel fuel)
    let args' := results.map Prod.fst
    let changed := results.any Prod.snd
    (.Constr tag args', changed)
  | fuel + 1, .Case scrut alts =>
    let (scrut', c1) := etaReduceFuel fuel scrut
    let results := alts.map (etaReduceFuel fuel)
    let alts' := results.map Prod.fst
    let changed := results.any Prod.snd
    (.Case scrut' alts', c1 || changed)
  | fuel + 1, .Let binds body =>
    let bindResults := binds.map fun (v, rhs, er) =>
      let (rhs', changed) := etaReduceFuel fuel rhs
      ((v, rhs', er), changed)
    let binds' := bindResults.map Prod.fst
    let c1 := bindResults.any Prod.snd
    let (body', c2) := etaReduceFuel fuel body
    (.Let binds' body', c1 || c2)
  | _ + 1, e => (e, false)

/-- Run eta reduction over the entire expression tree.
    Returns the reduced expression and whether any reduction occurred. -/
def etaReduce (e : Expr) : Expr × Bool :=
  etaReduceFuel (exprSize e) e

end Moist.MIR
