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

private def etaReduceLam (expression : Expr) : Expr :=
  match expression with
  | .Lam parameter (.App function (.Var argument)) =>
    if parameter == argument && !(freeVars function).contains parameter && isCallableValue function then
      function
    else expression
  | _ => expression

/-- Run eta reduction over the entire expression tree.
    Returns the reduced expression and whether any reduction occurred. -/
partial def etaReduce : Expr → Expr × Bool
  | .Lam x body =>
    let (body', changed) := etaReduce body
    let full := Expr.Lam x body'
    let reduced := etaReduceLam full
    if alphaEq reduced full then (full, changed)
    else
      -- Recurse into the result in case it exposed more eta opportunities
      let (reduced', changed2) := etaReduce reduced
      (reduced', true || changed2)
  | .Fix f (.Lam parameter body) =>
    let (body', changed) := etaReduce body
    (.Fix f (.Lam parameter body'), changed)
  | .Fix f body =>
    let (body', changed) := etaReduce body
    (.Fix f body', changed)
  | .App f x =>
    let (f', c1) := etaReduce f
    let (x', c2) := etaReduce x
    (.App f' x', c1 || c2)
  | .Force e =>
    let (e', changed) := etaReduce e
    (.Force e', changed)
  | .Delay e =>
    let (e', changed) := etaReduce e
    (.Delay e', changed)
  | .Constr tag args =>
    let results := args.map etaReduce
    let args' := results.map Prod.fst
    let changed := results.any Prod.snd
    (.Constr tag args', changed)
  | .Case scrut alts =>
    let (scrut', c1) := etaReduce scrut
    let results := alts.map etaReduce
    let alts' := results.map Prod.fst
    let changed := results.any Prod.snd
    (.Case scrut' alts', c1 || changed)
  | .Let binds body =>
    let bindResults := binds.map fun (v, rhs, er) =>
      let (rhs', changed) := etaReduce rhs
      ((v, rhs', er), changed)
    let binds' := bindResults.map Prod.fst
    let c1 := bindResults.any Prod.snd
    let (body', c2) := etaReduce body
    (.Let binds' body', c1 || c2)
  | e => (e, false)

end Moist.MIR
