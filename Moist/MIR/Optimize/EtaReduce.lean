import Moist.MIR.Expr
import Moist.MIR.Analysis

namespace Moist.MIR

/-! # Eta Reduction

Simplifies `λx. f x` to `f` when `x` is not free in `f`.

Generalizes to multi-argument eta:
  `λa b c. f a b c` → `f`   (when a,b,c ∉ FV(f))

## CEK Safety

Always safe. `(λx. f x) v` and `f v` produce identical results
under CEK evaluation — the lambda wrapper is pure overhead.
-/

/-- Peel trailing applications that exactly match the lambda parameters
    in order. Returns the function head and whether eta reduction applied.

    Given `body` and a list of lambda-bound vars `[a, b, c]` (outermost first),
    checks if body = `f a b c` where f doesn't reference a, b, or c. -/
private def tryEtaReduce (body : Expr) (params : List VarId) : Option Expr :=
  let nParams := params.length
  -- Uncurry the body: f a1 a2 ... an
  let (head, args) := uncurryApp body
  -- Must have at least nParams args
  if args.length < nParams then none
  else
    -- The trailing args must exactly match params in order
    let trailingArgs := args.drop (args.length - nParams)
    let matchesParams := (trailingArgs.zip params.reverse).all fun (arg, param) =>
      match arg with
      | .Var v => v == param
      | _ => false
    if !matchesParams then none
    else
      -- The head + leading args must not reference any of the params
      let leadingArgs := args.take (args.length - nParams)
      let headExpr := leadingArgs.foldl (init := head) fun acc a => .App acc a
      let headFV := freeVars headExpr
      let captured := params.any fun p => headFV.contains p
      if captured then none
      else some headExpr

/-- Eta-reduce a single lambda nest. Peels all leading Lam binders,
    attempts eta reduction on the body, re-wraps any remaining binders. -/
private def etaReduceLam (e : Expr) : Expr :=
  go e []
where
  go : Expr → List VarId → Expr
    | .Lam x body, params => go body (params ++ [x])
    | body, params =>
      if params.isEmpty then body
      else
        match tryEtaReduce body params with
        | some reduced => reduced
        | none =>
          -- Try partial eta: remove trailing params one at a time
          goPartial body params
  goPartial : Expr → List VarId → Expr
    | body, [] => body
    | body, params =>
      -- Try removing the last param
      let last := params.getLast!
      match body with
      | .App f (.Var v) =>
        if v == last && !(freeVars f).contains last then
          -- η-reduce one layer: λ...last. f last → λ... f
          let remaining := params.dropLast
          if remaining.isEmpty then f
          else goPartial f remaining
        else
          -- Can't reduce, re-wrap all params
          params.foldr (init := body) fun p acc => .Lam p acc
      | _ =>
        params.foldr (init := body) fun p acc => .Lam p acc

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
    let bindResults := binds.map fun (v, rhs) =>
      let (rhs', changed) := etaReduce rhs
      ((v, rhs'), changed)
    let binds' := bindResults.map Prod.fst
    let c1 := bindResults.any Prod.snd
    let (body', c2) := etaReduce body
    (.Let binds' body', c1 || c2)
  | e => (e, false)

end Moist.MIR
