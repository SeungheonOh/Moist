import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity
import Moist.MIR.Optimize.Safety

namespace Moist.MIR

/-! # Pre-Lowering Inline Pass

Substitutes trivially cheap let bindings and beta-reduces single-use
applications before lowering to UPLC, so that Lower can be a clean
structural translation.

## Let Inlining Rules

For each `let v = rhs in rest; body`:

| RHS kind              | Uses | Position | Decision                            |
|------------------------|------|----------|-------------------------------------|
| Atom (Var/Lit/Builtin) | any  | --       | Substitute (zero cost, no effects)  |
| Pure                   | 0    | --       | Drop (dead binding)                 |
| Value/pure             | 1    | any      | Substitute (no evaluation effects)  |
| Impure non-value       | 1    | first evaluation | Substitute (same order)      |
| Impure non-value       | 1    | later/deferred   | Keep (preserve effects)      |
| Otherwise              | ≥ 2  | --       | Keep                                |

## Beta Reduction

Reduces `(λx. body) arg` → `body[x := arg]` when `x` occurs at most
once in `body` and the substitution is safe:
- Zero use + pure arg: `arg` is dropped (pure, no observable effect).
- Zero use + impure arg: kept as-is (must preserve evaluation of `arg`).
- Single use + value arg: always safe (values have no evaluation effects).
- Single use + non-value arg at the first evaluation position: safe.
- Single use + non-value arg after a potentially effectful expression or
  in a deferred position: kept as-is to preserve errors and trace order.

The recursive worker assumes unique binders and an adequate fresh supply.
Use `preLowerInlineExpr` for arbitrary lexically scoped input; it establishes
both conditions before substitution.

Correctly forced unsaturated builtin states with total arguments are also
safe to move or discard. This removes ANF call-state bindings without moving
effects or dropping a saturated call's runtime type validation. General purity
and its proof contract are unchanged.
-/

/-- Flatten degenerate empty-binding Lets that arise from substitution. -/
def flattenLet : Expr → Expr
  | .Let [] body => flattenLet body
  | e => e

def isTotalPreLowerValue (expression : Expr) : Bool :=
  isPure expression || (builtinRemainder expression).isSome

/-- Count occurrences of `v` in the remaining bindings and body,
    which is the scope where `v` is live. -/
def usesInScope (v : VarId) (rest : List (VarId × Expr × Bool)) (body : Expr) : Nat :=
  match rest with
  | [] => countOccurrences v body
  | _  => countOccurrences v (.Let rest body)

/-- Rebuild a let from the kept bindings (accumulated in reverse). -/
def preLowerKeep (acc : List (VarId × Expr × Bool)) (body : Expr) : Expr :=
  match acc.reverse with
  | [] => body
  | kept => .Let kept body

/-- Beta-reduce `(λx. body) arg` when x occurs at most once in body
    and the substitution is safe; the contractum is processed again by
    `recurse`, which handles multi-argument beta `(λa. λb. e) x y`. -/
def preLowerBeta (recurse : Expr → FreshM Expr) (f x : Expr) : FreshM Expr :=
  match f with
  | .Lam param body =>
    let uses := countOccurrences param body
    if uses <= 1 then
      if uses == 0 && !isTotalPreLowerValue x then
        -- Zero uses, impure arg: can't drop, keep the application
        pure (.App f x)
      else if uses == 1 && !x.isValue && !isTotalPreLowerValue x && !firstEvaluationUse param body then
        pure (.App f x)
      else do
        let result ← subst param x body
        recurse result
    else
      pure (.App f x)
  | _ => pure (.App f x)

/-- Process let bindings left-to-right. `acc` holds the kept bindings in
    reverse; after a substitution the remaining scope is processed again by
    `recurse`. -/
def preLowerLet (recurse : Expr → FreshM Expr) :
    List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → FreshM Expr
  | [], acc, body => do
    let body' ← recurse body
    pure (preLowerKeep acc body')
  | (v, rhs, er) :: rest, acc, body => do
    let rhs' ← recurse rhs
    let uses := usesInScope v rest body
    -- Atom RHS: always substitute (trivially cheap, no effects)
    if rhs'.isAtom then do
      let restBody ← subst v rhs' (.Let rest body)
      let body' ← recurse (flattenLet restBody)
      pure (preLowerKeep acc body')
    -- Zero uses, pure RHS: drop dead binding
    else if uses == 0 && isTotalPreLowerValue rhs' then
      preLowerLet recurse rest acc body
    else if uses == 1 &&
        (rhs'.isValue || isTotalPreLowerValue rhs' || firstEvaluationUse v (.Let rest body)) then do
      let restBody ← subst v rhs' (.Let rest body)
      let body' ← recurse (flattenLet restBody)
      pure (preLowerKeep acc body')
    -- General case: keep the binding
    else
      preLowerLet recurse rest ((v, rhs', er) :: acc) body

/-- Apply a fresh-name computation to each element, left to right. -/
def preLowerList (recurse : Expr → FreshM Expr) : List Expr → FreshM (List Expr)
  | [] => pure []
  | e :: rest => do
    let e' ← recurse e
    let rest' ← preLowerList recurse rest
    pure (e' :: rest')

/-- Pre-lowering inline with an explicit recursion budget. Every nested call
    is on an expression strictly smaller than its caller (substitution only
    replaces single uses or atoms), so `exprSize` is always enough budget. -/
def preLowerInlineFuel : Nat → Expr → FreshM Expr
  | 0, e => pure e
  | fuel + 1, e =>
    match e with
    | .Lam x body => do pure (.Lam x (← preLowerInlineFuel fuel body))
    | .Fix f body => do pure (.Fix f (← preLowerInlineFuel fuel body))
    | .App f x => do
      let f' ← preLowerInlineFuel fuel f
      let x' ← preLowerInlineFuel fuel x
      preLowerBeta (preLowerInlineFuel fuel) f' x'
    | .Force e => do pure (.Force (← preLowerInlineFuel fuel e))
    | .Delay e => do pure (.Delay (← preLowerInlineFuel fuel e))
    | .Constr tag args => do pure (.Constr tag (← preLowerList (preLowerInlineFuel fuel) args))
    | .Case scrut alts => do
      let scrut' ← preLowerInlineFuel fuel scrut
      let alts' ← preLowerList (preLowerInlineFuel fuel) alts
      pure (.Case scrut' alts')
    | .Let binds body => preLowerLet (preLowerInlineFuel fuel) binds [] body
    | e => pure e  -- Var, Lit, Builtin, Error

/-- Pre-lowering inline: substitute atoms, dead-pure, and single-use bindings.
    Walks the MIR tree and processes Let binding lists left-to-right. -/
def preLowerInline (e : Expr) : FreshM Expr :=
  preLowerInlineFuel (exprSize e + 1) e

/-- Run the pre-lowering inline pass with a given fresh variable start. -/
def preLowerInlineExpr (e : Expr) (freshStart : Nat := 5000) : Expr :=
  let prepared := uniqueOptimizationBinders e
  runFresh (preLowerInline prepared) (max freshStart (maxUidExpr prepared + 1))

end Moist.MIR
