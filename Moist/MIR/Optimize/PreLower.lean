import Moist.MIR.Expr
import Moist.MIR.Analysis
import Moist.MIR.Optimize.Purity

namespace Moist.MIR

/-! # Pre-Lowering Inline Pass

Substitutes trivially cheap let bindings and beta-reduces single-use
applications before lowering to UPLC, so that Lower can be a clean
structural translation.

## Let Inlining Rules

For each `let v = rhs in rest; body`:

| RHS kind              | Uses | Decision                               |
|------------------------|------|----------------------------------------|
| Atom (Var/Lit/Builtin) | any  | Substitute (zero cost, no effects)     |
| Pure                   | 0    | Drop (dead binding)                    |
| Any                    | 1    | Substitute (single evaluation, safe)   |
| Otherwise              | ≥ 2  | Keep                                   |

## Beta Reduction

Reduces `(λx. body) arg` → `body[x := arg]` when `x` occurs at most
once in `body`. Safe under CEK because:
- Single use: `arg` is evaluated exactly once in both cases.
- Zero use + pure arg: `arg` is dropped (pure, no observable effect).
- Zero use + impure arg: kept as-is (must preserve evaluation of `arg`).
-/

/-- Flatten degenerate empty-binding Lets that arise from substitution. -/
private def flattenLet : Expr → Expr
  | .Let [] body => flattenLet body
  | e => e

/-- Count occurrences of `v` in the remaining bindings and body,
    which is the scope where `v` is live. -/
private def usesInScope (v : VarId) (rest : List (VarId × Expr × Bool)) (body : Expr) : Nat :=
  match rest with
  | [] => countOccurrences v body
  | _  => countOccurrences v (.Let rest body)

/-- Pre-lowering inline: substitute atoms, dead-pure, and single-use bindings.
    Walks the MIR tree and processes Let binding lists left-to-right. -/
partial def preLowerInline (e : Expr) : FreshM Expr := do
  match e with
  | .Lam x body => return .Lam x (← preLowerInline body)
  | .Fix f body => return .Fix f (← preLowerInline body)
  | .App f x    => do
    let f' ← preLowerInline f
    let x' ← preLowerInline x
    preLowerBeta f' x'
  | .Force e    => return .Force (← preLowerInline e)
  | .Delay e    => return .Delay (← preLowerInline e)
  | .Constr tag args => return .Constr tag (← args.mapM preLowerInline)
  | .Case scrut alts =>
    return .Case (← preLowerInline scrut) (← alts.mapM preLowerInline)
  | .Let binds body => preLowerLetBindings binds body
  | e => return e  -- Var, Lit, Builtin, Error
where
  /-- Beta-reduce `(λx. body) arg` when x occurs at most once in body.
      Recurses to handle multi-arg beta: `(λa. λb. e) x y`. -/
  preLowerBeta (f : Expr) (x : Expr) : FreshM Expr := do
    match f with
    | .Lam param body =>
      let uses := countOccurrences param body
      if uses <= 1 then
        if uses == 0 && !isPure x then
          -- Zero uses, impure arg: can't drop, keep the application
          return .App f x
        else
          let result ← subst param x body
          -- Recurse: the result may be another App (Lam ..) from multi-arg beta
          preLowerInline result
      else
        return .App f x
    | _ => return .App f x
  preLowerLetBindings (binds : List (VarId × Expr × Bool)) (body : Expr) : FreshM Expr :=
    go binds [] body
  go : List (VarId × Expr × Bool) → List (VarId × Expr × Bool) → Expr → FreshM Expr
    | [], acc, body => do
      let body' ← preLowerInline body
      match acc.reverse with
      | [] => return body'
      | kept => return .Let kept body'
    | (v, rhs, er) :: rest, acc, body => do
      let rhs' ← preLowerInline rhs
      let uses := usesInScope v rest body
      -- Atom RHS: always substitute (trivially cheap, no effects)
      if rhs'.isAtom then
        let restBody ← subst v rhs' (.Let rest body)
        go [] acc (flattenLet restBody)
      -- Zero uses, pure RHS: drop dead binding
      else if uses == 0 && isPure rhs' then
        go rest acc body
      -- Single use: always substitute (UPLC has no mutable state)
      else if uses == 1 then
        let restBody ← subst v rhs' (.Let rest body)
        go [] acc (flattenLet restBody)
      -- General case: keep the binding
      else
        go rest ((v, rhs', er) :: acc) body

/-- Run the pre-lowering inline pass with a given fresh variable start. -/
def preLowerInlineExpr (e : Expr) (freshStart : Nat := 5000) : Expr :=
  runFresh (preLowerInline e) freshStart

end Moist.MIR
