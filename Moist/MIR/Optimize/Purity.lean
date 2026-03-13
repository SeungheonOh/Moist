import Moist.MIR.Expr
import Moist.Onchain.Builtins

namespace Moist.MIR

open Moist.Plutus.Term
open Moist.Onchain (builtinArity builtinIsTotal)

/-! # Purity Analysis

Determines whether an expression is guaranteed to evaluate without error.
Used by optimization passes (FloatOut, DCE, PreLower) to decide when it
is safe to move, speculate, or eliminate expressions.

## Design

An expression is **pure** when evaluating it is guaranteed to succeed,
regardless of runtime values. The sources of impurity are:

1. **Error** nodes — always fail.
2. **Any application with a `Var` head** — the variable could alias a
   fallible builtin (e.g. `headList`, `divideInteger`).
3. **Saturated application of a fallible builtin** — e.g. `divideInteger x 0`,
   `headList []`. We cannot statically determine argument values, so any
   fully-applied fallible builtin is conservatively impure.

### Safe builtin applications

- **Partial application** of any builtin (fewer args than arity) always
  succeeds — it just builds a partially-applied closure.
- **Saturated application of a total builtin** always succeeds — e.g.
  `addInteger 3 5`, `equalsInteger x y`.

### Value forms (body not evaluated at construction time)

- **Lam, Delay, Fix** — building a closure/thunk never fails.
-/

/-! ## Builtin Application Analysis -/

/-- Extract the builtin from a head expression, stripping Force wrappers. -/
private def extractBuiltin : Expr → Option BuiltinFun
  | .Builtin b => some b
  | .Force e => extractBuiltin e
  | _ => none

/-- Unwrap an application spine to get (head, argCount). -/
private def countArgs : Expr → Expr × Nat
  | .App f _ =>
    let (head, n) := countArgs f
    (head, n + 1)
  | e => (e, 0)

/-! ## Core Purity Check -/

/-- Return `true` when evaluating the expression is guaranteed to succeed.

- Value forms (Var, Lit, Builtin, Lam, Delay, Fix) are always pure.
- `Force e` is pure when `e` is pure.
- `App f x`: only pure when the head is a **known builtin** (possibly
  Force-wrapped) AND either partially applied or saturated on a total
  builtin. All other applications are impure — a `Var`-headed
  application could alias any function, including a fallible builtin
  like `headList` or `divideInteger`.
- `Case`, `Let`, `Constr`: pure when all sub-expressions are pure.
- `Error`: always impure. -/
partial def isPure : Expr → Bool
  | .Error => false
  | .Var _ | .Lit _ | .Builtin _ => true
  | .Lam _ _ | .Delay _ | .Fix _ _ => true
  | .Constr _ args => args.all isPure
  | .Force e => isPure e
  | .Case scrut alts => isPure scrut && alts.all isPure
  | .Let binds body => binds.all (fun (_, rhs, _) => isPure rhs) && isPure body
  | .App f x =>
    let (head, nArgs) := countArgs (.App f x)
    match extractBuiltin head with
    | some b =>
      if nArgs < builtinArity b || builtinIsTotal b then
        isPure f && isPure x
      else
        false
    | none => false

end Moist.MIR
