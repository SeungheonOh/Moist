import Moist.MIR.Expr
import Moist.Onchain.Builtins
import Moist.CEK.Builtins

namespace Moist.MIR

open Moist.Plutus.Term
open Moist.Onchain (builtinArity)
open Moist.CEK (expectedArgs ExpectedArgs ArgKind)
open Moist.Plutus.Term (BuiltinFun)

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
- **Saturated applications** are always impure — even "total" builtins
  like `addInteger` can error on wrong-type arguments, and we cannot
  statically verify argument types.

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

mutual
  /-- Check whether `Force e` is safe by verifying `e` produces a forceable
      value. Returns `true` when:
      - `e` is `Delay _` (force-delay always succeeds, body purity checked separately)
      - `e` is a builtin (possibly under more Forces) whose next expected
        arg is `argQ` at the right depth -/
  def isForceable : Expr → Bool
    | .Delay _ => true
    | .Builtin b => (expectedArgs b).head == .argQ
    | .Force e =>
      -- nested Force: inner must be forceable AND after consuming
      -- the inner force, the result must also be forceable
      match e with
      | .Builtin b => match expectedArgs b with
        | .more .argQ rest => rest.head == .argQ
        | _ => false
      | _ => false
    | _ => false

  /-- Return `true` when evaluating the expression is guaranteed to succeed.

  - Value forms (Var, Lit, Builtin, Lam, Delay, Fix) are always pure.
  - `Force e` is pure when `e` is pure AND produces a forceable value
    (a `Delay` or a builtin expecting a type-force argument).
  - `App f x`: only pure when the head is a **known builtin** (possibly
    Force-wrapped) AND partially applied (fewer args than arity).
    All other applications are impure — saturated builtins may error
    on wrong-type arguments, and `Var`-headed applications could alias
    any function.
  - `Case`, `Let`, `Constr`: pure when all sub-expressions are pure.
  - `Error`: always impure. -/
  def isPure : Expr → Bool
    | .Error => false
    | .Var _ | .Lit _ | .Builtin _ => true
    | .Lam _ _ | .Delay _ | .Fix _ _ => true
    | .Constr _ args => isPureList args
    | .Force (.Delay body) => isPure body
    | .Force e => isForceable e && isPure e
    | .Case _ _ => false  -- Case can fail at runtime (bad tag, non-constructor scrutinee)
    | .Let binds body => isPureBinds binds && isPure body
    | .App _ _ => false  -- Application can fail (non-function, wrong arity, etc.)
  termination_by e => sizeOf e

  def isPureList : List Expr → Bool
    | [] => true
    | e :: rest => isPure e && isPureList rest
  termination_by es => sizeOf es

  def isPureBinds : List (VarId × Expr × Bool) → Bool
    | [] => true
    | (_, rhs, _) :: rest => isPure rhs && isPureBinds rest
  termination_by bs => sizeOf bs
end

end Moist.MIR
