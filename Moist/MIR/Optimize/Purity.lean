import Moist.MIR.Expr
import Moist.CEK.Builtins

namespace Moist.MIR

open Moist.Plutus.Term
open Moist.CEK (expectedArgs ExpectedArgs ArgKind)
open Moist.Plutus.Term (BuiltinFun)

/-! # Conservative Purity Analysis

isPure recognizes computations guaranteed to terminate successfully without
logging, assuming free variables denote already-evaluated values.

Atoms, lambdas, and delays are pure. Constructors and sequential lets are
pure only when their evaluated children are pure. A direct force of a delay
uses the body's purity. Builtin forces must match the expected type-force
protocol at every level.

Applications, cases, and Fix nodes are conservatively rejected. No argument
types or constructor arities are inferred here. In particular, a saturated
apparently total builtin can fail on wrong-type inputs, and an unknown force
may fail or execute a trace. The separate builtinRemainder helper recognizes
safe partial builtin states for eta and repeatability without weakening this
predicate's existing proof contract.
-/

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

  - Value forms (Var, Lit, Builtin, Lam, Delay) are pure.
  - `Force e` is pure when `e` is pure AND produces a forceable value
    (a `Delay` or a builtin expecting a type-force argument).
  - `App`, `Case`, and `Fix` are conservatively impure.
  - `Let` and `Constr` are pure when all evaluated sub-expressions are pure.
  - `Error`: always impure. -/
  def isPure : Expr → Bool
    | .Error => false
    | .Var _ | .Lit _ | .Builtin _ => true
    | .Lam _ _ | .Delay _ => true
    | .Fix _ _ => false
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
