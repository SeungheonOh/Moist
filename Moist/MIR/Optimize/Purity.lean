import Moist.MIR.Expr

namespace Moist.MIR

/-! # Purity Analysis

Determines whether an expression is guaranteed to evaluate without error.
Used by optimization passes to decide when it is safe to move, duplicate,
or eliminate expressions.

## Design

The MIR is compiled from well-typed Lean, so type errors (applying a
non-function, forcing a non-delay, etc.) cannot occur at runtime. The two
sources of impurity are:

1. **Error** nodes -- always fail.
2. **Builtin application** -- a builtin applied to an argument may fail
   at runtime (e.g. `divideInteger x 0`). We cannot statically determine
   argument values, so any application whose head is a builtin (possibly
   wrapped in `Force`) is conservatively treated as impure.

### Value forms (body not evaluated at construction time)

- **Lam, Delay, Fix** -- building a closure/thunk never fails regardless
  of what the body contains.

### Evaluated positions

- **App f x** -- impure when the head function is a builtin (possibly
  Force-wrapped); otherwise pure when both `f` and `x` are pure.
- **Force e** -- pure when `e` is pure.
- **Case scrut alts** -- pure when scrutinee and all branches are pure.
- **Let binds body** -- pure when all binding RHS's and body are pure.
- **Constr tag args** -- pure when all args are pure.
- **Error** -- always impure.
-/

/-- Check whether `e` is a builtin, possibly wrapped in Force nodes
(from polymorphic instantiation). -/
private def isBuiltinHead : Expr → Bool
  | .Builtin _ => true
  | .Force e => isBuiltinHead e
  | _ => false

/-- Return `true` when evaluating the expression is guaranteed to succeed
(no error, no failing builtin application). -/
partial def isPure : Expr → Bool
  | .Error => false
  | .Var _ | .Lit _ | .Builtin _ => true
  | .Lam _ _ | .Delay _ | .Fix _ _ => true
  | .Constr _ args => args.all isPure
  | .App f x => !isBuiltinHead f && isPure f && isPure x
  | .Force e => isPure e
  | .Case scrut alts => isPure scrut && alts.all isPure
  | .Let binds body => binds.all (fun (_, rhs) => isPure rhs) && isPure body

end Moist.MIR
