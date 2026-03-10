import Moist.MIR.Expr

namespace Moist.MIR

/-! # Purity Analysis

Conservative analysis determining whether an expression is guaranteed to
evaluate without error or divergence. Used by optimization passes to decide
when it is safe to move, duplicate, or eliminate expressions.

## Design

An expression is **pure** if evaluating it always terminates successfully
(produces a value without raising an error). This is a conservative
approximation: some expressions we classify as impure may in fact be safe
at runtime, but we never classify a potentially-failing expression as pure.

### Pure expressions

- **Var, Lit, Builtin** -- atoms are already values; evaluating them is free.
- **Lam** -- building a closure never fails.
- **Delay** -- building a thunk never fails.
- **Fix** -- produces a recursive closure value (not evaluated yet).
- **Constr** with atom arguments -- in ANF, constructor arguments are always
  atoms (already evaluated), so constructing the node cannot fail.

### Impure expressions

- **App** -- applying a function may diverge or error (e.g. partial builtin
  application failing at runtime).
- **Force** -- forcing a non-Delay value is an error.
- **Case** -- evaluates the scrutinee and then a branch; either step can fail.
- **Let** -- evaluates bindings sequentially; any binding may fail.
- **Error** -- always fails.

## Examples

```
isPure (Var x)               = true   -- already a value
isPure (Lit (Integer 42, _)) = true   -- literal constant
isPure (Lam x (App (Var x) (Var x)))
                             = true   -- closure, body not evaluated yet
isPure (Delay (Error))       = true   -- thunk, body not evaluated yet
isPure (Constr 0 [Var a, Var b])
                             = true   -- constructor with atom args
isPure (App (Var f) (Var x)) = false  -- application may fail
isPure (Force (Var x))       = false  -- forcing may fail
isPure (Let [(v, e)] body)   = false  -- let evaluates bindings
isPure Error                 = false  -- always fails
```
-/

/-- Return `true` when evaluating the expression is guaranteed to succeed
(no error, no divergence). See the module doc comment for the full
classification and examples. -/
def isPure : Expr → Bool
  | .Var _ | .Lit _ | .Builtin _ => true
  | .Lam _ _ | .Delay _ | .Fix _ _ => true
  | .Constr _ args => args.all Expr.isAtom
  | .App _ _ | .Force _ | .Case _ _ | .Let _ _ | .Error => false

end Moist.MIR
