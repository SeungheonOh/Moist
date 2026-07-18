import Moist.CEK.Builtins

/-!
# Exact ground-builtin adapter

This module is the executable compiler's single boundary to the CEK builtin
implementation.  The symbolic compiler hands it literal `Const` arguments in
the CEK value-stack order (most recently applied/source-last argument first),
and receives one of three explicit results:

* `.value c` when CEK returns the constant `c`;
* `.error` when CEK reports a builtin failure; or
* `.deferred` if CEK ever returns a non-constant value.

The adapter deliberately calls `Moist.CEK.evalBuiltin` instead of duplicating
any builtin semantics.  A port can isolate its native implementation behind
this small data-only interface while preserving the argument-order contract.
The matching proof module, `Moist.SMT.Soundness.GroundBuiltin`, establishes
the exact correspondence with CEK used by compiler soundness.
-/

namespace Moist.SMT.Compiler.GroundBuiltin

open Moist.Plutus.Term (BuiltinFun Const)

/-- Result of trying to evaluate a fully literal builtin application.

`deferred` is distinct from `error`: it asks the symbolic compiler to use its
proved symbolic encoding, whereas `error` is the actual CEK runtime result.
-/
inductive Result where
  | value (constant : Const)
  | error
  | deferred

/-- Evaluate literal arguments in CEK stack order using the canonical CEK
builtin evaluator.  This is the only executable compiler definition that
calls `Moist.CEK.evalBuiltin` directly. -/
def evaluateStackArguments (builtin : BuiltinFun)
    (arguments : List Const) : Result :=
  match Moist.CEK.evalBuiltin builtin
      (arguments.map Moist.CEK.CekValue.VCon) with
  | some (.VCon constant) => .value constant
  | none => .error
  | some _ => .deferred

end Moist.SMT.Compiler.GroundBuiltin
