import Moist.Plutus.Term

namespace Moist.CEK

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)

/-! # CEK Machine Values and Environment

Runtime values for the UPLC CEK machine, adapted for de Bruijn indexed terms.

Following the sc-fvt reference implementation (input-output-hk/sc-fvt staging branch)
but using positional environments instead of named lookups.

## de Bruijn Convention

`Term.Var n` refers to the variable bound `n` levels up (1-based).
`Var 1` is the innermost binding (head of environment).
-/

/-! ## Expected Builtin Arguments

Tracks remaining forces (type instantiations) and value arguments
needed before a builtin is fully saturated. Mirrors sc-fvt's
`ExpectedBuiltinArgs` / `ExpectedBuiltinArg`. -/

/-- A single expected argument: either a value (Apply) or a type force. -/
inductive ArgKind where
  | argV : ArgKind  -- expects a value via Apply
  | argQ : ArgKind  -- expects a type instantiation via Force
deriving Repr, BEq

/-- The remaining argument signature of a partially applied builtin.
`one` = final argument, `more` = at least one more after this. -/
inductive ExpectedArgs where
  | one  : ArgKind → ExpectedArgs
  | more : ArgKind → ExpectedArgs → ExpectedArgs
deriving Repr

namespace ExpectedArgs

/-- The kind of the next expected argument. -/
def head : ExpectedArgs → ArgKind
  | .one k => k
  | .more k _ => k

/-- Whether this is the final argument. -/
def isFinal : ExpectedArgs → Bool
  | .one _ => true
  | .more _ _ => false

/-- Pop the head, returning the remaining args. Only valid for non-final. -/
def tail : ExpectedArgs → Option ExpectedArgs
  | .one _ => none
  | .more _ rest => some rest

end ExpectedArgs

/-! ## CEK Values and Environment -/

mutual
  /-- Runtime value produced by the CEK machine. -/
  inductive CekValue where
    /-- Constant value (integer, bytestring, bool, unit, data, etc.). -/
    | VCon : Const → CekValue
    /-- Delayed computation (thunk): body + captured environment. -/
    | VDelay : Term → CekEnv → CekValue
    /-- Lambda closure: body + captured environment.
    The de Bruijn parameter is implicit — `Var 1` in body refers to
    the argument, higher indices shift into the captured env. -/
    | VLam : Term → CekEnv → CekValue
    /-- Fully evaluated constructor: tag + evaluated fields. -/
    | VConstr : Nat → List CekValue → CekValue
    /-- Partially applied builtin: function, accumulated args (reversed),
    and remaining expected arguments. -/
    | VBuiltin : BuiltinFun → List CekValue → ExpectedArgs → CekValue

  /-- Environment for de Bruijn indexed terms.
  A stack of values where `Var 1` = head, `Var 2` = second, etc. -/
  inductive CekEnv where
    | nil : CekEnv
    | cons : CekValue → CekEnv → CekEnv
end

namespace CekEnv

/-- Look up a de Bruijn index (1-based). Returns `none` if out of bounds. -/
def lookup : CekEnv → Nat → Option CekValue
  | .nil, _ => none
  | .cons _ _, 0 => none
  | .cons v _, 1 => some v
  | .cons _ rest, n + 1 => lookup rest n

/-- Extend environment with a new binding (becomes Var 1). -/
@[inline] def extend (env : CekEnv) (v : CekValue) : CekEnv :=
  .cons v env

end CekEnv

/-! ## Pretty Printing -/

mutual
  partial def CekValue.toString : CekValue → String
    | .VCon c => s!"VCon({repr c})"
    | .VDelay _ _ => "VDelay(..)"
    | .VLam _ _ => "VLam(..)"
    | .VConstr tag fields =>
      let fs := ", ".intercalate (fields.map CekValue.toString)
      s!"VConstr({tag}, [{fs}])"
    | .VBuiltin b args _ =>
      s!"VBuiltin({repr b}, args={args.length})"
end

instance : ToString CekValue where toString := CekValue.toString

end Moist.CEK
