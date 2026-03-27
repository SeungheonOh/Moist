import Moist.CEK.Builtins
import Moist.Plutus.Term

namespace Moist.CEK

open Moist.Plutus.Term

instance : Inhabited Term where default := .Error

/-! # CekValue → Term Readback

Converts a CEK machine value back to a UPLC Term for comparison
with expected conformance test outputs.

## Closure readback

For VLam and VDelay, the body may contain free de Bruijn indices
that reference the captured environment. We substitute these during
readback to produce a closed term.
-/

/-- Shift all free de Bruijn variables in a term by `delta`.
Variables bound at depth ≥ cutoff are free (from the environment). -/
partial def shiftTerm (delta : Int) (cutoff : Nat) : Term → Term
  | .Var n => if n > cutoff then .Var (Int.toNat (n + delta)) else .Var n
  | .Lam x body => .Lam x (shiftTerm delta (cutoff + 1) body)
  | .Apply f a => .Apply (shiftTerm delta cutoff f) (shiftTerm delta cutoff a)
  | .Force e => .Force (shiftTerm delta cutoff e)
  | .Delay e => .Delay (shiftTerm delta cutoff e)
  | .Constr tag args => .Constr tag (args.map (shiftTerm delta cutoff))
  | .Case scrut alts => .Case (shiftTerm delta cutoff scrut) (alts.map (shiftTerm delta cutoff))
  | t => t  -- Constant, Builtin, Error

/-- Substitute de Bruijn variable `idx` with `replacement` in `term`.
`replacement` is shifted appropriately when going under binders. -/
partial def substTerm (idx : Nat) (replacement : Term) : Term → Term
  | .Var n =>
    if n == idx then replacement
    else if n > idx then .Var (n - 1)
    else .Var n
  | .Lam x body => .Lam x (substTerm (idx + 1) (shiftTerm 1 0 replacement) body)
  | .Apply f a => .Apply (substTerm idx replacement f) (substTerm idx replacement a)
  | .Force e => .Force (substTerm idx replacement e)
  | .Delay e => .Delay (substTerm idx replacement e)
  | .Constr tag args => .Constr tag (args.map (substTerm idx replacement))
  | .Case scrut alts =>
    .Case (substTerm idx replacement scrut) (alts.map (substTerm idx replacement))
  | t => t

/-- Compare two ExpectedArgs for structural equality. -/
private def eqExpectedArgs : ExpectedArgs → ExpectedArgs → Bool
  | .one a, .one b => a == b
  | .more a ar, .more b br => a == b && eqExpectedArgs ar br
  | _, _ => false

/-- Compute the consumed argument steps (forces and values) by comparing
the full expected args against the remaining expected args.
Returns the list of ArgKinds consumed in application order. -/
private def consumedSteps (full remaining : ExpectedArgs) : List ArgKind :=
  if eqExpectedArgs full remaining then []
  else match full with
    | .one k => [k]
    | .more k rest => k :: consumedSteps rest remaining

mutual
  /-- Close a term body over a captured environment.
  Substitutes environment values (readback'd to terms) for free de Bruijn indices.
  `depth` = number of binders above the body (1 for VLam, 0 for VDelay). -/
  partial def closeOver (body : Term) (env : CekEnv) (depth : Nat) : Term :=
    match env with
    | .nil => body
    | .cons v rest =>
      let vTerm := readbackValue v
      let body' := substTerm (depth + 1) vTerm body
      closeOver body' rest depth

  /-- Reconstruct a term from consumed steps, applying forces and accumulated args.
  `steps` is the list of consumed ArgKinds in application order.
  `args` is the accumulated argument list in application order (already reversed). -/
  partial def reconstructBuiltin (t : Term) (steps : List ArgKind) (args : List CekValue) : Term :=
    match steps with
    | [] => t
    | .argQ :: rest => reconstructBuiltin (.Force t) rest args
    | .argV :: rest => match args with
      | a :: as => reconstructBuiltin (.Apply t (readbackValue a)) rest as
      | [] => t  -- should not happen with well-formed builtins

  /-- Convert a CekValue to a closed UPLC Term. -/
  partial def readbackValue : CekValue → Term
    | .VCon c => .Constant (c, constType c)
    | .VLam body env =>
      let body' := closeOver body env 1
      .Lam 0 body'
    | .VDelay body env =>
      let body' := closeOver body env 0
      .Delay body'
    | .VConstr tag fields =>
      .Constr tag (fields.map readbackValue)
    | .VBuiltin b args ea =>
      let steps := consumedSteps (expectedArgs b) ea
      -- args is in reversed order (most recent first), reverse for application order
      reconstructBuiltin (.Builtin b) steps args.reverse
end

/-! ## Structural Term Comparison

Compare two de Bruijn terms structurally (no alpha-equivalence needed
since both are in de Bruijn form). -/

mutual
  partial def termEq : Term → Term → Bool
    | .Var a, .Var b => a == b
    | .Constant (c1, _), .Constant (c2, _) => c1 == c2
    | .Builtin a, .Builtin b => a == b
    | .Lam _ body1, .Lam _ body2 => termEq body1 body2
    | .Apply f1 a1, .Apply f2 a2 => termEq f1 f2 && termEq a1 a2
    | .Force e1, .Force e2 => termEq e1 e2
    | .Delay e1, .Delay e2 => termEq e1 e2
    | .Constr t1 args1, .Constr t2 args2 =>
      t1 == t2 && termListEq args1 args2
    | .Case s1 alts1, .Case s2 alts2 =>
      termEq s1 s2 && termListEq alts1 alts2
    | .Error, .Error => true
    | _, _ => false

  partial def termListEq : List Term → List Term → Bool
    | [], [] => true
    | a :: as, b :: bs => termEq a b && termListEq as bs
    | _, _ => false
end

end Moist.CEK
