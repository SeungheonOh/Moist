import Moist.Plutus.Term

/-! # `closedAt` for UPLC terms (Verified copy)

Self-contained Boolean `closedAt` predicate used throughout the
`Verified` tower. Lives in its own file so `Contextual.lean`,
`Equivalence.lean`, etc. can import it without dragging in heavier
semantic machinery. -/

namespace Moist.Verified

open Moist.Plutus.Term

mutual
  /-- `closedAt d t` — every `.Var n` node in `t` satisfies `n ≤ d`. -/
  def closedAt (d : Nat) (t : Term) : Bool := match t with
    | .Var n => decide (n ≤ d)
    | .Lam _ body => closedAt (d + 1) body
    | .Apply f x => closedAt d f && closedAt d x
    | .Force e | .Delay e => closedAt d e
    | .Constr _ args => closedAtList d args
    | .Case scrut alts => closedAt d scrut && closedAtList d alts
    | .Constant _ | .Builtin _ | .Error => true
  termination_by sizeOf t

  def closedAtList (d : Nat) (ts : List Term) : Bool := match ts with
    | [] => true
    | t :: rest => closedAt d t && closedAtList d rest
  termination_by sizeOf ts
end

end Moist.Verified
