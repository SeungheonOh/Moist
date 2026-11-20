import Moist.Plutus.DecidableEq
import Moist.Verified.ClosedAt

namespace Moist.MIR.RecursionPeeling

open Moist.Plutus.Term
open Moist.Verified (closedAt liftRename renameTerm shiftRename substTerm)

def selfApplication (body : Term) : Term := .Apply (.Lam 0 body) (.Lam 0 body)

def fixedPoint (body : Term) : Term :=
  .Apply (.Lam 0 (.Apply (.Var 1) (.Var 1))) (.Lam 0 body)

mutual
  /-- Count guarded self applications. Other references to the self binder make the worker ineligible. -/
  def recursiveUses (self : Nat) (guarded : Bool) : Term → Nat
    | .Var index => if index = self then 2 else 0
    | .Apply (.Var first) (.Var second) =>
      if first = self ∧ second = self then
        if guarded then 1 else 2
      else
        (if first = self then 2 else 0) + (if second = self then 2 else 0)
    | .Apply function argument => recursiveUses self guarded function + recursiveUses self guarded argument
    | .Lam _ body => recursiveUses (self + 1) guarded body
    | .Force body | .Delay body => recursiveUses self guarded body
    | .Constr _ fields => recursiveUsesList self guarded fields
    | .Case scrutinee branches => recursiveUses self guarded scrutinee + recursiveUsesList self true branches
    | _ => 0
  termination_by term => sizeOf term

  def recursiveUsesList (self : Nat) (guarded : Bool) : List Term → Nat
    | [] => 0
    | term :: rest => recursiveUses self guarded term + recursiveUsesList self guarded rest
  termination_by terms => sizeOf terms
end

/-- Substitution of a bound variable contracts one application on a peeled call spine. -/
def contractArgument (scope : Nat) (function argument : Term) : Term :=
  match function, argument with
  | .Lam 0 body, .Var index =>
    if 1 ≤ index ∧ index ≤ scope ∧ closedAt (scope + 1) body = true then
      substTerm 1 argument body
    else
      .Apply function argument
  | _, _ => .Apply function argument

mutual
  def peelSelf (steps scope : Nat) (worker : Term) (term : Term) : Term :=
    if term = selfApplication worker then
      match steps with
      | 0 => fixedPoint worker
      | n + 1 =>
        if closedAt (scope + 1) worker then
          peelSelf n scope worker (substTerm 1 (.Lam 0 worker) worker)
        else term
    else
      match term with
      | .Lam name body =>
        .Lam name (peelSelf steps (scope + 1) (renameTerm (liftRename (shiftRename 1)) worker) body)
      | .Apply function argument =>
        let function' := peelSelf steps scope worker function
        let argument' := peelSelf steps scope worker argument
        if function' = function then .Apply function' argument'
        else contractArgument scope function' argument'
      | .Force body => .Force (peelSelf steps scope worker body)
      | .Delay body => .Delay (peelSelf steps scope worker body)
      | .Constr tag fields => .Constr tag (peelSelfList steps scope worker fields)
      | .Case scrutinee branches =>
        .Case (peelSelf steps scope worker scrutinee) (peelSelfList steps scope worker branches)
      | _ => term
  termination_by (steps, sizeOf term)

  def peelSelfList (steps scope : Nat) (worker : Term) (terms : List Term) : List Term :=
    match terms with
    | [] => []
    | term :: rest => peelSelf steps scope worker term :: peelSelfList steps scope worker rest
  termination_by (steps, sizeOf terms)
end

def peelRoot (steps scope : Nat) (term : Term) : Term :=
  match steps, term with
  | n + 1, .Apply (.Lam 0 (.Apply (.Var 1) (.Var 1))) (.Lam 0 (.Lam name body)) =>
    if recursiveUses 2 false body = 1 then
      peelSelf (n + 1) scope (.Lam name body) (selfApplication (.Lam name body))
    else term
  | _, _ => term

mutual
  def peelTerm (steps scope : Nat) (term : Term) : Term :=
    peelRoot steps scope <| match term with
    | .Lam name body => .Lam name (peelTerm steps (scope + 1) body)
    | .Apply function argument => .Apply (peelTerm steps scope function) (peelTerm steps scope argument)
    | .Delay body => .Delay (peelTerm steps scope body)
    | .Force body => .Force (peelTerm steps scope body)
    | .Constr tag fields => .Constr tag (peelTermList steps scope fields)
    | .Case scrutinee branches => .Case (peelTerm steps scope scrutinee) (peelTermList steps scope branches)
    | _ => term
  termination_by sizeOf term

  def peelTermList (steps scope : Nat) (terms : List Term) : List Term :=
    match terms with
    | [] => []
    | term :: rest => peelTerm steps scope term :: peelTermList steps scope rest
  termination_by sizeOf terms
end

end Moist.MIR.RecursionPeeling

namespace Moist.MIR

open Moist.Plutus.Term
open Moist.Verified (closedAt)

/-- Peel the guarded entry iterations of eligible fixed points in lowered UPLC. -/
def peelRecursion (steps : Nat) (term : Term) : Term :=
  if steps ≠ 0 ∧ closedAt 0 term = true then RecursionPeeling.peelTerm steps 0 term else term

end Moist.MIR
