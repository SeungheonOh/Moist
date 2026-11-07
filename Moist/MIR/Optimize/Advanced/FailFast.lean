import Moist.MIR.Optimize.Advanced.Shapes
import Moist.MIR.Optimize.PreLower

namespace Moist.MIR.Advanced

open Moist.Plutus.Term
open Moist.CEK (ExpectedArgs expectedArgs)

/-! # Fail-fast reordering

Reject paths should not pay for work whose result they never use. A strict
binding that a check does not mention is moved into the check's
non-failing alternatives:

  `let x = e in case c alts  ⟶  case c [if alt = error then error else let x = e in alt]`

The check `c` must halt or error in every environment (`terminates`), since
the target evaluates it first: if `e` errors, the source errors, and so does
the target once `c` has returned. Divergence of `e` imposes no obligation
under halting/error refinement. Neither the binding nor the
check may contain `Trace`, so no trace is dropped, duplicated or reordered.
A binding is only moved when exactly one alternative keeps it, so no code is
duplicated.

`terminates` accepts values, `error`, constructors, cases whose alternatives
are safe for any number of fields, strict bindings, saturated or partial
builtin applications that never over-apply, and the
`force (ifThenElse c (delay a) (delay b))` idiom. `inert` additionally
guarantees that a returned value is a constant or a constructor, so applying
it to further arguments errors.
-/

/-- Number of arguments (type forces and values) a builtin takes. -/
def argCount : ExpectedArgs → Nat
  | .one _ => 1
  | .more _ rest => argCount rest + 1

def builtinArity (b : BuiltinFun) : Nat := argCount (expectedArgs b)

/-- Builtins whose result may be one of their arguments. -/
def passThroughBuiltin : BuiltinFun → Bool
  | .IfThenElse | .ChooseUnit | .Trace | .ChooseData | .ChooseList | .MkCons => true
  | _ => false

/-- The parts of `force (ifThenElse c (delay a) (delay b))` below the force. -/
def iteView : Expr → Option (Expr × Expr × Expr)
  | .App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay a)) (.Delay b) => some (c, a, b)
  | _ => none

theorem iteView_some {e c a b : Expr} (h : iteView e = some (c, a, b)) :
    e = .App (.App (.App (.Force (.Builtin .IfThenElse)) c) (.Delay a)) (.Delay b) := by
  unfold iteView at h
  split at h
  · cases h; rfl
  · cases h

theorem iteView_sizeOf {e c a b : Expr} (h : iteView e = some (c, a, b)) :
    sizeOf c < sizeOf e ∧ sizeOf a < sizeOf e ∧ sizeOf b < sizeOf e := by
  rw [iteView_some h]
  simp only [Expr.App.sizeOf_spec, Expr.Force.sizeOf_spec, Expr.Delay.sizeOf_spec]
  omega

theorem delayBody_sizeOf {e body : Expr} (h : delayBody e = some body) : sizeOf body < sizeOf e := by
  unfold delayBody at h
  split at h
  · cases h; simp only [Expr.Delay.sizeOf_spec]; omega
  · cases h

/-- Whether a spine with this head and count may take one more argument
    (`saturate = false`) or is exactly saturated by it and returns a
    constant (`saturate = true`). -/
def spineAccepts (saturate : Bool) : Option (BuiltinFun × Nat) → Bool
  | some (b, n) =>
    if saturate then decide (n + 1 = builtinArity b) && !passThroughBuiltin b
    else decide (n + 1 ≤ builtinArity b)
  | none => false

mutual
  /-- The builtin at the head of a spine of forces and applications whose
      arguments terminate, with the number of forces and arguments. -/
  def spineHead : Expr → Option (BuiltinFun × Nat)
    | .Builtin b => some (b, 0)
    | .Force e => (spineHead e).map fun r => (r.1, r.2 + 1)
    | .App f a => if terminates a then (spineHead f).map fun r => (r.1, r.2 + 1) else none
    | _ => none
  termination_by e => (sizeOf e, 0)

  /-- Evaluation halts or errors in every environment. -/
  def terminates : Expr → Bool
    | .Var _ | .Lit _ | .Builtin _ | .Lam _ _ | .Delay _ | .Error => true
    | .Fix _ _ => false
    | .Constr _ fields => terminatesList fields
    | .Case scrutinee alternatives => terminates scrutinee && altsSafe alternatives
    | .Let bindings body => terminatesBinds bindings && terminates body
    | .Force e =>
      match _h₁ : delayBody e with
      | some body => terminates body
      | none =>
        match _h₂ : iteView e with
        | some (c, a, b) => terminates c && terminates a && terminates b
        | none => spineAccepts false (spineHead e)
    | .App f a => terminates a && spineAccepts false (spineHead f)
  termination_by e => (sizeOf e, 0)
  decreasing_by
    all_goals first
      | (have := delayBody_sizeOf _h₁; simp only [Expr.Force.sizeOf_spec]; omega)
      | (have := iteView_sizeOf _h₂; simp only [Expr.Force.sizeOf_spec]; omega)
      | (simp_wf; omega)

  /-- Evaluation errors, or returns a constant or a constructor. -/
  def inert : Expr → Bool
    | .Lit _ | .Error => true
    | .Constr _ fields => terminatesList fields
    | .Case scrutinee alternatives => terminates scrutinee && inertList alternatives
    | .Let bindings body => terminatesBinds bindings && inert body
    | .Force e =>
      match _h₁ : delayBody e with
      | some body => inert body
      | none =>
        match _h₂ : iteView e with
        | some (c, a, b) => terminates c && inert a && inert b
        | none => spineAccepts true (spineHead e)
    | .App f a => terminates a && spineAccepts true (spineHead f)
    | _ => false
  termination_by e => (sizeOf e, 0)
  decreasing_by
    all_goals first
      | (have := delayBody_sizeOf _h₁; simp only [Expr.Force.sizeOf_spec]; omega)
      | (have := iteView_sizeOf _h₂; simp only [Expr.Force.sizeOf_spec]; omega)
      | (simp_wf; omega)

  /-- An alternative terminates whatever number of fields it is applied to. -/
  def altSafe : Expr → Bool
    | .Lam _ body => altSafe body
    | e => inert e
  termination_by e => (sizeOf e, 1)

  def terminatesList : List Expr → Bool
    | [] => true
    | e :: rest => terminates e && terminatesList rest
  termination_by es => (sizeOf es, 0)

  def inertList : List Expr → Bool
    | [] => true
    | e :: rest => inert e && inertList rest
  termination_by es => (sizeOf es, 0)

  def altsSafe : List Expr → Bool
    | [] => true
    | e :: rest => altSafe e && altsSafe rest
  termination_by es => (sizeOf es, 0)

  def terminatesBinds : List (VarId × Expr × Bool) → Bool
    | [] => true
    | (_, rhs, _) :: rest => terminates rhs && terminatesBinds rest
  termination_by bs => (sizeOf bs, 0)
end

/-- `Trace` does not occur. -/
def traceFree : Expr → Bool
  | .Builtin b => b != .Trace
  | .Var _ | .Lit _ | .Error => true
  | .Lam _ body | .Fix _ body | .Force body | .Delay body => traceFree body
  | .App f a => traceFree f && traceFree a
  | .Constr _ fields => fields.attach.all fun ⟨field, _⟩ => traceFree field
  | .Case scrutinee alternatives =>
    traceFree scrutinee && alternatives.attach.all fun ⟨alternative, _⟩ => traceFree alternative
  | .Let bindings body =>
    (bindings.attach.all fun ⟨(_, rhs, _), _⟩ => traceFree rhs) && traceFree body
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)
    | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this; omega)

def isErrorExpr : Expr → Bool
  | .Error => true
  | _ => false

/-- A check that the binding `x = rhs` may be moved below. -/
def sinkCheck (x : VarId) (rhs scrutinee : Expr) (alternatives : List Expr) : Bool :=
  !(freeVars scrutinee).contains x && terminates scrutinee && traceFree scrutinee &&
    traceFree rhs && alternatives.any isErrorExpr &&
    decide ((alternatives.filter fun a => !isErrorExpr a).length ≤ 1)

/-- Move `x = rhs` into the alternatives of the check `body`, and further
    into the checks those alternatives start with. -/
def sinkInto (x : VarId) (rhs : Expr) (erased : Bool) (body : Expr) : Expr :=
  match body with
  | .Case scrutinee alternatives =>
    if sinkCheck x rhs scrutinee alternatives then
      .Case scrutinee (alternatives.attach.map fun ⟨a, _⟩ =>
        if isErrorExpr a then .Error else sinkInto x rhs erased a)
    else .Let [(x, rhs, erased)] body
  | _ => .Let [(x, rhs, erased)] body
termination_by sizeOf body
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)

/-- `x = rhs` is followed directly by a check it may move below. -/
def reachesCheck (x : VarId) (rhs : Expr) : Expr → Bool
  | .Case scrutinee alternatives => sinkCheck x rhs scrutinee alternatives
  | _ => false

/-- Bottom-up walk; every single binding tries to sink into its body. -/
def failFastWalk (expression : Expr) : Expr :=
  match expression with
  | .Let [] body => failFastWalk body
  | .Let ((x, rhs, erased) :: rest) body =>
    let rhs' := failFastWalk rhs
    let body' := failFastWalk (.Let rest body)
    if reachesCheck x rhs' body' then sinkInto x rhs' erased body'
    else .Let [(x, rhs', erased)] body'
  | .Lam x body => .Lam x (failFastWalk body)
  | .Fix f body => .Fix f (failFastWalk body)
  | .App f a => .App (failFastWalk f) (failFastWalk a)
  | .Force body => .Force (failFastWalk body)
  | .Delay body => .Delay (failFastWalk body)
  | .Constr tag fields => .Constr tag (fields.attach.map fun ⟨field, _⟩ => failFastWalk field)
  | .Case scrutinee alternatives =>
    .Case (failFastWalk scrutinee) (alternatives.attach.map fun ⟨a, _⟩ => failFastWalk a)
  | .Var _ | .Lit _ | .Builtin _ | .Error => expression
termination_by exprSize expression
decreasing_by
  all_goals first
    | (simp only [exprSize]; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos rhs; omega)

/-- Fail-fast reordering on a binder-hygienic copy of the program, followed by
    pre-lowering inlining of the moved single-use bindings. -/
def failFast (expression : Expr) : Expr :=
  let prepared := uniqueOptimizationBinders expression
  preLowerInlineExpr (if wellScoped prepared then failFastWalk prepared else prepared)

end Moist.MIR.Advanced
