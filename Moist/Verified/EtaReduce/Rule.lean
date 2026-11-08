import Moist.Verified.EtaReduce.Local
import Moist.Verified.MIR

variable [sv : Moist.CEK.SemVariant]

/-! # The MIR eta rule

`λx. f x ⊑ f` at the MIR level when `x` is not free in `f` and `f` is a
callable value (`isCallableValue`): a lambda, or an unsaturated builtin state
with pure arguments whose next expected argument is a value.
-/

namespace Moist.Verified.EtaReduce

open Moist.MIR (Expr VarId expandFix lowerTotal lowerTotalExpr freeVars isCallableValue
  builtinRemainder)
open Moist.Verified.MIR (MIRCtxRefines lowerTotal_closedAt)

omit sv in
theorem isCallableValue_expandFix (f : Expr) (callable : isCallableValue f = true) :
    isCallableValue (expandFix f) = true := by
  by_cases lambda : ∃ x body, f = .Lam x body
  · obtain ⟨x, body, rfl⟩ := lambda
    simp [expandFix, isCallableValue]
  · have remainder : (builtinRemainder f).any (·.head == .argV) = true := by
      unfold isCallableValue at callable
      split at callable
      · exact absurd ⟨_, _, rfl⟩ lambda
      · exact callable
    cases remaining : builtinRemainder f with
    | none => simp [remaining] at remainder
    | some state =>
      have expanded := BuiltinState.builtinRemainder_expandFix f state remaining
      rw [remaining] at remainder
      unfold isCallableValue
      split
      · rfl
      · rw [expanded]; exact remainder

omit sv in
theorem lowerTotalExpr_eta (env : List VarId) {x y : VarId} (same : (x == y) = true)
    (f : Expr) :
    lowerTotalExpr env (.Lam x (.App f (.Var y))) =
      (lowerTotal (x :: env) (expandFix f)).map
        (fun body => .Lam 0 (.Apply body (.Var 1))) := by
  have lookup : Moist.MIR.envLookupT (x :: env) y = some 0 := by
    simp [Moist.MIR.envLookupT, Moist.MIR.envLookupT.go, same]
  simp only [lowerTotalExpr, expandFix, lowerTotal, lookup, Option.bind_eq_bind]
  cases lowerTotal (x :: env) (expandFix f) <;> rfl

/-- Eta reduction of a callable head. -/
theorem eta_mirCtxRefines {x y : VarId} {f : Expr} (same : (x == y) = true)
    (unused : (freeVars f).contains x = false) (callable : isCallableValue f = true) :
    MIRCtxRefines (.Lam x (.App f (.Var y))) f := by
  intro env
  have unused' := Moist.MIR.expandFix_freeVars_not_contains f x unused
  rw [lowerTotalExpr_eta env same]
  cases lowered : lowerTotalExpr env f with
  | none =>
    have none' : lowerTotal (x :: env) (expandFix f) = none :=
      Moist.MIR.lowerTotal_prepend_unused_none env x _ unused' lowered
    simp [none']
  | some F =>
    have shifted := Moist.MIR.lowerTotal_prepend_unused env x _ unused' F lowered
    rw [shifted]
    refine ⟨fun _ => rfl, ?_⟩
    simp only [Option.map_some]
    refine eta_ctxRefines env.length F (lowerTotal_closedAt env _ F lowered) ?_
    intro ρ sized
    exact BuiltinState.isCallableValue_returns (expandFix f) env F
      (isCallableValue_expandFix f callable) lowered ρ sized

end Moist.Verified.EtaReduce
