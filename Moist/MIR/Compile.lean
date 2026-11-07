import Moist.MIR.Optimize
import Moist.MIR.Lower
import Moist.MIR.FromUPLC

namespace Moist.MIR

/-! Shared production compiler entry point. Validate lexical scope and Fix
structure before dead-code removal can hide invalid input. Allocation trade-offs
run after Fix lowering and are never followed by an inverse case-reduction pass.
Invariant recursive parameters move outside workers before ANF obscures direct
recursive application spines. Post-success result summaries enable checked
Boolean simplification within the normal optimizer, without erasing producers. -/

mutual
  def validateCompilationInput (environment : List VarId)
      (expression : Expr) : Except String Unit :=
    match expression with
    | .Var binder =>
      if environment.any (· == binder) then pure ()
      else throw s!"unbound variable: {binder}"
    | .Lam binder body => validateCompilationInput (binder :: environment) body
    | .Fix binder (.Lam parameter body) =>
      validateCompilationInput (binder :: environment) (.Lam parameter body)
    | .Fix _ body => throw s!"Fix body must be a Lam, got: {repr body}"
    | .Let bindings body => validateCompilationBindings environment bindings body
    | .App function argument => do
      validateCompilationInput environment function
      validateCompilationInput environment argument
    | .Force body | .Delay body => validateCompilationInput environment body
    | .Constr _ fields => validateCompilationList environment fields
    | .Case scrutinee alternatives => do
      validateCompilationInput environment scrutinee
      validateCompilationList environment alternatives
    | _ => pure ()
  termination_by sizeOf expression

  def validateCompilationList (environment : List VarId) (expressions : List Expr) :
      Except String Unit :=
    match expressions with
    | [] => pure ()
    | expression :: rest => do
      validateCompilationInput environment expression
      validateCompilationList environment rest
  termination_by sizeOf expressions

  def validateCompilationBindings (environment : List VarId)
      (bindings : List (VarId × Expr × Bool)) (body : Expr) : Except String Unit :=
    match bindings with
    | [] => validateCompilationInput environment body
    | (binder, rhs, _) :: rest => do
      validateCompilationInput environment rhs
      validateCompilationBindings (binder :: environment) rest body
  termination_by sizeOf bindings + sizeOf body
end

def prepareForLowering (expression : Expr) (optFresh : Nat := 1000)
    (lowerFresh : Nat := 5000) : Expr :=
  Advanced.structural (Advanced.preLower (preLowerInlineExpr
    (optimizeExpr (Advanced.staticArguments expression) optFresh) lowerFresh))

def compileOptimized (expression : Expr) (optFresh : Nat := 1000)
    (lowerFresh : Nat := 5000) (options : Advanced.Options := {})
    : Except String Moist.Plutus.Term.Term := do
  validateCompilationInput [] expression
  let term ← lowerExpr (prepareForLowering expression optFresh lowerFresh) (lowerFresh + 1000)
  if options.packApplications || options.shareBuiltinStates || options.poolConstants then
    lowerExpr (Advanced.finish (liftUPLC term) options) (lowerFresh + 1000)
  else pure term

end Moist.MIR
