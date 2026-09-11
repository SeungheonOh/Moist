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

private partial def validateCompilationInput (environment : List VarId)
    (expression : Expr) : Except String Unit := do
  match expression with
  | .Var binder =>
    if environment.any (· == binder) then pure ()
    else throw s!"unbound variable: {binder}"
  | .Lam binder body => validateCompilationInput (binder :: environment) body
  | .Fix binder body =>
    match body with
    | .Lam _ _ => validateCompilationInput (binder :: environment) body
    | _ => throw s!"Fix body must be a Lam, got: {repr body}"
  | .Let bindings body =>
    let mut available := environment
    for (binder, rhs, _) in bindings do
      validateCompilationInput available rhs
      available := binder :: available
    validateCompilationInput available body
  | .App function argument =>
    validateCompilationInput environment function
    validateCompilationInput environment argument
  | .Force body | .Delay body => validateCompilationInput environment body
  | .Constr _ fields => fields.forM (validateCompilationInput environment)
  | .Case scrutinee alternatives =>
    validateCompilationInput environment scrutinee
    alternatives.forM (validateCompilationInput environment)
  | _ => pure ()

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
