import Moist.MIR.Optimize.Advanced.Facts

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! Conservative post-success Boolean result summaries. Recursive summaries
are checked with unknown formal parameters, never specialized using one call's
argument types. The recursive hypothesis applies only to saturated calls.
It describes finite successful evaluation, not termination or purity.
-/

private def resultParameters : Expr → List VarId × Expr
  | .Lam binder body =>
    let (parameters, result) := resultParameters body
    (binder :: parameters, result)
  | expression => ([], expression)

private def booleanResultCore : Nat → List (VarId × Expr) → List (VarId × Nat) → Expr → Bool
  | 0, _, _, _ => false
  | fuel + 1, environment, summaries, expression =>
    let recur := booleanResultCore fuel environment summaries
    match expression with
    | .Lit (.Bool _, .AtomicType .TypeBool) | .Error => true
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any (fun entry => recur entry.2)
    | .Let bindings body =>
      let environment' := bindings.foldl (fun available (binder, rhs, _) => (binder, rhs) :: available) environment
      booleanResultCore fuel environment' summaries body
    | .Case _ alternatives => !alternatives.isEmpty && alternatives.all recur
    | .Force body =>
      match resolveHead fuel environment body with
      | .Delay delayed => recur delayed
      | .App (.App (.App selector _) (.Delay first)) (.Delay second) =>
        (selector == .Force (.Builtin .IfThenElse) ||
          selector == .Force (.Force (.Builtin .ChooseList))) && recur first && recur second
      | _ => false
    | .App function _ =>
      let resolved := resolveHead fuel environment function
      let builtinResult := (builtinProtocolAfterSuccess resolved).any fun (builtin, remaining) =>
        remaining.head == .argV && remaining.isFinal && booleanBuiltin builtin
      if builtinResult then true else
        let (head, arguments) := applicationSpine (resolveHead fuel environment expression)
        match head with
        | .Var binder => (summaries.find? (fun entry => entry.1 == binder)).any (fun entry => entry.2 == arguments.length)
        | .Fix recursive body =>
          let (parameters, result) := resultParameters body
          let hidden := recursive :: parameters
          let available := environment.filter (fun entry => !hidden.contains entry.1)
          let inherited := summaries.filter (fun entry => !hidden.contains entry.1)
          !parameters.isEmpty && parameters.length == arguments.length &&
            booleanResultCore fuel available ((recursive, parameters.length) :: inherited) result
        | .Lam _ _ =>
          let (parameters, result) := resultParameters head
          let available := environment.filter (fun entry => !parameters.contains entry.1)
          let inherited := summaries.filter (fun entry => !parameters.contains entry.1)
          parameters.length == arguments.length &&
            booleanResultCore fuel ((parameters.zip arguments).reverse ++ available) inherited result
        | _ => false
    | _ => false

def knownBooleanResult (fuel : Nat) (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  booleanResultCore fuel environment [] expression

end Moist.MIR.Advanced
