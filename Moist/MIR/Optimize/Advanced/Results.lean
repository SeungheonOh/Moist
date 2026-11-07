import Moist.MIR.Optimize.Advanced.Facts

namespace Moist.MIR.Advanced

open Moist.Plutus.Term

/-! Conservative post-success Boolean result summaries. Recursive summaries
are checked with unknown formal parameters, never specialized using one call's
argument types. The recursive hypothesis applies only to saturated calls.
It describes finite successful evaluation, not termination or purity.
Application heads are read from the application itself, so a summarized
function and its arguments share the scope of the analysed expression.
A saturated call of a `let`-bound lambda or Fix is checked the same way, with
the body read in the scope of its binding and its parameters unknown. A case
alternative may bind fields only up to the number the scrutinee is known to
supply; a longer telescope would return a partial application.
-/

def resultParameters : Expr → List VarId × Expr
  | .Lam binder body =>
    let (parameters, result) := resultParameters body
    (binder :: parameters, result)
  | expression => ([], expression)

/-- Lower bounds on the number of fields a `case` on the scrutinee passes to
    each alternative, by constructor index: a list delivers two fields to its
    cons alternative and none to its nil alternative, and the pair produced by
    `unConstrData` delivers two fields. Unknown scrutinees promise nothing. -/
def scrutineeFieldCounts (fuel : Nat) (environment : List (VarId × Expr)) (scrutinee : Expr) : List Nat :=
  if knownList fuel environment scrutinee then [2, 0]
  else if constructorPair fuel environment scrutinee then [2] else []

def booleanResultCore : Nat → List (VarId × Expr) → List (VarId × Nat) → Expr → Bool
  | 0, _, _, _ => false
  | fuel + 1, environment, summaries, expression =>
    let recur := booleanResultCore fuel environment summaries
    match expression with
    | .Lit (.Bool _, .AtomicType .TypeBool) | .Error => true
    | .Var binder =>
      (environment.find? (fun entry => entry.1 == binder)).any (fun entry => recur entry.2)
    | .Let bindings body =>
      let environment' := bindings.foldl (fun available (binder, rhs, _) => (binder, rhs) :: available) environment
      let bound := bindings.map (·.1)
      booleanResultCore fuel environment' (summaries.filter (fun entry => !bound.contains entry.1)) body
    | .Case scrutinee alternatives =>
      let counts := scrutineeFieldCounts fuel environment scrutinee
      !alternatives.isEmpty && alternatives.zipIdx.all fun (alternative, index) =>
        let (parameters, result) := resultParameters alternative
        decide (parameters.length ≤ counts.getD index 0) &&
          booleanResultCore fuel (environment.filter (fun entry => !parameters.contains entry.1))
            (summaries.filter (fun entry => !parameters.contains entry.1)) result
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
        let (head, arguments) := applicationSpine expression
        match head with
        | .Var binder =>
          (summaries.find? (fun entry => entry.1 == binder)).any (fun entry => entry.2 == arguments.length) ||
            match environment.find? (fun entry => entry.1 == binder) with
            | some (_, .Lam parameter body) =>
              let (parameters, result) := resultParameters (.Lam parameter body)
              parameters.length == arguments.length &&
                booleanResultCore fuel (environment.filter (fun entry => !parameters.contains entry.1))
                  (summaries.filter (fun entry => !parameters.contains entry.1)) result
            | some (_, .Fix recursive body) =>
              let (parameters, result) := resultParameters body
              let hidden := recursive :: parameters
              !parameters.isEmpty && parameters.length == arguments.length &&
                booleanResultCore fuel (environment.filter (fun entry => !hidden.contains entry.1))
                  ((recursive, parameters.length) ::
                    summaries.filter (fun entry => !hidden.contains entry.1)) result
            | _ => false
        | .Fix recursive body =>
          let (parameters, result) := resultParameters body
          let hidden := recursive :: parameters
          let available := environment.filter (fun entry => !hidden.contains entry.1)
          let inherited := summaries.filter (fun entry => !hidden.contains entry.1)
          !parameters.isEmpty && parameters.length == arguments.length &&
            booleanResultCore fuel available ((recursive, parameters.length) :: inherited) result
        | .Lam binder body =>
          let (parameters, result) := resultParameters (.Lam binder body)
          let available := environment.filter (fun entry => !parameters.contains entry.1)
          let inherited := summaries.filter (fun entry => !parameters.contains entry.1)
          parameters.length == arguments.length &&
            booleanResultCore fuel ((parameters.zip arguments).reverse ++ available) inherited result
        | _ => false
    | _ => false

def knownBooleanResult (fuel : Nat) (environment : List (VarId × Expr)) (expression : Expr) : Bool :=
  booleanResultCore fuel environment [] expression

end Moist.MIR.Advanced
