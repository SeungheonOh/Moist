import Test.MIR.Helpers
import Moist.MIR.Lower
import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Pretty
import Test.Framework

/-! Recursive calls lower to `[[s s] a]`: the production encoding of `Fix`
must behave exactly like the certified redex encoding of `lowerTotalExpr`,
including trace order and failures, and must not take more machine steps. -/

namespace Test.MIR.Lower.FixCalls

open Moist.MIR
open Moist.Plutus.Term
open Test.MIR
open Test.Framework

private def recursive := sourceVar 900
private def counter := sourceVar 901
private def other := sourceVar 902
private def alias := sourceVar 903
private def helper := sourceVar 904
private def inner := sourceVar 905
private def argument := sourceVar 906
private def partialCall := sourceVar 907

private def traced (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def lessOrZero (value : Expr) : Expr :=
  .App (.App (.Builtin .LessThanEqualsInteger) value) (intLit 0)

private def minusOne (value : Expr) : Expr :=
  .App (.App (.Builtin .SubtractInteger) value) (intLit 1)

private def plus (left right : Expr) : Expr :=
  .App (.App (.Builtin .AddInteger) left) right

/-- `if counter ≤ 0 then base else step`, as a `case` on the Bool. -/
private def countdown (step base : Expr) : Expr :=
  .Case (lessOrZero (.Var counter)) [step, base]

/-- Sum `counter + … + 1`, tracing every recursive argument. -/
private def sumTo : Expr :=
  .Fix recursive (.Lam counter (countdown
    (plus (.Var counter) (.App (.Var recursive) (traced "argument" (minusOne (.Var counter)))))
    (intLit 0)))

/-- Two curried arguments, with a partial application bound before use. -/
private def twoArguments : Expr :=
  .Fix recursive (.Lam counter (.Lam other (countdown
    (.Let [(partialCall, .App (.Var recursive) (minusOne (.Var counter)), false)]
      (.App (.Var partialCall) (traced "other" (plus (.Var other) (.Var counter)))))
    (.Var other))))

/-- The recursive binder used as a value, then called through an alias. -/
private def aliased : Expr :=
  .Fix recursive (.Lam counter (countdown
    (.Let [(alias, .Var recursive, false)]
      (plus (intLit 2) (.App (.Var alias) (minusOne (.Var counter)))))
    (intLit 1)))

/-- The recursive binder passed to a higher-order helper. -/
private def higherOrder : Expr :=
  .Let [(helper, .Lam alias (.Lam argument (traced "helper" (.App (.Var alias) (.Var argument)))), false)]
    (.Fix recursive (.Lam counter (countdown
      (plus (intLit 3) (.App (.App (.Var helper) (.Var recursive)) (minusOne (.Var counter))))
      (intLit 0))))

/-- A recursive call under a delay, forced later. -/
private def delayed : Expr :=
  .Fix recursive (.Lam counter (countdown
    (.Let [(alias, .Delay (.App (.Var recursive) (minusOne (.Var counter))), false)]
      (traced "before" (plus (intLit 1) (.Force (.Var alias)))))
    (intLit 0)))

/-- An inner recursive function that calls the outer one. -/
private def nested : Expr :=
  .Fix recursive (.Lam counter (countdown
    (.App
      (.Fix inner (.Lam other (countdown
        (.App (.Var recursive) (minusOne (.Var counter)))
        (.App (.Var inner) (minusOne (.Var other))))))
      (intLit 2))
    (intLit 7)))

/-- The argument of a recursive call fails after a trace. -/
private def failingArgument : Expr :=
  .Fix recursive (.Lam counter (countdown
    (.App (.Var recursive) (traced "doomed" .Error))
    (intLit 0)))

private def stepMessages : Moist.CEK.State → List String
  | .ret (.funV (.VBuiltin .Trace [.VCon (.String message)] remaining) :: _) _ =>
    if remaining.head == .argV && remaining.isFinal then [message] else []
  | .ret (.applyArg _ :: _) (.VBuiltin .Trace [.VCon (.String message)] remaining) =>
    if remaining.head == .argV && remaining.isFinal then [message] else []
  | _ => []

/-- Result, traces and machine steps of a closed term. -/
private def run : Nat → Nat → Moist.CEK.State → List String →
    Except String (String × List String × Nat)
  | 0, _, _, _ => .error "step limit exceeded"
  | fuel + 1, count, state, messages =>
    match state with
    | .halt value =>
      .ok (Moist.Plutus.Pretty.prettyTerm (Moist.CEK.readbackValue value), messages, count)
    | .error => .ok ("failure", messages, count)
    | _ => run fuel (count + 1) (Moist.CEK.step state) (messages ++ stepMessages state)

private def observe (label : String) (term : Term) : IO (String × List String × Nat) :=
  match run 200000 0 (.compute [] .nil term) [] with
  | .ok result => pure result
  | .error message => throw (IO.userError s!"{label}: {message}")

private def compareEncodings (label : String) (expression : Expr)
    (fewerSteps : Bool := true) : IO Unit := do
  let production ← match lowerExpr expression with
    | .ok term => pure term
    | .error message => throw (IO.userError s!"{label}: {message}")
  let some certified := lowerTotalExpr [] expression
    | throw (IO.userError s!"{label}: lowerTotalExpr failed")
  let (result, traces, steps) ← observe label production
  let (result₀, traces₀, steps₀) ← observe label certified
  checkEq s!"{label}/result" result result₀
  checkEq s!"{label}/traces" traces traces₀
  if fewerSteps then
    check s!"{label}/steps {steps} < {steps₀}" (steps < steps₀)
  else
    check s!"{label}/steps {steps} ≤ {steps₀}" (steps ≤ steps₀)

def tests : TestTree := suite "fix_calls" do
  test "recursive_call_is_direct_self_application" do
    let expression := Expr.Fix recursive (.Lam counter (.App (.Var recursive) (.Var counter)))
    let expected : Term :=
      .Apply (.Lam 0 (.Apply (.Var 1) (.Var 1)))
        (.Lam 0 (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1))))
    match lowerExpr expression with
    | .ok term => checkEq "direct call" (Moist.Plutus.Pretty.prettyTerm term) (Moist.Plutus.Pretty.prettyTerm expected)
    | .error message => throw (IO.userError message)

  test "reference_under_binders_uses_shifted_self" do
    let expression := Expr.Fix recursive (.Lam counter (.Lam other
      (.App (.App (.Var recursive) (.Var other)) (.Var counter))))
    let expected : Term :=
      .Apply (.Lam 0 (.Apply (.Var 1) (.Var 1)))
        (.Lam 0 (.Lam 0 (.Lam 0
          (.Apply (.Apply (.Apply (.Var 3) (.Var 3)) (.Var 1)) (.Var 2)))))
    match lowerExpr expression with
    | .ok term => checkEq "curried direct call" (Moist.Plutus.Pretty.prettyTerm term) (Moist.Plutus.Pretty.prettyTerm expected)
    | .error message => throw (IO.userError message)

  test "production_encoding_matches_certified_encoding" do
    for input in [0, 1, 5] do
      let called := input > 0
      compareEncodings s!"sum/{input}" (.App sumTo (intLit input)) called
      compareEncodings s!"two/{input}"
        (.App (.App twoArguments (intLit input)) (intLit 10)) called
      compareEncodings s!"aliased/{input}" (.App aliased (intLit input)) false
      compareEncodings s!"higherOrder/{input}" (.App higherOrder (intLit input)) false
      compareEncodings s!"delayed/{input}" (.App delayed (intLit input)) called
      compareEncodings s!"nested/{input}" (.App nested (intLit input)) called
      compareEncodings s!"failing/{input}" (.App failingArgument (intLit input)) false

end Test.MIR.Lower.FixCalls
