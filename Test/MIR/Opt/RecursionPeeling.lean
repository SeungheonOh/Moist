import Test.MIR.Opt.Soundness
import Moist.MIR.Tune
import Moist.Onchain
import Moist.Onchain.Prelude
import Moist.Plutus.DecidableEq

namespace Test.MIR.Opt.RecursionPeeling

open Moist.MIR Moist.Plutus.Term Test.Framework

private def recur := sourceVar 1
private def counter := sourceVar 2
private def ignored := sourceVar 3
private def captured := sourceVar 4

private def trace (message : String) (body : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace)) (.Lit (.String message, .AtomicType .TypeString))) body

private def minusOne : Expr := .App (.App (.Builtin .SubtractInteger) (.Var counter)) (intLit 1)

private def countdown (step : Expr) : Expr :=
  .Fix recur (.Lam counter
    (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Var counter)) (intLit 0)) [step, intLit 0]))

private def lower (expression : Expr) : IO Term :=
  IO.ofExcept (lowerExpr expression)

private def compile (worker : Expr) (depth : Nat) : IO Term :=
  IO.ofExcept (compileOptimized worker (options := { recursionPeelDepth := depth }))

private def call (worker : Term) (argument : Int) : Term :=
  .Apply worker (.Constant (.Integer argument, .AtomicType .TypeInteger))

private def compareRuns (baseline candidate : Term) (argument : Int) : IO Unit := do
  let before ← Soundness.tracedTermObservation (call baseline argument)
  let after ← Soundness.tracedTermObservation (call candidate argument)
  checkEq s!"result on {argument}" after.1 before.1
  check s!"trace order on {argument}: {repr after.2}" (after.2 == before.2)

open Moist.Onchain.Prelude in
@[onchain] def sumDown (n : Int) : Int :=
  if lessThanEqInteger n 0 then 0
  else addInteger n (sumDown (subtractInteger n 1))
termination_by n.toNat
decreasing_by simp_all [lessThanEqInteger, subtractInteger]; omega

private def frontendDefault : Term := compile! sumDown

set_option moist.optimize.recursionPeelDepth 5 in
private def frontendPeeled : Term := compile! sumDown

def tests : TestTree := suite "recursion peeling" do
  test "production option peels a traced countdown and keeps its fallback" do
    let worker := countdown (.App (.Var recur) (trace "recursive argument" minusOne))
    let baseline ← compile worker 0
    let candidate ← compile worker 5
    check "candidate differs from the production baseline" (decide (candidate ≠ baseline))
    for input in [-7, 0, 1, 5, 6, 17] do
      compareRuns baseline candidate input
    let malformed := Term.Constant (.Bool true, .AtomicType .TypeBool)
    let before ← Soundness.tracedTermObservation (.Apply baseline malformed)
    let after ← Soundness.tracedTermObservation (.Apply candidate malformed)
    checkEq "type error remains a failure" after.1 "failure"
    check "malformed input has the same trace" (after == before)

  test "recursive argument errors stay strict" do
    let step := Expr.App (.Var recur)
      (.App (.Lam ignored .Error) (trace "before failure" (intLit 4)))
    let baseline ← lower (countdown step)
    let candidate := peelRecursion 5 baseline
    check "peel reached the recursion" (decide (candidate ≠ baseline))
    compareRuns baseline candidate 0
    compareRuns baseline candidate 1
    let (result, messages) ← Soundness.tracedTermObservation (call candidate 1)
    checkEq "error remains a failure" result "failure"
    check "trace ran before the error" (messages == ["before failure"])

  test "guards preserve nonlinear and nonrecursive terms" do
    let twoCalls := Expr.App (.App (.Builtin .AddInteger) (.App (.Var recur) minusOne))
      (.App (.Var recur) minusOne)
    let nonlinear ← lower (countdown twoCalls)
    let identity ← lower (.Lam counter (.Var counter))
    check "depth zero is the identity" (decide (peelRecursion 0 nonlinear = nonlinear))
    check "a worker with two recursive occurrences is left alone" (decide (peelRecursion 5 nonlinear = nonlinear))
    check "nonrecursive function is unchanged" (decide (peelRecursion 5 identity = identity))

  test "peeled calls preserve a worker's outer binding" do
    let worker := Expr.Lam captured (.Fix recur (.Lam counter
      (.Case (.App (.App (.Builtin .LessThanEqualsInteger) (.Var counter)) (intLit 0))
        [.App (.Var recur) minusOne, .Var captured])))
    let baseline ← lower worker
    let candidate := peelRecursion 5 baseline
    check "worker under a binder was peeled" (decide (candidate ≠ baseline))
    for input in [0, 2, 5, 11] do
      compareRuns (call baseline 37) (call candidate 37) input

  test "compile! enables general recursion peeling" do
    check "frontend flag changed the compiled script" (decide (frontendDefault ≠ frontendPeeled))
    for input in [0, 3, 12] do
      compareRuns frontendDefault frontendPeeled input

  test "tuning searches bounded depths and honors the inclusive Flat limit" do
    let worker := countdown (.App (.Var recur) minusOne)
    let profiles : List OptimizationProfile := [⟨"countdown", { recursionPeelDepth := 5 }⟩]
    let depth2 ← compile worker 2
    let depth3 ← compile worker 3
    let limit := flatProgramBytes depth2
    check "the next depth exceeds the limit" (flatProgramBytes depth3 > limit)
    let score := fun term => some (-(Int.ofNat (flatProgramBytes term)))
    let winner ← IO.ofExcept (compileTuned worker score profiles
      (peeling := some { maxDepth := 3, maxScriptBytes := limit }))
    check "the cap admits a candidate of exactly the limit" (decide (winner.term = depth2))
    checkEq "winning depth is recorded in the profile" (toString winner.profile.options.recursionPeelDepth) "2"
    let deepest ← IO.ofExcept (compileTuned worker score profiles
      (peeling := some { maxDepth := 3, maxScriptBytes := 4096 }))
    check "the search stops at the requested bound" (decide (deepest.term = depth3))
    let tied ← IO.ofExcept (compileTuned worker (fun _ => some (0 : Nat)) profiles
      (peeling := some { maxDepth := 3, maxScriptBytes := 4096 }))
    checkEq "an exact score tie selects unpeeled depth zero"
      (toString tied.profile.options.recursionPeelDepth) "0"

  test "tuning filters oversize scripts before running an effectful scorer" do
    let worker := countdown (.App (.Var recur) minusOne)
    let profiles : List OptimizationProfile := [⟨"countdown", {}⟩]
    let baseline ← compile worker 0
    let limit := flatProgramBytes baseline
    let sizes ← IO.mkRef ([] : List Nat)
    let score : Term → IO (Option Nat) := fun term => do
      sizes.modify (flatProgramBytes term :: ·)
      return some 0
    let winner ← IO.ofExcept (← compileTunedM worker score profiles
      (peeling := some { maxDepth := 3, maxScriptBytes := limit }))
    check "only the baseline was scored" ((← sizes.get) == [limit])
    check "the unpeeled candidate was selected" (decide (winner.term = baseline))
    sizes.set []
    let noFit ← compileTunedM worker score profiles
      (peeling := some { maxDepth := 3, maxScriptBytes := 0 })
    match noFit with
    | .error message => checkEq "size error" message "no optimization profile fits the 0-byte Flat limit"
    | .ok _ => throw (IO.userError "no Flat script should fit a zero-byte limit")
    check "the scorer was never invoked" (← sizes.get).isEmpty

end Test.MIR.Opt.RecursionPeeling
