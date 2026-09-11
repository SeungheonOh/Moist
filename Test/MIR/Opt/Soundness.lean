import Test.MIR.Helpers
import Moist.MIR.Optimize
import Moist.MIR.Optimize.PreLower
import Moist.MIR.Lower
import Moist.CEK.Machine
import Moist.CEK.Readback

namespace Test.MIR.Opt.Soundness

open Moist.MIR
open Moist.Plutus.Term
open Test.MIR
open Test.Framework

def observation (expression : Expr) : IO String := do
  let term ← match lowerExpr expression with
    | .ok term => pure term
    | .error message => throw (IO.userError s!"Lowering failed: {message}")
  match (Moist.CEK.eval term 100000000 100000000).result with
  | .success value => return Moist.Plutus.Pretty.prettyTerm (Moist.CEK.readbackValue value)
  | .failure => return "failure"
  | .outOfBudget => throw (IO.userError "Semantic regression exceeded its evaluation budget")

def preserves (label : String) (before after : Expr) : IO Unit := do
  let expected ← observation before
  let actual ← observation after
  checkEq label actual expected

private def traceExpression (message : String) (result : Expr) : Expr :=
  .App (.App (.Force (.Builtin .Trace))
    (.Lit (.String message, .AtomicType .TypeString))) result

private def stepMessages : Moist.CEK.State → List String
  | .ret (.funV (.VBuiltin .Trace [.VCon (.String message)] remaining) :: _) _ =>
    if remaining.head == .argV && remaining.isFinal then [message] else []
  | .ret (.applyArg _ :: _) (.VBuiltin .Trace [.VCon (.String message)] remaining) =>
    if remaining.head == .argV && remaining.isFinal then [message] else []
  | _ => []

private def tracedSteps : Nat → Moist.CEK.State → List String → Except String (String × List String)
  | 0, _, _ => .error "Trace regression exceeded its step limit"
  | fuel + 1, state, messages =>
    match state with
    | .halt value => .ok (Moist.Plutus.Pretty.prettyTerm (Moist.CEK.readbackValue value), messages)
    | .error => .ok ("failure", messages)
    | _ => tracedSteps fuel (Moist.CEK.step state) (messages ++ stepMessages state)

def tracedObservation (expression : Expr) : IO (String × List String) := do
  let term ← match lowerExpr expression with
    | .ok term => pure term
    | .error message => throw (IO.userError s!"Lowering failed: {message}")
  match tracedSteps 10000 (.compute [] .nil term) [] with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

def transformations : List (String × (Expr → Expr)) :=
  [("FloatOut", fun expression => (floatOut expression).1),
   ("BetaReduce", fun expression => (runFresh (betaReducePass expression)).1),
   ("ANF", fun expression => runFresh (anfNormalize (uniqueOptimizationBinders expression))),
   ("CaseMerge", fun expression => (caseMergePass expression).1),
   ("CSE", fun expression => (cse [] expression).1),
   ("DCE", fun expression => (dce expression).1),
   ("Inline", fun expression => (runFresh (inlinePassWithCanon expression)).1),
   ("EtaReduce", fun expression => (etaReduce expression).1),
   ("ForceDelay", fun expression => (forceDelay expression).1),
   ("PreLower", preLowerInlineExpr),
   ("Pipeline", optimizeExpr),
   ("CompilePipeline", fun expression => preLowerInlineExpr (optimizeExpr expression))]

def preservesAll (label : String) (expression : Expr) : IO Unit := do
  let expected ← tracedObservation expression
  for (passName, transform) in transformations do
    let actual ← tracedObservation (transform expression)
    check s!"{label}/{passName}: expected {repr expected}, got {repr actual}" (actual == expected)

def tests : TestTree := suite "soundness" do
  test "alpha_equivalence_distinguishes_origins" do
    let generated : VarId := { uid := x.uid, origin := .gen }
    let freeUse := Expr.Lam x (.Var generated)
    let boundUse := Expr.Lam y (.Var y)
    check "free generated variable is not source-bound" (!freeUse.alphaEq boundUse)
    check "both alpha checkers agree" (freeUse.alphaEq boundUse == alphaEq freeUse boundUse)

  test "eta_preserves_noncommutative_argument_order" do
    let function := Expr.Lam x (.Lam y
      (.App (.App (.Builtin .SubtractInteger) (.Var y)) (.Var x)))
    let applyArguments := fun expression => Expr.App (.App expression (intLit 10)) (intLit 3)
    preserves "swapped subtraction" (applyArguments function) (applyArguments (etaReduce function).1)

  test "eta_does_not_evaluate_a_deferred_error" do
    let expression := Expr.Let [(a, .Lam x (.App .Error (.Var x)), false)] (intLit 42)
    preserves "deferred failure" expression (etaReduce expression).1

  test "eta_does_not_turn_a_lambda_into_a_delay" do
    let expression := Expr.Force (.Lam x (.App (.Delay (intLit 42)) (.Var x)))
    preserves "untyped force" expression (etaReduce expression).1

  test "eta_does_not_assume_unknown_heads_are_functions" do
    let expression := Expr.App (.Lam f
      (.Force (.Lam x (.App (.Var f) (.Var x))))) (.Delay (intLit 42))
    preserves "unknown head" expression (etaReduce expression).1

  test "eta_preserves_partial_application_laziness" do
    let function := Expr.Lam x (.Lam y (.App (.App .Error (.Var x)) (.Var y)))
    let expression := Expr.Let [(a, .App function (intLit 1), false)] (intLit 42)
    preserves "partial application" expression (etaReduce expression).1

  test "eta_preserves_fix_outer_lambda" do
    let function := Expr.Fix f (.Lam x (.App (.Builtin .AddInteger) (.Var x)))
    let applyArguments := fun expression => Expr.App (.App expression (intLit 10)) (intLit 3)
    preserves "fix lowering" (applyArguments function) (applyArguments (etaReduce function).1)

  test "eta_still_reduces_safe_builtin_and_lambda_heads" do
    let function := Expr.Lam x (.Lam y
      (.App (.App (.Builtin .SubtractInteger) (.Var x)) (.Var y)))
    checkPassResult "known builtin" (etaReduce function) (.Builtin .SubtractInteger) true
    let lambda := Expr.Lam y (.Var y)
    checkPassResult "known lambda" (etaReduce (.Lam x (.App lambda (.Var x)))) lambda true

  test "case_fields_are_not_inferred_from_lambda_count" do
    let expression := Expr.Let
      [(x, .Constr 0 [], false),
       (a, .Case (.Var x) [.Lam y (intLit 1)], false),
       (b, .Case (.Var x) [.Lam z (intLit 2)], false)]
      (.App (.App (.Builtin .AddInteger) (.Var a)) (.Var b))
    preservesAll "partial case alternatives" expression

  test "case_constructor_arity_matrix" do
    for fieldCount in List.range 4 do
      for parameterCount in List.range 4 do
        let parameters := (List.range parameterCount).map (fun index => sourceVar (100 + index))
        let alternative := parameters.foldr Expr.Lam (intLit 42)
        let fields := (List.range fieldCount).map (fun index => intLit (Int.ofNat index))
        let expression := Expr.Case (.Constr 0 fields) [alternative]
        let transformed := (caseMergePass expression).1
        preserves s!"arity {fieldCount}/{parameterCount}" expression transformed
        let consume := fun result => Expr.App (.Lam a (intLit 7)) result
        preservesAll s!"arity context {fieldCount}/{parameterCount}" (consume expression)

  test "case_preserves_eager_fields_and_missing_branch_errors" do
    for tag in [0, 1] do
      let expression := Expr.Case (.Constr tag [.Error]) [.Lam x (intLit 42)]
      preservesAll s!"eager error field {tag}" expression
      let traced := Expr.Case (.Constr tag [traceExpression "field" (intLit 1)]) [.Lam x (intLit 42)]
      preservesAll s!"eager trace field {tag}" traced

  test "case_preserves_constant_alternative_limits" do
    let expression := Expr.Let
      [(x, boolLit true, false),
       (a, .Case (.Var x) [intLit 1, intLit 2], false),
       (b, .Case (.Var x) [intLit 3, intLit 4, intLit 5], false)] (.Var b)
    preservesAll "boolean alternative count" expression

  test "case_specializes_known_constructors" do
    let expression := Expr.Case (.Constr 0 [intLit 41])
      [.Lam x (.App (.App (.Builtin .AddInteger) (.Var x)) (intLit 1))]
    let (result, changed) := caseMergePass expression
    check "known case is simplified" changed
    preservesAll "known field" expression
    preserves "known case result" expression result

  test "case_does_not_specialize_unknown_constructor_arity" do
    let expression := Expr.Let
      [(a, .Case (.Var x) [.Lam y (.Var y)], false),
       (b, .Case (.Var x) [.Lam z (intLit 42)], false)] (.Var b)
    checkPassResult "unknown arity" (caseMergePass expression) expression false

  test "force_delay_preserves_captured_environment" do
    let expression := Expr.Let [(x, intLit 1, false), (a, .Delay (.Var x), false)]
      (.App (.Lam x (.Force (.Var a))) (intLit 2))
    preservesAll "delay capture" expression

  test "sequential_shadowing_preserves_binding_identity" do
    let expression := Expr.Let
      [(x, intLit 1, false), (x, intLit 2, false), (a, intLit 1, false)]
      (.App (.App (.Builtin .SubtractInteger) (.Var x)) (.Var a))
    preservesAll "sequential shadowing" expression

  test "substitution_alpha_renaming_stops_at_sequential_shadowing" do
    let body := Expr.Let [(x, intLit 1, false), (x, intLit 2, false)]
      (.Constr 0 [.Var a, .Var x])
    let close := fun expression => Expr.Let [(x, intLit 7, false)] expression
    let expected := Expr.Constr 0 [intLit 7, intLit 2]
    let substituted := runFresh (subst a (.Var x) body) 100
    preserves "capture-avoiding substitution" expected (close substituted)
    preserves "capture-avoiding renameMany" expected (close (renameMany [(a, x)] body))

  test "rename_many_is_simultaneous" do
    let expression := Expr.Constr 0 [.Var a, .Var b]
    checkAlphaEq "swapping free variables" (renameMany [(a, b), (b, a)] expression)
      (.Constr 0 [.Var b, .Var a])

  test "cse_does_not_capture_its_replacement" do
    let expression := Expr.App
      (.Let [(a, intLit 1, false), (b, intLit 1, false)] (.Lam a (.Var b))) (intLit 2)
    preservesAll "CSE capture" expression

  test "float_out_preserves_recursive_function_shape" do
    let function := Expr.Fix f (.Lam x
      (.Let [(a, .Lam y (.App (.Var f) (.Var y)), false)]
        (.Case (.Var x) [intLit 42, .App (.Var a) (boolLit false)])))
    preservesAll "Fix-dependent binding" (.App function (boolLit true))

  test "float_out_does_not_capture_other_alternatives" do
    let expression := Expr.Let [(a, intLit 7, false)]
      (.Case (.Constr 1 []) [.Let [(a, intLit 1, false)] (.Var a), .Var a])
    preservesAll "case float capture" expression

  test "lowering_reserves_fresh_generated_identifiers" do
    let captured : VarId := { uid := 10000, origin := .gen, hint := "captured" }
    let function := Expr.Lam captured (.Fix f (.Lam x (.Var captured)))
    let expression := Expr.App (.App function (intLit 42)) (intLit 1)
    checkEq "fresh lowering result" (← observation expression) (← observation (intLit 42))
    preservesAll "fresh supply" expression

  test "inlining_preserves_trace_order" do
    let expression := Expr.Let
      [(a, traceExpression "first" (intLit 1), false),
       (b, traceExpression "second" (intLit 2), false)] (.Constr 0 [.Var b, .Var a])
    check "trace harness sees both messages" ((← tracedObservation expression).2 == ["first", "second"])
    preservesAll "trace order" expression

  test "inlining_does_not_move_errors_past_traces" do
    let expression := Expr.Let [(a, .Error, false), (b, traceExpression "unreachable" (intLit 2), false)] (.Var a)
    preservesAll "error ordering" expression

  test "inlining_does_not_move_errors_past_divergence" do
    let loop := Expr.Fix f (.Lam x (.App (.Var f) (.Var x)))
    let continuation := Expr.App
      (.App (.Builtin .AddInteger) (.App loop (intLit 0))) (.Var a)
    preservesAll "error before divergent continuation"
      (.Let [(a, .Error, false)] continuation)
    preservesAll "beta error before divergent continuation"
      (.App (.Lam a continuation) .Error)

  test "cse_preserves_direct_and_aliased_traces" do
    let direct := Expr.Let
      [(a, traceExpression "message" (intLit 1), false),
       (b, traceExpression "message" (intLit 1), false)] (.Constr 0 [.Var a, .Var b])
    preservesAll "direct trace" direct
    let aliased := Expr.Let
      [(f, .Lam x (traceExpression "call" (.Var x)), false),
       (a, .App (.Var f) (intLit 1), false),
       (b, .App (.Var f) (intLit 1), false)] (.Constr 0 [.Var a, .Var b])
    preservesAll "aliased trace" aliased

  test "cse_still_shares_nonlogging_builtin_calls" do
    let rhs := Expr.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)
    let expression := Expr.Let [(a, rhs, false), (b, rhs, false)] (.Constr 0 [.Var a, .Var b])
    let (result, changed) := cse [] expression
    check "builtin CSE remains active" changed
    preserves "builtin CSE result" expression result

  test "trace_and_normal_pipeline_agree" do
    let expression := Expr.App (.Lam x (.App (.App (.Builtin .SubtractInteger) (.Var x)) (intLit 2))) (intLit 9)
    let trace := optimizeTraceExpr expression 0
    let result := optimizeExpr expression 0
    check "trace is populated" (!trace.isEmpty)
    match trace.back? with
    | some step => checkAlphaEq "same final pipeline expression" step.expr result
    | none => throw (IO.userError "Optimization trace is empty")
    preserves "same pipeline behavior" expression result

end Test.MIR.Opt.Soundness
