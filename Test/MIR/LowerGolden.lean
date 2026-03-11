import Test.MIR.Helpers
import Moist.MIR.Lower
import Moist.MIR.Optimize
import Moist.Plutus.Pretty
import Test.Framework

namespace Test.MIR.LowerGolden

open Moist.MIR
open Moist.Plutus.Pretty (prettyTerm)
open Test.MIR

/-! # Lowering Golden Tests

Golden tests for MIR → UPLC lowering. Each test lowers a MIR expression
and pretty-prints the resulting UPLC term.
-/

private def mkLowerGolden (name : String) (input : Expr) (freshStart : Nat := 10000)
    : Test.Framework.GoldenSpec :=
  let result := lowerExpr input freshStart
  let output := match result with
    | .ok term =>
      s!"--- Input ---\n{pretty input}\n--- UPLC ---\n{prettyTerm term}"
    | .error msg =>
      s!"--- Input ---\n{pretty input}\n--- Error ---\n{msg}"
  { name, render := pure output }

/-- Lower after running the full optimization pipeline. -/
private def mkLowerOptGolden (name : String) (input : Expr)
    (optStart : Nat := 1000) (lowerStart : Nat := 5000) : Test.Framework.GoldenSpec :=
  let opt := optimizeExpr input optStart
  let result := lowerExpr opt lowerStart
  let output := match result with
    | .ok term =>
      s!"--- Input ---\n{pretty input}\n--- Optimized ---\n{pretty opt}\n--- UPLC ---\n{prettyTerm term}"
    | .error msg =>
      s!"--- Input ---\n{pretty input}\n--- Optimized ---\n{pretty opt}\n--- Error ---\n{msg}"
  { name, render := pure output }

def lowerGoldenTests : List Test.Framework.GoldenSpec := [

  -- ## Atoms

  mkLowerGolden "lower_var"
    (.Lam x (.Var x)),

  mkLowerGolden "lower_lit"
    (intLit 42),

  mkLowerGolden "lower_builtin"
    (.Builtin .AddInteger),

  mkLowerGolden "lower_error"
    .Error,

  -- ## Simple structures

  mkLowerGolden "lower_app"
    (.Lam f (.Lam x (.App (.Var f) (.Var x)))),

  mkLowerGolden "lower_force_delay"
    (.Force (.Delay (intLit 1))),

  mkLowerGolden "lower_constr"
    (.Lam x (.Constr 0 [.Var x, intLit 1])),

  mkLowerGolden "lower_case"
    (.Lam x (.Case (.Var x) [intLit 10, intLit 20])),

  -- ## Let inlining: atom RHS always substituted

  mkLowerGolden "lower_let_atom_var"
    (.Lam x (.Let [(a, .Var x)] (.App (.Var a) (.Var a)))),

  mkLowerGolden "lower_let_atom_lit"
    (.Let [(a, intLit 42)] (.Var a)),

  mkLowerGolden "lower_let_atom_builtin"
    (.Let [(a, .Builtin .AddInteger)] (.App (.Var a) (.Var a))),

  -- ## Let inlining: single-use pure RHS substituted

  mkLowerGolden "lower_let_single_use_lam"
    (.Let [(a, .Lam x (.Var x))] (.App (.Var a) (intLit 5))),

  mkLowerGolden "lower_let_single_use_delay"
    (.Let [(a, .Delay (intLit 1))] (.Force (.Var a))),

  -- ## Let: dead pure binding dropped

  mkLowerGolden "lower_let_dead_pure"
    (.Let [(a, intLit 99), (b, .Lam x (.Var x))] (intLit 1)),

  -- ## Let: impure binding kept even if unused

  mkLowerGolden "lower_let_impure_kept"
    (.Lam f (.Let [(a, .App (.Var f) (intLit 1))] (intLit 2))),

  -- ## Let: multi-use keeps lambda encoding

  mkLowerGolden "lower_let_multi_use"
    (.Lam f (.Lam x
      (.Let [(a, .App (.Var f) (.Var x))]
        (.App (.Var a) (.Var a))))),

  -- ## Let: multiple bindings with mixed inlining

  mkLowerGolden "lower_let_mixed"
    (.Lam f (.Lam x
      (.Let
        [(a, .Var x),
         (b, .App (.Var f) (.Var a)),
         (c, intLit 99)]
        (.App (.Var b) (.Var c))))),

  -- ## Fix: standard Z combinator (Lam body)

  mkLowerGolden "lower_fix_lam"
    (.Fix f (.Lam x (.App (.Var f) (.Var x)))),

  -- ## Fix: factorial

  mkLowerGolden "lower_factorial" factorialMIR,

  -- ## Error: unbound variable

  mkLowerGolden "lower_unbound"
    (.Var ⟨999, "oops"⟩),

  -- ## Nested lets with single-use chain (should all inline)

  mkLowerGolden "lower_let_chain"
    (.Let [(a, .Delay (intLit 1))]
      (.Let [(b, .Delay (.Var a))]
        (.Force (.Var b)))),

  -- ## Data.Constr deconstruction: optimize then lower
  -- Extract fields 0, 2, 3 from Data-encoded constructor and sum them.
  -- CSE should share: force headList, force tailList,
  -- tailList(flds), tailList(tailList(flds))
  mkLowerOptGolden "lower_data_deconstruct" dataDeconstructMIR
]

end Test.MIR.LowerGolden
