import Test.MIR.Helpers
import Moist.MIR.Lower
import Moist.MIR.Optimize
import Moist.Plutus.Pretty
import Test.Framework

namespace Test.MIR.Lower.Golden

open Moist.MIR
open Moist.Plutus.Pretty (prettyTerm)
open Test.MIR
open Test.Framework

private def mkLowerGolden (name : String) (input : Expr) (freshStart : Nat := 10000)
    : TreeBuilder Unit :=
  golden name <| pure <|
    let result := lowerExpr input freshStart
    match result with
    | .ok term => goldenSections [("uplc", prettyTerm term)]
    | .error msg => goldenSections [("error", msg)]

private def mkLowerOptGolden (name : String) (input : Expr)
    (optStart : Nat := 1000) (lowerStart : Nat := 5000) : TreeBuilder Unit :=
  golden name <| pure <|
    let opt := optimizeExpr input optStart
    let result := lowerExpr opt lowerStart
    match result with
    | .ok term =>
      goldenSections [("optimized", pretty opt), ("uplc", prettyTerm term)]
    | .error msg =>
      goldenSections [("optimized", pretty opt), ("error", msg)]

def goldenTree : TestTree := suite "golden" do
  mkLowerGolden "lower_var"
    (.Lam x (.Var x))
  mkLowerGolden "lower_lit"
    (intLit 42)
  mkLowerGolden "lower_builtin"
    (.Builtin .AddInteger)
  mkLowerGolden "lower_error"
    .Error
  mkLowerGolden "lower_app"
    (.Lam f (.Lam x (.App (.Var f) (.Var x))))
  mkLowerGolden "lower_force_delay"
    (.Force (.Delay (intLit 1)))
  mkLowerGolden "lower_constr"
    (.Lam x (.Constr 0 [.Var x, intLit 1]))
  mkLowerGolden "lower_case"
    (.Lam x (.Case (.Var x) [intLit 10, intLit 20]))
  mkLowerGolden "lower_let_atom_var"
    (.Lam x (.Let [(a, .Var x, false)] (.App (.Var a) (.Var a))))
  mkLowerGolden "lower_let_atom_lit"
    (.Let [(a, intLit 42, false)] (.Var a))
  mkLowerGolden "lower_let_atom_builtin"
    (.Let [(a, .Builtin .AddInteger, false)] (.App (.Var a) (.Var a)))
  mkLowerGolden "lower_let_single_use_lam"
    (.Let [(a, .Lam x (.Var x), false)] (.App (.Var a) (intLit 5)))
  mkLowerGolden "lower_let_single_use_delay"
    (.Let [(a, .Delay (intLit 1), false)] (.Force (.Var a)))
  mkLowerGolden "lower_let_dead_pure"
    (.Let [(a, intLit 99, false), (b, .Lam x (.Var x), false)] (intLit 1))
  mkLowerGolden "lower_let_impure_kept"
    (.Lam f (.Let [(a, .App (.Var f) (intLit 1), false)] (intLit 2)))
  mkLowerGolden "lower_let_multi_use"
    (.Lam f (.Lam x
      (.Let [(a, .App (.Var f) (.Var x), false)]
        (.App (.Var a) (.Var a)))))
  mkLowerGolden "lower_let_mixed"
    (.Lam f (.Lam x
      (.Let
        [(a, .Var x, false),
         (b, .App (.Var f) (.Var a), false),
         (c, intLit 99, false)]
        (.App (.Var b) (.Var c)))))
  mkLowerGolden "lower_fix_lam"
    (.Fix f (.Lam x (.App (.Var f) (.Var x))))
  mkLowerGolden "lower_factorial" factorialMIR
  mkLowerGolden "lower_unbound"
    (.Var ⟨999, "oops"⟩)
  mkLowerGolden "lower_let_chain"
    (.Let [(a, .Delay (intLit 1), false)]
      (.Let [(b, .Delay (.Var a), false)]
        (.Force (.Var b))))
  mkLowerOptGolden "lower_data_deconstruct" dataDeconstructMIR

end Test.MIR.Lower.Golden
