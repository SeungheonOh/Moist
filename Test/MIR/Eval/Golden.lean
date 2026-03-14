import Test.MIR.Helpers
import Moist.MIR.Lower
import Moist.MIR.Optimize
import Moist.Plutus.Eval
import Moist.Plutus.Pretty
import Test.Framework

namespace Test.MIR.Eval.Golden

open Moist.MIR
open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Plutus.Eval
open Test.MIR
open Test.Framework

private def mkEvalGolden (name : String) (input : Expr)
    (optStart : Nat := 1000) (lowerStart : Nat := 5000) : TreeBuilder Unit :=
  golden name (do
    let opt := optimizeExpr input optStart
    match lowerExpr opt lowerStart with
    | .error msg => pure <| goldenSections [("error", s!"lower: {msg}")]
    | .ok term =>
      match ← evalTerm term with
      | .ok r =>
        pure <| goldenSections [("result", prettyTerm r.term), ("cpu", s!"{r.budget.cpu}"), ("mem", s!"{r.budget.mem}")]
      | .error (err, budget, msg) =>
        pure <| goldenSections [("error", s!"{err}: {msg}"), ("cpu", s!"{budget.cpu}"), ("mem", s!"{budget.mem}")])

def goldenTree : TestTree := suite "golden" do
  mkEvalGolden "eval_lit" (intLit 42)
  mkEvalGolden "eval_add"
    (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2))
  mkEvalGolden "eval_identity"
    (.App (.Lam x (.Var x)) (intLit 5))
  mkEvalGolden "eval_equals_true"
    (.App (.App (.Builtin .EqualsInteger) (intLit 1)) (intLit 1))
  mkEvalGolden "eval_equals_false"
    (.App (.App (.Builtin .EqualsInteger) (intLit 1)) (intLit 2))
  mkEvalGolden "eval_ifthenelse"
    (.Force (.App (.App (.App (.Builtin .IfThenElse)
      (.App (.App (.Builtin .EqualsInteger) (intLit 1)) (intLit 1)))
      (.Delay (intLit 10)))
      (.Delay (intLit 20))))
  mkEvalGolden "eval_multiply"
    (.App (.App (.Builtin .MultiplyInteger) (intLit 6)) (intLit 7))
  mkEvalGolden "eval_subtract"
    (.App (.App (.Builtin .SubtractInteger) (intLit 10)) (intLit 3))
  mkEvalGolden "eval_nested_let"
    (.Let [(a, intLit 10, false),
           (b, .App (.App (.Builtin .AddInteger) (.Var a)) (intLit 5), false)]
      (.App (.App (.Builtin .MultiplyInteger) (.Var a)) (.Var b)))
  mkEvalGolden "eval_lam_app"
    (.App (.Lam x (.App (.App (.Builtin .AddInteger) (.Var x)) (intLit 1)))
      (intLit 5))
  mkEvalGolden "eval_factorial" factorialMIR
  mkEvalGolden "eval_error" .Error

end Test.MIR.Eval.Golden
