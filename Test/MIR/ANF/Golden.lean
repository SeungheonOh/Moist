import Test.MIR.Helpers

namespace Test.MIR.ANF.Golden

open Moist.MIR
open Test.MIR
open Test.Framework

def goldenTree : TestTree := suite "golden" do
  mkGoldenCase "atom_var" (.Var x)
  mkGoldenCase "atom_lit" (intLit 42)
  mkGoldenCase "atom_builtin" (.Builtin .AddInteger)
  mkGoldenCase "atom_error" .Error
  mkGoldenCase "app_atomic" (.App (.Var f) (.Var x))
  mkGoldenCase "app_nonatomic_fun"
    (.App (.App (.Var f) (.Var x)) (.Var y))
  mkGoldenCase "app_nonatomic_arg"
    (.App (.Var f) (.App (.Var g) (.Var x)))
  mkGoldenCase "app_both_nonatomic"
    (.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y)))
  mkGoldenCase "force_nonatomic"
    (.Force (.App (.Var f) (.Var x)))
  mkGoldenCase "constr_mixed"
    (.Constr 0 [.App (.Var f) (.Var x), .Var y, .App (.Var g) (.Var z)])
  mkGoldenCase "case_nonatomic_scrut"
    (.Case (.App (.Var f) (.Var x)) [.Var y, .Var z])
  mkGoldenCase "case_nonatomic_alts"
    (.Case (.Var x) [
      .App (.App (.Var f) (.Var y)) (.Var z),
      .Var a])
  mkGoldenCase "let_nonatomic_rhs"
    (.Let [(a, .App (.App (.Var f) (.Var x)) (.Var y), false)] (.Var a))
  mkGoldenCase "lam_body"
    (.Lam x (.App (.App (.Var f) (.Var x)) (.Var y)))
  mkGoldenCase "fix_body"
    (.Fix f (.Lam x (.App (.App (.Var f) (.Var x)) (.Var y))))
  mkGoldenCase "delay_body"
    (.Delay (.App (.App (.Var f) (.Var x)) (.Var y)))
  mkGoldenCase "nested_app_chain"
    (.App (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)) (intLit 3))
  mkGoldenCase "ifthenelse_pattern"
    (.Force (.App (.App (.App (.Builtin .IfThenElse) (.Var x))
      (.Delay (intLit 1)))
      (.Delay (intLit 0))))
  mkGoldenCase "let_multi_bind"
    (.Let
      [(a, .App (.App (.Var f) (.Var x)) (.Var y), false),
       (b, .App (.Var g) (.Var a), false)]
      (.App (.App (.Var a) (.Var b)) (.Var z)))
  mkGoldenCase "factorial" factorialMIR
  mkIdempotencyCase "idempotency_app"
    (.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y)))
  mkIdempotencyCase "idempotency_factorial" factorialMIR

end Test.MIR.ANF.Golden
