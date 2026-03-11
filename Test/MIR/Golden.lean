import Test.MIR.Helpers

namespace Test.MIR.Golden

open Moist.MIR
open Test.MIR

/-! # Golden Test Case Definitions

Each entry is (filename, expected_output). The golden runner compares these
against Test/golden/{filename}.expected.
-/

def goldenTests : List Test.Framework.GoldenSpec :=
  let cases : List Test.Framework.GoldenSpec := [
    -- Atoms
    mkGoldenCase "atom_var" (.Var x),
    mkGoldenCase "atom_lit" (intLit 42),
    mkGoldenCase "atom_builtin" (.Builtin .AddInteger),
    mkGoldenCase "atom_error" .Error,

    -- App: already ANF
    mkGoldenCase "app_atomic" (.App (.Var f) (.Var x)),

    -- App: non-atomic function
    mkGoldenCase "app_nonatomic_fun"
      (.App (.App (.Var f) (.Var x)) (.Var y)),

    -- App: non-atomic argument
    mkGoldenCase "app_nonatomic_arg"
      (.App (.Var f) (.App (.Var g) (.Var x))),

    -- App: both non-atomic
    mkGoldenCase "app_both_nonatomic"
      (.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y))),

    -- Force non-atomic
    mkGoldenCase "force_nonatomic"
      (.Force (.App (.Var f) (.Var x))),

    -- Constr with mixed args
    mkGoldenCase "constr_mixed"
      (.Constr 0 [.App (.Var f) (.Var x), .Var y, .App (.Var g) (.Var z)]),

    -- Case with non-atomic scrutinee
    mkGoldenCase "case_nonatomic_scrut"
      (.Case (.App (.Var f) (.Var x)) [.Var y, .Var z]),

    -- Case with non-ANF alternatives
    mkGoldenCase "case_nonatomic_alts"
      (.Case (.Var x) [
        .App (.App (.Var f) (.Var y)) (.Var z),
        .Var a]),

    -- Let with non-ANF RHS
    mkGoldenCase "let_nonatomic_rhs"
      (.Let [(a, .App (.App (.Var f) (.Var x)) (.Var y))] (.Var a)),

    -- Lam with non-ANF body
    mkGoldenCase "lam_body"
      (.Lam x (.App (.App (.Var f) (.Var x)) (.Var y))),

    -- Fix with non-ANF body
    mkGoldenCase "fix_body"
      (.Fix f (.Lam x (.App (.App (.Var f) (.Var x)) (.Var y)))),

    -- Delay with non-ANF content
    mkGoldenCase "delay_body"
      (.Delay (.App (.App (.Var f) (.Var x)) (.Var y))),

    -- Deeply nested application
    mkGoldenCase "nested_app_chain"
      (.App (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)) (intLit 3)),

    -- IfThenElse pattern (common in Plutus)
    mkGoldenCase "ifthenelse_pattern"
      (.Force (.App (.App (.App (.Builtin .IfThenElse) (.Var x))
        (.Delay (intLit 1)))
        (.Delay (intLit 0)))),

    -- Let with multiple bindings, body needs normalization
    mkGoldenCase "let_multi_bind"
      (.Let
        [(a, .App (.App (.Var f) (.Var x)) (.Var y)),
         (b, .App (.Var g) (.Var a))]
        (.App (.App (.Var a) (.Var b)) (.Var z))),

    -- Factorial
    mkGoldenCase "factorial" factorialMIR
  ]
  let idempotency : List Test.Framework.GoldenSpec := [
    -- Idempotency: simple
    mkIdempotencyCase "idempotency_app"
      (.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y))),

    -- Idempotency: complex
    mkIdempotencyCase "idempotency_factorial" factorialMIR
  ]
  cases ++ idempotency

end Test.MIR.Golden
