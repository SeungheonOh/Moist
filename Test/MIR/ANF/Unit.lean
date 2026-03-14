import Test.MIR.Helpers

namespace Test.MIR.ANF.Unit

open Moist.MIR
open Test.MIR
open Test.Framework

def unitTree : TestTree := suite "unit" do
  test "atoms" do
    for (name, e) in [
      ("atom_var",     Expr.Var x),
      ("atom_lit",     intLit 42),
      ("atom_builtin", Expr.Builtin .AddInteger),
      ("atom_error",   Expr.Error)
    ] do
      let r := normalize e
      checkAlphaEq s!"{name}" r e
      checkANF s!"{name}_anf" r
  test "app_atomic" do
    let e := Expr.App (.Var f) (.Var x)
    let r := normalize e
    checkAlphaEq "app_atomic" r e
    checkANF "app_atomic_anf" r
  test "app_nonatomic_fun" do
    let e := Expr.App (.App (.Var f) (.Var x)) (.Var y)
    let r := normalize e
    let expected := Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y))
    checkAlphaEq "app_nonatomic_fun" r expected
    checkANF "app_nonatomic_fun_anf" r
  test "app_nonatomic_arg" do
    let e := Expr.App (.Var f) (.App (.Var g) (.Var x))
    let r := normalize e
    let expected := Expr.Let [(t1, .App (.Var g) (.Var x), false)] (.App (.Var f) (.Var t1))
    checkAlphaEq "app_nonatomic_arg" r expected
    checkANF "app_nonatomic_arg_anf" r
  test "app_both_nonatomic" do
    let e := Expr.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y))
    let r := normalize e
    let expected :=
      Expr.Let [(t1, .App (.Var f) (.Var x), false),
                (t2, .App (.Var g) (.Var y), false)]
        (.App (.Var t1) (.Var t2))
    checkAlphaEq "app_both_nonatomic" r expected
    checkANF "app_both_nonatomic_anf" r
  test "force_atomic" do
    let e := Expr.Force (.Var x)
    let r := normalize e
    checkAlphaEq "force_atomic" r e
    checkANF "force_atomic_anf" r
  test "force_nonatomic" do
    let e := Expr.Force (.App (.Var f) (.Var x))
    let r := normalize e
    let expected := Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.Force (.Var t1))
    checkAlphaEq "force_nonatomic" r expected
    checkANF "force_nonatomic_anf" r
  test "constr_atomic" do
    let e := Expr.Constr 0 [.Var x, .Var y, .Var z]
    let r := normalize e
    checkAlphaEq "constr_atomic" r e
    checkANF "constr_atomic_anf" r
  test "constr_one_nonatomic" do
    let e := Expr.Constr 0 [.App (.Var f) (.Var x), .Var y]
    let r := normalize e
    let expected := Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.Constr 0 [.Var t1, .Var y])
    checkAlphaEq "constr_one_nonatomic" r expected
    checkANF "constr_one_nonatomic_anf" r
  test "constr_multi_nonatomic" do
    let e := Expr.Constr 0 [.App (.Var f) (.Var x), .App (.Var g) (.Var y), .Var z]
    let r := normalize e
    let expected :=
      Expr.Let [(t1, .App (.Var f) (.Var x), false),
                (t2, .App (.Var g) (.Var y), false)]
        (.Constr 0 [.Var t1, .Var t2, .Var z])
    checkAlphaEq "constr_multi_nonatomic" r expected
    checkANF "constr_multi_nonatomic_anf" r
  test "case_atomic_scrut" do
    let e := Expr.Case (.Var x) [.Var y, .Var z]
    let r := normalize e
    checkAlphaEq "case_atomic_scrut" r e
    checkANF "case_atomic_scrut_anf" r
  test "case_nonatomic_scrut" do
    let e := Expr.Case (.App (.Var f) (.Var x)) [.Var y, .Var z]
    let r := normalize e
    let expected :=
      Expr.Let [(t1, .App (.Var f) (.Var x), false)] (.Case (.Var t1) [.Var y, .Var z])
    checkAlphaEq "case_nonatomic_scrut" r expected
    checkANF "case_nonatomic_scrut_anf" r
  test "case_normalize_alts" do
    let e := Expr.Case (.Var x) [
      .App (.App (.Var f) (.Var y)) (.Var z),
      .Var a
    ]
    let r := normalize e
    let expected := Expr.Case (.Var x) [
      .Let [(t1, .App (.Var f) (.Var y), false)] (.App (.Var t1) (.Var z)),
      .Var a
    ]
    checkAlphaEq "case_normalize_alts" r expected
    checkANF "case_normalize_alts_anf" r
  test "let_normalize_rhs" do
    let e := Expr.Let [(a, .App (.App (.Var f) (.Var x)) (.Var y), false)] (.Var a)
    let r := normalize e
    let expected := Expr.Let
      [(t1, .App (.Var f) (.Var x), false),
       (a, .App (.Var t1) (.Var y), false)]
      (.Var a)
    checkAlphaEq "let_normalize_rhs" r expected
    checkANF "let_normalize_rhs_anf" r
  test "let_normalize_body" do
    let e := Expr.Let [(a, intLit 1, false)] (.App (.App (.Var f) (.Var a)) (.Var x))
    let r := normalize e
    let expected := Expr.Let
      [(a, intLit 1, false),
       (t1, .App (.Var f) (.Var a), false)]
      (.App (.Var t1) (.Var x))
    checkAlphaEq "let_normalize_body" r expected
    checkANF "let_normalize_body_anf" r
  test "let_multi_bind" do
    let e := Expr.Let
      [(a, .App (.App (.Var f) (.Var x)) (.Var y), false),
       (b, .App (.App (.Var g) (.Var a)) (.Var z), false)]
      (.App (.Var a) (.Var b))
    let r := normalize e
    checkANF "let_multi_bind_anf" r
  test "lam_normalize_body" do
    let e := Expr.Lam x (.App (.App (.Var f) (.Var x)) (.Var y))
    let r := normalize e
    let expected := Expr.Lam x
      (.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y)))
    checkAlphaEq "lam_normalize_body" r expected
    checkANF "lam_normalize_body_anf" r
  test "fix_normalize_body" do
    let e := Expr.Fix f (.Lam x (.App (.App (.Var f) (.Var x)) (.Var y)))
    let r := normalize e
    let expected := Expr.Fix f (.Lam x
      (.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y))))
    checkAlphaEq "fix_normalize_body" r expected
    checkANF "fix_normalize_body_anf" r
  test "delay_normalize" do
    let e := Expr.Delay (.App (.App (.Var f) (.Var x)) (.Var y))
    let r := normalize e
    let expected := Expr.Delay
      (.Let [(t1, .App (.Var f) (.Var x), false)] (.App (.Var t1) (.Var y)))
    checkAlphaEq "delay_normalize" r expected
    checkANF "delay_normalize_anf" r
  test "nested_app_chain" do
    let add := Expr.Builtin .AddInteger
    let e := Expr.App (.App (.App add (intLit 1)) (intLit 2)) (intLit 3)
    let r := normalize e
    checkANF "nested_app_chain_anf" r
    check "nested_app_chain_structure" r.isANF
  test "idempotent" do
    let e := Expr.App (.App (.Var f) (.Var x)) (.App (.Var g) (.Var y))
    let n1 := normalize e 100
    let n2 := normalize n1 200
    checkAlphaEq "idempotent" n2 n1
    checkANF "idempotent_anf" n2
  test "idempotent_complex" do
    let e := Expr.Force (.App (.App (.Builtin .IfThenElse) (boolLit true))
      (.Delay (intLit 1)))
    let n1 := normalize e 100
    let n2 := normalize n1 200
    checkAlphaEq "idempotent_complex" n2 n1
    checkANF "idempotent_complex_anf" n2
  test "factorial" do
    let r := normalize factorialMIR
    checkANF "factorial_anf" r
  test "noSelfRef_after_normalize" do
    let inputs := [
      Expr.App (.App (.Var f) (.Var x)) (.Var y),
      Expr.App (.Var f) (.App (.Var g) (.Var x)),
      Expr.Force (.App (.Var f) (.Var x)),
      Expr.Constr 0 [.App (.Var f) (.Var x), .Var y],
      factorialMIR
    ]
    for (e, i) in inputs.zipIdx do
      let r := normalize e (100 + i * 50)
      checkANF s!"noSelfRef_after_normalize_{i}" r
  test "let_empty_binds" do
    let e := Expr.Let [] (.Var x)
    let r := normalize e
    checkAlphaEq "let_empty_binds" r (.Let [] (.Var x))
    checkANF "let_empty_binds_anf" r
  test "constr_no_args" do
    let e := Expr.Constr 0 []
    let r := normalize e
    checkAlphaEq "constr_no_args" r (.Constr 0 [])
    checkANF "constr_no_args_anf" r

end Test.MIR.ANF.Unit
