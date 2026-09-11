import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.EtaReduce

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "etaReduce" do
  test "eta_simple" do
    let e := Expr.Lam x (.App (.Var f) (.Var x))
    checkPassResult "eta_simple" (etaReduce e) e false

  test "eta_multi_arg" do
    let e := Expr.Lam a (.Lam b (.App (.App (.Var f) (.Var a)) (.Var b)))
    checkPassResult "eta_multi_arg" (etaReduce e) e false

  test "eta_three_args" do
    let e := Expr.Lam a (.Lam b (.Lam c (.App (.App (.App (.Var f) (.Var a)) (.Var b)) (.Var c))))
    checkPassResult "eta_three_args" (etaReduce e) e false

  test "eta_no_reduce_unused_param" do
    let e := Expr.Lam x (.Lam y (.App (.Var f) (.Var x)))
    checkPassResult "eta_no_reduce_unused_param" (etaReduce e) e false

  test "eta_partial_trailing" do
    let e := Expr.Lam x (.Lam y (.App (.App (.Builtin .AddInteger) (.Var x)) (.Var y)))
    let expected := Expr.Builtin .AddInteger
    checkPassResult "eta_partial_trailing" (etaReduce e) expected true

  test "eta_arg_order_mismatch" do
    let e := Expr.Lam x (.Lam y (.App (.App (.Builtin .AddInteger) (.Var y)) (.Var x)))
    checkPassResult "eta_arg_order_mismatch" (etaReduce e) e false

  test "eta_not_simple_pattern" do
    let e := Expr.Lam x (.App (.App (.Var y) (.Var x)) (.Var x))
    checkPassResult "eta_not_simple_pattern" (etaReduce e) e false

  test "eta_lam_head" do
    let e := Expr.Lam x (.App (.Lam y (.Var y)) (.Var x))
    let expected := Expr.Lam y (.Var y)
    checkPassResult "eta_lam_head" (etaReduce e) expected true

  test "eta_captured_in_head" do
    let e := Expr.Lam x (.App (.App (.Builtin .AddInteger) (.Var x)) (.Var x))
    checkPassResult "eta_captured_in_head" (etaReduce e) e false

  test "eta_partial_one_layer" do
    let e := Expr.Lam x (.Lam y (.App (.Var g) (.Var y)))
    checkPassResult "eta_partial_one_layer" (etaReduce e) e false

  test "eta_body_not_app" do
    let e := Expr.Lam x (.Var x)
    checkPassResult "eta_body_not_app" (etaReduce e) e false

  test "eta_body_literal" do
    let e := Expr.Lam x (intLit 42)
    checkPassResult "eta_body_literal" (etaReduce e) e false

  test "eta_recurse_fix" do
    let e := Expr.Fix f (.Lam x (.App (.Var g) (.Var x)))
    checkPassResult "eta_recurse_fix" (etaReduce e) e false

  test "eta_recurse_let_rhs" do
    let e := Expr.Let [(a, .Lam x (.App (.Var f) (.Var x)), false)] (.Var a)
    checkPassResult "eta_recurse_let_rhs" (etaReduce e) e false

  test "eta_recurse_let_body" do
    let e := Expr.Let [(a, intLit 1, false)]
      (.Lam x (.App (.Var f) (.Var x)))
    checkPassResult "eta_recurse_let_body" (etaReduce e) e false

  test "eta_recurse_case_alt" do
    let e := Expr.Case (.Var x)
      [.Lam y (.App (.Var f) (.Var y)), .Var z]
    checkPassResult "eta_recurse_case_alt" (etaReduce e) e false

  test "eta_recurse_app_fn" do
    let e := Expr.App (.Lam x (.App (.Var f) (.Var x))) (.Var y)
    checkPassResult "eta_recurse_app_fn" (etaReduce e) e false

  test "eta_recurse_delay" do
    let e := Expr.Delay (.Lam x (.App (.Var f) (.Var x)))
    checkPassResult "eta_recurse_delay" (etaReduce e) e false

  test "eta_recurse_constr" do
    let e := Expr.Constr 0 [.Lam x (.App (.Var f) (.Var x)), .Var y]
    checkPassResult "eta_recurse_constr" (etaReduce e) e false

  test "eta_leaves_unchanged" do
    for (name, e) in [("eta_var", Expr.Var x), ("eta_lit", intLit 42),
                       ("eta_builtin", Expr.Builtin .AddInteger), ("eta_error", Expr.Error)] do
      let (r, ch) := etaReduce e
      checkAlphaEq name r e
      check s!"{name}_unchanged" (!ch)

end Test.MIR.Opt.EtaReduce
