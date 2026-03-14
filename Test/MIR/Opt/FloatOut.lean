import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.FloatOut

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "floatOut" do
  test "leaves_unchanged" do
    let leaves : List (String × Expr) :=
      [("float_var", .Var x), ("float_lit", intLit 42),
       ("float_builtin", .Builtin .AddInteger), ("float_error", .Error)]
    for (name, e) in leaves do
      let (r, ch) := floatOut e
      checkAlphaEq name r e
      check s!"{name}_unchanged" (!ch)
  test "float_pure_out_of_lam" do
    let e := Expr.Lam x (.Let [(a, intLit 1, false)] (.Var a))
    let expected := Expr.Let [(a, intLit 1, false)] (.Lam x (.Var a))
    checkPassResult "float_pure_out_of_lam" (floatOut e) expected true
  test "float_pure_var_out_of_lam" do
    let e := Expr.Lam x (.Let [(a, .Var y, false)] (.App (.Var a) (.Var x)))
    let expected := Expr.Let [(a, .Var y, false)] (.Lam x (.App (.Var a) (.Var x)))
    checkPassResult "float_pure_var_out_of_lam" (floatOut e) expected true
  test "float_mentions_binder" do
    let e := Expr.Lam x (.Let [(a, .App (.Var x) (.Var x), false)] (.Var a))
    checkPassResult "float_mentions_binder" (floatOut e) e false
  test "float_pure_mentions_binder" do
    let e := Expr.Lam x (.Let [(a, .Var x, false)] (.Var a))
    checkPassResult "float_pure_mentions_binder" (floatOut e) e false
  test "float_impure_app_stays" do
    let e := Expr.Lam x (.Let [(a, .App (.Var f) (.Var y), false)] (.Var a))
    checkPassResult "float_impure_app_stays" (floatOut e) e false
  test "float_total_builtin_out" do
    let e := Expr.Lam x (.Let [(a, .App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2), false)] (.Var a))
    let expected := Expr.Let [(a, .App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2), false)] (.Lam x (.Var a))
    checkPassResult "float_total_builtin_out" (floatOut e) expected true
  test "float_pure_force_out" do
    let e := Expr.Lam x (.Let [(a, .Force (.Var y), false)] (.Var a))
    let expected := Expr.Let [(a, .Force (.Var y), false)] (.Lam x (.Var a))
    checkPassResult "float_pure_force_out" (floatOut e) expected true
  test "float_mixed_partition" do
    let e := Expr.Lam x
      (.Let [(a, intLit 1, false), (b, .App (.Var a) (.Var x), false)]
        (.App (.Var a) (.Var b)))
    let expected := Expr.Let [(a, intLit 1, false)]
      (.Lam x (.Let [(b, .App (.Var a) (.Var x), false)]
        (.App (.Var a) (.Var b))))
    checkPassResult "float_mixed_partition" (floatOut e) expected true
  test "float_all_float" do
    let e := Expr.Lam x (.Let [(a, intLit 1, false), (b, intLit 2, false)] (.Var x))
    let expected := Expr.Let [(a, intLit 1, false), (b, intLit 2, false)] (.Lam x (.Var x))
    checkPassResult "float_all_float" (floatOut e) expected true
  test "float_all_stay" do
    let e := Expr.Lam x
      (.Let [(a, .App (.Var x) (.Var x), false), (b, .App (.Var f) (.Var x), false)]
        (.App (.Var a) (.Var b)))
    checkPassResult "float_all_stay" (floatOut e) e false
  test "float_seq_dep_stay" do
    let e := Expr.Lam x
      (.Let [(a, .App (.Var x) (.Var x), false), (b, .Lam y (.Var a), false)]
        (.App (.Var a) (.Var b)))
    checkPassResult "float_seq_dep_stay" (floatOut e) e false
  test "float_seq_dep_chain" do
    let e := Expr.Lam x
      (.Let [(a, .App (.Var x) (.Var y), false), (b, .Var a, false), (c, intLit 1, false)]
        (.App (.Var b) (.Var c)))
    let expected := Expr.Let [(c, intLit 1, false)]
      (.Lam x
        (.Let [(a, .App (.Var x) (.Var y), false), (b, .Var a, false)]
          (.App (.Var b) (.Var c))))
    checkPassResult "float_seq_dep_chain" (floatOut e) expected true
  test "float_seq_pure_chain_floats" do
    let e := Expr.Lam x
      (.Let [(a, intLit 1, false), (b, .Lam y (.Var a), false)]
        (.App (.Var b) (.Var x)))
    let expected := Expr.Let [(a, intLit 1, false), (b, .Lam y (.Var a), false)]
      (.Lam x (.App (.Var b) (.Var x)))
    checkPassResult "float_seq_pure_chain_floats" (floatOut e) expected true
  test "float_fix_pure" do
    let e := Expr.Fix f (.Let [(a, intLit 1, false)] (.Lam x (.App (.Var f) (.Var a))))
    let expected := Expr.Let [(a, intLit 1, false)] (.Fix f (.Lam x (.App (.Var f) (.Var a))))
    checkPassResult "float_fix_pure" (floatOut e) expected true
  test "float_fix_mentions_binder" do
    let e := Expr.Fix f (.Let [(a, .Var f, false)] (.Lam x (.Var a)))
    checkPassResult "float_fix_mentions_binder" (floatOut e) e false
  test "float_body_not_let" do
    let e := Expr.Lam x (.Var y)
    checkPassResult "float_body_not_let" (floatOut e) e false
  test "float_body_app" do
    let e := Expr.Lam x (.App (.Var f) (.Var x))
    checkPassResult "float_body_app" (floatOut e) e false
  test "float_inside_delay_at_lam" do
    let e := Expr.Delay (.Lam x (.Let [(a, intLit 1, false)] (.Var a)))
    let expected := Expr.Delay (.Let [(a, intLit 1, false)] (.Lam x (.Var a)))
    checkPassResult "float_inside_delay_at_lam" (floatOut e) expected true
  test "float_recurse_app" do
    let e := Expr.App (.Lam x (.Let [(a, intLit 1, false)] (.Var a))) (.Var y)
    let expected := Expr.App (.Let [(a, intLit 1, false)] (.Lam x (.Var a))) (.Var y)
    checkPassResult "float_recurse_app" (floatOut e) expected true
  test "float_recurse_force" do
    let e := Expr.Force (.Lam x (.Let [(a, intLit 1, false)] (.Var a)))
    let expected := Expr.Force (.Let [(a, intLit 1, false)] (.Lam x (.Var a)))
    checkPassResult "float_recurse_force" (floatOut e) expected true
  test "float_recurse_constr" do
    let e := Expr.Constr 0 [.Lam x (.Let [(a, intLit 1, false)] (.Var a)), .Var y]
    let expected := Expr.Constr 0 [.Let [(a, intLit 1, false)] (.Lam x (.Var a)), .Var y]
    checkPassResult "float_recurse_constr" (floatOut e) expected true
  test "float_recurse_let_rhs" do
    let e := Expr.Let [(b, .Lam x (.Let [(a, intLit 1, false)] (.Var a)), false)] (.Var b)
    let expected := Expr.Let [(b, .Let [(a, intLit 1, false)] (.Lam x (.Var a)), false)] (.Var b)
    checkPassResult "float_recurse_let_rhs" (floatOut e) expected true
  test "float_recurse_let_body" do
    let e := Expr.Let [(b, intLit 1, false)] (.Lam x (.Let [(a, intLit 2, false)] (.Var a)))
    let expected := Expr.Let [(b, intLit 1, false), (a, intLit 2, false)] (.Lam x (.Var a))
    checkPassResult "float_recurse_let_body" (floatOut e) expected true
  test "float_recurse_case_alt" do
    let e := Expr.Case (.Var x) [.Lam y (.Let [(a, intLit 1, false)] (.Var a)), .Var z]
    let expected := Expr.Let [(a, intLit 1, false)] (.Case (.Var x) [.Lam y (.Var a), .Var z])
    checkPassResult "float_recurse_case_alt" (floatOut e) expected true
  test "float_case_pure_binding" do
    let e := Expr.Case (.Var x) [.Let [(a, intLit 1, false)] (.App (.Var a) (.Var x)), .Var z]
    let expected := Expr.Let [(a, intLit 1, false)] (.Case (.Var x) [.App (.Var a) (.Var x), .Var z])
    checkPassResult "float_case_pure_binding" (floatOut e) expected true
  test "float_case_impure_stays" do
    let e := Expr.Case (.Var x) [.Let [(a, .Error, false)] (.Var a), .Var z]
    checkPassResult "float_case_impure_stays" (floatOut e) e false
  test "float_case_mixed" do
    let e := Expr.Case (.Var x)
      [.Let [(a, intLit 1, false), (b, .Error, false)] (.App (.Var a) (.Var b)), .Var z]
    let expected := Expr.Let [(a, intLit 1, false)]
      (.Case (.Var x) [.Let [(b, .Error, false)] (.App (.Var a) (.Var b)), .Var z])
    checkPassResult "float_case_mixed" (floatOut e) expected true
  test "float_case_multi_alt" do
    let e := Expr.Case (.Var x)
      [.Let [(a, intLit 1, false)] (.App (.Var a) (.Var x)),
       .Let [(b, intLit 2, false)] (.App (.Var b) (.Var x))]
    let expected := Expr.Let [(a, intLit 1, false), (b, intLit 2, false)]
      (.Case (.Var x) [.App (.Var a) (.Var x), .App (.Var b) (.Var x)])
    checkPassResult "float_case_multi_alt" (floatOut e) expected true
  test "float_empty_let" do
    let e := Expr.Lam x (.Let [] (.Var y))
    checkPassResult "float_empty_let" (floatOut e) e false

end Test.MIR.Opt.FloatOut
