import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.DCE

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "dce" do
  test "dce_unused_pure" do
    checkPassResult "dce_unused_var"
      (dce (.Let [(a, .Var y, false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_lit"
      (dce (.Let [(a, intLit 42, false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_lam"
      (dce (.Let [(a, .Lam y (.Var y), false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_delay"
      (dce (.Let [(a, .Delay (.Var y), false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_fix"
      (dce (.Let [(a, .Fix f (.Lam y (.Var y)), false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_builtin"
      (dce (.Let [(a, .Builtin .AddInteger, false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_constr_atoms"
      (dce (.Let [(a, .Constr 0 [.Var y, .Var z], false)] (.Var x))) (.Var x) true
  test "dce_unused_pure_extended" do
    checkPassResult "dce_unused_force"
      (dce (.Let [(a, .Force (.Var x), false)] (.Var y))) (.Var y) true
    checkPassResult "dce_unused_let_rhs"
      (dce (.Let [(a, .Let [(b, intLit 1, false)] (.Var b), false)] (.Var x))) (.Var x) true
    checkPassResult "dce_unused_total_builtin"
      (dce (.Let [(a, .App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2), false)] (.Var y))) (.Var y) true
    checkPassResult "dce_unused_app_kept"
      (dce (.Let [(a, .App (.Var f) (.Var x), false)] (.Var y)))
      (.Let [(a, .App (.Var f) (.Var x), false)] (.Var y)) false
    checkPassResult "dce_unused_constr_app_kept"
      (dce (.Let [(a, .Constr 0 [.App (.Var f) (.Var x)], false)] (.Var y)))
      (.Let [(a, .Constr 0 [.App (.Var f) (.Var x)], false)] (.Var y)) false
    checkPassResult "dce_unused_case_pure"
      (dce (.Let [(a, .Case (.Var x) [.Var y], false)] (.Var z))) (.Var z) true
  test "dce_impure_error" do
    let e4 := Expr.Let [(a, .Error, false)] (.Var x)
    checkPassResult "dce_impure_error" (dce e4) e4 false
    let e5 := Expr.Let [(a, .App .Error (.Var x), false)] (.Var y)
    checkPassResult "dce_impure_app_error" (dce e5) e5 false
    let e6 := Expr.Let [(a, .Case .Error [.Var y], false)] (.Var z)
    checkPassResult "dce_impure_case_error" (dce e6) e6 false
  test "dce_used_kept" do
    let e1 := Expr.Let [(a, intLit 1, false)] (.Var a)
    checkPassResult "dce_used_pure" (dce e1) e1 false
    let e2 := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.Var a)
    checkPassResult "dce_used_impure" (dce e2) e2 false
  test "dce_transitive_2" do
    let e := Expr.Let [(a, intLit 42, false), (b, .Lam y (.Var a), false)] (.Var z)
    checkPassResult "dce_transitive_2" (dce e) (.Var z) true
  test "dce_transitive_3" do
    let e := Expr.Let [(a, intLit 1, false), (b, .Var a, false), (c, .Lam y (.Var b), false)] (.Var x)
    checkPassResult "dce_transitive_3" (dce e) (.Var x) true
  test "dce_transitive_used" do
    let e := Expr.Let [(a, intLit 1, false), (b, .Var a, false)] (.Var b)
    checkPassResult "dce_transitive_used" (dce e) e false
  test "dce_mixed_remove_end" do
    let e := Expr.Let [(a, intLit 1, false), (b, .Var a, false), (c, intLit 2, false)] (.Var b)
    let expected := Expr.Let [(a, intLit 1, false), (b, .Var a, false)] (.Var b)
    checkPassResult "dce_mixed_remove_end" (dce e) expected true
  test "dce_remove_middle" do
    let e := Expr.Let [(a, intLit 1, false), (b, intLit 2, false), (c, intLit 3, false)]
                (.App (.Var a) (.Var c))
    let expected := Expr.Let [(a, intLit 1, false), (c, intLit 3, false)]
                      (.App (.Var a) (.Var c))
    checkPassResult "dce_remove_middle" (dce e) expected true
  test "dce_all_dead" do
    let e := Expr.Let [(a, intLit 1, false), (b, intLit 2, false)] (.Var x)
    checkPassResult "dce_all_dead" (dce e) (.Var x) true
  test "dce_empty_bindings" do
    let e := Expr.Let [] (.Var x)
    checkPassResult "dce_empty_bindings" (dce e) (.Var x) true
  test "dce_recurse" do
    checkPassResult "dce_recurse_lam"
      (dce (.Lam x (.Let [(a, intLit 1, false)] (.Var x))))
      (.Lam x (.Var x)) true
    checkPassResult "dce_recurse_fix"
      (dce (.Fix f (.Let [(a, intLit 1, false)] (.Var f))))
      (.Fix f (.Var f)) true
    checkPassResult "dce_recurse_app_fn"
      (dce (.App (.Let [(a, intLit 1, false)] (.Var f)) (.Var x)))
      (.App (.Var f) (.Var x)) true
    checkPassResult "dce_recurse_app_arg"
      (dce (.App (.Var f) (.Let [(a, intLit 1, false)] (.Var x))))
      (.App (.Var f) (.Var x)) true
    checkPassResult "dce_recurse_force"
      (dce (.Force (.Let [(a, intLit 1, false)] (.Var x))))
      (.Force (.Var x)) true
    checkPassResult "dce_recurse_delay"
      (dce (.Delay (.Let [(a, intLit 1, false)] (.Var x))))
      (.Delay (.Var x)) true
    checkPassResult "dce_recurse_constr"
      (dce (.Constr 0 [.Let [(a, intLit 1, false)] (.Var x)]))
      (.Constr 0 [.Var x]) true
    checkPassResult "dce_recurse_case_scrut"
      (dce (.Case (.Let [(a, intLit 1, false)] (.Var x)) [.Var y]))
      (.Case (.Var x) [.Var y]) true
    checkPassResult "dce_recurse_case_alt"
      (dce (.Case (.Var x) [.Let [(a, intLit 1, false)] (.Var y)]))
      (.Case (.Var x) [.Var y]) true
  test "dce_recurse_let_rhs" do
    let e := Expr.Let [(b, .Let [(a, intLit 1, false)] (.App (.Var f) (.Var x)), false)] (.Var b)
    let expected := Expr.Let [(b, .App (.Var f) (.Var x), false)] (.Var b)
    checkPassResult "dce_recurse_let_rhs" (dce e) expected true
  test "dce_leaves_unchanged" do
    for (name, e) in [("dce_var", Expr.Var x), ("dce_lit", intLit 42),
                       ("dce_builtin", Expr.Builtin .AddInteger), ("dce_error", Expr.Error)] do
      let (r, ch) := dce e
      checkAlphaEq name r e
      check s!"{name}_unchanged" (!ch)

end Test.MIR.Opt.DCE
