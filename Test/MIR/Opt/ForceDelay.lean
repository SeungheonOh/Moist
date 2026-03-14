import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.ForceDelay

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "forceDelay" do
  test "fd_direct" do
    checkPassResult "fd_direct_var"
      (forceDelay (.Force (.Delay (.Var x)))) (.Var x) true
    checkPassResult "fd_direct_app"
      (forceDelay (.Force (.Delay (.App (.Var f) (.Var x))))) (.App (.Var f) (.Var x)) true
    checkPassResult "fd_direct_error"
      (forceDelay (.Force (.Delay .Error))) .Error true
    checkPassResult "fd_direct_nested_delay"
      (forceDelay (.Force (.Delay (.Delay (.Var x))))) (.Delay (.Var x)) true
  test "fd_post_recursion" do
    let e := Expr.Force (.Force (.Delay (.Delay (.Var x))))
    let (r, ch) := forceDelay e
    checkAlphaEq "fd_post_recursion" r (.Var x)
    check "fd_post_recursion_changed" ch
  test "fd_through_let_single" do
    let e := Expr.Let [(v, .Delay (.Var x), false)] (.Force (.Var v))
    let expected := Expr.Let [(v, .Delay (.Var x), false)] (.Var x)
    checkPassResult "fd_through_let_single" (forceDelay e) expected true
  test "fd_through_let_multi_force" do
    let e := Expr.Let [(v, .Delay (.Var x), false)]
                (.App (.Force (.Var v)) (.Force (.Var v)))
    let expected := Expr.Let [(v, .Delay (.Var x), false)]
                      (.App (.Var x) (.Var x))
    checkPassResult "fd_through_let_multi_force" (forceDelay e) expected true
  test "fd_through_let_mixed" do
    let e := Expr.Let [(v, .Delay (.Var x), false)]
                (.App (.Var v) (.Force (.Var v)))
    checkPassResult "fd_through_let_mixed" (forceDelay e) e false
  test "fd_through_let_in_rest" do
    let e := Expr.Let [(v, .Delay (.Var x), false), (b, .Force (.Var v), false)]
                (.Var b)
    let expected := Expr.Let [(v, .Delay (.Var x), false), (b, .Var x, false)]
                      (.Var b)
    checkPassResult "fd_through_let_in_rest" (forceDelay e) expected true
  test "fd_through_let_shadow" do
    let e := Expr.Let [(v, .Delay (.Var x), false)]
                (.Lam v (.Force (.Var v)))
    let (r, ch) := forceDelay e
    checkAlphaEq "fd_through_let_shadow" r e
    check "fd_through_let_shadow_changed" ch
  test "fd_non_delay_binding" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.Force (.Var a))
    checkPassResult "fd_non_delay_binding" (forceDelay e) e false
  test "fd_force_no_cancel" do
    let e1 := Expr.Force (.Var x)
    checkPassResult "fd_force_var" (forceDelay e1) e1 false
    let e2 := Expr.Force (.App (.Var f) (.Var x))
    checkPassResult "fd_force_app" (forceDelay e2) e2 false
  test "fd_recurse" do
    checkPassResult "fd_recurse_lam"
      (forceDelay (.Lam x (.Force (.Delay (.Var x)))))
      (.Lam x (.Var x)) true
    checkPassResult "fd_recurse_fix"
      (forceDelay (.Fix f (.Force (.Delay (.Var f)))))
      (.Fix f (.Var f)) true
    checkPassResult "fd_recurse_app_fn"
      (forceDelay (.App (.Force (.Delay (.Var f))) (.Var x)))
      (.App (.Var f) (.Var x)) true
    checkPassResult "fd_recurse_app_arg"
      (forceDelay (.App (.Var f) (.Force (.Delay (.Var x)))))
      (.App (.Var f) (.Var x)) true
    checkPassResult "fd_recurse_delay_inner"
      (forceDelay (.Delay (.Force (.Delay (.Var x)))))
      (.Delay (.Var x)) true
    checkPassResult "fd_recurse_constr"
      (forceDelay (.Constr 0 [.Force (.Delay (.Var x)), .Var y]))
      (.Constr 0 [.Var x, .Var y]) true
    checkPassResult "fd_recurse_case_scrut"
      (forceDelay (.Case (.Force (.Delay (.Var x))) [.Var y]))
      (.Case (.Var x) [.Var y]) true
    checkPassResult "fd_recurse_case_alt"
      (forceDelay (.Case (.Var x) [.Force (.Delay (.Var y))]))
      (.Case (.Var x) [.Var y]) true
  test "fd_leaves_unchanged" do
    for (name, e) in [("fd_var", Expr.Var x), ("fd_lit", intLit 42),
                       ("fd_builtin", Expr.Builtin .AddInteger), ("fd_error", Expr.Error)] do
      let (r, ch) := forceDelay e
      checkAlphaEq name r e
      check s!"{name}_unchanged" (!ch)
  test "fd_let_rhs_simplify" do
    let e := Expr.Let [(a, .Force (.Delay (.Var x)), false)] (.Var a)
    let expected := Expr.Let [(a, .Var x, false)] (.Var a)
    checkPassResult "fd_let_rhs_simplify" (forceDelay e) expected true

end Test.MIR.Opt.ForceDelay
