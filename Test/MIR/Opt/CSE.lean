import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.CSE

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "cse" do
  test "cse_dup_app" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false),
                        (b, .App (.Var f) (.Var x), false)]
                (.App (.Var a) (.Var b))
    let expected := Expr.Let [(a, .App (.Var f) (.Var x), false)]
                      (.App (.Var a) (.Var a))
    checkPassResult "cse_dup_app" (cse e) expected true
  test "cse_no_dup" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false),
                        (b, .App (.Var f) (.Var y), false)]
                (.App (.Var a) (.Var b))
    checkPassResult "cse_no_dup" (cse e) e false
  test "cse_triple_dup" do
    let e := Expr.Let [(a, .Force (.Var x), false),
                        (b, .Force (.Var x), false),
                        (c, .Force (.Var x), false)]
                (.Constr 0 [.Var a, .Var b, .Var c])
    let expected := Expr.Let [(a, .Force (.Var x), false)]
                      (.Constr 0 [.Var a, .Var a, .Var a])
    checkPassResult "cse_triple_dup" (cse e) expected true
  test "cse_dup_var" do
    let e := Expr.Let [(a, .Var x, false), (b, .Var x, false)]
                (.App (.Var a) (.Var b))
    let expected := Expr.Let [(a, .Var x, false)]
                      (.App (.Var a) (.Var a))
    checkPassResult "cse_dup_var" (cse e) expected true
  test "cse_dup_delay" do
    let e := Expr.Let [(a, .Delay (.Var x), false), (b, .Delay (.Var x), false)]
                (.App (.Var a) (.Var b))
    let expected := Expr.Let [(a, .Delay (.Var x), false)]
                      (.App (.Var a) (.Var a))
    checkPassResult "cse_dup_delay" (cse e) expected true
  test "cse_dup_constr" do
    let e := Expr.Let [(a, .Constr 0 [.Var x, .Var y], false),
                        (b, .Constr 0 [.Var x, .Var y], false)]
                (.App (.Var a) (.Var b))
    let expected := Expr.Let [(a, .Constr 0 [.Var x, .Var y], false)]
                      (.App (.Var a) (.Var a))
    checkPassResult "cse_dup_constr" (cse e) expected true
  test "cse_dup_renames_rest" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false),
                        (b, .App (.Var f) (.Var x), false),
                        (c, .App (.Var g) (.Var b), false)]
                (.Var c)
    let expected := Expr.Let [(a, .App (.Var f) (.Var x), false),
                               (c, .App (.Var g) (.Var a), false)]
                      (.Var c)
    checkPassResult "cse_dup_renames_rest" (cse e) expected true
  test "cse_single_binding" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.Var a)
    checkPassResult "cse_single_binding" (cse e) e false
  test "cse_recurse_lam" do
    let e := Expr.Lam z
      (.Let [(a, .App (.Var f) (.Var z), false), (b, .App (.Var f) (.Var z), false)]
        (.App (.Var a) (.Var b)))
    let expected := Expr.Lam z
      (.Let [(a, .App (.Var f) (.Var z), false)]
        (.App (.Var a) (.Var a)))
    checkPassResult "cse_recurse_lam" (cse e) expected true
  test "cse_recurse_fix" do
    let e := Expr.Fix g
      (.Let [(a, .Var x, false), (b, .Var x, false)]
        (.App (.Var a) (.Var b)))
    let expected := Expr.Fix g
      (.Let [(a, .Var x, false)]
        (.App (.Var a) (.Var a)))
    checkPassResult "cse_recurse_fix" (cse e) expected true
  test "cse_recurse_let_rhs" do
    let e := Expr.Let
      [(c, .Let [(a, .Var x, false), (b, .Var x, false)] (.App (.Var a) (.Var b)), false)]
      (.Var c)
    let expected := Expr.Let
      [(c, .Let [(a, .Var x, false)] (.App (.Var a) (.Var a)), false)]
      (.Var c)
    checkPassResult "cse_recurse_let_rhs" (cse e) expected true
  test "cse_recurse_case_alt" do
    let e := Expr.Case (.Var x)
      [.Let [(a, .Var y, false), (b, .Var y, false)] (.App (.Var a) (.Var b))]
    let expected := Expr.Case (.Var x)
      [.Let [(a, .Var y, false)] (.App (.Var a) (.Var a))]
    checkPassResult "cse_recurse_case_alt" (cse e) expected true
  test "cse_recurse_delay" do
    let e := Expr.Delay
      (.Let [(a, .Var x, false), (b, .Var x, false)] (.App (.Var a) (.Var b)))
    let expected := Expr.Delay
      (.Let [(a, .Var x, false)] (.App (.Var a) (.Var a)))
    checkPassResult "cse_recurse_delay" (cse e) expected true
  test "cse_recurse_app" do
    let e := Expr.App
      (.Let [(a, .Var x, false), (b, .Var x, false)] (.App (.Var a) (.Var b)))
      (.Var y)
    let expected := Expr.App
      (.Let [(a, .Var x, false)] (.App (.Var a) (.Var a)))
      (.Var y)
    checkPassResult "cse_recurse_app" (cse e) expected true
  test "cse_separate_lets_no_merge" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)]
      (.Let [(b, .App (.Var f) (.Var x), false)]
        (.App (.Var a) (.Var b)))
    checkPassResult "cse_separate_lets_no_merge" (cse e) e false
  test "cse_atom_var" do
    let (r, ch) := cse (.Var x)
    checkAlphaEq "cse_atom_var" r (.Var x)
    check "cse_atom_var_unchanged" (!ch)

end Test.MIR.Opt.CSE
