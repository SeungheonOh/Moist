import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.InlinePass

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "inlinePass" do
  test "inline_atom_var" do
    let e := Expr.Let [(a, .Var x, false)] (.Var a)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_atom_var" r (.Var x)
    check "inline_atom_var_changed" ch
  test "inline_atom_var_multi" do
    let e := Expr.Let [(a, .Var x, false)] (.App (.Var a) (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_atom_var_multi" r (.App (.Var x) (.Var x))
    check "inline_atom_var_multi_changed" ch
  test "inline_atom_lit" do
    let e := Expr.Let [(a, intLit 42, false)] (.Var a)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_atom_lit" r (intLit 42)
    check "inline_atom_lit_changed" ch
  test "inline_atom_builtin" do
    let e := Expr.Let [(a, .Builtin .AddInteger, false)] (.App (.Var a) (.Var x))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_atom_builtin" r (.App (.Builtin .AddInteger) (.Var x))
    check "inline_atom_builtin_changed" ch
  test "inline_small_lam_dup" do
    let e := Expr.Let [(a, .Lam y (.Var y), false)]
                (.App (.Var a) (.App (.Var a) (.Var z)))
    let (r, ch) := runFresh (inlinePass e) 1000
    let expected := Expr.App (.Lam y (.Var y)) (.App (.Lam y (.Var y)) (.Var z))
    checkAlphaEq "inline_small_lam_dup" r expected
    check "inline_small_lam_dup_changed" ch
  test "inline_small_delay" do
    let e := Expr.Let [(a, .Delay (.Var x), false)] (.Force (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_small_delay" r (.Force (.Delay (.Var x)))
    check "inline_small_delay_changed" ch
  test "inline_large_0_occ" do
    let e := Expr.Let [(a, largeLam, false)] (.Var x)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_large_0_occ" r e
    check "inline_large_0_occ_no_change" (!ch)
  test "inline_large_1_no_fix" do
    let e := Expr.Let [(a, largeLam, false)] (.App (.Var a) (.Var z))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_large_1_no_fix" r (.App largeLam (.Var z))
    check "inline_large_1_no_fix_changed" ch
  test "inline_large_1_under_fix" do
    let e := Expr.Let [(a, largeLam, false)] (.Fix g (.App (.Var a) (.Var g)))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_large_1_under_fix" r e
    check "inline_large_1_under_fix_no_change" (!ch)
  test "inline_large_2_occ" do
    let e := Expr.Let [(a, largeLam, false)] (.App (.Var a) (.App (.Var a) (.Var z)))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_large_2_occ" r e
    check "inline_large_2_occ_no_change" (!ch)
  test "inline_nonval_0_occ" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.Var y)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_nonval_0_occ" r e
    check "inline_nonval_0_occ_no_change" (!ch)
  test "inline_nonval_1_no_fix" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.App (.Var g) (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_nonval_1_no_fix" r (.App (.Var g) (.App (.Var f) (.Var x)))
    check "inline_nonval_1_no_fix_changed" ch
  test "inline_nonval_force" do
    let e := Expr.Let [(a, .Force (.Var x), false)] (.App (.Var a) (.Var y))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_nonval_force" r (.App (.Force (.Var x)) (.Var y))
    check "inline_nonval_force_changed" ch
  test "inline_nonval_case" do
    let e := Expr.Let [(a, .Case (.Var x) [.Var y, .Var z], false)] (.Var a)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_nonval_case" r (.Case (.Var x) [.Var y, .Var z])
    check "inline_nonval_case_changed" ch
  test "inline_nonval_1_under_fix" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.Fix g (.App (.Var a) (.Var g)))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_nonval_1_under_fix" r e
    check "inline_nonval_1_under_fix_no_change" (!ch)
  test "inline_nonval_2_occ" do
    let e := Expr.Let [(a, .App (.Var f) (.Var x), false)] (.App (.Var a) (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_nonval_2_occ" r e
    check "inline_nonval_2_occ_no_change" (!ch)
  test "inline_expensive_across_fix" do
    let rep : VarId := ⟨60, "rep"⟩
    let add := Expr.Builtin .AddInteger
    let expensive :=
      Expr.App (.App add (.App (.App add (.App (.App add (.App (.App add (intLit 1)) (intLit 1))) (intLit 1))) (intLit 1))) (intLit 1)
    let e := Expr.Let
      [(a, expensive, false)]
      (.Fix rep (.Lam n (.App (.App (.Var rep) (.Var n)) (.Var a))))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_expensive_across_fix" r e
    check "inline_expensive_across_fix_no_change" (!ch)
  test "inline_beta_atom" do
    let e := Expr.App (.Lam x (.App (.Var x) (.Var x))) (.Var z)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_beta_atom" r (.App (.Var z) (.Var z))
    check "inline_beta_atom_changed" ch
  test "inline_beta_lit" do
    let e := Expr.App (.Lam x (.Var x)) (intLit 42)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_beta_lit" r (intLit 42)
    check "inline_beta_lit_changed" ch
  test "inline_beta_nonatomic" do
    let e := Expr.App (.Lam x (.Var x)) (.App (.Var f) (.Var y))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_beta_nonatomic" r e
    check "inline_beta_nonatomic_unchanged" (!ch)
  test "inline_beta_non_lam" do
    let e := Expr.App (.Var f) (.Var x)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_beta_non_lam" r e
    check "inline_beta_non_lam_unchanged" (!ch)
  test "inline_multi_cascade" do
    let e := Expr.Let [(a, .Var x, false), (b, .App (.Var a) (.Var y), false)] (.Var b)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_multi_cascade" r (.App (.Var x) (.Var y))
    check "inline_multi_cascade_changed" ch
  test "inline_chain_atoms" do
    let e := Expr.Let [(a, .Var x, false), (b, .Var a, false), (c, .Var b, false)] (.Var c)
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_chain_atoms" r (.Var x)
    check "inline_chain_atoms_changed" ch
  test "inline_occ_count_rest" do
    let e := Expr.Let [(a, largeLam, false), (b, .Var a, false)] (.Var a)
    let (r, ch) := runFresh (inlinePass e) 1000
    let expected := Expr.Let [(a, largeLam, false)] (.Var a)
    checkAlphaEq "inline_occ_count_rest" r expected
    check "inline_occ_count_rest_changed" ch
  test "inline_recurse_lam" do
    let e := Expr.Lam x (.Let [(a, .Var y, false)] (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_lam" r (.Lam x (.Var y))
    check "inline_recurse_lam_changed" ch
  test "inline_recurse_fix" do
    let e := Expr.Fix f (.Let [(a, .Var x, false)] (.App (.Var f) (.Var a)))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_fix" r (.Fix f (.App (.Var f) (.Var x)))
    check "inline_recurse_fix_changed" ch
  test "inline_recurse_delay" do
    let e := Expr.Delay (.Let [(a, .Var x, false)] (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_delay" r (.Delay (.Var x))
    check "inline_recurse_delay_changed" ch
  test "inline_recurse_force" do
    let e := Expr.Force (.Let [(a, .Var x, false)] (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_force" r (.Force (.Var x))
    check "inline_recurse_force_changed" ch
  test "inline_recurse_constr" do
    let e := Expr.Constr 0 [.Let [(a, .Var x, false)] (.Var a)]
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_constr" r (.Constr 0 [.Var x])
    check "inline_recurse_constr_changed" ch
  test "inline_recurse_case_scrut" do
    let e := Expr.Case (.Let [(a, .Var x, false)] (.Var a)) [.Var y]
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_case_scrut" r (.Case (.Var x) [.Var y])
    check "inline_recurse_case_scrut_changed" ch
  test "inline_recurse_case_alt" do
    let e := Expr.Case (.Var x) [.Let [(a, .Var y, false)] (.Var a)]
    let (r, ch) := runFresh (inlinePass e) 1000
    checkAlphaEq "inline_recurse_case_alt" r (.Case (.Var x) [.Var y])
    check "inline_recurse_case_alt_changed" ch
  test "inline_capture_avoid" do
    let e := Expr.Let [(a, .Lam y (.Var z), false)] (.Lam z (.Var a))
    let (r, ch) := runFresh (inlinePass e) 1000
    let expected := Expr.Lam t1 (.Lam y (.Var z))
    checkAlphaEq "inline_capture_avoid" r expected
    check "inline_capture_avoid_changed" ch
  test "inline_leaves_unchanged" do
    for (name, e) in [("inline_var", Expr.Var x), ("inline_lit", intLit 42),
                       ("inline_builtin", Expr.Builtin .AddInteger),
                       ("inline_error", Expr.Error)] do
      let (r, ch) := runFresh (inlinePass e) 1000
      checkAlphaEq name r e
      check s!"{name}_unchanged" (!ch)

end Test.MIR.Opt.InlinePass
