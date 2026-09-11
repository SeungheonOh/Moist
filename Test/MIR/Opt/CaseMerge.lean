import Test.MIR.Helpers
import Moist.MIR.Optimize
import Test.MIR.Opt.Soundness

namespace Test.MIR.Opt.CaseMerge

open Moist.MIR
open Test.MIR
open Test.Framework

/-! ## Extra fixtures for case merge tests (uids 70+) -/

private def f0 : VarId := ⟨70, .source, "f0"⟩
private def f1 : VarId := ⟨71, .source, "f1"⟩
private def f2 : VarId := ⟨72, .source, "f2"⟩
private def f3 : VarId := ⟨73, .source, "f3"⟩
private def g0 : VarId := ⟨74, .source, "g0"⟩
private def g1 : VarId := ⟨75, .source, "g1"⟩
private def g2 : VarId := ⟨76, .source, "g2"⟩
private def g3 : VarId := ⟨77, .source, "g3"⟩
private def t1 : VarId := ⟨80, .source, "t1"⟩
private def t2 : VarId := ⟨81, .source, "t2"⟩
private def r  : VarId := ⟨82, .source, "r"⟩

def tests : TestTree := suite "caseMerge" do
  test "cm_basic_two_cases" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
       (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
      (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2))
    checkPassResult "cm_basic_two_cases" (caseMergePass e) e false

  test "cm_two_ctors" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0), .Lam f0 (.Lam f1 (.Var f0))], false),
       (t2, .Case (.Var x) [.Lam g0 (.Var g0), .Lam g0 (.Lam g1 (.Var g1))], false)]
      (.Constr 0 [.Var t1, .Var t2])
    checkPassResult "cm_two_ctors" (caseMergePass e) e false

  test "cm_different_scrutinees" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.Var y) [.Lam g0 (.Var g0)], false)]
      (.App (.Var t1) (.Var t2))
    checkPassResult "cm_different_scrutinees" (caseMergePass e) e false

  test "cm_single_case" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false)]
      (.Var t1)
    checkPassResult "cm_single_case" (caseMergePass e) e false

  test "cm_bindings_between" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
       (r,  .App (.App (.Builtin .AddInteger) (.Var t1)) (intLit 1), false),
       (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false)]
      (.App (.App (.Builtin .AddInteger) (.Var r)) (.Var t2))
    checkPassResult "cm_bindings_between" (caseMergePass e) e false

  test "cm_bindings_before" do
    let e := Expr.Let
      [(r,  .App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2), false),
       (t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.Var x) [.Lam g0 (.Var g0)], false)]
      (.App (.App (.Builtin .AddInteger) (.Var r))
        (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2)))
    checkPassResult "cm_bindings_before" (caseMergePass e) e false

  test "cm_scrutinee_shadowed" do
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (x,  intLit 42, false),
       (t2, .Case (.Var x) [.Lam g0 (.Var g0)], false)]
      (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2))
    let closed := Expr.Let [(x, .Constr 0 [intLit 1], false)] e
    let (result, changed) := caseMergePass closed
    check "cm_scrutinee_shadowed_changed" changed
    Soundness.preserves "cm_scrutinee_shadowed" closed result

  test "cm_known_ctor_resolution" do
    let e := Expr.Let
      [(t1, .Case (.Var x)
        [.Lam f0 (.Lam f1 (.Var f0)),
         .Lam f0 (.Lam f1 (.Lam f2 (.Var f2)))], false),
       (t2, .Case (.Var x)
        [.Lam g0 (.Lam g1 (.Var g1)),
         .Lam g0 (.Lam g1 (.Lam g2 (.Var g0)))], false)]
      (.Constr 0 [.Var t1, .Var t2])
    let closed := Expr.Let [(x, .Constr 0 [intLit 1, intLit 2], false)] e
    let (result, changed) := caseMergePass closed
    check "cm_known_ctor_resolution_changed" changed
    Soundness.preserves "cm_known_ctor_resolution" closed result

  test "cm_triple_case" do
    let t3 : VarId := ⟨83, .source, "t3"⟩
    let h0 : VarId := ⟨84, .source, "h0"⟩
    let h1 : VarId := ⟨85, .source, "h1"⟩
    let e := Expr.Let
      [(t1, .Case (.Var x) [.Lam f0 (.Lam f1 (.Var f0))], false),
       (t2, .Case (.Var x) [.Lam g0 (.Lam g1 (.Var g1))], false),
       (t3, .Case (.Var x) [.Lam h0 (.Lam h1
         (.App (.App (.Builtin .AddInteger) (.Var h0)) (.Var h1)))], false)]
      (.Constr 0 [.Var t1, .Var t2, .Var t3])
    checkPassResult "cm_triple_case" (caseMergePass e) e false

  test "cm_non_case_first" do
    let e := Expr.Let
      [(r,  intLit 100, false),
       (t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.Var x) [.Lam g0 (.App (.App (.Builtin .AddInteger) (.Var g0)) (.Var r))], false)]
      (.App (.App (.Builtin .AddInteger) (.Var t1)) (.Var t2))
    checkPassResult "cm_non_case_first" (caseMergePass e) e false

  test "cm_recurse_lam" do
    let e := Expr.Lam z
      (.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var x) [.Lam g0 (.App (.Var g0) (.Var z))], false)]
        (.App (.Var t1) (.Var t2)))
    checkPassResult "cm_recurse_lam" (caseMergePass e) e false

  test "cm_recurse_fix" do
    let e := Expr.Fix f
      (.Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var x) [.Lam g0 (.App (.Var f) (.Var g0))], false)]
        (.App (.Var t1) (.Var t2)))
    checkPassResult "cm_recurse_fix" (caseMergePass e) e false

  test "cm_recurse_let_rhs" do
    let e := Expr.Let
      [(r, .Let
        [(t1, .Case (.Var x) [.Lam f0 (.Var f0)], false),
         (t2, .Case (.Var x) [.Lam g0 (.Var g0)], false)]
        (.App (.Var t1) (.Var t2)), false)]
      (.Var r)
    checkPassResult "cm_recurse_let_rhs" (caseMergePass e) e false

  test "cm_leaves_unchanged" do
    for (name, e) in [("cm_var", Expr.Var x), ("cm_lit", intLit 42),
                       ("cm_builtin", Expr.Builtin .AddInteger), ("cm_error", Expr.Error)] do
      let (_, ch) := caseMergePass e
      check s!"{name}_unchanged" (!ch)

  test "cm_non_var_scrutinee" do
    let e := Expr.Let
      [(t1, .Case (.App (.Var f) (.Var x)) [.Lam f0 (.Var f0)], false),
       (t2, .Case (.App (.Var f) (.Var x)) [.Lam g0 (.Var g0)], false)]
      (.App (.Var t1) (.Var t2))
    checkPassResult "cm_non_var_scrutinee" (caseMergePass e) e false

end Test.MIR.Opt.CaseMerge
