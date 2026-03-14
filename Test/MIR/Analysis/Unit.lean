import Test.MIR.Helpers

namespace Test.MIR.Analysis.Unit

open Moist.MIR
open Test.MIR
open Test.Framework

def unitTree : TestTree := suite "unit" do
  group "isAtom" do
    test "isAtom" do
      check "isAtom_var" (Expr.Var x).isAtom
      check "isAtom_lit" (intLit 42).isAtom
      check "isAtom_builtin" (Expr.Builtin .AddInteger).isAtom
      check "not_isAtom_app" (!(Expr.App (.Var f) (.Var x)).isAtom)
      check "not_isAtom_lam" (!(Expr.Lam x (.Var x)).isAtom)
      check "not_isAtom_let" (!(Expr.Let [(x, .Var y, false)] (.Var x)).isAtom)
      check "not_isAtom_error" (!Expr.Error.isAtom)
  group "isValue" do
    test "isValue" do
      check "isValue_var" (Expr.Var x).isValue
      check "isValue_lit" (intLit 42).isValue
      check "isValue_builtin" (Expr.Builtin .AddInteger).isValue
      check "isValue_lam" (Expr.Lam x (.Var x)).isValue
      check "isValue_delay" (Expr.Delay (.Var x)).isValue
      check "isValue_fix" (Expr.Fix f (.Lam x (.Var x))).isValue
      check "not_isValue_app" (!(Expr.App (.Var f) (.Var x)).isValue)
      check "not_isValue_force" (!(Expr.Force (.Var x)).isValue)
      check "not_isValue_constr" (!(Expr.Constr 0 [.Var x]).isValue)
  group "freeVars" do
    test "basic" do
      check "fv_var" ((freeVars (.Var x)).contains x)
      check "fv_var_only" (!(freeVars (.Var x)).contains y)
      check "fv_lit_empty" ((freeVars (intLit 42)).data.isEmpty)
      check "fv_builtin_empty" ((freeVars (.Builtin .AddInteger)).data.isEmpty)
      check "fv_error_empty" ((freeVars .Error).data.isEmpty)
    test "lam" do
      check "fv_lam_binds" (!(freeVars (.Lam x (.Var x))).contains x)
      check "fv_lam_free" ((freeVars (.Lam x (.Var y))).contains y)
      check "fv_lam_free_not_bound" (!(freeVars (.Lam x (.Var y))).contains x)
    test "app" do
      let e := Expr.App (.Var x) (.Var y)
      let fv := freeVars e
      check "fv_app_left" (fv.contains x)
      check "fv_app_right" (fv.contains y)
    test "fix" do
      let e := Expr.Fix f (.Lam x (.App (.Var f) (.Var x)))
      let fv := freeVars e
      check "fv_fix_binds_self" (!fv.contains f)
      check "fv_fix_lam_binds_param" (!fv.contains x)
      check "fv_fix_closed" (fv.data.isEmpty)
    test "let_sequential" do
      let e := Expr.Let
        [(x, .Var a, false),
         (y, .App (.Var x) (.Var b), false)]
        (.App (.Var x) (.Var y))
      let fv := freeVars e
      check "fv_let_seq_a_free" (fv.contains a)
      check "fv_let_seq_b_free" (fv.contains b)
      check "fv_let_seq_x_bound" (!fv.contains x)
      check "fv_let_seq_y_bound" (!fv.contains y)
    test "let_forward_ref" do
      let e := Expr.Let
        [(x, .Var y, false),
         (y, intLit 1, false)]
        (.Var x)
      let fv := freeVars e
      check "fv_let_forward_ref_y_free" (fv.contains y)
  group "noSelfRef" do
    test "noSelfRef" do
      check "noSelfRef_ok" (noSelfRef [(x, .Var y, false)])
      check "noSelfRef_ok_refs_earlier" (noSelfRef [(x, intLit 1, false), (y, .Var x, false)])
      check "noSelfRef_fail" (!(noSelfRef [(x, .Var x, false)]))
      check "noSelfRef_fail_second" (!(noSelfRef [(x, intLit 1, false), (y, .App (.Var y) (.Var x), false)]))
      check "noSelfRef_empty" (noSelfRef [])
  group "countOccurrences" do
    test "basic" do
      checkEq "count_zero" (countOccurrences x (intLit 42)) 0
      checkEq "count_one" (countOccurrences x (.Var x)) 1
      checkEq "count_two" (countOccurrences x (.App (.Var x) (.Var x))) 2
    test "shadowed_lam" do
      checkEq "count_shadowed_lam" (countOccurrences x (.Lam x (.Var x))) 0
    test "let_before_shadow" do
      let e := Expr.Let
        [(y, .Var x, false),
         (x, intLit 1, false)]
        (.Var x)
      checkEq "count_let_before_shadow" (countOccurrences x e) 1
    test "let_no_shadow" do
      let e := Expr.Let [(y, .Var x, false)] (.Var x)
      checkEq "count_let_no_shadow" (countOccurrences x e) 2
  group "exprSize" do
    test "exprSize" do
      checkEq "size_var" (exprSize (.Var x)) 1
      checkEq "size_lit" (exprSize (intLit 42)) 1
      checkEq "size_app" (exprSize (.App (.Var f) (.Var x))) 3
      checkEq "size_lam" (exprSize (.Lam x (.Var x))) 2
      checkEq "size_let" (exprSize (.Let [(x, intLit 1, false)] (.Var x))) 3
  group "isANF" do
    test "valid" do
      check "isANF_var" (Expr.Var x).isANF
      check "isANF_lit" (intLit 42).isANF
      check "isANF_builtin" (Expr.Builtin .AddInteger).isANF
      check "isANF_error" Expr.Error.isANF
      check "isANF_app_atoms" (Expr.App (.Var f) (.Var x)).isANF
      check "isANF_force_atom" (Expr.Force (.Var x)).isANF
      check "isANF_constr_atoms" (Expr.Constr 0 [.Var x, .Var y]).isANF
      check "isANF_case_atom_scrut" (Expr.Case (.Var x) [.Var y, .Var z]).isANF
      check "isANF_lam_anf_body" (Expr.Lam x (.App (.Var f) (.Var x))).isANF
      check "isANF_let_valid" (Expr.Let [(x, intLit 1, false)] (.Var x)).isANF
    test "invalid" do
      check "not_isANF_app_complex_fun"
        (!(Expr.App (.App (.Var f) (.Var x)) (.Var y)).isANF)
      check "not_isANF_app_complex_arg"
        (!(Expr.App (.Var f) (.App (.Var g) (.Var x))).isANF)
      check "not_isANF_force_complex"
        (!(Expr.Force (.App (.Var f) (.Var x))).isANF)
      check "not_isANF_constr_complex"
        (!(Expr.Constr 0 [.App (.Var f) (.Var x)]).isANF)
      check "not_isANF_self_ref"
        (!(Expr.Let [(x, .Var x, false)] (.Var x)).isANF)
  group "uncurryApp" do
    test "uncurryApp" do
      let (head, args) := uncurryApp (.App (.App (.Var f) (.Var x)) (.Var y))
      check "uncurry_head" (alphaEq head (.Var f))
      checkEq "uncurry_args_len" args.length 2
  group "isClosed_fixIsRecursive" do
    test "isClosed" do
      check "isClosed_lit" (isClosed (intLit 42))
      check "not_isClosed_var" (!isClosed (.Var x))
      check "isClosed_lam" (isClosed (.Lam x (.Var x)))
    test "fixIsRecursive" do
      check "fixIsRecursive_yes" (fixIsRecursive f (.App (.Var f) (.Var x)))
      check "fixIsRecursive_no" (!fixIsRecursive f (.Var x))

end Test.MIR.Analysis.Unit
