import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.ExprStructEq

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "exprStructEq" do
  test "exprStructEq" do
    check "structEq_var_same" (exprStructEq (.Var x) (.Var x))
    check "structEq_lit_int" (exprStructEq (intLit 1) (intLit 1))
    check "structEq_lit_bool" (exprStructEq (boolLit true) (boolLit true))
    check "structEq_builtin_same" (exprStructEq (.Builtin .AddInteger) (.Builtin .AddInteger))
    check "structEq_error" (exprStructEq .Error .Error)
    check "structEq_lam_same" (exprStructEq (.Lam x (.Var x)) (.Lam x (.Var x)))
    check "structEq_fix_same" (exprStructEq (.Fix f (.Var f)) (.Fix f (.Var f)))
    check "structEq_app_same" (exprStructEq (.App (.Var f) (.Var x)) (.App (.Var f) (.Var x)))
    check "structEq_force_same" (exprStructEq (.Force (.Var x)) (.Force (.Var x)))
    check "structEq_delay_same" (exprStructEq (.Delay (.Var x)) (.Delay (.Var x)))
    check "structEq_constr_same" (exprStructEq (.Constr 0 [.Var x, .Var y]) (.Constr 0 [.Var x, .Var y]))
    check "structEq_constr_empty" (exprStructEq (.Constr 0 []) (.Constr 0 []))
    check "structEq_case_same" (exprStructEq (.Case (.Var x) [.Var y]) (.Case (.Var x) [.Var y]))
    check "structEq_let_same" (exprStructEq (.Let [(a, .Var x, false)] (.Var a)) (.Let [(a, .Var x, false)] (.Var a)))
    check "structEq_var_diff" (!exprStructEq (.Var x) (.Var y))
    check "structEq_lit_diff_val" (!exprStructEq (intLit 1) (intLit 2))
    check "structEq_lit_diff_type" (!exprStructEq (intLit 1) (boolLit true))
    check "structEq_builtin_diff" (!exprStructEq (.Builtin .AddInteger) (.Builtin .SubtractInteger))
    check "structEq_lam_diff_binder" (!exprStructEq (.Lam x (.Var x)) (.Lam y (.Var y)))
    check "structEq_fix_diff_binder" (!exprStructEq (.Fix f (.Var f)) (.Fix g (.Var g)))
    check "structEq_app_diff_fun" (!exprStructEq (.App (.Var f) (.Var x)) (.App (.Var g) (.Var x)))
    check "structEq_app_diff_arg" (!exprStructEq (.App (.Var f) (.Var x)) (.App (.Var f) (.Var y)))
    check "structEq_constr_diff_tag" (!exprStructEq (.Constr 0 [.Var x]) (.Constr 1 [.Var x]))
    check "structEq_constr_diff_args" (!exprStructEq (.Constr 0 [.Var x]) (.Constr 0 [.Var y]))
    check "structEq_constr_diff_len" (!exprStructEq (.Constr 0 [.Var x]) (.Constr 0 [.Var x, .Var y]))
    check "structEq_let_diff_binder" (!exprStructEq (.Let [(a, .Var x, false)] (.Var a)) (.Let [(b, .Var x, false)] (.Var b)))
    check "structEq_cross_ctor" (!exprStructEq (.Var x) (intLit 1))
    check "structEq_cross_ctor2" (!exprStructEq (.Lam x (.Var x)) (.Fix x (.Var x)))

end Test.MIR.Opt.ExprStructEq
