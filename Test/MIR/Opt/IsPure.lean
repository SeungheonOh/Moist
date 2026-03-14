import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.IsPure

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "isPure" do
  test "isPure" do
    check "isPure_var" (isPure (.Var x))
    check "isPure_lit_int" (isPure (intLit 42))
    check "isPure_lit_bool" (isPure (boolLit true))
    check "isPure_builtin" (isPure (.Builtin .AddInteger))
    check "isPure_lam" (isPure (.Lam x (.Var x)))
    check "isPure_lam_impure_body" (isPure (.Lam x (.App (.Var x) (.Var x))))
    check "isPure_lam_error_body" (isPure (.Lam x .Error))
    check "isPure_delay" (isPure (.Delay (.Var x)))
    check "isPure_delay_error" (isPure (.Delay .Error))
    check "isPure_delay_app" (isPure (.Delay (.App (.Var f) (.Var x))))
    check "isPure_fix" (isPure (.Fix f (.Lam x (.Var x))))
    check "isPure_fix_recursive" (isPure (.Fix f (.Lam x (.App (.Var f) (.Var x)))))
    check "isPure_constr_empty" (isPure (.Constr 0 []))
    check "isPure_constr_vars" (isPure (.Constr 0 [.Var x, .Var y]))
    check "isPure_constr_lits" (isPure (.Constr 1 [intLit 1, intLit 2]))
    check "isPure_constr_builtin" (isPure (.Constr 0 [.Builtin .AddInteger]))
    check "isPure_constr_mixed_atoms" (isPure (.Constr 0 [.Var x, intLit 1, .Builtin .AddInteger]))
    check "isPure_constr_lam_arg" (isPure (.Constr 0 [.Lam x (.Var x)]))
    check "isPure_constr_delay_arg" (isPure (.Constr 0 [.Delay (.Var x)]))
    check "isPure_constr_app_arg" (!isPure (.Constr 0 [.App (.Var f) (.Var x)]))
    check "isPure_constr_one_good" (!isPure (.Constr 0 [.Var x, .App (.Var f) (.Var y)]))
    check "isPure_constr_first_good" (!isPure (.Constr 0 [.App (.Var f) (.Var x), .Var y]))
    check "isPure_app_var" (!isPure (.App (.Var f) (.Var x)))
    check "isPure_force" (isPure (.Force (.Var x)))
    check "isPure_force_delay" (isPure (.Force (.Delay (.Var x))))
    check "isPure_case" (isPure (.Case (.Var x) [.Var y, .Var z]))
    check "isPure_let" (isPure (.Let [(a, intLit 1, false)] (.Var a)))
    check "isPure_let_pure_bindings" (isPure (.Let [(a, .Var x, false)] (.Var a)))
    check "isPure_app_builtin_partial" (isPure (.App (.Builtin .AddInteger) (intLit 1)))
    check "isPure_app_builtin_total" (isPure (.App (.App (.Builtin .AddInteger) (intLit 1)) (intLit 2)))
    check "isPure_app_forced_builtin" (!isPure (.App (.Force (.Builtin .HeadList)) (.Var x)))
    check "isPure_app_divideInteger" (!isPure (.App (.App (.Builtin .DivideInteger) (intLit 1)) (intLit 2)))
    check "isPure_app_unIData" (!isPure (.App (.Builtin .UnIData) (.Var x)))
    check "isPure_error" (!isPure .Error)
    check "isPure_app_error_fn" (!isPure (.App .Error (.Var x)))
    check "isPure_app_error_arg" (!isPure (.App (.Var f) .Error))
    check "isPure_constr_error_arg" (!isPure (.Constr 0 [.Var x, .Error]))
    check "isPure_let_error_rhs" (!isPure (.Let [(a, .Error, false)] (.Var a)))
    check "isPure_let_error_body" (!isPure (.Let [(a, .Var x, false)] .Error))
    check "isPure_case_error_scrut" (!isPure (.Case .Error [.Var y]))
    check "isPure_case_error_alt" (!isPure (.Case (.Var x) [.Error]))
    check "isPure_force_error" (!isPure (.Force .Error))

end Test.MIR.Opt.IsPure
