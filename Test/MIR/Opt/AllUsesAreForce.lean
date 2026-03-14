import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.AllUsesAreForce

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "allUsesAreForce" do
  test "allUsesAreForce" do
    check "allForce_bare_var" (!allUsesAreForce v (.Var v))
    check "allForce_force_var" (allUsesAreForce v (.Force (.Var v)))
    check "allForce_force_other_var" (allUsesAreForce v (.Force (.Var x)))
    check "allForce_no_occ_atom" (allUsesAreForce v (intLit 1))
    check "allForce_no_occ_complex" (allUsesAreForce v (.App (.Var f) (.Var x)))
    check "allForce_nested_force" (allUsesAreForce v (.Force (.Force (.Var v))))
    check "allForce_force_app_containing_v" (!allUsesAreForce v (.Force (.App (.Var v) (.Var x))))
    check "allForce_lam_shadow" (allUsesAreForce v (.Lam v (.Var v)))
    check "allForce_fix_shadow" (allUsesAreForce v (.Fix v (.Var v)))
    check "allForce_app_both_force" (allUsesAreForce v (.App (.Force (.Var v)) (.Force (.Var v))))
    check "allForce_app_mixed_bad" (!allUsesAreForce v (.App (.Var v) (.Force (.Var v))))
    check "allForce_constr_bare" (!allUsesAreForce v (.Constr 0 [.Var v]))
    check "allForce_constr_force" (allUsesAreForce v (.Constr 0 [.Force (.Var v)]))
    check "allForce_case_all_force" (allUsesAreForce v (.Case (.Force (.Var v)) [.Force (.Var v)]))
    check "allForce_case_scrut_bare" (!allUsesAreForce v (.Case (.Var v) [.Force (.Var v)]))
    check "allForce_let_shadow" (allUsesAreForce v (.Let [(v, .Var x, false)] (.Var v)))
    check "allForce_let_rhs_before_shadow" (!allUsesAreForce v (.Let [(a, .Var v, false), (v, intLit 1, false)] (.Var v)))
    check "allForce_delay_inner" (allUsesAreForce v (.Delay (.Force (.Var v))))
    check "allForce_delay_bare" (!allUsesAreForce v (.Delay (.Var v)))

end Test.MIR.Opt.AllUsesAreForce
