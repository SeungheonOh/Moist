import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.OccursUnderFix

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "occursUnderFix" do
  test "occursUnderFix" do
    check "underFix_inside" (occursUnderFix v (.Fix f (.App (.Var v) (.Var f))))
    check "underFix_outside" (!occursUnderFix v (.App (.Var v) (.Fix f (.Var f))))
    check "underFix_rebound_fix" (!occursUnderFix v (.Fix v (.Var v)))
    check "underFix_rebound_lam_inside" (!occursUnderFix v (.Fix f (.Lam v (.Var v))))
    check "underFix_not_present" (!occursUnderFix v (.Var x))
    check "underFix_nested_fix" (occursUnderFix v (.Fix f (.Fix g (.Var v))))
    check "underFix_let_shadow" (!occursUnderFix v (.Fix f (.Let [(v, intLit 1, false)] (.Var v))))
    check "underFix_let_rhs_before_shadow" (occursUnderFix v (.Fix f (.Let [(a, .Var v, false), (v, intLit 1, false)] (.Var v))))
    check "underFix_both_in_out" (occursUnderFix v (.App (.Var v) (.Fix f (.Var v))))
    check "underFix_in_app_fn" (occursUnderFix v (.Fix f (.App (.Var v) (.Var x))))
    check "underFix_deep_nested" (occursUnderFix v (.Fix f (.Lam x (.App (.Var x) (.Var v)))))
    check "underFix_in_constr" (occursUnderFix v (.Fix f (.Constr 0 [.Var v])))
    check "underFix_in_case_scrut" (occursUnderFix v (.Fix f (.Case (.Var v) [.Var x])))
    check "underFix_in_delay" (occursUnderFix v (.Fix f (.Delay (.Var v))))
    check "underFix_in_force" (occursUnderFix v (.Fix f (.Force (.Var v))))

end Test.MIR.Opt.OccursUnderFix
