import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.ShouldInline

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "shouldInline" do
  test "shouldInline" do
    check "should_atom_var_0" (shouldInline (.Var x) 0 false false)
    check "should_atom_var_multi" (shouldInline (.Var x) 5 true true)
    check "should_atom_lit" (shouldInline (intLit 42) 3 false false)
    check "should_atom_builtin" (shouldInline (.Builtin .AddInteger) 2 true true)
    check "should_small_lam" (shouldInline (.Lam y (.Var y)) 3 true true)
    check "should_small_delay" (shouldInline (.Delay (.Var x)) 2 false false)
    check "should_small_fix" (shouldInline (.Fix f (.Var f)) 2 true true)
    check "should_large_0_occ" (!shouldInline largeLam 0 false false)
    check "should_large_1_no_fix" (shouldInline largeLam 1 false false)
    check "should_large_1_under_fix" (!shouldInline largeLam 1 true true)
    check "should_large_1_deferred_no_fix" (shouldInline largeLam 1 false true)
    check "should_large_2" (!shouldInline largeLam 2 false false)
    check "should_large_2_under_fix" (!shouldInline largeLam 2 true true)
    check "should_large_3" (!shouldInline largeLam 3 false false)
    let nonVal := Expr.App (.Var f) (.Var x)
    check "should_nonval_0" (!shouldInline nonVal 0 false false)
    check "should_nonval_1_strict" (shouldInline nonVal 1 false false)
    check "should_nonval_1_deferred" (!shouldInline nonVal 1 false true)
    check "should_nonval_1_under_fix" (!shouldInline nonVal 1 true true)
    check "should_nonval_2" (!shouldInline nonVal 2 false false)
    check "should_nonval_2_deferred" (!shouldInline nonVal 2 false true)
    let pureNonVal := Expr.App (.Builtin .AddInteger) (.Var x)
    check "should_pure_nonval_1_strict" (shouldInline pureNonVal 1 false false)
    check "should_pure_nonval_1_deferred" (shouldInline pureNonVal 1 false true)
    check "should_pure_nonval_1_under_fix" (shouldInline pureNonVal 1 true true)
    check "should_error_0" (!shouldInline .Error 0 false false)
    check "should_error_1_strict" (shouldInline .Error 1 false false)
    check "should_error_1_deferred" (!shouldInline .Error 1 false true)

end Test.MIR.Opt.ShouldInline
