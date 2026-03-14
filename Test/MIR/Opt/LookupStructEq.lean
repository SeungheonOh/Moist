import Test.MIR.Helpers
import Moist.MIR.Optimize

namespace Test.MIR.Opt.LookupStructEq

open Moist.MIR
open Test.MIR
open Test.Framework

def tests : TestTree := suite "lookupStructEq" do
  test "lookupStructEq" do
    check "lookup_empty" (lookupStructEq [] (.Var x) == none)
    check "lookup_found" (lookupStructEq [(.App (.Var f) (.Var x), a)] (.App (.Var f) (.Var x)) == some a)
    check "lookup_found_second" (lookupStructEq [(intLit 1, a), (.App (.Var f) (.Var x), b)] (.App (.Var f) (.Var x)) == some b)
    check "lookup_not_found" (lookupStructEq [(.App (.Var f) (.Var x), a)] (.App (.Var f) (.Var y)) == none)
    check "lookup_first_match_wins" (lookupStructEq [(.Var x, a), (.Var x, b)] (.Var x) == some a)

end Test.MIR.Opt.LookupStructEq
