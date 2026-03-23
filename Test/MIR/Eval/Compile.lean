import Test.MIR.Helpers
import Test.Onchain.Debug
import Moist.Onchain
import Moist.Onchain.Prelude

namespace Test.MIR.Eval.Compile

open PlutusCore.UPLC.Term
open Moist.Onchain.Prelude
open Test.MIR
open Test.Framework
open Test.Debug

/-! ## UPLC constant helpers -/

private def intTerm (n : Int) : Term :=
  .Const (.Integer n)

/-! ## SOP test data (@[plutus_sop]) -/

@[onchain]
def mkA1 : A := { x := 1, y := 2, z := 3, a := 4 }

@[onchain]
def mkA2 : A := { x := 5, y := 6, z := 7, a := 8 }

def testingUPLC   : Term := compile! testing
def mkA1UPLC      : Term := compile! mkA1
def mkA2UPLC      : Term := compile! mkA2

/-! ## Data test data (@[plutus_data]) -/

@[onchain]
def mkBazBaz : Baz := Baz.baz 10 20 30

@[onchain]
def mkBazAaa : Baz := Baz.aaa 1 123

@[onchain]
def mkBazFoo : Baz := Baz.foo 5

@[onchain]
def mkBazQux : Baz := Baz.qux

def mkBazBazUPLC  : Term := compile! mkBazBaz
def mkBazAaaUPLC  : Term := compile! mkBazAaa
def mkBazFooUPLC  : Term := compile! mkBazFoo
def mkBazQuxUPLC  : Term := compile! mkBazQux

def cccUPLC       : Term := compile! ccc
def fffUPLC       : Term := compile! fff

/-! ## Abbrev field test data (@[plutus_data] with Lovelace, POSIXTime, Credential) -/

def mkTestPaymentUPLC     : Term := compile! mkTestPayment
def mkTestActionPayUPLC   : Term := compile! mkTestActionPay
def mkTestActionEmptyUPLC : Term := compile! mkTestActionEmpty
def mkTestNestedUPLC      : Term := compile! mkTestNested
def mkTestTimeUPLC        : Term := compile! mkTestTime
def extractLovelaceUPLC   : Term := compile! extractLovelace
def matchTestActionUPLC   : Term := compile! matchTestAction
def extractPOSIXTimeUPLC  : Term := compile! extractPOSIXTime
def factorialUPLC : Term := compile! factorial
def treeSumUPLC   : Term := compile! treeSum
def treeLeaf5UPLC : Term := compile! treeLeaf5
def treeSmallUPLC : Term := compile! treeSmall
def treeBigUPLC   : Term := compile! treeBig

/-! ## Golden tests -/

def compileTree : TestTree := suite "compile" do
  -- SOP encoding (@[plutus_sop]): Constr/Case
  group "sop" do
    -- Foo.foo 1 2 3 4 5 6 42 standalone construction
    mkTermEvalGolden "sop_construct_foo" bbbb
    -- A{1,2,3,4} standalone construction
    mkTermEvalGolden "sop_construct_a" mkA1UPLC
    -- aaa extracts a+g+e+c from Foo.foo 1 2 3 4 5 6 42 → 1+42+5+3 = 51
    mkTermApplyEvalGolden "sop_foo_extract" aaaa [bbbb]
    -- testing(A{1,2,3,4}, A{5,6,7,8}) = x.y+x.a+y.y+y.x = 2+4+6+5 = 17
    mkTermApplyEvalGolden "sop_struct_access" testingUPLC [mkA1UPLC, mkA2UPLC]

  -- Data encoding (@[plutus_data]): ConstrData/UnConstrData
  group "data" do
    -- Bar{x:=1, y:=2, z:=3} construction
    mkTermEvalGolden "data_construct_bar" cccUPLC
    -- Baz.bar 1 2 construction
    mkTermEvalGolden "data_construct_baz_bar" eeee
    -- Baz.baz 10 20 30 construction
    mkTermEvalGolden "data_construct_baz_baz" mkBazBazUPLC
    -- ddd(Baz.bar 1 2)  = 1+2  = 3
    mkTermApplyEvalGolden "data_match_bar" dddd [eeee]
    -- ddd(Baz.baz 10 20 30) = 10+20+30 = 60
    mkTermApplyEvalGolden "data_match_baz" dddd [mkBazBazUPLC]
    -- ddd(Baz.aaa 1 123) = 1+123 = 124
    mkTermApplyEvalGolden "data_match_aaa" dddd [mkBazAaaUPLC]
    -- ddd(Baz.foo 5) = 5+1 = 6
    mkTermApplyEvalGolden "data_match_foo" dddd [mkBazFooUPLC]
    -- ddd(Baz.qux)  = 0
    mkTermApplyEvalGolden "data_match_qux" dddd [mkBazQuxUPLC]
    -- fff: nested match (Maybe SOPHi), bad .none = 0
    mkTermEvalGolden "data_nested_match" fffUPLC

  -- Recursion (WellFounded.fix → Z combinator)
  group "recursion" do
    -- factorial(1) = 1
    mkTermApplyEvalGolden "factorial_1" factorialUPLC [intTerm 1]
    -- factorial(5) = 120
    mkTermApplyEvalGolden "factorial_5" factorialUPLC [intTerm 5]
    -- factorial(10) = 3628800
    mkTermApplyEvalGolden "factorial_10" factorialUPLC [intTerm 10]

  -- Abbrev field types (@[plutus_data] with Lovelace, POSIXTime, Credential)
  group "abbrev" do
    -- TestPayment{amount:=1000000, time:=42} construction
    mkTermEvalGolden "abbrev_construct_payment" mkTestPaymentUPLC
    -- TestAction.pay 500 construction
    mkTermEvalGolden "abbrev_construct_action_pay" mkTestActionPayUPLC
    -- TestAction.empty construction
    mkTermEvalGolden "abbrev_construct_action_empty" mkTestActionEmptyUPLC
    -- TestNested{inner:=Bar{10,20,30}, tag:=7} construction (nested @[plutus_data])
    mkTermEvalGolden "abbrev_construct_nested" mkTestNestedUPLC
    -- TestTime{start:=1000, end_:=2000} construction
    mkTermEvalGolden "abbrev_construct_time" mkTestTimeUPLC
    -- extractLovelace(TestPayment{1000000, 42}) = 1000000
    mkTermApplyEvalGolden "abbrev_extract_lovelace" extractLovelaceUPLC [mkTestPaymentUPLC]
    -- matchTestAction(.pay 500) = 500
    mkTermApplyEvalGolden "abbrev_match_action_pay" matchTestActionUPLC [mkTestActionPayUPLC]
    -- matchTestAction(.empty) = 0
    mkTermApplyEvalGolden "abbrev_match_action_empty" matchTestActionUPLC [mkTestActionEmptyUPLC]
    -- extractPOSIXTime(TestTime{1000, 2000}) = 1000 + 2000 = 3000
    mkTermApplyEvalGolden "abbrev_extract_posixtime" extractPOSIXTimeUPLC [mkTestTimeUPLC]

  -- Structural recursion on user-defined SOP type (Tree)
  group "tree" do
    -- treeSum(leaf 5) = 5
    mkTermApplyEvalGolden "tree_sum_leaf" treeSumUPLC [treeLeaf5UPLC]
    -- treeSum(node (leaf 2) (leaf 3)) = 2 + 3 = 5
    mkTermApplyEvalGolden "tree_sum_small" treeSumUPLC [treeSmallUPLC]
    -- treeSum(node (node (leaf 1) (leaf 2)) (node (leaf 3) (leaf 4))) = 1+2+3+4 = 10
    mkTermApplyEvalGolden "tree_sum_big" treeSumUPLC [treeBigUPLC]

end Test.MIR.Eval.Compile
