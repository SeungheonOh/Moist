import Test.Framework
import Test.MIR.ANF.Golden
import Test.MIR.ANF.Unit
import Test.MIR.Opt.Golden
import Test.MIR.Opt.IsPure
import Test.MIR.Opt.ExprStructEq
import Test.MIR.Opt.LookupStructEq
import Test.MIR.Opt.AllUsesAreForce
import Test.MIR.Opt.OccursUnderFix
import Test.MIR.Opt.ShouldInline
import Test.MIR.Opt.FloatOut
import Test.MIR.Opt.CSE
import Test.MIR.Opt.DCE
import Test.MIR.Opt.ForceDelay
import Test.MIR.Opt.InlinePass
import Test.MIR.Opt.Pipeline
import Test.MIR.Opt.CaseMerge
import Test.MIR.Opt.EtaReduce
import Test.MIR.Opt.BetaReduce
import Test.MIR.Lower.Golden
import Test.MIR.Lower.FixTotal
import Test.MIR.Eval.Golden
import Test.MIR.Eval.Compile
import Test.MIR.Eval.Policy
import Test.MIR.Analysis.Unit

namespace Test.MIR

open Test.Framework

def testTree : TestTree := suite "mir" do
  group "anf" do
    Test.MIR.ANF.Golden.goldenTree
    Test.MIR.ANF.Unit.unitTree
  group "opt" do
    Test.MIR.Opt.Golden.goldenTree
    group "unit" do
      Test.MIR.Opt.IsPure.tests
      Test.MIR.Opt.ExprStructEq.tests
      Test.MIR.Opt.LookupStructEq.tests
      Test.MIR.Opt.AllUsesAreForce.tests
      Test.MIR.Opt.OccursUnderFix.tests
      Test.MIR.Opt.ShouldInline.tests
      Test.MIR.Opt.FloatOut.tests
      Test.MIR.Opt.CSE.tests
      Test.MIR.Opt.DCE.tests
      Test.MIR.Opt.ForceDelay.tests
      Test.MIR.Opt.InlinePass.tests
      Test.MIR.Opt.Pipeline.tests
      Test.MIR.Opt.CaseMerge.tests
      Test.MIR.Opt.EtaReduce.tests
      Test.MIR.Opt.BetaReduce.tests
  group "lower" do
    Test.MIR.Lower.Golden.goldenTree
    Test.MIR.Lower.FixTotal.fixTotalTree
  group "eval" do
    Test.MIR.Eval.Golden.goldenTree
    Test.MIR.Eval.Compile.compileTree
    Test.MIR.Eval.Policy.policyTree
  group "analysis" do
    Test.MIR.Analysis.Unit.unitTree

end Test.MIR
