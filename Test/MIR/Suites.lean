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
import Test.MIR.Opt.Soundness
import Test.MIR.Opt.Differential
import Test.MIR.Opt.Production
import Test.MIR.Opt.Structural
import Test.MIR.Lower.Golden
import Test.MIR.Eval.Golden
import Test.MIR.Eval.Compile
import Test.MIR.Eval.Policy
import Test.MIR.Analysis.Unit
import Test.Comparison.Tests
import Test.MIR.Opt.Recursion
import Test.MIR.Opt.CheckedBranches
import Test.MIR.Opt.SoundnessAudit
import Test.MIR.Opt.FormalCoverage
import Test.MIR.Opt.FormalAxioms
import Test.Onchain.ConstitutionEncoding
import Test.Onchain.CollectionEncoding

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
      Test.MIR.Opt.Soundness.tests
      Test.MIR.Opt.Differential.tests
      Test.MIR.Opt.Production.tests
      Test.MIR.Opt.Structural.tests
      Test.MIR.Opt.Recursion.tests
      Test.MIR.Opt.CheckedBranches.tests
      Test.MIR.Opt.SoundnessAudit.tests
      Test.MIR.Opt.FormalCoverage.tests
  group "lower" do
    Test.MIR.Lower.Golden.goldenTree
  group "eval" do
    Test.ConstitutionEncoding.tests
    Test.CollectionEncoding.tests
    Test.Comparison.tests
    Test.MIR.Eval.Golden.goldenTree
    Test.MIR.Eval.Compile.compileTree
    Test.MIR.Eval.Policy.policyTree
  group "analysis" do
    Test.MIR.Analysis.Unit.unitTree

end Test.MIR
