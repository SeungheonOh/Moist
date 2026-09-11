import Test.MIR.Opt.Soundness
import Test.MIR.Opt.Differential
import Test.MIR.Opt.BudgetModel
import Test.MIR.Opt.Production
import Test.MIR.Opt.Structural
import Test.MIR.Opt.Recursion
import Test.MIR.Opt.CheckedBranches
import Test.MIR.Opt.SoundnessAudit
import Test.MIR.Opt.FormalCoverage
import Test.MIR.Opt.FormalAxioms

def main (arguments : List String) : IO UInt32 :=
  Test.Framework.runTestTree (.group "mir-audit"
    [Test.MIR.Opt.Soundness.tests, Test.MIR.Opt.Differential.tests,
     Test.MIR.Opt.Production.tests, Test.MIR.Opt.Structural.tests,
     Test.MIR.Opt.Recursion.tests, Test.MIR.Opt.CheckedBranches.tests,
     Test.MIR.Opt.SoundnessAudit.tests, Test.MIR.Opt.FormalCoverage.tests]) arguments
