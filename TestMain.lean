import Test.Framework
import Test.MIR.Suites
import Test.Symbolic.Parity

def main (args : List String) : IO UInt32 :=
  Test.Framework.runTestTree (.group "all" [Test.MIR.testTree,
    Test.Symbolic.Parity.testTree]) args
