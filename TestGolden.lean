import Test.Framework
import Test.MIR.Suites

def main (args : List String) : IO UInt32 :=
  Test.Framework.runSuites [Test.MIR.anfGoldenSuite] args
