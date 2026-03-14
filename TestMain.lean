import Test.Framework
import Test.MIR.Suites

def main (args : List String) : IO UInt32 :=
  Test.Framework.runTestTree Test.MIR.testTree args
