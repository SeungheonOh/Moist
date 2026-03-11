import Test.Framework
import Test.MIR.Golden
import Test.MIR.LowerGolden
import Test.MIR.OptimizeGolden

namespace Test.MIR

open System

def anfGoldenSuite : Test.Framework.Suite :=
  Test.Framework.goldenSuite "mir/golden" ("Test" / "golden") Test.MIR.Golden.goldenTests

def optimizeGoldenSuite : Test.Framework.Suite :=
  Test.Framework.goldenSuite "mir/opt-golden" ("Test" / "golden-opt") Test.MIR.OptGolden.optGoldenTests

def lowerGoldenSuite : Test.Framework.Suite :=
  Test.Framework.goldenSuite "mir/lower-golden" ("Test" / "golden-lower") Test.MIR.LowerGolden.lowerGoldenTests

def goldenSuites : List Test.Framework.Suite := [
  anfGoldenSuite,
  optimizeGoldenSuite,
  lowerGoldenSuite
]

end Test.MIR
