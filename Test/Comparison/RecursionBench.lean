import Test.Comparison.Bench
import Moist.MIR.Optimize.Advanced.Recursion

namespace Test.Comparison.RecursionBench

open Moist.MIR Moist.Plutus.Term Validators Fixtures

open Lean Elab Term in
elab "staticComparison! " target:ident : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let expression ← Moist.Onchain.translateDefByName name body
  let transformed := Advanced.staticArguments expression
  match compileOptimized transformed with
  | .error message => throwError message
  | .ok script => return Moist.Onchain.ToExprInstances.uplcTermToExpr script

open Lean Elab Term in
elab "resultComparison! " target:ident : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let expression ← Moist.Onchain.translateDefByName name body
  let prepared := Advanced.structural (Advanced.preLower (preLowerInlineExpr (optimizeExpr expression)))
  match lowerExpr prepared with
  | .error message => throwError message
  | .ok lowered =>
    match lowerExpr (Advanced.finish (liftUPLC lowered)) with
    | .error message => throwError message
    | .ok script => return Moist.Onchain.ToExprInstances.uplcTermToExpr script

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def votingResults := resultComparison! voting

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def certifyingResults := resultComparison! certifying

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingResults := resultComparison! vesting

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def votingCandidate := staticComparison! voting

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def certifyingCandidate := staticComparison! certifying

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingCandidate := staticComparison! vesting

def run (scaling : Bool := false) : IO Unit := do
  IO.println "validator,scenario,profile,cpu,memory,flat_bytes"
  let workloads := if scaling then generatedVoting.filter (·.accepts) else scenarios
  for scenario in workloads do
    let candidate := if scenario.validator == "Voting" then votingCandidate
      else if scenario.validator == "Certifying" then certifyingCandidate else vestingCandidate
    let some (_,production) := (scripts scenario.validator)[1]? | throw (IO.userError "Missing production profile")
    unless flatHex candidate == flatHex production do
      throw (IO.userError "Combined candidate differs from production defaults")
    let encoded ← IO.FS.readFile s!"docs/benchmarks/real-validators/{scenario.validator}-default.flat.hex"
    let some (.Program _ baseline) := Moist.Plutus.Decode.Internal.decodeProgramFromHexString encoded.trim
      | throw (IO.userError "Invalid frozen default")
    let resultsOnly := if scenario.validator == "Voting" then votingResults
      else if scenario.validator == "Certifying" then certifyingResults else vestingResults
    let expected ← measure baseline scenario.arguments
    for (profile,script) in [("frozen-default",baseline),("result-summaries",resultsOnly),("combined",candidate)] do
      let result ← measure script scenario.arguments
      unless result.1 == expected.1 do throw (IO.userError s!"{scenario.name}/{profile}: changed outcome")
      IO.println s!"{scenario.validator},{scenario.name},{profile},{result.2.1},{result.2.2},{(flatHex script).length / 2}"

end Test.Comparison.RecursionBench

def main (arguments : List String) : IO Unit := Test.Comparison.RecursionBench.run (arguments.contains "--scaling")
