import Test.Comparison.Bench
import Moist.MIR.Optimize.Advanced.CheckedBranches

namespace Test.Comparison.CheckedBranchBench

open Moist.MIR Moist.Plutus.Term Validators Fixtures

open Lean Elab Term in
elab "checkedBranchComparison! " target:ident " mode " mode:num : term => do
  let name ← resolveGlobalConstNoOverload target
  let info ← getConstInfo name
  let some body := info.value? | throwError "Expected a definition"
  let expression ← Moist.Onchain.translateDefByName name body
  let baseline := Advanced.destructureProducts (Advanced.fuseListChoices
    (Advanced.preLower (preLowerInlineExpr
      (optimizeExpr (Advanced.staticArguments expression) 1000) 5000)))
  let prepared := match mode.getNat with
    | 0 => baseline
    | 1 => Advanced.fuseCheckedListBranches baseline
    | 2 => Advanced.lowerDelayedListChoices baseline
    | _ => Advanced.optimizeCheckedBranches baseline
  match lowerExpr prepared with
  | .error message => throwError message
  | .ok lowered =>
    match lowerExpr (Advanced.finish (liftUPLC lowered)) with
    | .error message => throwError message
    | .ok script => return Moist.Onchain.ToExprInstances.uplcTermToExpr script

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def votingCandidate := checkedBranchComparison! voting mode 3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def certifyingCandidate := checkedBranchComparison! certifying mode 3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingCandidate := checkedBranchComparison! vesting mode 3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def votingBefore := checkedBranchComparison! voting mode 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def certifyingBefore := checkedBranchComparison! certifying mode 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingBefore := checkedBranchComparison! vesting mode 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def votingFusion := checkedBranchComparison! voting mode 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def certifyingFusion := checkedBranchComparison! certifying mode 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingFusion := checkedBranchComparison! vesting mode 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def votingSelector := checkedBranchComparison! voting mode 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def certifyingSelector := checkedBranchComparison! certifying mode 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
def vestingSelector := checkedBranchComparison! vesting mode 2

def run (scaling : Bool := false) : IO Unit := do
  IO.println "validator,scenario,profile,cpu,memory,flat_bytes"
  for scenario in (if scaling then generatedVoting.filter (·.accepts) else scenarios) do
    let encoded ← IO.FS.readFile s!"docs/benchmarks/checked-branches-baseline/{scenario.validator}.flat.hex"
    let some (.Program _ baseline) := Moist.Plutus.Decode.Internal.decodeProgramFromHexString encoded.trim
      | throw (IO.userError "Invalid frozen default")
    let candidate := if scenario.validator == "Voting" then votingCandidate
      else if scenario.validator == "Certifying" then certifyingCandidate else vestingCandidate
    let before := if scenario.validator == "Voting" then votingBefore
      else if scenario.validator == "Certifying" then certifyingBefore else vestingBefore
    let fusion := if scenario.validator == "Voting" then votingFusion
      else if scenario.validator == "Certifying" then certifyingFusion else vestingFusion
    let selector := if scenario.validator == "Voting" then votingSelector
      else if scenario.validator == "Certifying" then certifyingSelector else vestingSelector
    unless flatHex before == flatHex baseline do
      throw (IO.userError s!"{scenario.validator}: ablation baseline no longer matches frozen script")
    let some (_,production) := (scripts scenario.validator)[1]?
      | throw (IO.userError "Missing production profile")
    unless flatHex candidate == flatHex production do
      throw (IO.userError s!"{scenario.validator}: candidate differs from production")
    let expected ← measure baseline scenario.arguments
    for (profile,script) in [("frozen-default",baseline),("fusion-only",fusion),
        ("selector-only",selector),("checked-branches",candidate)] do
      let result ← measure script scenario.arguments
      unless result.1 == expected.1 do throw (IO.userError s!"{scenario.name}/{profile}: changed outcome")
      unless result.2.1 <= expected.2.1 && result.2.2 <= expected.2.2 do
        throw (IO.userError s!"{scenario.name}/{profile}: resource regression")
      IO.println s!"{scenario.validator},{scenario.name},{profile},{result.2.1},{result.2.2},{(flatHex script).length / 2}"

end Test.Comparison.CheckedBranchBench

def main (arguments : List String) : IO Unit :=
  Test.Comparison.CheckedBranchBench.run (arguments.contains "--scaling")
