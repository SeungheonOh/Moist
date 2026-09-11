import Test.Comparison.Bench
import Test.Framework

namespace Test.Comparison

open Fixtures Test.Framework

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

def validateScenario (scenario : Scenario) : IO Unit := do
  let mut baseline : Option (Option String) := none
  for (profile,script) in scripts scenario.validator do
    let (result,_,_) ← measure script scenario.arguments
    check s!"{scenario.validator}/{scenario.name}/{profile}" (result.isSome == scenario.accepts)
    if let some expected := baseline then
      check s!"{scenario.name}/{profile}/equivalence" (result == expected)
    else baseline := some result

def tests : TestTree := suite "comparison" do
  test "upstream_scenarios_and_boundaries" do
    for scenario in scenarios ++ vestingEdges do validateScenario scenario
  test "generated_voting_search" do
    for scenario in generatedVoting do validateScenario scenario
  test "generated_vesting_states" do
    for scenario in generatedVesting do validateScenario scenario
  test "malformed_context_differential" do
    let malformed : List Moist.Plutus.Data := [.I 0,bytes "",.Map [],.List [],unitData,.Constr 42 []]
    for scenario in scenarios.filter (·.reference.isSome) do
      let some original := scenario.arguments.getLast? | throw (IO.userError "Missing context")
      for value in malformed do
        let contexts := [value] ++ (List.range 3).map (replaceField original · value) ++
          (List.range 16).map (replaceInfoField original · value)
        for context in contexts do
          let arguments := scenario.arguments.dropLast ++ [context]
          let mut baseline : Option (Option String) := none
          for (profile,script) in scripts scenario.validator do
            let (result,_,_) ← measure script arguments
            if let some expected := baseline then
              check s!"{scenario.validator}/{scenario.name}/{profile}/malformed" (result == expected)
            else baseline := some result
  test "invalid_expiration_parameter" do
    for value in [bytes "",unitData,.List []] do
      validateScenario ⟨"Certifying","invalid expiration",[value,certContext (certificate 0)],false,none⟩
  test "default_resource_regressions" do
    for scenario in scenarios.filter (·.reference.isSome) do
      let profiles := scripts scenario.validator
      let some (_,raw) := profiles[0]? | throw (IO.userError "Missing raw profile")
      let some (_,optimized) := profiles[1]? | throw (IO.userError "Missing default profile")
      let (_,rawCpu,rawMemory) ← measure raw scenario.arguments
      let (_,cpu,memory) ← measure optimized scenario.arguments
      check s!"{scenario.validator}/{scenario.name}/cpu" (cpu <= rawCpu)
      check s!"{scenario.validator}/{scenario.name}/memory" (memory <= rawMemory)
  test "frozen_real_validator_resource_regressions" do
    for scenario in scenarios do
      let encoded ← IO.FS.readFile s!"docs/benchmarks/real-validators/{scenario.validator}-default.flat.hex"
      let some (.Program _ frozen) := Moist.Plutus.Decode.Internal.decodeProgramFromHexString encoded.trim
        | throw (IO.userError "Invalid frozen validator")
      let some (_,optimized) := (scripts scenario.validator)[1]? | throw (IO.userError "Missing default")
      let (expected,oldCpu,oldMemory) ← measure frozen scenario.arguments
      let (actual,cpu,memory) ← measure optimized scenario.arguments
      check s!"{scenario.validator}/{scenario.name}/frozen-equivalence" (expected == actual)
      check s!"{scenario.validator}/{scenario.name}/frozen-cpu" (cpu <= oldCpu)
      check s!"{scenario.validator}/{scenario.name}/frozen-memory" (memory <= oldMemory)

  test "checked_branch_checkpoint_resource_regressions" do
    for scenario in scenarios ++ generatedVoting.filter (·.accepts) do
      let encoded ← IO.FS.readFile s!"docs/benchmarks/checked-branches-baseline/{scenario.validator}.flat.hex"
      let some (.Program _ frozen) := Moist.Plutus.Decode.Internal.decodeProgramFromHexString encoded.trim
        | throw (IO.userError "Invalid checked-branch checkpoint")
      let some (_,optimized) := (scripts scenario.validator)[1]? | throw (IO.userError "Missing default")
      let (expected,oldCpu,oldMemory) ← measure frozen scenario.arguments
      let (actual,cpu,memory) ← measure optimized scenario.arguments
      check s!"{scenario.validator}/{scenario.name}/checkpoint-equivalence" (expected == actual)
      check s!"{scenario.validator}/{scenario.name}/checkpoint-cpu" (cpu <= oldCpu)
      check s!"{scenario.validator}/{scenario.name}/checkpoint-memory" (memory <= oldMemory)

end Test.Comparison
