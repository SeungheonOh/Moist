import Test.Comparison.Validators
import Test.Comparison.Fixtures
import Moist.Plutus.Eval
import Moist.Plutus.Encode
import Moist.Plutus.Pretty

namespace Test.Comparison

open Moist.Plutus.Term
open Fixtures Validators

def scripts (validator : String) : List (String × Term) :=
  if validator == "Voting" then [("unoptimized",votingRaw),("default",votingScript),("size-options",votingSize)]
  else if validator == "Certifying" then [("unoptimized",certifyingRaw),("default",certifyingScript),("size-options",certifyingSize)]
  else [("unoptimized",vestingRaw),("default",vestingScript),("size-options",vestingSize)]

def dataTerm (value : Moist.Plutus.Data) : Term := .Constant (.Data value,.AtomicType .TypeData)
def flatHex (script : Term) : String :=
  (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) script)).toHexString

def measure (script : Term) (arguments : List Moist.Plutus.Data) : IO (Option String × UInt64 × UInt64) := do
  match ← Moist.Plutus.Eval.evalTerm (arguments.foldl (fun term value => .Apply term (dataTerm value)) script)
      Moist.Plutus.Eval.defaultCpuBudget Moist.Plutus.Eval.defaultMemBudget with
  | .ok result =>
    match result.term with
    | .Constant (.Unit,.AtomicType .TypeUnit) => pure ()
    | _ => throw (IO.userError s!"Validator returned non-unit: {Moist.Plutus.Pretty.prettyTerm result.term}")
    return (some (Moist.Plutus.Pretty.prettyTerm result.term),result.budget.cpu,result.budget.mem)
  | .error (kind,budget,message) =>
    match kind with
    | .outOfBudget | .outOfMemory | .decodeError | .encodeError | .unboundVariable =>
      throw (IO.userError s!"Invalid benchmark observation: {kind}: {message}")
    | _ => return (none,budget.cpu,budget.mem)

def run (arguments : List String) : IO Unit := do
  let exportDirectory := arguments.head?
  if let some directory := exportDirectory then
    IO.FS.createDirAll directory
    for validator in ["Voting","Certifying","Vesting"] do
      for (profile,script) in scripts validator do
        IO.FS.writeFile (s!"{directory}/{validator}-{profile}.flat.hex") (flatHex script ++ "\n")
    IO.FS.writeFile (s!"{directory}/inputs.csv") ("validator,scenario,accepts,arguments\n" ++
      String.intercalate "\n" (validationScenarios.map fun scenario =>
        s!"{scenario.validator},{scenario.name},{scenario.accepts},{String.intercalate ";" (scenario.arguments.map (flatHex ∘ dataTerm))}") ++ "\n")
  IO.println "validator,scenario,implementation,accepts,cpu,memory,flat_bytes,cbor_bytes"
  for scenario in scenarios do
    let mut baseline : Option (Option String) := none
    for (profile,script) in scripts scenario.validator do
      let (result,cpu,memory) ← measure script scenario.arguments
      unless result.isSome == scenario.accepts do
        throw (IO.userError s!"{scenario.validator}/{scenario.name}/{profile}: expected accepts={scenario.accepts}, got {result}")
      if let some expected := baseline then
        unless result == expected do
          throw (IO.userError s!"Optimizer result mismatch: {scenario.validator}/{scenario.name}/{profile}")
      else baseline := some result
      let size := (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) script)).toByteList.length
      let cborSize := size + if size < 24 then 1 else if size < 256 then 2 else if size < 65536 then 3 else 5
      IO.println s!"{scenario.validator},{scenario.name},Moist-{profile},{scenario.accepts},{cpu},{memory},{size},{cborSize}"
    if let some (plutarchCpu,plutarchMemory,plinthCpu,plinthMemory) := scenario.reference then
      let (plutarchSize,plinthSize) := if scenario.validator == "Voting" then (272,244)
        else if scenario.validator == "Certifying" then (317,381) else (1219,1184)
      IO.println s!"{scenario.validator},{scenario.name},Plutarch-reported,true,{plutarchCpu},{plutarchMemory},,{plutarchSize}"
      IO.println s!"{scenario.validator},{scenario.name},Plinth-reported,true,{plinthCpu},{plinthMemory},,{plinthSize}"
  IO.eprintln s!"Validated {scenarios.length} scenarios across three Moist profiles; compared {scenarios.filter (·.reference.isSome) |>.length} accepting reference scenarios."

end Test.Comparison
