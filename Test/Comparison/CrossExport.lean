import Test.Comparison.Validators
import Test.Comparison.Cross.Sample
import Test.Comparison.Cross.Constitution
import Test.Comparison.Cross.Crowdfund
import Test.Comparison.Cross.Settings
import Test.Comparison.Cross.Hydra
import Test.Comparison.Cross.ProgrammableLogicGlobal
import Test.Comparison.Edge.ListSum
import Test.Comparison.Edge.MapFilterCount
import Test.Comparison.Edge.WideRecord
import Test.Comparison.Edge.ValueLookup
import Test.Comparison.Edge.EnumDispatch
import Test.Comparison.Edge.GuardOrder
import Test.Comparison.Edge.ByteSearch
import Test.Comparison.Edge.NestedLists
import Test.Comparison.Edge.Horner
import Test.Comparison.Edge.AllAny
import Moist.Plutus.Encode

/-! Writes every cross-language comparison script as flat hex:
`<dir>/<Validator>/moist.flat.hex` (default options) and
`<dir>/<Validator>/moist-size.flat.hex` (builtin sharing and constant pooling). -/

namespace Test.Comparison.CrossExport

open Moist.Plutus.Term

def flatHex (script : Term) : String :=
  (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) script)).toHexString

/-- `(validator, default script, size-options script)`. -/
def registry : List (String × Term × Term) := [
  ("Voting", Validators.votingScript, Validators.votingSize),
  ("Certifying", Validators.certifyingScript, Validators.certifyingSize),
  ("Vesting", Validators.vestingScript, Validators.vestingSize),
  ("Sample", Cross.Sample.script, Cross.Sample.scriptSize),
  ("Constitution", Cross.Constitution.script, Cross.Constitution.scriptSize),
  ("Crowdfund", Cross.Crowdfund.script, Cross.Crowdfund.scriptSize),
  ("Settings", Cross.Settings.script, Cross.Settings.scriptSize),
  ("Hydra", Cross.Hydra.script, Cross.Hydra.scriptSize),
  ("ProgrammableLogicGlobal", Cross.ProgrammableLogicGlobal.script, Cross.ProgrammableLogicGlobal.scriptSize),
  ("EdgeListSum", Edge.ListSum.script, Edge.ListSum.scriptSize),
  ("EdgeMapFilterCount", Edge.MapFilterCount.script, Edge.MapFilterCount.scriptSize),
  ("EdgeWideRecord", Edge.WideRecord.script, Edge.WideRecord.scriptSize),
  ("EdgeValueLookup", Edge.ValueLookup.script, Edge.ValueLookup.scriptSize),
  ("EdgeEnumDispatch", Edge.EnumDispatch.script, Edge.EnumDispatch.scriptSize),
  ("EdgeGuardOrder", Edge.GuardOrder.script, Edge.GuardOrder.scriptSize),
  ("EdgeByteSearch", Edge.ByteSearch.script, Edge.ByteSearch.scriptSize),
  ("EdgeNestedLists", Edge.NestedLists.script, Edge.NestedLists.scriptSize),
  ("EdgeHorner", Edge.Horner.script, Edge.Horner.scriptSize),
  ("EdgeAllAny", Edge.AllAny.script, Edge.AllAny.scriptSize)]

def main (arguments : List String) : IO Unit := do
  let directory := arguments.headD "/Users/sho/fun/cross-bench-data"
  for (name, defaultScript, sizeScript) in registry do
    IO.FS.createDirAll s!"{directory}/{name}"
    IO.FS.writeFile s!"{directory}/{name}/moist.flat.hex" (flatHex defaultScript ++ "\n")
    IO.FS.writeFile s!"{directory}/{name}/moist-size.flat.hex" (flatHex sizeScript ++ "\n")
    IO.println s!"{name}: wrote moist.flat.hex and moist-size.flat.hex"

end Test.Comparison.CrossExport

def main (arguments : List String) : IO Unit := Test.Comparison.CrossExport.main arguments
