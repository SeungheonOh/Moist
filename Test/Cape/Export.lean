import Test.Cape.Arithmetic
import Test.Cape.HTLC
import Test.Cape.LinearVesting
import Test.Cape.TwoPartyEscrow
import Moist.Plutus.Encode

open Test.Cape Moist.Plutus.Term

private def compilePtah (source : Moist.Ptah.Term α) (options : Moist.MIR.Advanced.Options := {}) : IO Term := do
  let .Program _ script ← IO.ofExcept (Moist.Ptah.compile source (options := options))
  return script

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected an output directory")
  IO.FS.createDirAll directory
  let shareSteps : Moist.MIR.Advanced.Options := { shareBuiltinStates := true, minimumBuiltinUses := 1 }
  let scripts : List (String × Term) := [
    ("ecd", ← compilePtah ecd),
    ("factorial", factorialScript),
    ("factorial_naive_recursion", ← compilePtah factorialNaive shareSteps),
    ("fibonacci", ← compilePtah fibonacci),
    ("fibonacci_naive_recursion", ← compilePtah fibonacciNaive shareSteps),
    ("htlc", HTLC.script),
    ("linear_vesting", LinearVesting.script),
    ("two_party_escrow", TwoPartyEscrow.script)]
  for (name, script) in scripts do
    IO.FS.writeBinFile (System.FilePath.mk directory / s!"{name}.flat")
      ⟨(Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) script)).toByteList.toArray⟩
