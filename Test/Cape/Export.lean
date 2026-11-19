import Test.Cape.Arithmetic
import Test.Cape.HTLC
import Test.Cape.LinearVesting
import Test.Cape.TwoPartyEscrow
import Moist.Plutus.Encode

open Test.Cape Moist.Plutus.Term

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected an output directory")
  IO.FS.createDirAll directory
  let scripts : List (String × Term) := [
    ("ecd", ecdScript),
    ("factorial", factorialScript),
    ("factorial_naive_recursion", factorialNaiveScript),
    ("fibonacci", fibonacciScript),
    ("fibonacci_naive_recursion", fibonacciNaiveScript),
    ("htlc", HTLC.script),
    ("linear_vesting", LinearVesting.script),
    ("two_party_escrow", TwoPartyEscrow.script)]
  for (name, script) in scripts do
    IO.FS.writeBinFile (System.FilePath.mk directory / s!"{name}.flat")
      ⟨(Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) script)).toByteList.toArray⟩
