import Test.MIR.Opt.Acceptance
import Lean.Data.Json

open Moist.MIR Moist.Plutus.Term Test.MIR.Opt.Acceptance

private def flatHex (term : Term) : String :=
  (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) term)).toHexString

private def exportScript (name : String) (script : Expr) (arguments : List Expr) : IO Unit := do
  let before ← requireTerm (lowerExpr script)
  let values ← arguments.mapM fun argument => do
    return Lean.Json.str (flatHex (← requireTerm (lowerExpr argument)))
  let variants ← match candidates script with
    | .ok terms => pure terms
    | .error message => throw (IO.userError message)
  for (pass, after) in variants do
    IO.println (Lean.Json.compress (Lean.Json.mkObj [
      ("label", .str s!"{name}/{pass}"),
      ("before", .str (flatHex before)), ("after", .str (flatHex after)),
      ("inputs", .arr values.toArray)]))

def main (arguments : List String) : IO UInt32 := do
  if arguments == ["--export"] then
    for (name, script) in scripts do
      exportScript name script inputs
    for (name, script) in protocolScripts do
      exportScript name script protocolInputs
    for (name, script) in generatedScripts do
      exportScript name script (protocolInputs ++ [.Error])
    return 0
  if !arguments.isEmpty then
    IO.eprintln "Usage: pass_audit [--export]"
    return 1
  Test.Framework.runTestTree tests []
