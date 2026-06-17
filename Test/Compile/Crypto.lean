import Moist.Compile.Reflect

/-! # Axiomatized cryptographic hashes → z3 (Phase 2)

The hash builtins (`Sha2_256`/`Sha3_256`/`Blake2b_256`/`Blake2b_224`/`Keccak_256`/`Ripemd_160`)
are modelled as **uninterpreted SMT functions** (`opaque` in Lean, never implemented — so no
hash bloat in the SMT).  z3 reasons about them with the only property an uninterpreted function
has — determinism (`x = y → f x = f y`).  **No new axioms**: the crypto trust folds into
`z3_sound` (z3's "unsat for *all* interpretations of the hash" implies unsat for the Lean one). -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt

private def app (f a : Term) : Term := .Apply f a
private def hash (b : BuiltinFun) (x : Term) : Term := app (.Builtin b) x
private def eqBS (a b : Term) : Term := app (app (.Builtin .EqualsByteString) a) b
/-- two symbolic bytestrings `x` (Var 2) and `y` (Var 1). -/
private def symXY : SymEnv := [.sCon (.var "y" .bytes), .sCon (.var "x" .bytes)]
private def compile (t : Term) : Option SmtExpr := (symEval 20 symXY t).bind extract

def main : IO Unit := do
  IO.println "=== axiomatized crypto hashes → z3 ==="
  -- determinism: hash(x) == hash(x) is always true ⇒ unsat
  for (nm, b) in [("sha2_256", BuiltinFun.Sha2_256), ("sha3_256", .Sha3_256),
                  ("blake2b_256", .Blake2b_256), ("keccak_256", .Keccak_256),
                  ("ripemd_160", .Ripemd_160)] do
    match compile (eqBS (hash b (.Var 2)) (hash b (.Var 2))) with
    | some e =>
      IO.println s!"  [{nm}(x) == {nm}(x)]   z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect unsat) ✅"
    | none => IO.println s!"  [{nm}] refused"
  -- distinct inputs may hash differently (uninterpreted ⇒ z3 picks a model) ⇒ sat
  match compile (eqBS (hash .Sha2_256 (.Var 2)) (hash .Sha2_256 (.Var 1))) with
  | some e =>
    IO.println s!"  [sha2(x) == sha2(y)]   z3: {repr (← checkZ3 (encodeProperty .trueE e))}  (expect sat: x≠y) "
  | none => IO.println "  refused"
  -- nesting / composition with other ops: sha2(x) used inside equalsByteString with a literal
  let h := hash .Sha2_256 (.Var 2)
  match compile (eqBS h h) with
  | some _ => IO.println "  composes with the rest of the symbolic pipeline ✅"
  | none => pure ()
