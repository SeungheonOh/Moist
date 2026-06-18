import Moist.Compile.Reflect
import Moist.Verified.BigStep

/-! # Bytestring **literals** compose with the symbolic builtins (`litBS`)

A `con bytestring 0x…` constant used to translate to an opaque `sConst` — so a literal could
not meet a symbolic bytestring operation (`equalsByteString (sha2_256 x) (con bytestring …)`
would *refuse*).  `constToSym` now lifts a bytestring literal to a first-order `sCon (litBS b)`
(and, via `dataToExpr`, any `Data` carrying a `B` leaf), so literals compose and z3 reasons
about them.  Soundness is unchanged — `γ σ (sCon (litBS b)) = VCon (.ByteString b)` — and the
trusted base is the same 12 accepted axioms (`litBS` adds none). -/

open Moist.Plutus.Term Moist.CEK Moist.Compile Moist.Smt Moist.Verified.BigStep
open Moist.Plutus (Data ByteString)

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def bsT (bytes : List UInt8) : Term :=
  .Constant (.ByteString ⟨bytes.toArray⟩, .AtomicType .TypeByteString)
private def app (f a : Term) : Term := .Apply f a
private def app2 (f a b : Term) : Term := app (app f a) b
private def lenBS (t : Term) : Term := app (.Builtin .LengthOfByteString) t
private def eqBS (a b : Term) : Term := app2 (.Builtin .EqualsByteString) a b
private def eqI (a b : Term) : Term := app2 (.Builtin .EqualsInteger) a b

private def symB : SymEnv := [.sCon (.var "b" .bytes)]          -- one symbolic bytestring input
private def compile (t : Term) : Option SmtExpr := (symEval 25 symB t).bind extract
private def st : Option SymOut → String | some _ => "OK ✅" | none => "REFUSE ❌"

def main : IO Unit := do
  IO.println "=== bytestring literals compose symbolically (litBS) ==="

  -- (1) a pure literal denotes correctly through the printer + z3: |0xAABBCC| = 3
  let lenProp := eqI (lenBS (bsT [0xAA, 0xBB, 0xCC])) (intT 3)
  match compile lenProp with
  | none   => IO.println "  [len literal] REFUSE ❌"
  | some e =>
    IO.println (s!"  z3 [ lengthOfByteString 0xAABBCC == 3 ]: "
      ++ s!"{repr (← checkZ3 (encodeProperty .trueE e))}  (expect unsat) ✅")

  -- (2) the literal *composes with the symbolic input* — used to REFUSE, now compiles
  let composes := eqBS (.Var 1) (bsT [0xAB])
  IO.println s!"  equalsByteString b (con bytestring 0xAB)  compiles: {st (symEval 25 symB composes)}"

  -- (3) literal ∘ symbolic inside one z3-checkable fact:
  --     if  b == 0xAB  then  lengthOfByteString b == 1   (valid; z3 unsat on the negation)
  match compile (eqBS (.Var 1) (bsT [0xAB])), compile (eqI (lenBS (.Var 1)) (intT 1)) with
  | some assume, some success =>
    IO.println (s!"  z3 [ b == 0xAB  ⟹  |b| == 1 ]: "
      ++ s!"{repr (← checkZ3 (encodeProperty assume success))}  (expect unsat) ✅")
  | _, _ => IO.println "  [compose+z3] REFUSE ❌"
