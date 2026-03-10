import Moist.Plutus.Term
import Moist.Plutus.Encode
import Moist.Plutus.Decode
import Moist.Plutus.BitBuffer
import Moist.Plutus.Pretty

namespace Moist.Plutus.Eval

open Moist.Plutus.Term
open Moist.Plutus.Encode (encode_program)
open Moist.Plutus.Decode.Internal (decodeProgramFromBits)

/-- Error codes returned by the Plutuz CEK machine. -/
inductive CEKError
  | outOfBudget
  | unboundVariable
  | typeMismatch
  | nonFunctionalApplication
  | nonConstrScrutinee
  | missingCaseBranch
  | builtinError
  | builtinTermArgumentExpected
  | nonPolymorphicInstantiation
  | unexpectedBuiltinTermArgument
  | openTermEvaluated
  | outOfMemory
  | decodeError
  | encodeError
  | unknown
deriving Repr, BEq

private def errCodeToError : UInt32 → CEKError
  | 1  => .outOfBudget
  | 2  => .unboundVariable
  | 3  => .typeMismatch
  | 4  => .nonFunctionalApplication
  | 5  => .nonConstrScrutinee
  | 6  => .missingCaseBranch
  | 7  => .builtinError
  | 8  => .builtinTermArgumentExpected
  | 9  => .nonPolymorphicInstantiation
  | 10 => .unexpectedBuiltinTermArgument
  | 11 => .openTermEvaluated
  | 12 => .outOfMemory
  | 13 => .decodeError
  | 14 => .encodeError
  | _  => .unknown

instance : ToString CEKError where
  toString
    | .outOfBudget                   => "OutOfBudget"
    | .unboundVariable               => "UnboundVariable"
    | .typeMismatch                  => "TypeMismatch"
    | .nonFunctionalApplication      => "NonFunctionalApplication"
    | .nonConstrScrutinee            => "NonConstrScrutinee"
    | .missingCaseBranch             => "MissingCaseBranch"
    | .builtinError                  => "BuiltinError"
    | .builtinTermArgumentExpected   => "BuiltinTermArgumentExpected"
    | .nonPolymorphicInstantiation   => "NonPolymorphicInstantiation"
    | .unexpectedBuiltinTermArgument => "UnexpectedBuiltinTermArgument"
    | .openTermEvaluated             => "OpenTermEvaluated"
    | .outOfMemory                   => "OutOfMemory"
    | .decodeError                   => "DecodeError"
    | .encodeError                   => "EncodeError"
    | .unknown                       => "Unknown"

/-- Budget consumed during evaluation. -/
structure ExBudget where
  cpu : UInt64
  mem : UInt64
deriving Repr, BEq

instance : ToString ExBudget where
  toString b := s!"cpu: {b.cpu} | mem: {b.mem}"

/-- Result of CEK machine evaluation. -/
structure EvalResult where
  term   : Term
  budget : ExBudget
deriving Repr

instance : ToString EvalResult where
  toString r := s!"{r.term}\n({r.budget})"

/-- Convert a byte to 8 bits (MSB first). -/
private def byteToBits (b : UInt8) : List Bool :=
  let bv := b.toBitVec
  [bv.getLsbD 7, bv.getLsbD 6, bv.getLsbD 5, bv.getLsbD 4,
   bv.getLsbD 3, bv.getLsbD 2, bv.getLsbD 1, bv.getLsbD 0]

/-- Convert a ByteArray to a bit sequence for flat decoding. -/
private def byteArrayToBits (ba : ByteArray) : List Bool :=
  ba.toList.flatMap byteToBits

/-- Convert a BitBuffer to a ByteArray. -/
private def bitBufferToByteArray (buf : Moist.Plutus.BitBuffer) : ByteArray :=
  ByteArray.mk (buf.toByteList.toArray)

/-- Raw FFI call into the Zig CEK machine.
    Returns (errCode, cpuUsed, memUsed, payload). -/
@[extern "lean_plutuz_eval_flat"]
opaque evalFlatRaw (program : @& ByteArray) (cpuBudget : UInt64) (memBudget : UInt64)
    : IO (UInt32 × UInt64 × UInt64 × ByteArray)

/-- Evaluate a UPLC Program using the Plutuz CEK machine.

    Encodes the program to flat bytes, sends it to the Zig machine,
    and decodes the result back to a Lean Term. -/
def evalProgram (prog : Program) (cpuBudget memBudget : UInt64) : IO (Except (CEKError × ExBudget × String) EvalResult) := do
  let flatBytes := bitBufferToByteArray (encode_program prog)
  let (errCode, cpuUsed, memUsed, payload) ← evalFlatRaw flatBytes cpuBudget memBudget
  let budget := ExBudget.mk cpuUsed memUsed
  if errCode == 0 then
    match decodeProgramFromBits (byteArrayToBits payload) with
    | some resultProg =>
      let (.Program _ resultTerm) := resultProg
      return .ok { term := resultTerm, budget := budget }
    | none =>
      return .error (.decodeError, budget, "Failed to decode result program from flat bytes")
  else
    let errMsg := String.fromUTF8! payload
    return .error (errCodeToError errCode, budget, errMsg)

/-- Default budget: 10 billion CPU, 14 million memory (Cardano mainnet parameters). -/
def defaultCpuBudget : UInt64 := 10000000000
def defaultMemBudget : UInt64 := 14000000

/-- Evaluate a Program with default Cardano mainnet budget. -/
def eval (prog : Program) : IO (Except (CEKError × ExBudget × String) EvalResult) :=
  evalProgram prog defaultCpuBudget defaultMemBudget

/-- Evaluate a Term directly. Wraps it in a Program v1.0.0, evaluates, and returns the result Term. -/
def evalTerm (term : Term) (cpuBudget memBudget : UInt64 := defaultCpuBudget) : IO (Except (CEKError × ExBudget × String) EvalResult) :=
  evalProgram (.Program (.Version 1 0 0) term) cpuBudget memBudget

end Moist.Plutus.Eval

namespace Moist.Plutus.Term.Term

open Moist.Plutus.Eval

def evaluate (t : Term) (cpuBudget memBudget : UInt64 := defaultCpuBudget) : IO (Except (CEKError × ExBudget × String) EvalResult) :=
  evalTerm t cpuBudget memBudget

def evaluatePretty (t : Term) (cpuBudget memBudget : UInt64 := defaultCpuBudget) : IO Unit := do
  match ← evalTerm t cpuBudget memBudget with
  | .ok r =>
    IO.println s!"Result: {r.term}"
    IO.println s!"CPU:    {r.budget.cpu}"
    IO.println s!"Memory: {r.budget.mem}"
  | .error (err, budget, msg) =>
    IO.println s!"Error: {err} — {msg}"
    IO.println s!"CPU:    {budget.cpu}"
    IO.println s!"Memory: {budget.mem}"

end Moist.Plutus.Term.Term

open Moist.Plutus.Eval in
def Moist.Plutus.Term.Program.evaluate (p : Moist.Plutus.Term.Program) (cpuBudget memBudget : UInt64 := defaultCpuBudget) : IO (Except (CEKError × ExBudget × String) EvalResult) :=
  evalProgram p cpuBudget memBudget

open Moist.Plutus.Eval in
def Moist.Plutus.Term.Program.evaluatePretty (p : Moist.Plutus.Term.Program) (cpuBudget memBudget : UInt64 := defaultCpuBudget) : IO Unit := do
  match ← evalProgram p cpuBudget memBudget with
  | .ok r =>
    IO.println s!"Result: {r.term}"
    IO.println s!"CPU:    {r.budget.cpu}"
    IO.println s!"Memory: {r.budget.mem}"
  | .error (err, budget, msg) =>
    IO.println s!"Error: {err} — {msg}"
    IO.println s!"CPU:    {budget.cpu}"
    IO.println s!"Memory: {budget.mem}"
