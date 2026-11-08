import Test.MIR.FuzzReal.Run
import Moist.Plutus.Decode
import Moist.Plutus.Pretty
import Moist.Plutus.CBOR

/-! # Huge constants through serialisation, readback and printing

`fuzz_real --stress VALUE PATH` runs one value through one path and prints
`ok` (or the process dies, e.g. of a stack overflow); `stress.py` runs every
pair in its own process. Values: bound-sized and larger integers, 1 MB
bytestrings and strings, 200k-element lists, Data nested 100k deep and Data
lists/maps 200k wide. Paths: flat encoding, flat decoding, the Lean model
returning the value and reading it back, the model passing it through
builtins, UPLC and MIR printing, CBOR encoding and decoding, and the
production compiler on a program holding the value. -/

namespace Test.MIR.FuzzReal.Stress

open Moist.MIR
open Moist.Plutus (Data)
open Moist.Plutus.Term
open Test.MIR.FuzzReal

def deepConstr (n : Nat) : Data := Nat.repeat (fun d => .Constr 0 [d]) n (.I 0)

def deepList (n : Nat) : Data := Nat.repeat (fun d => .List [d]) n (.I 0)

def intT : BuiltinType := .AtomicType .TypeInteger
def dataT : BuiltinType := .AtomicType .TypeData

def valueNames : List String :=
  ["int-2^262143", "int-2^600000", "int-neg-2^600000", "bytes-1MB", "string-1MB", "intlist-200k", "datalist-200k", "data-constr-deep-100k", "data-list-deep-100k", "data-list-wide-200k", "data-map-wide-100k", "data-int-2^600000", "data-bytes-1MB", "bytes-64KB",
   "bytes-40000", "bytes-60000", "bytes-80000", "bytes-120000", "intlist-20000", "intlist-50000",
   "data-constr-deep-1000", "data-constr-deep-5000", "data-constr-deep-10000", "data-constr-deep-20000",
   "data-list-wide-20000", "data-list-wide-50000"]

/-- Only the selected value is built. Powers of two are built by shifting:
    `Nat.pow` with an exponent known only at runtime overflows the stack for
    exponents in the hundreds of thousands (Lean runtime, not Moist).
    Only the selected value is built (and `k`, 1 at runtime, keeps the values
    from being closed terms evaluated at module initialisation). Deep Data is
    built tail-recursively, so building it cannot overflow. -/
def valueOf (k : Nat) : String → Option (Const × BuiltinType)
  | "int-2^262143" => some (.Integer ((1 <<< (262143 * k) : Nat) : Int), intT)
  | "int-2^600000" => some (.Integer ((1 <<< (600000 * k) : Nat) : Int), intT)
  | "int-neg-2^600000" => some (.Integer (-((1 <<< (600000 * k) : Nat) : Int)), intT)
  | "bytes-1MB" => some (.ByteString ⟨(List.replicate (1048576 * k) (7 : UInt8)).toArray⟩, .AtomicType .TypeByteString)
  | "string-1MB" => some (.String (String.mk (List.replicate (1048576 * k) 'x')), .AtomicType .TypeString)
  | "intlist-200k" => some (.ConstList intT ((List.range (200000 * k)).map fun (i : Nat) => .Integer (i : Int)),
      .TypeOperator (.TypeList intT))
  | "datalist-200k" => some (.ConstList dataT ((List.range (200000 * k)).map fun (i : Nat) => .Data (.I (i : Int))),
      .TypeOperator (.TypeList dataT))
  | "data-constr-deep-100k" => some (.Data (deepConstr (100000 * k)), dataT)
  | "data-list-deep-100k" => some (.Data (deepList (100000 * k)), dataT)
  | "data-list-wide-200k" => some (.Data (.List ((List.range (200000 * k)).map fun (i : Nat) => .I (i : Int))), dataT)
  | "data-map-wide-100k" => some (.Data (.Map ((List.range (100000 * k)).map fun (i : Nat) => (.I (i : Int), .B ⟨#[1]⟩))), dataT)
  | "data-int-2^600000" => some (.Data (.I ((1 <<< (600000 * k) : Nat) : Int)), dataT)
  | "bytes-64KB" => some (.ByteString ⟨(List.replicate (65537 * k) (7 : UInt8)).toArray⟩, .AtomicType .TypeByteString)
  | "data-bytes-1MB" => some (.Data (.B ⟨(List.replicate (1048576 * k) (7 : UInt8)).toArray⟩), dataT)
  | name =>
    -- parameterised sizes: bytes-N, intlist-N, data-constr-deep-N, data-list-wide-N
    match name.splitOn "-" |>.reverse with
    | n :: rest =>
      let size := n.toNat?.getD 0 * k
      match ("-".intercalate rest.reverse) with
      | "bytes" => some (.ByteString ⟨(List.replicate size (7 : UInt8)).toArray⟩, .AtomicType .TypeByteString)
      | "intlist" => some (.ConstList intT ((List.range size).map fun (i : Nat) => .Integer (i : Int)),
          .TypeOperator (.TypeList intT))
      | "data-constr-deep" => some (.Data (deepConstr size), dataT)
      | "data-list-wide" => some (.Data (.List ((List.range size).map fun (i : Nat) => .I (i : Int))), dataT)
      | _ => none
    | [] => none

def paths : List String :=
  ["flat-encode", "flat-decode", "model-readback", "model-builtins", "uplc-pretty",
   "mir-pretty", "cbor", "compile", "model-bytes-builtins"]

/-- `k` is 1 at runtime; taking it as an argument keeps the values from being
    closed terms, which the compiler would evaluate at module initialisation. -/
def run (k : Nat) (valueName path : String) : IO Unit := do
  let some (c, ty) := valueOf k valueName | throw (IO.userError "unknown value")
  let term : Term := .Constant (c, ty)
  match path with
  | "flat-encode" => IO.println s!"ok {(flatHex term).length}"
  | "flat-decode" =>
    let hex := flatHex term
    match Moist.Plutus.Decode.decodeProgramFromHexString hex with
    | some _ => IO.println "ok"
    | none => IO.println "decode-failed"
  | "model-readback" =>
    let run := modelEval (sv := .E) term 10000000000000 10000000000
    match run.outcome with
    | .halted v => IO.println s!"ok {(flatHex v).length == (flatHex term).length}"
    | .failed => IO.println "model-failed"
    | .budget => IO.println "model-budget"
  | "model-builtins" =>
    -- equality with itself, and serialisation for Data
    let program := match c with
      | .Data _ => Term.Apply (.Builtin .SerializeData) term
      | .Integer _ => .Apply (.Apply (.Builtin .EqualsInteger) term) term
      | .ByteString _ => .Apply (.Apply (.Builtin .EqualsByteString) term) term
      | .String _ => .Apply (.Apply (.Builtin .EqualsString) term) term
      | _ => .Apply (.Force (.Builtin .NullList)) term
    let run := modelEval (sv := .C) program 10000000000000 10000000000
    IO.println s!"ok {match run.outcome with | .halted _ => "halted" | .failed => "failed" | .budget => "budget"}"
    if let .Data d := c then
      let eq := modelEval (sv := .C) (.Apply (.Apply (.Builtin .EqualsData) (.Constant (.Data d, dataT)))
        (.Constant (.Data d, dataT))) 10000000000000 10000000000
      IO.println s!"equalsData {match eq.outcome with | .halted _ => "halted" | .failed => "failed" | .budget => "budget"}"
  | "uplc-pretty" => IO.println s!"ok {(Moist.Plutus.Pretty.prettyTerm term).length}"
  | "mir-pretty" => IO.println s!"ok {(pretty (.Lit (c, ty))).length}"
  | "cbor" =>
    match c with
    | .Data d =>
      match Moist.Plutus.CBOR.dataToCBORBytes d with
      | some bytes =>
        match Moist.Plutus.CBOR.dData bytes with
        | some ([], _) => IO.println s!"ok {bytes.length}"
        | _ => IO.println "cbor-decode-failed"
      | none => IO.println "cbor-encode-failed"
    | _ => IO.println "ok n/a"
  | "compile" =>
    let x : VarId := { uid := 0, hint := "x" }
    let program := Expr.Lam x (.Case (.App (.App (.Builtin .EqualsInteger) (.Var x)) (.Lit (.Integer 0, intT)))
      [.Lit (c, ty), .Lit (c, ty)])
    match compileOptimized program with
    | .ok t => IO.println s!"ok {(flatHex t).length}"
    | .error e => IO.println s!"compile-error {e}"
  | "b2i" =>
    -- the E unlifting bound against the builtin's cost: budget 1e10 and unbounded
    let program := Term.Apply (.Apply (.Builtin .ByteStringToInteger)
      (.Constant (.Bool false, .AtomicType .TypeBool))) term
    for (vname, variant) in [("C", Moist.CEK.SemVariant.C), ("E", .E)] do
      for budget in [10000000000, 1000000000000000] do
        let run := modelEval (sv := variant) program budget 10000000000
        IO.println s!"ok b2i/{vname}/budget {budget}: {match run.outcome with | .halted _ => "halted" | .failed => "failed" | .budget => "budget"} cpu {run.consumed.cpu}"
  | "model-bytes-builtins" =>
    -- shift/rotate/integerToByteString/byteStringToInteger on the value, under C and E
    match c with
    | .ByteString bytes =>
      let b := Term.Constant (.ByteString bytes, .AtomicType .TypeByteString)
      let i (n : Int) := Term.Constant (.Integer n, intT)
      let bool (v : Bool) := Term.Constant (.Bool v, .AtomicType .TypeBool)
      let programs : List (String × Term) :=
        [("shift", .Apply (.Apply (.Builtin .ShiftByteString) b) (i 3)),
         ("rotate", .Apply (.Apply (.Builtin .RotateByteString) b) (i 3)),
         ("countSetBits", .Apply (.Builtin .CountSetBits) b),
         ("b2i", .Apply (.Apply (.Builtin .ByteStringToInteger) (bool true)) b),
         ("i2b", .Apply (.Apply (.Apply (.Builtin .IntegerToByteString) (bool true)) (i 8192))
            (.Apply (.Apply (.Builtin .ByteStringToInteger) (bool true)) b))]
      for (name, program) in programs do
        for (vname, variant) in [("C", Moist.CEK.SemVariant.C), ("E", .E)] do
          let run := modelEval (sv := variant) program 10000000000000 10000000000
          IO.println s!"ok {name}/{vname} {match run.outcome with | .halted _ => "halted" | .failed => "failed" | .budget => "budget"}"
          (← IO.getStdout).flush
    | _ => IO.println "ok n/a"
  | _ => throw (IO.userError "unknown path")

end Test.MIR.FuzzReal.Stress
