import Moist.Verified.VerifiedOptimize
import Moist.MIR.Lower
import Moist.MIR.FromUPLC
import Moist.Plutus.Eval
import Moist.Plutus.Decode
import Moist.Plutus.Encode
import Moist.Plutus.BitBuffer

/-! # Verified Optimizer Benchmark

Loads UPLC flat files, decompiles to MIR (recognizing `(λ.body) arg` as
let-bindings), runs the verified optimizer (ANF + DCE + Inline), re-encodes
to flat, and compares CPU, memory, and script size using the Plutuz CEK
machine (Zig FFI).
-/

open Moist.MIR (Expr VarId FreshState lowerExpr liftUPLC)
open Moist.Plutus.Term (Term Program Version)
open Moist.Plutus.Eval (evalFlatRaw)
open Moist.Plutus.Encode (encode_program)
open Moist.Plutus.Decode.Internal (decodeProgramFromBits)

private def byteToBits (b : UInt8) : List Bool :=
  let bv := b.toBitVec
  [bv.getLsbD 7, bv.getLsbD 6, bv.getLsbD 5, bv.getLsbD 4,
   bv.getLsbD 3, bv.getLsbD 2, bv.getLsbD 1, bv.getLsbD 0]

private def byteArrayToBits (ba : ByteArray) : List Bool :=
  ba.toList.flatMap byteToBits

private def bitBufferToByteArray (buf : Moist.Plutus.BitBuffer) : ByteArray :=
  ByteArray.mk (buf.toByteList.toArray)

private def defaultCpu : UInt64 := 10000000000
private def defaultMem : UInt64 := 14000000

private def runFlat (flatBytes : ByteArray) : IO (String × UInt64 × UInt64) := do
  let (errCode, cpuUsed, memUsed, _) ← evalFlatRaw flatBytes defaultCpu defaultMem
  if errCode == 0 then
    return ("success", cpuUsed, memUsed)
  else
    return (s!"error({errCode})", cpuUsed, memUsed)

private def pct (delta orig : Int) : String :=
  if orig == 0 then "—"
  else
    let p := (delta * 1000) / orig
    let whole := p / 10
    let frac := (p % 10).natAbs
    s!"{whole}.{frac}%"

private def fmtInt (n : Int) : String :=
  let s := toString n.natAbs
  let sign := if n < 0 then "-" else ""
  let chunks := go s.toList []
  sign ++ String.intercalate "," (chunks.map (String.mk ·))
where
  go (cs : List Char) (acc : List (List Char)) : List (List Char) :=
    if cs.length <= 3 then cs :: acc
    else go (cs.take (cs.length - 3)) (cs.drop (cs.length - 3) :: acc)

def main : IO Unit := do
  let benchDir := "/Users/sho/fun/llvm-uplc/benchmarks"
  let files := #["auction_1-1.flat", "auction_1-2.flat", "auction_1-3.flat",
                  "auction_1-4.flat", "auction_2-1.flat",
                  "coop-1.flat", "coop-2.flat", "coop-3.flat"]

  IO.println "╔═══════════════════════════════════════════════════════════════════════════╗"
  IO.println "║     Verified Optimizer Benchmark — Plutuz CEK (Zig FFI)                  ║"
  IO.println "║     Pipeline: UPLC → MIR (let-pattern) → ANF → DCE → Inline → UPLC      ║"
  IO.println "╚═══════════════════════════════════════════════════════════════════════════╝"
  IO.println ""

  for fname in files do
    let path := s!"{benchDir}/{fname}"
    let fileExists ← (System.FilePath.mk path).pathExists
    if !fileExists then
      IO.println s!"  [{fname}] not found"
      continue
    let origBytes ← IO.FS.readBinFile path
    let bits := byteArrayToBits origBytes

    match decodeProgramFromBits bits with
    | none =>
      IO.println s!"  [{fname}] decode failed"
    | some (Program.Program ver term) =>
      let mir := liftUPLC term 1
      let s : FreshState := ⟨100000⟩
      let (optimized, _) := Moist.Verified.MIR.verifiedOptimize mir s
      match lowerExpr optimized 200000 with
      | .error e =>
        IO.println s!"  [{fname}] lower failed: {e}"
      | .ok optTerm =>
        let optProg : Program := .Program ver optTerm
        let optBytes := bitBufferToByteArray (encode_program optProg)

        let (origStatus, origCpu, origMem) ← runFlat origBytes
        let (optStatus, optCpu, optMem) ← runFlat optBytes

        let origSize := origBytes.size
        let optSize := optBytes.size

        let cpuD : Int := origCpu.toNat - optCpu.toNat
        let memD : Int := origMem.toNat - optMem.toNat
        let sizeD : Int := origSize - optSize

        IO.println s!"  {fname}  [{origStatus} → {optStatus}]"
        IO.println s!"  ┌──────────┬─────────────────┬─────────────────┬─────────────────┬─────────┐"
        IO.println s!"  │          │ CPU             │ Memory          │ Script Size     │   Δ%    │"
        IO.println s!"  ├──────────┼─────────────────┼─────────────────┼─────────────────┼─────────┤"
        IO.println s!"  │ Original │ {fmtInt origCpu.toNat}\t│ {fmtInt origMem.toNat}\t│ {fmtInt origSize} bytes\t│         │"
        IO.println s!"  │ Optimized│ {fmtInt optCpu.toNat}\t│ {fmtInt optMem.toNat}\t│ {fmtInt optSize} bytes\t│         │"
        IO.println s!"  │ Saved    │ {fmtInt cpuD}\t│ {fmtInt memD}\t│ {fmtInt sizeD} bytes\t│         │"
        IO.println s!"  │ %        │ {pct cpuD origCpu.toNat}\t\t│ {pct memD origMem.toNat}\t\t│ {pct sizeD origSize}\t\t│         │"
        IO.println s!"  └──────────┴─────────────────┴─────────────────┴─────────────────┴─────────┘"
        IO.println ""
