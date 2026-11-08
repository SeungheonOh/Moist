import Test.MIR.FuzzReal.Run
import Test.MIR.FuzzReal.Validators

/-! `fuzz_validators OUTDIR CASESDIR [--validator V]... [--model-all]`

For every cross-language validator with a CASESDIR/<Validator>.tsv file
(lines `name<TAB>arg;arg;…`, each argument CBOR-encoded Data in hex, as in
cases.csv), writes the jobs of the validator's MIR compiled without
optimization (`base`, `lower`), through every pass and stage, under every
production option, and as exported by `cross_bench_export` (`export/*`), on
every case. Same output files as `fuzz_real`. -/

open Test.MIR.FuzzReal
open Moist.Plutus.Term
open Moist.MIR (Expr)

private def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def decodeHex (text : String) : Option (List UInt8) :=
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | high :: low :: rest => do
      let h ← hexValue high
      let l ← hexValue low
      return (h * 16 + l).toUInt8 :: (← go rest)
    | _ => none
  go text.toList

private def argument (hex : String) : Except String Argument := do
  let some bytes := decodeHex hex | throw s!"bad hex {hex.take 20}"
  match Moist.Plutus.CBOR.dData bytes with
  | some ([], value) =>
    return { field := s!"d:{hex}", term := .Constant (.Data value, .AtomicType .TypeData),
             shown := hex }
  | _ => throw s!"bad Data CBOR {hex.take 40}"

def main (arguments : List String) : IO UInt32 := do
  let (outDirectory, casesDirectory) ← match arguments with
    | out :: cases :: _ => pure (out, cases)
    | _ => do
      IO.eprintln "usage: fuzz_validators OUTDIR CASESDIR [--validator V]... [--model-all]"
      return 2
  let selected := (arguments.zip (arguments.drop 1)).filterMap fun (flag, value) =>
    if flag == "--validator" then some value else none
  let modelAll := arguments.contains "--model-all"
  let option (name : String) (default : Nat) : Nat :=
    match arguments.dropWhile (· != name) with
    | _ :: value :: _ => value.toNat?.getD default
    | _ => default
  let mutants := option "--mutants" 0
  let mutantFrom := option "--mutant-from" 0
  let sample := option "--sample" 40
  let seed := option "--seed" 1
  let modelEvery := option "--model-every" 1
  unless encoderBlsTagsCorrect do
    IO.eprintln "warning: Moist.Plutus.Encode writes non-plutus-core flat tags for BLS hashToGroup/compress/uncompress; jobs are encoded with plutus-core's tags"
  let sink ← openSink outDirectory
  let exported := Validators.exported
  let mut total := 0
  for (name, expression) in Validators.registry do
    if !selected.isEmpty && !selected.contains name then continue
    let path := s!"{casesDirectory}/{name}.tsv"
    if !(← System.FilePath.pathExists path) then
      IO.eprintln s!"fuzz_validators: {name}: no {path}, skipped"
      continue
    let lines := (← IO.FS.lines path).toList.filter (!·.isEmpty)
    let mut cases : Array String := #[]
    let mut argumentLists : Array (List Argument) := #[]
    for line in lines do
      match line.splitOn "\t" with
      | [caseName, field] =>
        match (field.splitOn ";").filter (!·.isEmpty) |>.mapM argument with
        | .ok list =>
          cases := cases.push caseName
          argumentLists := argumentLists.push list
        | .error message => throw (IO.userError s!"{name}/{caseName}: {message}")
      | _ => throw (IO.userError s!"{path}: bad line {line.take 60}")
    let extraVariants : List (String × Except String Term) :=
      match exported.find? (·.1 == name) with
      | some (_, defaultScript, sizeScript) =>
        [("export/default", .ok defaultScript), ("export/size", .ok sizeScript)]
      | none => []
    let started ← IO.monoMsNow
    if mutants == 0 then
      let count ← emitProgram sink name expression argumentLists.toList modelAll {}
        [("cases", .arr (cases.map .str))] extraVariants modelEvery
      for handle in sink.handles do handle.flush
      IO.eprintln s!"fuzz_validators: {name}: {cases.size} cases, {count} jobs ({(← IO.monoMsNow) - started} ms)"
      total := total + count
    else
      -- mutants of the validator, each on the exported cases and a sample of the others
      let exportedCases := (List.range cases.size).filter fun i => (cases[i]!.splitOn "|base||").length > 1
      for index in List.range' mutantFrom (mutants - min mutants mutantFrom) do
        let action : Gen (Expr × List Nat) := do
          let edits ← pick [1, 1, 2, 3]
          let program ← Mutate.mutant expression edits
          let others ← (List.range (sample - min sample exportedCases.length)).mapM fun _ => rand cases.size
          return (program, (exportedCases.take sample ++ others).eraseDups)
        let ((program, chosen), _) := action.run { seed := (seed * 1000003 + index * 7919 + name.length).toUInt64 }
        let count ← emitProgram sink s!"{name}~m{index}" program (chosen.map (argumentLists[·]!)) modelAll {}
          [("cases", .arr (chosen.toArray.map (.str cases[·]!))), ("mutant-of", .str name),
           ("mutant", .num index)] [] modelEvery
        total := total + count
      for handle in sink.handles do handle.flush
      IO.eprintln s!"fuzz_validators: {name}: {mutants} mutants ({(← IO.monoMsNow) - started} ms)"
  IO.eprintln s!"fuzz_validators: {total} jobs written to {outDirectory}"
  return 0
