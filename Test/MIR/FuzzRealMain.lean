import Test.MIR.FuzzReal.Run
import Test.MIR.FuzzReal.Probes

/-! `fuzz_real DIR [--from N] [--count N] [--inputs N] [--depth N] [--model-all]`

Generates `count` random programs (seeds `from` … `from + count - 1`) with
`inputs` argument lists each, and writes DIR/jobs.tsv, DIR/model.tsv,
DIR/model-values.tsv and DIR/manifest.jsonl (see Test.MIR.FuzzReal.Run). -/

open Test.MIR.FuzzReal

private def option (arguments : List String) (name : String) (default : Nat) : Nat :=
  match arguments.dropWhile (· != name) with
  | _ :: value :: _ => value.toNat?.getD default
  | _ => default

def main (arguments : List String) : IO UInt32 := do
  let some directory := arguments.head? | do
    IO.eprintln "usage: fuzz_real DIR [--from N] [--count N] [--inputs N] [--depth N] [--model-all]"
    return 2
  let start := option arguments "--from" 0
  let count := option arguments "--count" 100
  let inputs := option arguments "--inputs" 8
  let depth := option arguments "--depth" 4
  let modelAll := arguments.contains "--model-all"
  let untyped := arguments.contains "--untyped"
  if arguments.contains "--profile" then
    -- time every variant of each program, without writing jobs
    for seed in List.range' start count do
      let (program, _) := generate seed (3 + seed % (depth - 2)) inputs
      IO.println s!"seed {seed}: MIR size {(Moist.MIR.pretty program.expr).length} chars"
      (← IO.getStdout).flush
      for (name, thunk) in variantThunks program.expr do
        let started ← IO.monoMsNow
        let result := thunk ()
        let size := match result with | .ok term => (flatHex term).length | .error _ => 0
        IO.println s!"  {name}: {(← IO.monoMsNow) - started} ms, {size / 2} bytes"
        (← IO.getStdout).flush
    return 0
  unless encoderBlsTagsCorrect do
    IO.eprintln "warning: Moist.Plutus.Encode writes non-plutus-core flat tags for BLS hashToGroup/compress/uncompress; jobs are encoded with plutus-core's tags"
  let sink ← openSink directory
  let mut jobs := 0
  if arguments.contains "--probes" then
    for (name, program) in Probes.all do
      jobs := jobs + (← emitProgram sink s!"probe/{name}" program [[]] true {} [("family", .str "probe")])
    for handle in [sink.jobs, sink.model, sink.modelValues, sink.manifest] do handle.flush
    IO.eprintln s!"fuzz_real: {Probes.all.length} probes, {jobs} jobs written to {directory}"
    return 0
  for seed in List.range' start count do
    let started ← IO.monoMsNow
    if untyped then
      -- the untyped generator of the Lean-model differential audit, closed over
      -- one input and run on the audit's shared runtime inputs
      let input : Moist.MIR.VarId := { uid := 12000, origin := .source, hint := "input" }
      let body := (Test.MIR.Opt.Differential.generate (3 + seed % 3) [input] |>.run (seed + 29573)).1
      let program := Moist.MIR.Expr.Lam input body
      let pool := Test.MIR.Opt.Acceptance.inputs ++ Test.MIR.Opt.Acceptance.protocolInputs
      let chosen := (List.range inputs).map fun k => [pool[(seed * 13 + k * 5) % pool.length]!]
      let arguments ← match chosen.mapM (·.mapM argumentOfExpr) with
        | .ok arguments => pure arguments
        | .error message => throw (IO.userError s!"seed {seed}: {message}")
      jobs := jobs + (← emitProgram sink s!"u{seed}" program arguments modelAll {}
        [("seed", .num seed), ("family", .str "untyped")])
    else
    let (program, argumentLists) := generate seed (3 + seed % (depth - 2)) inputs
    let arguments ← match argumentLists.mapM (·.mapM argumentOfExpr) with
      | .ok arguments => pure arguments
      | .error message => throw (IO.userError s!"seed {seed}: {message}")
    jobs := jobs + (← emitProgram sink s!"s{seed}" program.expr arguments modelAll {}
      [("seed", .num seed), ("result", .str (toString (repr program.result)))])
    for handle in [sink.jobs, sink.model, sink.modelValues, sink.manifest] do handle.flush
    let elapsed := (← IO.monoMsNow) - started
    if elapsed > 3000 then IO.eprintln s!"fuzz_real: seed {seed} took {elapsed} ms"
  IO.eprintln s!"fuzz_real: {count} programs, {jobs} jobs written to {directory}"
  return 0
