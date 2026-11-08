import Test.MIR.FuzzReal.Run
import Test.MIR.FuzzReal.Probes
import Test.MIR.FuzzReal.Shrink
import Test.MIR.FuzzReal.Stress

/-! `fuzz_real DIR [--from N] [--count N] [--inputs N] [--depth N] [--model-all]`

Generates `count` random programs (seeds `from` … `from + count - 1`) with
`inputs` argument lists each, and writes DIR/jobs.tsv, DIR/model.tsv,
DIR/model-values.tsv and DIR/manifest.jsonl (see Test.MIR.FuzzReal.Run). -/

open Test.MIR.FuzzReal

private def option (arguments : List String) (name : String) (default : Nat) : Nat :=
  match arguments.dropWhile (· != name) with
  | _ :: value :: _ => value.toNat?.getD default
  | _ => default

partial def largeLiterals : Moist.MIR.Expr → List (Moist.Plutus.Term.Const × Moist.Plutus.Term.BuiltinType)
  | .Lit (c, t) => match c with
    | .Integer n => if n.natAbs ≥ 2 ^ 64 then [(c, t)] else []
    | .ByteString b => if b.size > 1000 then [(c, t)] else []
    | _ => []
  | .Lam _ b | .Fix _ b | .Force b | .Delay b => largeLiterals b
  | .App f x => largeLiterals f ++ largeLiterals x
  | .Constr _ fs => fs.flatMap largeLiterals
  | .Case s alts => largeLiterals s ++ alts.flatMap largeLiterals
  | .Let bs body => bs.flatMap (fun (_, e, _) => largeLiterals e) ++ largeLiterals body
  | _ => []

/-- The program and argument lists of a generated label (`s<seed>`,
    `u<seed>` or `probe/<name>`), as the generator emitted them. -/
def programOf (label : String) (inputs depth : Nat) : Option (Moist.MIR.Expr × List (List Moist.MIR.Expr)) :=
  if label.startsWith "probe/" then
    match (Probes.all.find? (·.1 == label.drop 6)) with
    | some (_, program) => some (program, [[]])
    | none => match (Probes.keyPrograms.find? (·.1 == label.drop 6)) with
      | some (_, program, argumentLists) => some (program, argumentLists)
      | none => (Probes.boundArguments.find? (·.1 == label.drop 6)).map fun (_, program, values) =>
        (program, values.map ([·]))
  else if label.startsWith "u" then
    (label.drop 1).toNat?.map fun seed =>
      let input : Moist.MIR.VarId := { uid := 12000, origin := .source, hint := "input" }
      let body := (Test.MIR.Opt.Differential.generate (3 + seed % 3) [input] |>.run (seed + 29573)).1
      let pool := Test.MIR.Opt.Acceptance.inputs ++ Test.MIR.Opt.Acceptance.protocolInputs
      (.Lam input body, (List.range inputs).map fun k => [pool[(seed * 13 + k * 5) % pool.length]!])
  else if label.startsWith "s" then
    (label.drop 1).toNat?.map fun seed =>
      let (program, argumentLists) := generate seed (3 + seed % (depth - 2)) inputs
      (program.expr, argumentLists)
  else none

def main (arguments : List String) : IO UInt32 := do
  if let ["--stress", value, path] := arguments then
    Stress.run (arguments.length - 2) value path
    return 0
  if arguments == ["--stress-list"] then
    for value in Stress.valueNames do
      for path in Stress.paths do IO.println s!"{value} {path}"
    return 0
  if let "--shrink" :: label :: input :: variant :: rest := arguments then
    -- shrink one disagreement: fuzz_real --shrink LABEL INPUT VARIANT [--semantics S]
    let semantics := match rest.dropWhile (· != "--semantics") with
      | _ :: value :: _ => value
      | _ => "E"
    let some (program, argumentLists) := programOf label (option rest "--inputs" 8) (option rest "--depth" 4)
      | IO.eprintln s!"unknown label {label}"; return 2
    let some chosen := argumentLists[input.toNat?.getD 0]? | IO.eprintln "no such input"; return 2
    let args ← match chosen.mapM argumentOfExpr with
      | .ok args => pure args
      | .error message => IO.eprintln message; return 2
    Shrink.report semantics program args variant
    return 0
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
      IO.println s!"seed {seed}: MIR size {(Moist.MIR.pretty program.expr).length} chars, {Mutate.countNodes program.expr} nodes"
      for (c, _) in largeLiterals program.expr do
        match c with
        | .Integer n => IO.println s!"  literal integer of {n.natAbs.log2 + 1} bits"
        | .ByteString b => IO.println s!"  literal bytestring of {b.size} bytes"
        | _ => IO.println "  large literal"
      (← IO.getStdout).flush
      for (name, thunk) in variantThunks program.expr do
        IO.print s!"  {name}: "
        (← IO.getStdout).flush
        let started ← IO.monoMsNow
        let result := thunk ()
        IO.print s!"{match result with | .ok _ => "ok" | .error e => e} {(← IO.monoMsNow) - started} ms, "
        (← IO.getStdout).flush
        let size := match result with | .ok term => (flatHex term).length | .error _ => 0
        IO.println s!"{size / 2} bytes"
        (← IO.getStdout).flush
    return 0
  unless encoderBlsTagsCorrect do
    IO.eprintln "warning: Moist.Plutus.Encode writes non-plutus-core flat tags for BLS hashToGroup/compress/uncompress; jobs are encoded with plutus-core's tags"
  let sink ← openSink directory
  let mut jobs := 0
  if arguments.contains "--probes" then
    for (name, program) in Probes.all do
      jobs := jobs + (← emitProgram sink s!"probe/{name}" program [[]] true {} [("family", .str "probe")])
    for (name, program, argumentLists) in Probes.keyPrograms do
      let arguments ← match argumentLists.mapM (·.mapM argumentOfExpr) with
        | .ok arguments => pure arguments
        | .error message => throw (IO.userError message)
      jobs := jobs + (← emitProgram sink s!"probe/{name}" program arguments true {} [("family", .str "probe")])
    for (name, program, values) in Probes.boundArguments do
      let arguments ← match values.mapM (fun v => (argumentOfExpr v).map ([·])) with
        | .ok arguments => pure arguments
        | .error message => throw (IO.userError message)
      jobs := jobs + (← emitProgram sink s!"probe/{name}" program arguments true {} [("family", .str "probe")])
    for handle in sink.handles do handle.flush
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
    for handle in sink.handles do handle.flush
    let elapsed := (← IO.monoMsNow) - started
    if elapsed > 3000 then IO.eprintln s!"fuzz_real: seed {seed} took {elapsed} ms"
  IO.eprintln s!"fuzz_real: {count} programs, {jobs} jobs written to {directory}"
  return 0
