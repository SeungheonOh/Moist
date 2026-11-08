import Test.MIR.FuzzReal.Gen
import Test.MIR.Opt.Acceptance
import Moist.MIR.Compile
import Moist.MIR.LowerTotal
import Moist.MIR.Pretty
import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Plutus.Encode
import Lean.Data.Json

/-! # Differential runs against the plutus-core CEK machine

For every program this computes the UPLC of

* `base`: `lowerTotalExpr` of the unoptimized program (the certified lowering,
  no optimization, recursion through the Z combinator);
* `lower`: `lowerExpr` of the unoptimized program (direct recursive calls);
* `alone/*`: each optimizer pass or stage applied alone, then lowered;
* `pipe/*`: the production pipeline cut after each stage, then lowered;
* `prod/*`: `compileOptimized` under every combination of the finishing
  options, and with each low-sharing component turned off;

and writes evaluation jobs (one per distinct term and closing argument list)
for `cross-bench batch`, together with the Lean model's outcome, readback
value and traces on the `base` jobs (or on every job). -/

namespace Test.MIR.FuzzReal

open Moist.MIR
open Moist.Plutus.Term

/-- plutus-core's flat tag of the BLS12-381 builtins whose order differs
    from the declaration order of `BuiltinFun`. -/
def referenceBlsTag : BuiltinFun → Option Nat
  | .Bls12_381_G1_compress => some 58 | .Bls12_381_G1_uncompress => some 59
  | .Bls12_381_G1_hashToGroup => some 60 | .Bls12_381_G2_compress => some 65
  | .Bls12_381_G2_uncompress => some 66 | .Bls12_381_G2_hashToGroup => some 67
  | _ => none

def blsBuiltins : List BuiltinFun :=
  [.Bls12_381_G1_compress, .Bls12_381_G1_uncompress, .Bls12_381_G1_hashToGroup,
   .Bls12_381_G2_compress, .Bls12_381_G2_uncompress, .Bls12_381_G2_hashToGroup]

/-- Whether `Moist.Plutus.Encode` writes plutus-core's tags for those builtins.
    At c2a37d2 it does not (hashToGroup/compress/uncompress are permuted), which
    would make every BLS job test a different program than the model runs. -/
def encoderBlsTagsCorrect : Bool :=
  blsBuiltins.all fun b => referenceBlsTag b == some (Moist.Plutus.Encode.builtinFunTag b)

/-- The builtin the encoder must be given to write plutus-core's tag for `b`. -/
def encoderBuiltin (b : BuiltinFun) : BuiltinFun :=
  if encoderBlsTagsCorrect then b else
  match referenceBlsTag b with
  | some tag => (blsBuiltins.find? fun c => Moist.Plutus.Encode.builtinFunTag c == tag).getD b
  | none => b

partial def remapBuiltins : Term → Term
  | .Builtin b => .Builtin (encoderBuiltin b)
  | .Lam n body => .Lam n (remapBuiltins body)
  | .Apply f x => .Apply (remapBuiltins f) (remapBuiltins x)
  | .Force e => .Force (remapBuiltins e)
  | .Delay e => .Delay (remapBuiltins e)
  | .Constr tag fields => .Constr tag (fields.map remapBuiltins)
  | .Case s alts => .Case (remapBuiltins s) (alts.map remapBuiltins)
  | t => t

/-- Flat hex of a program, with plutus-core's builtin tags. -/
def flatHex (term : Term) : String :=
  let term := if encoderBlsTagsCorrect then term else remapBuiltins term
  (Moist.Plutus.Encode.encode_program (.Program (.Version 1 1 0) term)).toHexString

def lowerPass (transform : Expr → Expr) : Expr → Except String Term :=
  fun expression => lowerExpr (transform expression)

def alonePasses : List (String × (Expr → Expr)) :=
  Test.MIR.Opt.Acceptance.transformations ++
  [("unpack-records", Advanced.unpackRecords),
   ("known-list-cases", Advanced.fuseKnownListCases),
   ("tag-guards", Advanced.tagGuards),
   ("fail-fast", Advanced.failFast),
   ("checks-first", Advanced.checksFirst),
   ("data-checks", Advanced.specializeDataChecks),
   ("tag-chains", Advanced.caseTagChains),
   ("simplify", Advanced.simplify),
   ("prepare", Advanced.prepare),
   ("share-low", Advanced.shareLow {}),
   ("finish", fun e => Advanced.finish e {})]

/-- The production pipeline, cut after each stage. -/
def pipelineStages (expression : Expr) : List (String × Expr) :=
  let s1 := Advanced.staticArguments expression
  let s2 := optimizeExpr s1 1000
  let s3 := preLowerInlineExpr s2 5000
  let s4 := Advanced.preLower s3
  let t1 := Advanced.fuseListChoices s4
  let t2 := Advanced.destructureProducts t1
  let t3 := Advanced.optimizeCheckedBranches t2
  let t4 := Advanced.unpackRecords t3
  let t5 := Advanced.fuseKnownListCases t4
  let t6 := Advanced.tagGuards t5
  let t7 := Advanced.failFast t6
  let t8 := Advanced.checksFirst t7
  [("01-static-arguments", s1), ("02-optimize", s2), ("03-pre-lower-inline", s3),
   ("04-advanced-pre-lower", s4), ("05-list-choices", t1), ("06-products", t2),
   ("07-checked-branches", t3), ("08-unpack-records", t4), ("09-known-list-cases", t5),
   ("10-tag-guards", t6), ("11-fail-fast", t7), ("12-checks-first", t8)]

def productionOptions : List (String × Advanced.Options) :=
  ((List.range 16).map fun mask =>
    (s!"pack{mask % 2}-low{(mask / 2) % 2}-builtins{(mask / 4) % 2}-pool{mask / 8}",
     ({ packApplications := mask % 2 == 1, shareLow := (mask / 2) % 2 == 1,
        shareBuiltinStates := (mask / 4) % 2 == 1, poolConstants := mask / 8 == 1 } :
       Advanced.Options))) ++
  [("low-no-values", { lowSharing := { values := false } }),
   ("low-no-constants", { lowSharing := { constants := false } }),
   ("low-no-builtins", { lowSharing := { builtins := false } }),
   ("low-no-guard", { lowSharing := { guardPaths := false } })]

/-- Every variant of a program, in a fixed order; `base` first. Each variant
    is a thunk, so a slow pass can be timed (and reported) on its own. -/
def variantThunks (expression : Expr) : List (String × (Unit → Except String Term)) :=
  let base := fun (_ : Unit) => match lowerTotalExpr [] expression with
    | some term => Except.ok term
    | none => .error "lowerTotalExpr failed"
  [("base", base), ("lower", fun (_ : Unit) => lowerExpr expression)] ++
  (alonePasses.map fun (name, transform) =>
    (s!"alone/{name}", fun (_ : Unit) => lowerExpr (transform expression))) ++
  ((List.range 12).map fun index =>
    let name := ["01-static-arguments", "02-optimize", "03-pre-lower-inline",
      "04-advanced-pre-lower", "05-list-choices", "06-products", "07-checked-branches",
      "08-unpack-records", "09-known-list-cases", "10-tag-guards", "11-fail-fast",
      "12-checks-first"][index]!
    (s!"pipe/{name}", fun (_ : Unit) => lowerExpr ((pipelineStages expression)[index]!).2)) ++
  [("prod/default", fun (_ : Unit) => compileOptimized expression),
   ("prod/size", fun (_ : Unit) => compileOptimized expression 1000 5000
     { shareBuiltinStates := true, poolConstants := true })] ++
  (productionOptions.map fun (name, options) =>
    (s!"prod/{name}", fun (_ : Unit) => compileOptimized expression 1000 5000 options))

/-- The variants of `variantThunks`, sharing the pipeline: the stages are
    computed once, and the option profiles other than the default and size
    ones finish the same lowered term the way `compileOptimized` does
    (`prod/default` and `prod/size` call `compileOptimized` itself). -/
def variants (expression : Expr) : List (String × Except String Term) :=
  let stages := pipelineStages expression
  let prepared := (stages.getLastD ("", expression)).2
  let lowered := lowerExpr prepared 6000
  let finishWith (options : Advanced.Options) : Except String Term := do
    validateCompilationInput [] expression
    let term ← lowered
    if options.packApplications || options.shareLow || options.shareBuiltinStates ||
        options.poolConstants then
      lowerExpr (Advanced.finish (liftUPLC term) options) 6000
    else pure term
  let base := match lowerTotalExpr [] expression with
    | some term => Except.ok term
    | none => .error "lowerTotalExpr failed"
  [("base", base), ("lower", lowerExpr expression)] ++
  (alonePasses.map fun (name, transform) => (s!"alone/{name}", lowerExpr (transform expression))) ++
  (stages.map fun (name, stage) => (s!"pipe/{name}", lowerExpr stage)) ++
  [("prod/default", compileOptimized expression),
   ("prod/size", compileOptimized expression 1000 5000
     { shareBuiltinStates := true, poolConstants := true })] ++
  (productionOptions.map fun (name, options) => (s!"prod/{name}", finishWith options))

/-! ## The Lean model, with traces -/

private def stepMessages : Moist.CEK.State → List String
  | .ret (.funV (.VBuiltin .Trace [.VCon (.String message)] remaining) :: _) _ =>
    if remaining.head == .argV && remaining.isFinal then [message] else []
  | .ret (.applyArg _ :: _) (.VBuiltin .Trace [.VCon (.String message)] remaining) =>
    if remaining.head == .argV && remaining.isFinal then [message] else []
  | _ => []

inductive ModelOutcome where
  | halted (value : Term)
  | failed
  | budget
  deriving Inhabited

structure ModelRun where
  outcome : ModelOutcome
  consumed : Moist.CEK.ExBudget
  traces : Array String
  deriving Inhabited

/-- `Moist.CEK.eval`, also collecting the trace messages. -/
partial def modelEval [sv : Moist.CEK.SemVariant] (term : Term) (cpu mem : Int) : ModelRun :=
  let initial : Moist.CEK.ExBudget := ⟨cpu, mem⟩
  let afterStartup := initial - Moist.CEK.startupCost
  if afterStartup.isExhausted then ⟨.budget, Moist.CEK.startupCost, #[]⟩
  else go afterStartup initial (.compute [] .nil term) #[]
where
  go (remaining initial : Moist.CEK.ExBudget) (s : Moist.CEK.State) (traces : Array String) : ModelRun :=
    match s with
    | .halt v => ⟨.halted (Moist.CEK.readbackValue v), initial - remaining, traces⟩
    | .error => ⟨.failed, initial - remaining, traces⟩
    | s =>
      let cost := Moist.CEK.computeStepCost s
      let remaining' := remaining - cost
      if remaining'.isExhausted then ⟨.budget, initial - remaining', traces⟩
      else go remaining' initial (Moist.CEK.step s) (traces ++ (stepMessages s).toArray)

/-- BLS points cannot be flat-encoded; a readback value that contains one is
    rendered through `uncompress` of its compressed payload, which the real
    machine evaluates back to the same point. -/
partial def renderable : Term → Term
  | .Constant (.Bls12_381_G1_element bytes, _) =>
    .Apply (.Builtin .Bls12_381_G1_uncompress) (.Constant (.ByteString bytes, .AtomicType .TypeByteString))
  | .Constant (.Bls12_381_G2_element bytes, _) =>
    .Apply (.Builtin .Bls12_381_G2_uncompress) (.Constant (.ByteString bytes, .AtomicType .TypeByteString))
  | .Lam n body => .Lam n (renderable body)
  | .Apply f x => .Apply (renderable f) (renderable x)
  | .Force e => .Force (renderable e)
  | .Delay e => .Delay (renderable e)
  | .Constr tag fields => .Constr tag (fields.map renderable)
  | .Case s alts => .Case (renderable s) (alts.map renderable)
  | t => t

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

/-- Linear-time hex of a bytestring. -/
def bytesHex (bytes : ByteArray) : String :=
  String.mk (bytes.toList.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

/-- The program and argument fields of a job that evaluates to a readback value. -/
def valueJob (value : Term) : String := s!"{flatHex (renderable value)}\t"

def utf8Hex (message : String) : String :=
  (Moist.Plutus.ByteString.toHex message.toUTF8)

/-! ## Job files -/

/-- One Lean model run per builtin semantics variant: its name, the variant,
    the outcome file and the value file. -/
structure ModelSink where
  name : String
  variant : Moist.CEK.SemVariant
  runs : IO.FS.Handle
  values : IO.FS.Handle

structure Sink where
  jobs : IO.FS.Handle
  models : List ModelSink
  manifest : IO.FS.Handle

def Sink.handles (sink : Sink) : List IO.FS.Handle :=
  [sink.jobs, sink.manifest] ++ sink.models.flatMap fun m => [m.runs, m.values]

/-- Budget of every run, on the model and on the real machine (`fuzz_real.py`
    passes the same numbers to `cross-bench batch`): running out is divergence. -/
structure Limits where
  cpu : Int := 10000000000
  mem : Int := 100000000

def applyArguments (term : Term) (arguments : List Term) : Term :=
  arguments.foldl .Apply term

/-- A closing argument: how a job passes it to `cross-bench batch`, the term
    the Lean model applies, and a readable rendering. -/
structure Argument where
  field : String
  term : Term
  shown : String

def shorten (text : String) : String :=
  if text.length > 200 then text.take 200 ++ s!"… ({text.length} chars)" else text

/-- A closing argument from an MIR expression. Bound-sized literals are shown
    by their size (printing them in decimal is slow). -/
def argumentOfExpr (argument : Expr) : Except String Argument :=
  match lowerTotalExpr [] argument with
  | some term =>
    let shown := match argument with
      | .Lit (.Integer n, _) => if n.natAbs ≥ 2 ^ 64 then s!"<integer of {n.natAbs.log2 + 1} bits, sign {n.sign}>" else toString n
      | .Lit (.ByteString bytes, _) => if bytes.size > 256 then s!"<{bytes.size} bytes>" else shorten (pretty argument)
      | _ => shorten (pretty argument)
    .ok { field := s!"t:{flatHex term}", term, shown }
  | none => .error "argument does not lower"

/-- Write the jobs of one program. Returns the number of jobs written. -/
def emitProgram (sink : Sink) (label : String) (expression : Expr)
    (arguments : List (List Argument)) (modelAll : Bool) (limits : Limits)
    (extra : List (String × Lean.Json) := [])
    (extraVariants : List (String × Except String Term) := [])
    (modelEvery : Nat := 1) : IO Nat := do
  let all := variants expression ++ extraVariants
  -- distinct terms, in order of first appearance
  let mut terms : Array (String × Term) := #[]
  let mut variantIndex : Array (String × Lean.Json) := #[]
  for (name, result) in all do
    match result with
    | .error message => variantIndex := variantIndex.push (name, .str s!"error: {message}")
    | .ok term =>
      let hex := flatHex term
      match terms.findIdx? (·.1 == hex) with
      | some index => variantIndex := variantIndex.push (name, .num index)
      | none =>
        variantIndex := variantIndex.push (name, .num terms.size)
        terms := terms.push (hex, term)
  let mut jobRows : Array Lean.Json := #[]
  let mut count := 0
  for ((hex, _), termIndex) in terms.zipIdx do
    sink.jobs.putStrLn s!"P\t{label}#{termIndex}\t{hex}"
  for (argumentList, inputIndex) in arguments.zipIdx do
    let argumentField := ",".intercalate (argumentList.map (·.field))
    let argumentTerms := argumentList.map (·.term)
    sink.jobs.putStrLn s!"A\t{argumentField}"
    let mut row : Array Lean.Json := #[]
    for ((_, term), termIndex) in terms.zipIdx do
      let jobId := s!"{label}/{inputIndex}/{termIndex}"
      sink.jobs.putStrLn s!"J\t{jobId}\t{label}#{termIndex}"
      row := row.push (.str jobId)
      count := count + 1
      if (modelAll || termIndex == 0) && modelEvery > 0 && inputIndex % modelEvery == 0 then
        for model in sink.models do
          let run := modelEval (sv := model.variant) (applyArguments term argumentTerms) limits.cpu limits.mem
          let traces := ",".intercalate (run.traces.toList.map utf8Hex)
          let outcome := match run.outcome with
            | .halted _ => "OK" | .failed => "FAIL" | .budget => "BUDGET"
          model.runs.putStrLn s!"{jobId}\t{outcome}\t{run.consumed.cpu}\t{run.consumed.mem}\t{traces}"
          if let .halted value := run.outcome then
            model.values.putStrLn s!"{jobId}\t{valueJob value}"
    jobRows := jobRows.push (.arr row)
  let manifest := Lean.Json.mkObj ([
    ("label", .str label),
    ("mir", .str (pretty expression)),
    ("repr", .str (toString (repr expression))),
    ("inputs", .arr (arguments.toArray.map fun argumentList =>
      .arr (argumentList.toArray.map fun argument => .str argument.shown))),
    ("variants", Lean.Json.mkObj variantIndex.toList),
    ("terms", .num terms.size),
    ("jobs", .arr jobRows)] ++ extra)
  sink.manifest.putStrLn manifest.compress
  return count

def openSink (directory : System.FilePath) : IO Sink := do
  IO.FS.createDirAll directory
  return {
    jobs := ← IO.FS.Handle.mk (directory / "jobs.tsv") .write
    models := ← [("E", Moist.CEK.SemVariant.E), ("C", .C)].mapM fun (name, variant) => do
      return { name, variant
               runs := ← IO.FS.Handle.mk (directory / s!"model.{name}.tsv") .write
               values := ← IO.FS.Handle.mk (directory / s!"model-values.{name}.tsv") .write }
    manifest := ← IO.FS.Handle.mk (directory / "manifest.jsonl") .write }

end Test.MIR.FuzzReal
