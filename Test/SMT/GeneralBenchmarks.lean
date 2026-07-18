import Test.SMT.ListBenchmarks
import Moist.SMT.Soundness.SolverBoundary

/-!
# General SMT compiler benchmarks

This suite complements the list benchmarks with workloads representative of
refinement typing: independent control-flow joins, symbolic arithmetic,
branch-heavy arithmetic, bytes, strings, data, and repeated raw refinement
assertions.  The UPLC-backed scripts use production Boolean-success or runtime-
error conditions and therefore compose with `BoolTrueQuery.sound` or
`ErrorQuery.sound` after the ordinary checked-query/model certification
boundary.  The repeated-refinement scripts are labelled separately because
they benchmark the generic SMT layer rather than a CEK program.
-/

namespace Test.SMT.GeneralBenchmarks

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC
open Test.SMT.Examples (app app1 app2 bool int lazyIf)

private abbrev tyBytes : BuiltinType := .AtomicType .TypeByteString
private abbrev tyString : BuiltinType := .AtomicType .TypeString

private def bytesLiteral (values : Array UInt8) : Term :=
  .Constant (.ByteString (ByteArray.mk values), tyBytes)

private def stringLiteral (value : String) : Term :=
  .Constant (.String value, tyString)

def tagDeclaration : SymDecl := symConstr "general_case_tag"

def integerAlternatives (width : Nat) : List Term :=
  (List.range width).map fun i => int (Int.ofNat i)

/-- Repeated independent UPLC `Case` joins.  This exposes multiplicative
outcome growth unless the compiler compacts each semantic join. -/
def caseChain : Nat → Nat → Term → Term
  | 0, width, current =>
      app2 .LessThanInteger current (int (Int.ofNat width))
  | depth + 1, width, current =>
      let branched := Term.Case current (integerAlternatives width)
      app (.Lam 0 (caseChain depth width (.Var 1))) branched

def caseWorkload (depth width : Nat) : Term :=
  caseChain depth width (.Case (.Var 1) (integerAlternatives width))

/-- A wide constructor case whose every alternative is a runtime error.
This stresses the general error-path and tag-coverage disjunctions rather than
any list-specific encoding. -/
def caseErrorWorkload (width : Nat) : Term :=
  .Case (.Var 1) (List.replicate width .Error)

/-- A long symbolic arithmetic pipeline, without list-specific operations. -/
def arithmeticWorkload (rounds : Nat) : Term :=
  let result := (List.range rounds).foldl (fun accumulator i =>
    app2 .AddInteger
      (app2 .MultiplyInteger accumulator (int 3))
      (app2 .SubtractInteger (.Var 1) (int (Int.ofNat i)))) (.Var 1)
  app2 .LessThanInteger result (int 1000000)

/-- Nested symbolic control flow feeding arithmetic expressions. -/
def branchWorkload : Nat → Term
  | 0 => app2 .LessThanEqualsInteger (.Var 1) (int 0)
  | depth + 1 =>
      lazyIf (app2 .LessThanInteger (.Var 1) (int (Int.ofNat depth)))
        (app2 .LessThanEqualsInteger
          (app2 .AddInteger (.Var 1) (int (Int.ofNat depth)))
          (int (Int.ofNat (2 * depth + 1))))
        (branchWorkload depth)

/- A general duplicate-result workload.  Independent symbolic branches all
select the same integer, then feed ordinary arithmetic.  Keeping a redundant
`ite guard 7 7` for every choice makes both construction and the rendered
solver term grow without adding information. -/
def sameValueDeclarations (depth : Nat) : List SymDecl :=
  (List.range depth).map fun i => symBool s!"same_value_guard_{i}"

def sameValueChoice (index : Nat) : Term :=
  lazyIf (.Var (index + 1)) (int 7) (int 7)

def sameValueSum (depth : Nat) : Term :=
  (List.range depth).foldl
    (fun accumulator index =>
      app2 .AddInteger accumulator (sameValueChoice index))
    (int 0)

/-- Declarations for a higher-order refinement pipeline: each Boolean chooses
an arithmetic function, and the final integer is the common input. -/
def higherOrderDeclarations (depth : Nat) : List SymDecl :=
  (List.range depth).map (fun i => symBool s!"apply_guard_{i}") ++
    [symInt "apply_input"]

/-- A symbolic function choice.  `Force` cannot compact the two closures, but
the enclosing application can compact their first-order integer results. -/
def selectedArithmeticFunction (guardIndex : Nat) : Term :=
  lazyIf (.Var (guardIndex + 1))
    (.Lam 0 (app2 .AddInteger (.Var 1) (int 1)))
    (.Lam 0 (app2 .SubtractInteger (.Var 1) (int 1)))

/-- Repeatedly invoke independently selected functions.  Without application
result compaction this multiplies the outcome count at every stage. -/
def higherOrderApplicationPipeline (depth : Nat) : Term :=
  (List.range depth).foldl
    (fun current i => app (selectedArithmeticFunction i) current)
    (.Var (depth + 1))

/- Native byte/string values used to remain as separate outcomes after every
symbolic branch.  Appending a sequence of independently chosen constants is a
non-list stress test for that general decision-tree growth. -/
private def nativeChoiceCondition (i : Nat) : Term :=
  app2 .LessThanInteger (.Var 1) (int (Int.ofNat i))

private def bytesChoice (i : Nat) : Term :=
  lazyIf (nativeChoiceCondition i)
    (bytesLiteral #[1, 2]) (bytesLiteral #[3, 4])

private def stringChoice (i : Nat) : Term :=
  lazyIf (nativeChoiceCondition i)
    (stringLiteral "ab") (stringLiteral "cd")

def appendByteChoices : Nat → Term
  | 0 => bytesLiteral #[]
  | depth + 1 =>
      app2 .AppendByteString (appendByteChoices depth) (bytesChoice depth)

def appendStringChoices : Nat → Term
  | 0 => stringLiteral ""
  | depth + 1 =>
      app2 .AppendString (appendStringChoices depth) (stringChoice depth)

def nativeBytesBranchWorkload (depth : Nat) : Term :=
  lazyIf (app2 .EqualsByteString (appendByteChoices depth) (bytesLiteral #[]))
    (bool false) (bool true)

def nativeStringBranchWorkload (depth : Nat) : Term :=
  lazyIf (app2 .EqualsString (appendStringChoices depth) (stringLiteral ""))
    (bool false) (bool true)

def bytesWorkload : Term :=
  app2 .EqualsByteString
    (app2 .AppendByteString (.Var 1) (.Var 1))
    (app2 .AppendByteString (.Var 1) (.Var 1))

def stringWorkload : Term :=
  app2 .EqualsString
    (app2 .AppendString (.Var 1) (.Var 1))
    (app2 .AppendString (.Var 1) (.Var 1))

/-- A symbolic data projection/reconstruction path with both success and
runtime-type-error outcomes. -/
def dataIntegerRoundTrip : Term :=
  app2 .EqualsData
    (app1 .IData (app1 .UnIData (.Var 1)))
    (.Var 1)

def indexByteStringWorkload : Term :=
  app2 .IndexByteString (.Var 1) (.Var 2)

def divisionByZeroWorkload : Term :=
  app2 .DivideInteger (.Var 1) (int 0)

def uplcBenchmarks : List (String × (Unit → Script)) :=
  [ ("case-3x8.smt2", fun _ => scriptForBoolTrue 220 [tagDeclaration]
      (caseWorkload 3 8))
  , ("case-3x16.smt2", fun _ => scriptForBoolTrue 260 [tagDeclaration]
      (caseWorkload 3 16))
  , ("case-100x8.smt2", fun _ => scriptForBoolTrue 4200 [tagDeclaration]
      (caseWorkload 100 8))
  , ("case-errors-1024.smt2", fun _ =>
      scriptForError 80 [tagDeclaration] (caseErrorWorkload 1024))
  , ("arithmetic-100.smt2", fun _ =>
      scriptForBoolTrue 2400 [symInt "arith_x"] (arithmeticWorkload 100))
  , ("branches-100.smt2", fun _ =>
      scriptForBoolTrue 5000 [symInt "branch_x"] (branchWorkload 100))
  , ("same-value-500.smt2", fun _ =>
      scriptForIntEq 20100 (sameValueDeclarations 500) (sameValueSum 500)
        (.int (Int.ofNat (7 * 500))))
  , ("higher-order-12.smt2", fun _ =>
      scriptForIntEq 440 (higherOrderDeclarations 12)
        (higherOrderApplicationPipeline 12)
        (.sym (sanitize "apply_input")))
  , ("native-bytes-18.smt2", fun _ =>
      scriptForBoolTrue 1000 [symInt "native_bytes_x"]
        (nativeBytesBranchWorkload 18))
  , ("native-string-18.smt2", fun _ =>
      scriptForBoolTrue 1000 [symInt "native_string_x"]
        (nativeStringBranchWorkload 18))
  , ("bytes.smt2", fun _ =>
      scriptForBoolTrue 100 [symBytes "bytes_x"] bytesWorkload)
  , ("string.smt2", fun _ =>
      scriptForBoolTrue 100 [symString "string_x"] stringWorkload)
  , ("data-integer-roundtrip.smt2", fun _ =>
      scriptForBoolTrue 120 [symData "data_x"] dataIntegerRoundTrip)
  , ("index-bytes-error.smt2", fun _ => scriptForError 100
      [symBytes "error_bytes", symInt "error_index"] indexByteStringWorkload)
  , ("division-by-zero-error.smt2", fun _ => scriptForError 100
      [symInt "division_x"] divisionByZeroWorkload)
  ]

/-- A generic SMT-only benchmark for a refinement context with many related
nonlinear bounds.  Unlike `uplcBenchmarks`, it intentionally has no CEK claim. -/
def repeatedRefinements (count : Nat) : Script :=
  let declarations := [symInt "refine_x", symInt "refine_y"]
  let x : SExpr := .sym (sanitize "refine_x")
  let y : SExpr := .sym (sanitize "refine_y")
  let polynomial := SExpr.add (SExpr.mul x x) (SExpr.mul y y)
  let assertions := (List.range count).map fun i =>
    SExpr.le polynomial (.int (Int.ofNat (1000 + i)))
  scriptWith declarations assertions

def genericBenchmarks : List (String × (Unit → Script)) :=
  [ ("refinements-100.smt2", fun _ => repeatedRefinements 100)
  , ("refinements-500.smt2", fun _ => repeatedRefinements 500)
  , ("refinements-5000.smt2", fun _ => repeatedRefinements 5000)
  ]

def benchmarkScripts : List (String × (Unit → Script)) :=
  uplcBenchmarks ++ genericBenchmarks

-- The production assertion accounting and actual-machine endpoint used by
-- every UPLC-backed entry above remain explicit at the benchmark boundary.
#check scriptForBoolTrue_assertions
#check scriptForIntEq_assertions
#check scriptForError_assertions
#check Moist.SMT.UPLC.Soundness.BoolTrueQuery.sound
#check Moist.SMT.UPLC.Soundness.IntEqQuery.sound
#check Moist.SMT.UPLC.Soundness.ErrorQuery.sound

-- Every application result is first-order here, so the production evaluator
-- should join the otherwise exponential function-choice paths immediately.
#guard (evalSym 200 (envOf (higherOrderDeclarations 4))
  (higherOrderApplicationPipeline 4)).length == 1

-- The wide failing case is represented by one balanced error outcome and is
-- covered by the same public error-to-CEK endpoint as other product queries.
#guard
  match evalSym 80 (envOf [tagDeclaration]) (caseErrorWorkload 128) with
  | [.error _] => true
  | _ => false

-- The production evaluator retains the disjunction of active paths while the
-- common result stays a single literal throughout the arithmetic pipeline.
#guard
  match evalSym 300 (envOf (sameValueDeclarations 8)) (sameValueSum 8) with
  | [.ok _ (.const (.integer (.int 56)))] => true
  | _ => false

-- Eighteen binary choices formerly represented 262,144 separate native
-- values.  The production evaluator now keeps one merged success throughout
-- each non-list workload; all statically impossible failures are pruned.
#guard (evalSym 1000 (envOf [symInt "native_bytes_x"])
  (nativeBytesBranchWorkload 18)).length == 1
#guard (evalSym 1000 (envOf [symInt "native_string_x"])
  (nativeStringBranchWorkload 18)).length == 1

-- Caller refinements are one semantic conjunction, exposing their shared
-- polynomial to the per-command DAG renderer.  Declaration assumptions stay
-- separate so production model decoding can consume each one directly.
#guard (repeatedRefinements 500).assertions.length == 1
#check groupedAssertions_true_iff

def outputDir : System.FilePath := "Test/generated/smt/general-benchmarks"

unsafe def writeBenchmarks : IO Unit := do
  IO.FS.createDirAll outputDir
  for (name, makeScript) in benchmarkScripts do
    let start ← IO.monoMsNow
    let script := makeScript ()
    let rendered := script.renderDag
    IO.FS.writeFile (outputDir / name) rendered
    let stop ← IO.monoMsNow
    IO.println s!"{name}: bytes={rendered.length} generation-ms={stop - start}"

end Test.SMT.GeneralBenchmarks
