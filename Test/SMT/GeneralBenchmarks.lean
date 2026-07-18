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
  , ("arithmetic-100.smt2", fun _ =>
      scriptForBoolTrue 2400 [symInt "arith_x"] (arithmeticWorkload 100))
  , ("branches-100.smt2", fun _ =>
      scriptForBoolTrue 5000 [symInt "branch_x"] (branchWorkload 100))
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
  ]

def benchmarkScripts : List (String × (Unit → Script)) :=
  uplcBenchmarks ++ genericBenchmarks

-- The production assertion accounting and actual-machine endpoint used by
-- every UPLC-backed entry above remain explicit at the benchmark boundary.
#check scriptForBoolTrue_assertions
#check scriptForError_assertions
#check Moist.SMT.UPLC.Soundness.BoolTrueQuery.sound
#check Moist.SMT.UPLC.Soundness.ErrorQuery.sound

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
