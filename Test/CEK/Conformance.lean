import Moist.CEK.Machine
import Moist.CEK.UplcParser
import Moist.CEK.Readback

open Moist.CEK
open Moist.CEK.UplcParser
open Moist.Plutus.Term (Term)

/-! # Plutus Conformance Test Runner

Runs the Plutus conformance test suite against our CEK machine.
Checks both evaluation results and cost budgets.
-/

structure TestResult where
  name     : String
  category : String
  status   : String
  detail   : String := ""
  budgetOk : Bool := true
  budgetDetail : String := ""
deriving Inhabited

private def extractInt (s : String) : Option Int :=
  let chars := s.toList.filter (fun c => c.isDigit || c == '-')
  String.mk chars |>.toInt?

def parseBudgetExpected (input : String) : Option (Int × Int) := do
  let parts := input.splitOn ":"
  if parts.length < 3 then none
  else
    let cpu ← extractInt parts[1]!
    let mem ← extractInt parts[2]!
    some (cpu, mem)

def isLeafTestDir (path : System.FilePath) : IO Bool := do
  let entries ← System.FilePath.readDir path
  let hasUplc := entries.any fun e => e.fileName.endsWith ".uplc" && !e.fileName.endsWith ".expected"
  let hasSubdir ← entries.anyM fun e => return (← (path / e.fileName).isDir)
  return (hasUplc && !hasSubdir)

partial def findTestDirs (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  if ← isLeafTestDir root then
    result := result.push root
  else
    for entry in (← System.FilePath.readDir root) do
      let p := root / entry.fileName
      if ← p.isDir then result := result ++ (← findTestDirs p)
  return result

def testName (path : System.FilePath) : String := path.fileName.getD "unknown"

def testCategory (root path : System.FilePath) : String :=
  let rootStr := root.toString
  let pathStr := path.toString
  if pathStr.startsWith rootStr then
    match (pathStr.drop (rootStr.length + 1)).splitOn "/" |>.dropLast with
    | [] => "root" | parts => "/".intercalate parts
  else "unknown"

/-- Use large budget for conformance tests (effectively unlimited for test programs). -/
def testCpuLimit : Int := 10000000000
def testMemLimit : Int := 14000000

def runTest (root testDir : System.FilePath) : IO TestResult := do
  let name := testName testDir
  let category := testCategory root testDir
  let uplcFile := testDir / (name ++ ".uplc")
  let expectedFile := testDir / (name ++ ".uplc.expected")
  let budgetFile := testDir / (name ++ ".uplc.budget.expected")

  let inputText ← IO.FS.readFile uplcFile
  let expectedText ← IO.FS.readFile expectedFile

  let budgetExpected ← do
    if ← budgetFile.pathExists then
      pure (parseBudgetExpected (← IO.FS.readFile budgetFile))
    else pure none

  match parseExpected expectedText with
  | .error msg => return { name, category, status := "skip", detail := s!"expected parse error: {msg}" }
  | .ok expected =>

  match expected with
  | .parseError =>
    match parseUplcProgram inputText with
    | .ok _ => return { name, category, status := "fail", detail := "expected parse error but parsed ok" }
    | .error _ => return { name, category, status := "pass" }

  | .evalFailure =>
    match parseUplcProgram inputText with
    | .error msg => return { name, category, status := "skip", detail := s!"input parse error: {msg}" }
    | .ok term =>
      let er := eval term testCpuLimit testMemLimit
      match er.result with
      | .failure =>
        let (bOk, bDet) := checkBudget budgetExpected er.consumed
        return { name, category, status := "pass", budgetOk := bOk, budgetDetail := bDet }
      | .outOfBudget => return { name, category, status := "fail", detail := "out of budget (expected failure)" }
      | .success v =>
        let d := "expected failure but got success: " ++ v.toString
        return { name, category, status := "fail", detail := d }

  | .success expectedTerm =>
    match parseUplcProgram inputText with
    | .error msg => return { name, category, status := "skip", detail := s!"input parse error: {msg}" }
    | .ok term =>
      let er := eval term testCpuLimit testMemLimit
      match er.result with
      | .failure => return { name, category, status := "fail", detail := "evaluation failed (expected success)" }
      | .outOfBudget => return { name, category, status := "fail", detail := "out of budget (expected success)" }
      | .success v =>
        let resultTerm := readbackValue v
        if termEq resultTerm expectedTerm then
          let (bOk, bDet) := checkBudget budgetExpected er.consumed
          return { name, category, status := "pass", budgetOk := bOk, budgetDetail := bDet }
        else
          let d := s!"result mismatch\n  got:      {repr resultTerm}\n  expected: {repr expectedTerm}"
          return { name, category, status := "fail", detail := d }
where
  checkBudget (expected : Option (Int × Int)) (actual : ExBudget) : Bool × String :=
    match expected with
    | none => (true, "")
    | some (eCpu, eMem) =>
      if actual.cpu == eCpu && actual.mem == eMem then (true, "")
      else
        (false, s!"budget: got cpu={actual.cpu} mem={actual.mem}, expected cpu={eCpu} mem={eMem}")

structure CategoryStats where
  pass : Nat := 0
  fail : Nat := 0
  skip : Nat := 0
  budgetMatch : Nat := 0
  budgetMismatch : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let root := match args with
    | [p] => System.FilePath.mk p
    | _ => "test-cases/uplc/evaluation"

  IO.println s!"Scanning tests in {root}..."
  let testDirs ← findTestDirs root
  IO.println s!"Found {testDirs.size} tests"

  let mut totalPass := 0
  let mut totalFail := 0
  let mut totalSkip := 0
  let mut totalBudgetMatch := 0
  let mut totalBudgetMismatch := 0
  let mut categoryMap : Array (String × CategoryStats) := #[]
  let mut failures : Array TestResult := #[]
  let mut budgetFailures : Array TestResult := #[]

  for dir in testDirs do
    let result ← runTest root dir
    let idx := categoryMap.findIdx? (fun (k, _) => k == result.category)
    let stats := match idx with
      | some i => (categoryMap[i]!).2 | none => {}
    let mut newStats := match result.status with
      | "pass" => { stats with pass := stats.pass + 1 }
      | "fail" => { stats with fail := stats.fail + 1 }
      | _ => { stats with skip := stats.skip + 1 }
    if result.status == "pass" then
      if result.budgetOk then
        newStats := { newStats with budgetMatch := newStats.budgetMatch + 1 }
        totalBudgetMatch := totalBudgetMatch + 1
      else
        newStats := { newStats with budgetMismatch := newStats.budgetMismatch + 1 }
        totalBudgetMismatch := totalBudgetMismatch + 1
        budgetFailures := budgetFailures.push result
    categoryMap := match idx with
      | some i => categoryMap.set! i (result.category, newStats) | none => categoryMap.push (result.category, newStats)
    match result.status with
    | "pass" => totalPass := totalPass + 1
    | "fail" => totalFail := totalFail + 1; failures := failures.push result
    | _ => totalSkip := totalSkip + 1

  -- Category summary
  IO.println "\n=== Category Summary ==="
  let sortedCats := categoryMap.qsort (fun a b => a.1 < b.1)
  for h : i in [:sortedCats.size] do
    let (cat, stats) := sortedCats[i]
    let total := stats.pass + stats.fail + stats.skip
    let budgetInfo := if stats.budgetMatch + stats.budgetMismatch > 0 then
      s!" | budget: {stats.budgetMatch}/{stats.budgetMatch + stats.budgetMismatch}"
    else ""
    IO.println s!"  {cat}: {stats.pass}/{total} pass, {stats.fail} fail, {stats.skip} skip{budgetInfo}"

  IO.println s!"\n=== Eval Failures ({failures.size} total, showing first 30) ==="
  for i in [:min failures.size 30] do
    let r : TestResult := failures[i]!
    IO.println s!"  FAIL [{r.category}] {r.name}: {r.detail}"

  IO.println s!"\n=== Budget Mismatches ({budgetFailures.size} total, showing first 30) ==="
  for i in [:min budgetFailures.size 30] do
    let r : TestResult := budgetFailures[i]!
    IO.println s!"  BUDGET [{r.category}] {r.name}: {r.budgetDetail}"

  let total := totalPass + totalFail + totalSkip
  let budgetTotal := totalBudgetMatch + totalBudgetMismatch
  IO.println s!"\n=== Grand Total ==="
  IO.println s!"  Eval:   {totalPass}/{total} pass ({totalPass * 100 / total}%), {totalFail} fail, {totalSkip} skip"
  IO.println s!"  Budget: {totalBudgetMatch}/{budgetTotal} match ({if budgetTotal > 0 then totalBudgetMatch * 100 / budgetTotal else 0}%)"

  return (if totalFail == 0 && totalBudgetMismatch == 0 then 0 else 1)
