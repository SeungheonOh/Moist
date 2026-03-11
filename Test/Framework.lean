import Std

namespace Test.Framework

open System

structure RunConfig where
  update : Bool := false
  filters : List String := []

inductive CaseResult where
  | passed
  | updated

structure TestCase where
  name : String
  run : RunConfig → IO CaseResult
  setup : Bool := false

structure GoldenSpec where
  name : String
  render : IO String

structure Suite where
  name : String
  cases : List TestCase

def unitCase (name : String) (action : IO Unit) : TestCase where
  name := name
  run _ := do
    action
    pure .passed

def parseArgs (args : List String) : RunConfig :=
  let update := args.contains "--update"
  let filters := args.filter (· != "--update")
  { update, filters }

def fullCaseName (suiteName caseName : String) : String :=
  s!"{suiteName}/{caseName}"

def matchesFilter (filters : List String) (suiteName caseName : String) : Bool :=
  filters.isEmpty ||
    filters.any (fun filter =>
      suiteName.startsWith filter || (fullCaseName suiteName caseName).startsWith filter
    )

private def sortStrings (xs : List String) : List String :=
  (xs.toArray.qsort (fun a b => a < b)).toList

private def expectedFileNames (dir : FilePath) : IO (List String) := do
  let entries ← dir.readDir
  let mut names : List String := []
  for entry in entries do
    if entry.fileName.endsWith ".expected" then
      names := entry.fileName.dropRight ".expected".length :: names
  pure (sortStrings names)

private def formatNameDiff (label : String) (names : List String) : String :=
  if names.isEmpty then
    ""
  else
    let body := "\n".intercalate (names.map (fun name => s!"  - {name}"))
    s!"{label}:\n{body}\n"

def fixtureParityCase (dir : FilePath) (specs : List GoldenSpec) : TestCase :=
  let caseNames := sortStrings (specs.map (·.name))
  {
    name := "_fixture_parity"
    setup := true
    run := fun _ => do
      let fileNames ← expectedFileNames dir
      let missing := caseNames.filter (fun name => !(fileNames.contains name))
      let extra := fileNames.filter (fun name => !(caseNames.contains name))
      unless missing.isEmpty && extra.isEmpty do
        throw <| IO.userError <|
          s!"Fixture parity mismatch in {dir.toString}\n" ++
          formatNameDiff "Missing fixtures" missing ++
          formatNameDiff "Extra fixtures" extra
      pure .passed
  }

private def readFileOpt (path : FilePath) : IO (Option String) := do
  try
    pure (some (← IO.FS.readFile path))
  catch _ =>
    pure none

private def diffMessage (expected actual : String) : String :=
  Id.run do
    let expectedLines := expected.splitOn "\n"
    let actualLines := actual.splitOn "\n"
    let maxLines := max expectedLines.length actualLines.length
    let mut chunks : List String := []
    for i in List.range maxLines do
      let expLine := expectedLines.getD i ""
      let actLine := actualLines.getD i ""
      if expLine != actLine then
        chunks := chunks ++ [
          s!"line {i + 1}:",
          s!"  exp: {expLine}",
          s!"  got: {actLine}"
        ]
    "\n".intercalate chunks

def goldenCase (dir : FilePath) (spec : GoldenSpec) : TestCase :=
  {
    name := spec.name
    run := fun cfg => do
      let path := dir / s!"{spec.name}.expected"
      let actual ← spec.render
      if cfg.update then
        IO.FS.createDirAll dir
        IO.FS.writeFile path (actual ++ "\n")
        pure .updated
      else
        match ← readFileOpt path with
        | none =>
          throw <| IO.userError s!"Missing fixture: {path.toString} (run with --update)"
        | some content =>
          let expected := content.trimRight
          let actual := actual.trimRight
          unless actual == expected do
            let diff := diffMessage expected actual
            throw <| IO.userError s!"Golden mismatch: {path.toString}\n{diff}"
          pure .passed
  }

def goldenSuite (suiteName : String) (dir : FilePath) (specs : List GoldenSpec) : Suite where
  name := suiteName
  cases := fixtureParityCase dir specs :: specs.map (goldenCase dir)

private def selectCases (cfg : RunConfig) (suite : Suite) : List TestCase :=
  let selected := suite.cases.filter (fun case => !case.setup && matchesFilter cfg.filters suite.name case.name)
  if selected.isEmpty then
    []
  else
    suite.cases.filter (fun case => case.setup || matchesFilter cfg.filters suite.name case.name)

private def renderError (err : IO.Error) : String :=
  toString err

def runSuites (suites : List Suite) (args : List String) : IO UInt32 := do
  let cfg := parseArgs args
  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut updated : Nat := 0

  for suite in suites do
    let cases := selectCases cfg suite
    unless cases.isEmpty do
      IO.println suite.name
      for case in cases do
        try
          match ← case.run cfg with
          | .passed =>
            unless case.setup do
              IO.println s!"  ok: {case.name}"
              passed := passed + 1
          | .updated =>
            IO.println s!"  updated: {case.name}"
            updated := updated + 1
        catch err =>
          IO.eprintln s!"  FAIL: {case.name}"
          IO.eprintln s!"{renderError err}"
          failed := failed + 1

  if cfg.update then
    IO.println s!"\n{updated} updated, {failed} failed"
  else
    IO.println s!"\n{passed} passed, {failed} failed"
  pure (if failed == 0 then 0 else 1)

end Test.Framework
