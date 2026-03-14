import Std

namespace Test.Framework

open System

inductive TestTree where
  | test   : String → IO Unit → TestTree
  | golden : String → IO String → TestTree
  | group  : String → List TestTree → TestTree

structure RunConfig where
  update : Bool := false
  filters : List String := []

structure RunResult where
  passed : Nat := 0
  failed : Nat := 0
  updated : Nat := 0

instance : Add RunResult where
  add a b := { passed := a.passed + b.passed, failed := a.failed + b.failed, updated := a.updated + b.updated }

def parseArgs (args : List String) : RunConfig :=
  let update := args.contains "--update"
  let filters := args.filter (· != "--update")
  { update, filters }

private def pathStr (path : List String) : String :=
  "/".intercalate path

private def indent (depth : Nat) : String :=
  String.mk (List.replicate (depth * 2) ' ')

/-- A filter matches a path if the path equals the filter, or either is a
    segment-aligned prefix of the other (so groups are entered when they
    could contain matching tests). -/
private def matchesFilter (filters : List String) (path : List String) : Bool :=
  if filters.isEmpty then true
  else
    let ps := pathStr path
    filters.any fun filter =>
      ps == filter ||
      filter.startsWith (ps ++ "/") ||
      ps.startsWith (filter ++ "/")

private def sortStrings (xs : List String) : List String :=
  (xs.toArray.qsort (fun a b => a < b)).toList

private def expectedFileNames (dir : FilePath) : IO (List String) := do
  try
    let entries ← dir.readDir
    let mut names : List String := []
    for entry in entries do
      if entry.fileName.endsWith ".expected" then
        names := entry.fileName.dropRight ".expected".length :: names
    pure (sortStrings names)
  catch _ =>
    pure []

private def formatNameDiff (label : String) (names : List String) : String :=
  if names.isEmpty then
    ""
  else
    let body := "\n".intercalate (names.map (fun name => s!"  - {name}"))
    s!"{label}:\n{body}\n"

private def goldenDir (path : List String) : FilePath :=
  path.foldl (fun acc (seg : String) => acc / seg) ("Test" / "golden")

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

/-- Collect names of direct `.golden` children. -/
private def goldenChildNames (children : List TestTree) : List String :=
  children.filterMap fun
    | .golden name _ => some name
    | _ => none

/-- Check parity between golden test names and `.expected` files in dir. -/
private def checkParity (dir : FilePath) (goldenNames : List String) (cfg : RunConfig)
    (depth : Nat) : IO Bool := do
  if cfg.update then
    IO.FS.createDirAll dir
  let fileNames ← expectedFileNames dir
  let sorted := sortStrings goldenNames
  -- In update mode, missing files will be created; only report extra files
  let missing := if cfg.update then [] else sorted.filter (fun name => !(fileNames.contains name))
  let extra := fileNames.filter (fun name => !(sorted.contains name))
  if missing.isEmpty && extra.isEmpty then
    return true
  else
    IO.eprintln <| s!"{indent depth}FAIL: _fixture_parity"
    IO.eprintln <| s!"Fixture parity mismatch in {dir.toString}\n" ++
      formatNameDiff "Missing fixtures" missing ++
      formatNameDiff "Extra fixtures" extra
    return false

/-- Run the test tree, printing results and returning counts. -/
partial def runTree (cfg : RunConfig) (tree : TestTree)
    (path : List String := []) (depth : Nat := 0) : IO RunResult := do
  match tree with
  | .group name children =>
    let newPath := path ++ [name]
    if !(matchesFilter cfg.filters newPath) then
      return { passed := 0, failed := 0, updated := 0 }
    IO.println s!"{indent depth}{name}"
    let mut result : RunResult := { passed := 0, failed := 0, updated := 0 }
    -- Parity check for groups whose direct children are golden tests
    let gNames := goldenChildNames children
    unless gNames.isEmpty do
      let dir := goldenDir newPath
      let ok ← checkParity dir gNames cfg (depth + 1)
      unless ok do
        result := result + { failed := 1, passed := 0, updated := 0 }
    for child in children do
      let r ← runTree cfg child newPath (depth + 1)
      result := result + r
    pure result
  | .test name action =>
    let testPath := path ++ [name]
    if !(matchesFilter cfg.filters testPath) then
      return { passed := 0, failed := 0, updated := 0 }
    try
      action
      IO.println s!"{indent depth}ok: {name}"
      pure { passed := 1, failed := 0, updated := 0 }
    catch err =>
      IO.eprintln s!"{indent depth}FAIL: {name}"
      IO.eprintln (toString err)
      pure { failed := 1, passed := 0, updated := 0 }
  | .golden name render =>
    let testPath := path ++ [name]
    if !(matchesFilter cfg.filters testPath) then
      return { passed := 0, failed := 0, updated := 0 }
    let dir := goldenDir path
    try
      let filePath := dir / s!"{name}.expected"
      let actual ← render
      if cfg.update then
        IO.FS.createDirAll dir
        IO.FS.writeFile filePath (actual ++ "\n")
        IO.println s!"{indent depth}updated: {name}"
        pure { updated := 1, passed := 0, failed := 0 }
      else
        match ← readFileOpt filePath with
        | none =>
          throw <| IO.userError s!"Missing fixture: {filePath.toString} (run with --update)"
        | some content =>
          let expected := content.trimRight
          let actual := actual.trimRight
          unless actual == expected do
            let diff := diffMessage expected actual
            throw <| IO.userError s!"Golden mismatch: {filePath.toString}\n{diff}"
          IO.println s!"{indent depth}ok: {name}"
          pure { passed := 1, failed := 0, updated := 0 }
    catch err =>
      IO.eprintln s!"{indent depth}FAIL: {name}"
      IO.eprintln (toString err)
      pure { failed := 1, passed := 0, updated := 0 }

def runTestTree (tree : TestTree) (args : List String) : IO UInt32 := do
  let cfg := parseArgs args
  let result ← runTree cfg tree
  if cfg.update then
    IO.println s!"\n{result.updated} updated, {result.failed} failed"
  else
    IO.println s!"\n{result.passed} passed, {result.failed} failed"
  pure (if result.failed == 0 then 0 else 1)

/-! ## TreeBuilder Monad -/

abbrev TreeBuilder := StateM (List TestTree)

instance : Coe TestTree (TreeBuilder Unit) where
  coe tree := modify (tree :: ·)

def suite (name : String) (body : TreeBuilder Unit) : TestTree :=
  let (_, trees) := body.run []
  .group name trees.reverse

def group (name : String) (body : TreeBuilder Unit) : TreeBuilder Unit :=
  let (_, trees) := body.run []
  modify ((.group name trees.reverse) :: ·)

def test (name : String) (action : IO Unit) : TreeBuilder Unit :=
  modify ((.test name action) :: ·)

def golden (name : String) (render : IO String) : TreeBuilder Unit :=
  modify ((.golden name render) :: ·)

def goldenSections (sections : List (String × String)) : String :=
  "\n\n".intercalate (sections.map fun (h, c) => s!"@ {h}\n{c}")

end Test.Framework
