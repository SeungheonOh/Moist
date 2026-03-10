import Test.MIR.OptimizeGolden

open Test.MIR.OptGolden

def readFileOpt (path : String) : IO (Option String) := do
  try
    let content ← IO.FS.readFile ⟨path⟩
    pure (some content)
  catch _ =>
    pure none

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let dir := "test/golden-opt"

  if update then
    IO.FS.createDirAll ⟨dir⟩

  let mut passed : Nat := 0
  let mut failed : Nat := 0
  let mut updated : Nat := 0

  for (name, actual) in optGoldenTests do
    let path := s!"{dir}/{name}.expected"

    if update then
      IO.FS.writeFile ⟨path⟩ (actual ++ "\n")
      IO.println s!"  updated: {name}"
      updated := updated + 1
    else
      match ← readFileOpt path with
      | none =>
        IO.eprintln s!"  MISSING: {name} (run with --update to generate)"
        failed := failed + 1
      | some content =>
        let expected := content.trimRight
        if actual.trimRight == expected then
          IO.println s!"  ok: {name}"
          passed := passed + 1
        else
          IO.eprintln s!"  FAIL: {name}"
          let expectedLines := expected.splitOn "\n"
          let actualLines := actual.trimRight.splitOn "\n"
          let maxLines := max expectedLines.length actualLines.length
          for i in List.range maxLines do
            let expLine := expectedLines.getD i ""
            let actLine := actualLines.getD i ""
            if expLine != actLine then
              IO.eprintln s!"    line {i + 1}:"
              IO.eprintln s!"      exp: {expLine}"
              IO.eprintln s!"      got: {actLine}"
          failed := failed + 1

  if update then
    IO.println s!"\nUpdated {updated} golden files in {dir}/"
    return 0
  else
    IO.println s!"\n{passed} passed, {failed} failed"
    return if failed > 0 then 1 else 0
