import Moist.SMT.Compiler.Operational

namespace Test.SMT.DagRender

open Moist.SMT
open Moist.SMT.UPLC

def collisionExpr : Expr :=
  let shared := Expr.add (.sym "moist.dag.0") (.sym "|moist.dag.1|")
  Expr.eq shared shared

def collisionScript : Script :=
  ⟨[ .declareConst "moist.dag.0" .int
   , .declareConst "|moist.dag.1|" .int
   , .assert collisionExpr
   , .checkSat
   ]⟩

def sharedInteger : Expr :=
  let shared := Expr.add (.int 20) (.int 22)
  Expr.mul shared shared

def sharedBytes : Expr :=
  let shared := Expr.app "seq.++"
    [.bytes (ByteArray.mk #[0, 255]), .bytes (ByteArray.mk #[1, 2])]
  Expr.app "seq.++" [shared, shared]

def sharedString : Expr :=
  let shared := Expr.app "seq.++" [.str "λ", .str "A"]
  Expr.app "seq.++" [shared, shared]

def sharedData : Expr :=
  let fields := Expr.app "DCons" [.dataLit (.I 1), .app "DNil" []]
  let shared := Expr.app "DConstr" [.int 7, fields]
  Expr.app "DList"
    [.app "DCons" [shared, .app "DCons" [shared, .app "DNil" []]]]

def cases : List (String × List Command × Expr) :=
  [ ("collision",
      [.declareConst "moist.dag.0" .int,
       .declareConst "|moist.dag.1|" .int], collisionExpr)
  , ("integer", [], sharedInteger)
  , ("bytes", [], sharedBytes)
  , ("string", [], sharedString)
  , ("data", [], sharedData)
  ]

private def firstLine (text : String) : String :=
  (text.splitOn "\n").head?.getD ""

/-- Ask Z3 whether the transparent and pointer-sharing renderings can differ.
`unsat` is an independent parser/sort/denotation regression for the unsafe
operational renderer; the kernel soundness boundary continues to use the
transparent renderer. -/
private unsafe def checkEquivalent
    (name : String) (declarations : List Command) (expression : Expr) : IO Unit := do
  let rendered := expression.renderDagResult
  unless rendered.bindings > 0 do
    throw <| IO.userError s!"{name}: test expression lost physical sharing"
  let assertion := Command.raw <|
    "(assert (not (= " ++ expression.render ++ " " ++ rendered.text ++ ")))"
  let script : Script :=
    ⟨preludeForAssertions [expression] ++ declarations ++ [assertion, .checkSat]⟩
  let path : System.FilePath := s!"/tmp/moist-dag-render-{name}.smt2"
  IO.FS.writeFile path script.render
  let result ← IO.Process.output { cmd := "z3", args := #[path.toString] }
  IO.FS.removeFile path
  unless result.exitCode == 0 && result.stderr.isEmpty &&
      firstLine result.stdout == "unsat" &&
      (result.stdout.splitOn "(error").length == 1 do
    throw <| IO.userError <|
      s!"{name}: reference/DAG renderings differ or are invalid:\n" ++
        result.stdout ++ result.stderr
  IO.println <|
    s!"{name}: reference and DAG renderings are Z3-equivalent " ++
      s!"({rendered.bindings} bindings)"

unsafe def main : IO Unit := do
  let rendered := collisionExpr.renderDagResult
  assert! rendered.bindings == 1
  assert! rendered.text.startsWith "(let ((|moist.dag.2|"
  for (name, declarations, expression) in cases do
    checkEquivalent name declarations expression

end Test.SMT.DagRender

unsafe def main : IO Unit := Test.SMT.DagRender.main
