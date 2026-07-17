import Moist.SMT.DagRender

namespace Test.SMT.DagRender

open Moist.SMT

def collisionExpr : Expr :=
  let shared := Expr.add (.sym "moist.dag.0") (.sym "|moist.dag.1|")
  Expr.eq shared shared

def collisionScript : Script :=
  ⟨[ .declareConst "moist.dag.0" .int
   , .declareConst "|moist.dag.1|" .int
   , .assert collisionExpr
   , .checkSat
   ]⟩

def referencePath : System.FilePath := "/tmp/moist-dag-render-reference.smt2"
def dagPath : System.FilePath := "/tmp/moist-dag-render-shared.smt2"

unsafe def main : IO Unit := do
  let rendered := collisionExpr.renderDagResult
  assert! rendered.bindings == 1
  assert! rendered.text.startsWith "(let ((|moist.dag.2|"
  IO.FS.writeFile referencePath collisionScript.render
  IO.FS.writeFile dagPath collisionScript.renderDag
  IO.println s!"bindings={rendered.bindings}"

end Test.SMT.DagRender

unsafe def main : IO Unit := Test.SMT.DagRender.main
