import Moist.SMT.Soundness.SolverBoundary

/-!
# Solver-strategy assertion neutrality

Solver tactics may change latency, memory use, or whether Z3 returns
`unknown`; they cannot change the formula certified by the product soundness
boundary.  These checks exercise that theorem for the former two-way strategy,
the production strategy, and an arbitrary caller-supplied tactic.
-/

namespace Test.SMT.SolverStrategy

open Moist.SMT
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

def formerTactic : String :=
  "(par-or (then simplify ctx-solver-simplify smt) smt)"

example (tactic : String) (decls : List SymDecl) (assertions : List SExpr) :
    (scriptWithTactic tactic decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++ groupedAssertions assertions :=
  scriptWithTactic_assertions tactic decls assertions

example (decls : List SymDecl) (assertions : List SExpr) :
    (scriptWithTactic formerTactic decls assertions).assertions =
      (scriptWith decls assertions).assertions := by
  rw [scriptWithTactic_assertions, scriptWith_assertions]

-- These actual-machine endpoints therefore remain the endpoints for every
-- model returned by the new strategy.
#check BoolTrueQuery.sound
#check IntEqQuery.sound
#check ErrorQuery.sound

end Test.SMT.SolverStrategy
