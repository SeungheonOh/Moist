import Moist.SMT.Compiler.UPLC.Prelude
import Moist.SMT.Compiler.UPLC.Evaluation
import Moist.SMT.Compiler.UPLC.Declarations

/-!
# UPLC compiler query assembly

Logical result conditions and canonical SMT script constructors.  This is the
top executable UPLC compiler layer.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term

/-! ## Assertion grouping

Refinement contexts commonly contribute hundreds of assertions which share
large subexpressions.  Keeping each assertion in a separate SMT command hides
that sharing from the per-command DAG renderer.  Group caller assertions into
one conjunction while leaving declaration assumptions separate (the latter
are used individually to decode the solver environment).

The singleton case is definitionally unchanged, so the three production CEK
queries still expose their exact generated condition. -/

def assertionConjunction : List SExpr → SExpr
  | [] => SExpr.trueE
  | expression :: expressions =>
      SExpr.and expression (assertionConjunction expressions)

def groupedAssertions : List SExpr → List SExpr
  | [] => []
  | [expression] => [expression]
  | expression :: next :: expressions =>
      [assertionConjunction (expression :: next :: expressions)]

def groupedAssertionCommands (assertions : List SExpr) :
    List Moist.SMT.Command :=
  (groupedAssertions assertions).map Moist.SMT.Command.assert

def okBoolTrueCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .ok pc v =>
        let b := asBool v
        some (SExpr.all [pc, b.guard, b.val])
    | _ => none

def okIntEqCond (outs : List Outcome) (rhs : SExpr) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .ok pc v =>
        let i := asInt v
        some (SExpr.all [pc, i.guard, SExpr.eq i.val rhs])
    | _ => none

def errorCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .error pc => some pc
    | _ => none

def timeoutCond (outs : List Outcome) : SExpr :=
  SExpr.any <| outs.filterMap fun
    | .timeout pc => some pc
    | _ => none

/-- Try a propagation-heavy refinement pass for at most one second, then fall
back to the former two-way portfolio of context-aware and direct SMT search.
The bounded fast path solves common arithmetic/control-flow obligations with
roughly half the solver memory, while the fallback retains the more robust
behavior needed by hard datatype equalities.

This changes only solver strategy.  `scriptWithTactic_assertions` in
`Moist.SMT.Soundness.Compiler` proves that the tactic string cannot add,
remove, or rewrite a logical assertion, and the production CEK endpoints
consume exactly that assertion list. -/
def z3QueryTactic : String :=
  "(or-else (try-for (then simplify propagate-values smt) 1000) " ++
    "(par-or (then simplify ctx-solver-simplify smt) smt))"

/-- Construct the typed command sequence with a caller-supplied solver tactic.
The production compiler uses only the fixed, reviewed `z3QueryTactic`; callers of
this benchmarking helper remain responsible for supplying well-formed Z3
tactic syntax at the external rendering boundary. -/
def scriptWithTactic (tactic : String) (decls : List SymDecl)
    (assertions : List SExpr) : Moist.SMT.Script :=
  let logicalAssertions :=
    decls.flatMap SymDecl.assumptions ++ groupedAssertions assertions
  ⟨preludeForAssertions logicalAssertions ++
    declCommands decls ++ assumptionCommands decls ++
    groupedAssertionCommands assertions ++
      [.checkSatUsing tactic, .getModel]⟩

def scriptWith (decls : List SymDecl) (assertions : List SExpr) : Moist.SMT.Script :=
  scriptWithTactic z3QueryTactic decls assertions

/-- Unoptimized reference used to state and benchmark prelude slicing. -/
def scriptWithFullPrelude (decls : List SymDecl)
    (assertions : List SExpr) : Moist.SMT.Script :=
  ⟨prelude ++ declCommands decls ++ assumptionCommands decls ++
    assertions.map Moist.SMT.Command.assert ++
      [.checkSatUsing z3QueryTactic, .getModel]⟩

/-- Opt-in final normalization for callers supplying arbitrary hand-written
assertions.  Compiler-generated queries already use the verified smart
constructors throughout; traversing their potentially shared decision DAG a
second time is both redundant and prohibitively expensive for symbolic list
programs. -/
def scriptWithSimplified (decls : List SymDecl)
    (assertions : List SExpr) : Moist.SMT.Script :=
  scriptWith decls (assertions.map Expr.simplifyBool)

def scriptForBoolTrue (fuel : Nat) (decls : List SymDecl) (t : Term) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls [okBoolTrueCond outs]

def scriptForIntEq (fuel : Nat) (decls : List SymDecl) (t : Term) (rhs : SExpr) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls [okIntEqCond outs rhs]

def scriptForError (fuel : Nat) (decls : List SymDecl) (t : Term) : Moist.SMT.Script :=
  let outs := evalSym fuel (envOf decls) t
  scriptWith decls [errorCond outs]

end Moist.SMT.UPLC
