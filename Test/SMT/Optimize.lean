import Test.SMT.Examples
import Test.SMT.Coverage

namespace Test.SMT.Optimize

open Moist.SMT
open Moist.SMT.UPLC
open Test.SMT.Examples

-- External names cannot collide with SMT literals, start with a digit, or
-- alias merely because their punctuation was replaced by the same character.
#guard sanitize "true" != "true"
#guard sanitize "false" != "false"
#guard sanitize "1x" == "$u$49_120"
#guard sanitize "a b" != sanitize "a?b"
#guard sanitize "" == "$u$"

def exprNodes : Expr → Nat
  | .sym _ | .int _ | .bytes _ | .dataLit _ | .dataListLit _
  | .dataPairListLit _ | .constListLit _ | .bool _ | .str _ => 1
  | .app _ xs => 1 + (xs.map exprNodes).sum
  | .ite c t e => 1 + exprNodes c + exprNodes t + exprNodes e

def rawRecursiveSum55 : Expr :=
  okIntEqCond (evalSym 100 (envOf [xInt]) recursiveSumTerm) (.int 55)

-- Focused reduction rules.
#guard (Expr.and (.bool false) (.sym "missing") == .bool false)
#guard (Expr.or (.bool true) (.sym "missing") == .bool true)
#guard (Expr.simplifyBool (.app "and" [.bool true, .sym "p"]) == .sym "p")
#guard (Expr.simplifyBool (.app "or" [.bool false, .sym "p"]) == .sym "p")
#guard (Expr.simplifyBool (.app "not" [.app "not" [.sym "p"]]) == .sym "p")
#guard (Expr.simplifyBool (.ite (.sym "p") (.bool true) (.bool false)) == .sym "p")
#guard (Expr.simplifyBool (.ite (.sym "p") (.bool false) (.bool true)) ==
  .app "not" [.sym "p"])

-- These tempting annihilator rewrites are deliberately absent: with the
-- partial executable SMT semantics, an ill-typed/undefined operand must stay
-- undefined rather than becoming a total Boolean constant.
#guard (Expr.simplifyBool (.app "and" [.bool false, .sym "missing"]) ==
  .app "and" [.bool false, .sym "missing"])
#guard (Expr.simplifyBool (.app "or" [.bool true, .sym "missing"]) ==
  .app "or" [.bool true, .sym "missing"])

-- A continuation below a syntactically false path is never constructed.
#guard (bindOk (.bool false) (.const .unit)
  (fun _ => [.error (.sym "large")])).isEmpty

-- The production compiler emits the already-smart-constructed condition
-- directly.  Explicit normalization remains available for hand-written
-- assertions and is structurally idempotent on this workload.
example : scriptForIntEq 100 [xInt] recursiveSumTerm (.int 55) =
    scriptWith [xInt] [rawRecursiveSum55] := rfl

example : scriptWithSimplified [xInt] [rawRecursiveSum55] =
    scriptWith [xInt] [rawRecursiveSum55.simplifyBool] := rfl

#guard Command.render (.checkSatUsing z3QueryTactic) ==
  "(check-sat-using (or-else (try-for (then simplify propagate-values smt) 1000) " ++
    "(par-or (then simplify ctx-solver-simplify smt) smt)))"

-- Solver preprocessing is deliberately outside the assertion list.  The
-- kernel checks that the optimized script still submits exactly the symbolic
-- environment assumptions followed by the compiler-generated query.
example (decls : List SymDecl) (assertions : List Expr) :
    (scriptWith decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++ assertions :=
  scriptWith_assertions decls assertions

-- Regression benchmark for the path-exploding recursive query.  Construction-
-- time smart constructors already reach this compact form; the exact query
-- normalizer is therefore idempotent on this workload.  The 18 merged paths
-- use lazy `ite` discriminators so the path and selected value are defined
-- together under the executable partial SMT semantics.
#guard exprNodes rawRecursiveSum55 == 1573
#guard exprNodes rawRecursiveSum55.simplifyBool == 1573
#guard rawRecursiveSum55.render.length == 5265
#guard rawRecursiveSum55.simplifyBool.render.length == 5265

-- The generic preservation theorem and all end-to-end CEK corollaries are
-- typechecked here at their public interfaces.
example (m : Semantics.Model) :
    Semantics.evalBool? m rawRecursiveSum55.simplifyBool =
      Semantics.evalBool? m rawRecursiveSum55 :=
  Semantics.evalBool?_simplifyBool m rawRecursiveSum55

#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkIntEqCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_errorCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_okBoolTrueCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_okIntEqCond_sound
#check scriptForBoolTrue_assertions
#check scriptForIntEq_assertions
#check scriptForError_assertions

end Test.SMT.Optimize
