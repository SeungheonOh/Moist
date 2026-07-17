import Test.SMT.Examples
import Moist.SMT.Soundness

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

-- The production script constructor applies exactly the verified pass.
example : scriptForIntEq 100 [xInt] recursiveSumTerm (.int 55) =
    scriptWith [xInt] [rawRecursiveSum55] := rfl

-- Regression benchmark for the path-exploding recursive query.  Construction-
-- time smart constructors already reach this compact form; the exact query
-- normalizer is therefore idempotent on this workload.
#guard exprNodes rawRecursiveSum55 == 5566
#guard exprNodes rawRecursiveSum55.simplifyBool == 5566
#guard rawRecursiveSum55.render.length == 19431
#guard rawRecursiveSum55.simplifyBool.render.length == 19431

-- The generic preservation theorem and both end-to-end CEK corollaries are
-- typechecked here at their public interfaces.
example (m : Semantics.Model) :
    Semantics.evalBool? m rawRecursiveSum55.simplifyBool =
      Semantics.evalBool? m rawRecursiveSum55 :=
  Semantics.evalBool?_simplifyBool m rawRecursiveSum55

#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound

end Test.SMT.Optimize
