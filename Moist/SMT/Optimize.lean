import Moist.SMT.Syntax

namespace Moist.SMT

/-!
# Verified Boolean normalization

The symbolic UPLC compiler generates large Boolean path conditions.  This pass
removes neutral constants, double negations, and Boolean `ite` wrappers.  It
deliberately treats every other SMT application as opaque.  The preservation
proof in `Moist.SMT.Soundness.Optimize` therefore does not depend on a typing
assumption for the open SMT expression language.
-/

namespace Expr

def isTrue : Expr → Bool
  | .bool true => true
  | _ => false

def isFalse : Expr → Bool
  | .bool false => true
  | _ => false

def smartNot : Expr → Expr
  | .bool b => .bool (!b)
  | .app "not" [a] => a
  | a => .app "not" [a]

def smartAnd (a b : Expr) : Expr :=
  if isTrue a then b
  else if isTrue b then a
  else .app "and" [a, b]

def smartOr (a b : Expr) : Expr :=
  if isFalse a then b
  else if isFalse b then a
  else .app "or" [a, b]

def smartIte (c t e : Expr) : Expr :=
  if isTrue c then t
  else if isFalse c then e
  else if isTrue t then
    if isFalse e then c else .ite c t e
  else if isFalse t then
    if isTrue e then smartNot c else .ite c t e
  else .ite c t e

def simplifyBool : Expr → Expr
  | .app "not" [a] => smartNot (simplifyBool a)
  | .app "and" [a, b] => smartAnd (simplifyBool a) (simplifyBool b)
  | .app "or" [a, b] => smartOr (simplifyBool a) (simplifyBool b)
  | .ite c t e => smartIte (simplifyBool c) (simplifyBool t) (simplifyBool e)
  | e => e

end Expr

end Moist.SMT
