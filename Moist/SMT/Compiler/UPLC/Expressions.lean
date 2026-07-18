import Moist.SMT.Optimize
import Moist.Plutus.DecidableEq

/-!
# UPLC compiler expression layer

Proof-free SMT expression aliases, exact syntactic checks, balancing, and
typed arithmetic smart constructors used by symbolic lowering.
-/

namespace Moist.SMT.UPLC

abbrev SExpr := Moist.SMT.Expr

namespace SExpr

abbrev trueE : SExpr := Moist.SMT.Expr.trueE
abbrev falseE : SExpr := Moist.SMT.Expr.falseE

/- Lift a proof-free element matcher to lists.  The soundness-side theorem
proves that a positive result from the complete Boolean check below implies
exact syntactic equality. -/
def sameListWith
    (same : SExpr → SExpr → Bool) :
    List SExpr → List SExpr → Bool
  | [], [] => true
  | x :: xs, y :: ys => same x y && sameListWith same xs ys
  | _, _ => false

/- Return `true` only when two SMT expressions have exactly the same syntax.
Fuel bounds compiler work only: exhaustion merely forgoes the optimization.
The executable compiler carries no dependent equality proof; the implication
from `true` to equality is established in `Soundness.Compiler`. -/
def same? : (fuel : Nat) → (a b : SExpr) → Bool
  | 0, _, _ => false
  | _ + 1, .sym x, .sym y =>
      decide (x = y)
  | _ + 1, .int x, .int y =>
      decide (x = y)
  | _ + 1, .bytes x, .bytes y =>
      decide (x = y)
  | _ + 1, .dataLit x, .dataLit y =>
      decide (x = y)
  | _ + 1, .dataListLit x, .dataListLit y =>
      decide (x = y)
  | _ + 1, .dataPairListLit x, .dataPairListLit y =>
      decide (x = y)
  | _ + 1, .constListLit x, .constListLit y =>
      decide (x = y)
  | _ + 1, .bool x, .bool y =>
      decide (x = y)
  | _ + 1, .str x, .str y =>
      decide (x = y)
  | fuel + 1, .app f xs, .app g ys =>
      decide (f = g) && sameListWith (same? fuel) xs ys
  | fuel + 1, .ite c t e, .ite c' t' e' =>
      same? fuel c c' && same? fuel t t' && same? fuel e e'
  | _ + 1, _, _ => false

/--
Equality specialized for values that are already protected by a successful
typed projection.  Equal syntax denotes the same projected value, so the
result can be emitted as `true`; the soundness lemmas in
`Moist.SMT.Soundness.Foundations` deliberately use this only after proving
both operands evaluate at the required SMT sort.
-/
def reflexiveEqFuel : Nat := 128

def reflexiveEq (a b : SExpr) : SExpr :=
  if same? reflexiveEqFuel a b then trueE
  else Moist.SMT.Expr.eq a b

/-- A conservative, proof-friendly equality test for atomic SMT expressions.
Returning `false` only misses an optimization; returning `true` is proved to
mean syntactic equality below. -/
def sameAtom : SExpr → SExpr → Bool
  | .sym a, .sym b => decide (a = b)
  | .int a, .int b => decide (a = b)
  | .bytes a, .bytes b => decide (a = b)
  | .dataLit a, .dataLit b => decide (a = b)
  | .dataListLit a, .dataListLit b => decide (a = b)
  | .dataPairListLit a, .dataPairListLit b => decide (a = b)
  | .constListLit a, .constListLit b => decide (a = b)
  | .bool a, .bool b => decide (a = b)
  | .str a, .str b => decide (a = b)
  | _, _ => false

def not (a : SExpr) : SExpr := Moist.SMT.Expr.not a
def and (a b : SExpr) : SExpr := Moist.SMT.Expr.and a b
def or (a b : SExpr) : SExpr := Moist.SMT.Expr.or a b
def eq (a b : SExpr) : SExpr := Moist.SMT.Expr.eq a b
def ne (a b : SExpr) : SExpr := Moist.SMT.Expr.ne a b
def add (a b : SExpr) : SExpr := Moist.SMT.Expr.add a b
def sub (a b : SExpr) : SExpr := Moist.SMT.Expr.sub a b
def mul (a b : SExpr) : SExpr := Moist.SMT.Expr.mul a b
def lt (a b : SExpr) : SExpr := Moist.SMT.Expr.lt a b
def le (a b : SExpr) : SExpr := Moist.SMT.Expr.le a b
def gt (a b : SExpr) : SExpr := Moist.SMT.Expr.gt a b
def ge (a b : SExpr) : SExpr := Moist.SMT.Expr.ge a b
def all (xs : List SExpr) : SExpr := Moist.SMT.Expr.all xs

/-- Combine adjacent Boolean alternatives in one bottom-up balancing round. -/
def orPairRound : List SExpr → List SExpr
  | left :: right :: rest => or left right :: orPairRound rest
  | [single] => [single]
  | [] => []

private theorem orPairRound_length_le :
    ∀ xs : List SExpr, (orPairRound xs).length ≤ xs.length
  | [] => by simp [orPairRound]
  | [single] => by simp [orPairRound]
  | left :: right :: rest => by
      simp only [orPairRound, List.length_cons]
      have hle := orPairRound_length_le rest
      omega

/-- A logarithmic-expression-depth disjunction.  Unlike balancing selector
`ite`s, balancing `or` does not duplicate subexpressions. -/
def anyBalanced : (xs : List SExpr) → SExpr
  | [] => falseE
  | [single] => single
  | left :: right :: rest =>
      anyBalanced (or left right :: orPairRound rest)
termination_by xs => xs.length
decreasing_by
  simp only [List.length_cons]
  have hle := orPairRound_length_le rest
  omega

/-- Disjoin a collection without constructing a linear-depth SMT term. -/
def any (xs : List SExpr) : SExpr := anyBalanced xs

def ite (c t e : SExpr) : SExpr := Moist.SMT.Expr.ite c t e
def isCtor (ctor : String) (e : SExpr) : SExpr := .app ("(_ is " ++ ctor ++ ")") [e]
def seqEmpty (sort : String) : SExpr := .sym ("(as seq.empty " ++ sort ++ ")")
def seqUnit (e : SExpr) : SExpr := .app "seq.unit" [e]
def seqAppend (a b : SExpr) : SExpr := .app "seq.++" [a, b]
def seqLen (a : SExpr) : SExpr := .app "seq.len" [a]
def seqNth (a i : SExpr) : SExpr := .app "seq.nth" [a, i]
def seqExtract (a start len : SExpr) : SExpr := .app "seq.extract" [a, start, len]
def strAppend (a b : SExpr) : SExpr := .app "seq.++" [a, b]

/-! Typed arithmetic smart constructors

These constructors are deliberately separate from the open SMT surface's
`add`, `sub`, and `mul`.  Removing a neutral element is not valid for an
arbitrary ill-sorted expression: `(+ true 0)` is undefined in the executable
semantics whereas `true` is defined.  The symbolic builtin compiler uses the
smart constructors only after `asInt` has supplied the integer projection and
its guard.  Their integer-denotation evaluator lemmas live at the soundness
boundary alongside the corresponding builtin proofs.
-/

def isIntZero : SExpr → Bool
  | .int value => value == 0
  | _ => false

def isIntOne : SExpr → Bool
  | .int value => value == 1
  | _ => false

def intAdd (a b : SExpr) : SExpr :=
  if a.isIntZero then b
  else if b.isIntZero then a
  else add a b

def intSub (a b : SExpr) : SExpr :=
  if b.isIntZero then a else sub a b

def intMul (a b : SExpr) : SExpr :=
  if a.isIntZero then .int 0
  else if b.isIntZero then .int 0
  else if a.isIntOne then b
  else if b.isIntOne then a
  else mul a b

end SExpr

end Moist.SMT.UPLC

