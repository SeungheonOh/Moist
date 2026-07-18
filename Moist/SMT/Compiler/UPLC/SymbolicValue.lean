import Moist.SMT.Compiler.UPLC.Expressions
import Moist.CEK.Builtins
import Moist.Plutus.DecidableEq

/-!
# UPLC compiler symbolic values

Proof-free symbolic values, path-conditioned outcomes, and their basic
combinators.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs)

/-! ## Proof-free constant-list lengths

`ChooseList` can avoid generating an impossible alternative when a constant
list's length is statically known.  Hints are ordinary executable data so the
compiler IR can be ported without dependent proof objects.  Before a hint can
prune a branch, `knownLength` rechecks it against the expression's exact
constructor shape.  A fabricated hint therefore degrades to `unknown`.

`Soundness.ListCertificates` proves that every successful structural recheck
equals the length of any list denoted by the expression.
-/

inductive ConstListLengthHint where
  | unknown
  | exact (length : Nat)
deriving Repr, BEq

namespace ConstListLengthHint

/-- Reconstruct an exact length only from syntax whose list length is
independent of the SMT model.  Returning `none` merely disables pruning. -/
def inferExact? : SExpr → Option Nat
  | .constListLit xs => some xs.length
  | .app "VCons" [_, tail] => (inferExact? tail).map (· + 1)
  | .app "vtail" [xs] =>
      match inferExact? xs with
      | some (n + 1) => some n
      | _ => none
  | .ite _ thenExpr elseExpr =>
      match inferExact? thenExpr, inferExact? elseExpr with
      | some thenLength, some elseLength =>
          if thenLength == elseLength then some thenLength else none
      | _, _ => none
  | _ => none

/-- Accept a cached length only after reconstructing the same length directly
from the expression.  This is the fail-closed boundary for arbitrary compiler
IR values. -/
def knownLength (hint : ConstListLengthHint) (expr : SExpr) : Option Nat :=
  match hint with
  | .unknown => none
  | .exact length =>
      if inferExact? expr == some length then some length else none

def literal (xs : List Const) : ConstListLengthHint :=
  .exact xs.length

def cons (_head : SExpr) (hint : ConstListLengthHint) :
    ConstListLengthHint :=
  match hint with
  | .unknown => .unknown
  | .exact n => .exact (n + 1)

def tail (hint : ConstListLengthHint) : ConstListLengthHint :=
  match hint with
  | .unknown | .exact 0 => .unknown
  | .exact (n + 1) => .exact n

def ite (_condition : SExpr)
    (thenHint elseHint : ConstListLengthHint) : ConstListLengthHint :=
  match thenHint, elseHint with
  | .exact thenLength, .exact elseLength =>
      if thenLength == elseLength then .exact thenLength else .unknown
  | _, _ => .unknown

end ConstListLengthHint

inductive SymConst where
  | integer : SExpr → SymConst
  | bytes : SExpr → SymConst
  | string : SExpr → SymConst
  | bool : SExpr → SymConst
  | unit : SymConst
  | data : SExpr → SymConst
  /-- A builtin constant list with a proof-free, structurally rechecked hint. -/
  | constList : SExpr → ConstListLengthHint → SymConst
  | dataList : SExpr → SymConst
  | pairDataList : SExpr → SymConst
  | pairData : SExpr → SExpr → SymConst
  | array : SExpr → SymConst
  | g1 : SExpr → SymConst
  | g2 : SExpr → SymConst
  | ml : SExpr → SymConst
deriving Repr

instance : BEq SymConst where
  beq a b :=
    match a, b with
    | .integer x, .integer y
    | .bytes x, .bytes y
    | .string x, .string y
    | .bool x, .bool y
    | .data x, .data y
    | .dataList x, .dataList y
    | .pairDataList x, .pairDataList y
    | .array x, .array y
    | .g1 x, .g1 y
    | .g2 x, .g2 y
    | .ml x, .ml y => x == y
    | .constList x hx, .constList y hy =>
        x == y && hx == hy
    | .unit, .unit => true
    | .pairData a b, .pairData c d => a == c && b == d
    | _, _ => false

inductive SymVal where
  | const : SymConst → SymVal
  | dyn : SExpr → SymVal
  | pair : SymVal → SymVal → SymVal
  | constr : SExpr → List SymVal → SymVal
  | lam : Term → List SymVal → SymVal
  | delay : Term → List SymVal → SymVal
  | builtin : BuiltinFun → List SymVal → ExpectedArgs → SymVal
deriving Repr

instance : Inhabited SymVal where
  default := .const .unit

inductive Outcome where
  | ok : SExpr → SymVal → Outcome
  | error : SExpr → Outcome
  | timeout : SExpr → Outcome
deriving Repr

namespace Outcome

def pc : Outcome → SExpr
  | .ok p _ => p
  | .error p => p
  | .timeout p => p

def guard (g : SExpr) : Outcome → Outcome
  | .ok p v => .ok (SExpr.and g p) v
  | .error p => .error (SExpr.and g p)
  | .timeout p => .timeout (SExpr.and g p)

end Outcome

def ok (v : SymVal) : List Outcome := [.ok SExpr.trueE v]
def err : List Outcome := [.error SExpr.trueE]
def timeout : List Outcome := [.timeout SExpr.trueE]

/-- Retain an error unless its path is syntactically impossible. -/
def carryError : SExpr → List Outcome
  | .bool false => []
  | pc => [.error pc]

/-- Retain a timeout unless its path is syntactically impossible. -/
def carryTimeout : SExpr → List Outcome
  | .bool false => []
  | pc => [.timeout pc]

def bindOk (pc : SExpr) (v : SymVal) (k : SymVal → List Outcome) : List Outcome :=
  match pc with
  -- A continuation below a syntactically impossible path cannot contribute an
  -- active result.  Avoid constructing it: recursive continuations may be
  -- exponentially larger than the path which rules them out.
  | .bool false => []
  | _ => (k v).map (Outcome.guard pc)

def bindOut (xs : List Outcome) (k : SymVal → List Outcome) : List Outcome :=
  xs.flatMap fun
    | .ok pc v => bindOk pc v k
    -- Errors and timeouts under a syntactically false path are unreachable.
    -- Carry reachable failures directly; no continuation or guard-map work is
    -- needed because their path condition is already complete.
    | .error pc => carryError pc
    | .timeout pc => carryTimeout pc

def mapPc (g : SExpr) (xs : List Outcome) : List Outcome :=
  xs.map (Outcome.guard g)

def valListExpr : List SExpr → SExpr
  | [] => .app "VNil" []
  | x :: xs => .app "VCons" [x, valListExpr xs]

def dataListExpr : List SExpr → SExpr
  | [] => .app "DNil" []
  | x :: xs => .app "DCons" [x, dataListExpr xs]

def dataPairListExpr : List (SExpr × SExpr) → SExpr
  | [] => .app "DPNil" []
  | (k, v) :: xs => .app "DPCons" [k, v, dataPairListExpr xs]

def encodeVal? : SymVal → Option SExpr
  | .const c => encodeConst? c
  | .dyn e => some e
  | .pair a b => do
      let a' ← encodeVal? a
      let b' ← encodeVal? b
      some (.app "VPair" [a', b'])
  | .constr tag fields => do
      let fs ← fields.mapM encodeVal?
      some (.app "VConstr" [tag, valListExpr fs])
  | .lam _ _ | .delay _ _ | .builtin _ _ _ => none
where
  encodeConst? : SymConst → Option SExpr
    | .integer i => some (.app "VInt" [i])
    | .bytes b => some (.app "VBytes" [b])
    | .string s => some (.app "VString" [s])
    | .bool b => some (.app "VBool" [b])
    | .unit => some (.app "VUnit" [])
    | .data d => some (.app "VData" [d])
    | .constList xs _ => some (.app "VList" [xs])
    | .dataList xs => some (.app "VDataList" [xs])
    | .pairDataList xs => some (.app "VPairDataList" [xs])
    | .pairData a b => some (.app "VPairData" [a, b])
    | .array xs => some (.app "VArray" [xs])
    | .g1 g => some (.app "VG1" [g])
    | .g2 g => some (.app "VG2" [g])
    | .ml r => some (.app "VMlResult" [r])


end Moist.SMT.UPLC

