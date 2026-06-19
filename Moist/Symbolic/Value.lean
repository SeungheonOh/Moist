import Moist.Symbolic.Smt
import Moist.CEK.Value

/-! # Symbolic values for the UPLC→SMT compiler

The compiler is a normalisation-by-evaluation interpreter (structurally a clone
of `Moist.Verified.BigStep.bigEval`) over the symbolic value domain `SymV`:

* **higher-order values stay structural** at Lean compile-time — `lam`/`delay`/
  `builtin`/known-tag `constr`;
* **first-order data is symbolic SMT** — `fo e` carries an `SExpr` of the
  universal value sort `V`;
* **symbolic merges are deferred** — `choice c a b` represents `if c then a else
  b` for two values whose *shapes* differ (e.g. a closure vs an integer); the
  eliminators (`Apply`/`Force`/`Case`) distribute over it, and it bottoms out at
  first-order `ite`s. This is what lets branching on symbolic data become SMT
  `ite` instead of a Lean-level fork (the thing that hangs Blaster).

A *computation* result is the total record `SymR = ⟨inc, err, val⟩`:

* `inc` — SMT boolean: the computation is **indeterminate** under the model (ran
  out of fuel, or used an unmodelled builtin). No claim is made about it.
* `err` — SMT boolean: the computation **errors** (a genuine UPLC failure:
  type mismatch, division by zero, head-of-nil, out-of-range tag, …).
* `val` — the resulting value (meaningful where `¬inc ∧ ¬err`).

All three are *symbolic*, so a single compiled result describes the behaviour
over the whole space of symbolic inputs at once: e.g. a recursive validator's
`inc` is a path condition like `x ≥ depth`, and its `err`/value vary with the
inputs. This three-outcome split is what makes bounded symbolic recursion work
and what makes the Stage-2 partiality soundness both true and useful.
-/

namespace Moist.Symbolic

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.Plutus (Data ByteString)
open Moist.CEK (ExpectedArgs)
open SExpr (sNot sAnd sOr sImplies sIte sEq)

/-! ## The symbolic value domain -/

/-- A symbolic UPLC value. -/
inductive SymV where
  /-- A first-order value, as an `SExpr` of the universal SMT sort `V`. -/
  | fo      : SExpr → SymV
  /-- A λ-closure (kept structural; β happens at compile time). -/
  | lam     : Term → List SymV → SymV
  /-- A delayed thunk (kept structural). -/
  | delay   : Term → List SymV → SymV
  /-- An SOP constructor with statically-known tag and symbolic fields. -/
  | constr  : Nat → List SymV → SymV
  /-- A partially-applied builtin (function, accumulated args reversed, remaining
      expected arguments) — mirrors `CekValue.VBuiltin`. -/
  | builtin : BuiltinFun → List SymV → ExpectedArgs → SymV
  /-- A deferred symbolic merge `if c then a else b` of two differing shapes. -/
  | choice  : SExpr → SymV → SymV → SymV
deriving Inhabited

/-- A symbolic environment: a stack of values (`Var 1` = head), mirroring `CekEnv`. -/
abbrev SymEnv := List SymV

/-- A computation outcome (total): indeterminate iff `inc`, else errors iff `err`,
else yields `val`. -/
structure SymR where
  /-- SMT boolean: indeterminate (fuel exhausted / unmodelled builtin). -/
  inc : SExpr
  /-- SMT boolean: the (definite) UPLC error condition. -/
  err : SExpr
  /-- The resulting value (meaningful where `¬inc ∧ ¬err`). -/
  val : SymV
deriving Inhabited

/-- A throwaway value for error positions (never semantically observed). -/
def junk : SymV := .fo V.unit

/-- Fold a list of error conditions with `or`. -/
def sOrs (es : List SExpr) : SExpr := es.foldr sOr (.bool false)

/-! ## Smart folding projectors / testers on the `V` sort

These fold against statically-known constructors (`viVal (VInt e) ↦ e`,
`is-VInt (VInt …) ↦ true`) so concrete sub-terms don't bloat the formula. -/

namespace V

/-- Known unary `V` constructors (for tester folding). -/
def knownVCons : List String :=
  ["VInt","VBS","VBool","VStr","VData","VList","VDList","VPDList",
   "VPair","VPairD","VArr","VConstr","VG1","VG2","VMl"]

/-- The `V` constructor head of `e`, if statically apparent. -/
def vConName : SExpr → Option String
  | .atom "VUnit" => some "VUnit"
  | .app c _      => if knownVCons.contains c then some c else none
  | _             => none

/-- Smart discriminator `(is-Con e)`, folded when `e`'s head is statically known. -/
def sIsCon (con : String) (e : SExpr) : SExpr :=
  match vConName e with
  | some c => .bool (c == con)
  | none   => isCon con e

def sAsInt  : SExpr → SExpr | .app "VInt"   [e] => e | e => asInt e
def sAsBool : SExpr → SExpr | .app "VBool"  [e] => e | e => asBool e
def sAsBS   : SExpr → SExpr | .app "VBS"    [e] => e | e => asBS e
def sAsStr  : SExpr → SExpr | .app "VStr"   [e] => e | e => asStr e
def sAsData : SExpr → SExpr | .app "VData"  [e] => e | e => asData e
def sAsList : SExpr → SExpr | .app "VList"  [e] => e | e => asList e
def sAsDL   : SExpr → SExpr | .app "VDList" [e] => e | e => asDL e
def sAsDM   : SExpr → SExpr | .app "VPDList" [e] => e | e => asDM e
def sAsArr  : SExpr → SExpr | .app "VArr"   [e] => e | e => asArr e
def sFst    : SExpr → SExpr | .app "VPair"  [a, _] => a | e => fst e
def sSnd    : SExpr → SExpr | .app "VPair"  [_, b] => b | e => snd e
def sFstD   : SExpr → SExpr | .app "VPairD" [a, _] => a | e => fstD e
def sSndD   : SExpr → SExpr | .app "VPairD" [_, b] => b | e => sndD e
def sCTag   : SExpr → SExpr | .app "VConstr" [t, _] => t | e => cTag e
def sCArgs  : SExpr → SExpr | .app "VConstr" [_, a] => a | e => cArgs e

end V

namespace VL

/-- Smart `is-vnil`, folded against `vnil`/`vcons`. -/
def sIsNil : SExpr → SExpr
  | .atom "vnil"   => .bool true
  | .app "vcons" _ => .bool false
  | e              => isNil e
/-- Smart head, folded against `vcons`. -/
def sHd : SExpr → SExpr | .app "vcons" [h, _] => h | e => hd e
/-- Smart tail, folded against `vcons`. -/
def sTl : SExpr → SExpr | .app "vcons" [_, t] => t | e => tl e

end VL

namespace DL

/-- Smart `is-dnil`, folded against `dnil`/`dcons`. -/
def sIsNil : SExpr → SExpr
  | .atom "dnil"   => .bool true
  | .app "dcons" _ => .bool false
  | e              => isNil e
/-- Smart head (a `D`), folded against `dcons`. -/
def sHd : SExpr → SExpr | .app "dcons" [h, _] => h | e => hd e
/-- Smart tail (a `DL`), folded against `dcons`. -/
def sTl : SExpr → SExpr | .app "dcons" [_, t] => t | e => tl e

end DL

/-! ## Constant / Data → universal value `V`

Total encodings: every `Const`/`Data` maps to a `V`/`D`-sorted `SExpr`. Totality
on `Const` is essential — a `Constant` node must never get *stuck* (it always
succeeds in `bigEval`), or the Stage-2 simulation would break. -/

mutual
/-- Encode a Plutus `Data` value as a `D`-sorted `SExpr`. -/
def dataToSExpr : Data → SExpr
  | .Constr i ds => D.constr (.int i) (dataToDL ds)
  | .Map ps      => D.map (dataPairsToDM ps)
  | .List ds     => D.list (dataToDL ds)
  | .I i         => D.i (.int i)
  | .B bs        => D.b (Seq.ofBytes bs.data.toList)
/-- A list of `Data` as a `DL`-sorted `SExpr`. -/
def dataToDL : List Data → SExpr
  | []      => DL.nil
  | d :: ds => DL.cons (dataToSExpr d) (dataToDL ds)
/-- A `Data` map as a `DM`-sorted `SExpr`. -/
def dataPairsToDM : List (Data × Data) → SExpr
  | []           => DM.nil
  | (k, v) :: ps => DM.cons (dataToSExpr k) (dataToSExpr v) (dataPairsToDM ps)
end

mutual
/-- Encode a UPLC `Const` as a `V`-sorted `SExpr` (total, faithful to `Const`). -/
def constToSExpr : Const → SExpr
  | .Integer n            => V.int (.int n)
  | .ByteString bs        => V.bs (Seq.ofBytes bs.data.toList)
  | .String s             => V.str (.str s)
  | .Unit                 => V.unit
  | .Bool b               => V.bool (.bool b)
  | .ConstList cs         => V.list (constListToVL cs)
  | .ConstDataList ds     => V.dlist (dataToDL ds)
  | .ConstPairDataList ps => V.pdlist (dataPairsToDM ps)
  | .Pair (a, b)          => V.pair (constToSExpr a) (constToSExpr b)
  | .PairData (a, b)      => V.pairD (dataToSExpr a) (dataToSExpr b)
  | .Data d               => V.data (dataToSExpr d)
  | .ConstArray cs        => V.arr (constListToVL cs)
  | .Bls12_381_G1_element => V.g1 (.atom "bls_g1_default")
  | .Bls12_381_G2_element => V.g2 (.atom "bls_g2_default")
  | .Bls12_381_MlResult   => V.ml (.atom "bls_ml_default")
/-- A list of `Const` as a `VL`-sorted `SExpr`. -/
def constListToVL : List Const → SExpr
  | []      => VL.nil
  | c :: cs => VL.cons (constToSExpr c) (constListToVL cs)
end

/-! ## Reification to first-order

`reifyFO v = (err, e)` turns a symbolic value into a `V`-sorted `SExpr` together
with the condition `err` under which `v` is *not* first-order (a closure/thunk/
partial-builtin forced into a value position — a genuine UPLC type error). -/

mutual
/-- Reify a symbolic value to `(non-first-order-condition, V-expr)`. -/
def reifyFO : SymV → SExpr × SExpr
  | .fo e          => (.bool false, e)
  | .constr t fs   =>
      let (err, vs) := reifyFOList fs
      (err, V.constr (.int (Int.ofNat t)) (VL.ofList vs))
  | .choice c a b  =>
      let (ea, va) := reifyFO a
      let (eb, vb) := reifyFO b
      (sIte c ea eb, sIte c va vb)
  | .lam _ _       => (.bool true, V.unit)
  | .delay _ _     => (.bool true, V.unit)
  | .builtin _ _ _ => (.bool true, V.unit)
/-- Reify a list of values, OR-ing their non-first-order conditions. -/
def reifyFOList : List SymV → SExpr × List SExpr
  | []      => (.bool false, [])
  | v :: vs =>
      let (e1, x)  := reifyFO v
      let (e2, xs) := reifyFOList vs
      (sOr e1 e2, x :: xs)
end

/-- Reify to a single `V`-expr, ignoring the error condition (use only when the
caller threads the error separately). -/
def reifyV (v : SymV) : SExpr := (reifyFO v).2
/-- The non-first-order error condition of a value. -/
def reifyErr (v : SymV) : SExpr := (reifyFO v).1

/-! ## Symbolic merge

`mergeVal c x y` builds `if c then x else y`, keeping structure where the shapes
agree (so a later `Case` can still see a `constr`), and otherwise deferring to a
`choice`. `symMerge` lifts it to full computations (propagating *stuck*). -/

mutual
/-- Merge two values under symbolic condition `c`. -/
def mergeVal (c : SExpr) : SymV → SymV → SymV
  | .fo a, .fo b => .fo (sIte c a b)
  | .constr t1 fs1, .constr t2 fs2 =>
      if t1 == t2 && fs1.length == fs2.length then
        .constr t1 (mergeValList c fs1 fs2)
      else
        .choice c (.constr t1 fs1) (.constr t2 fs2)
  | a, b => .choice c a b
/-- Pointwise merge of equal-length field lists. -/
def mergeValList (c : SExpr) : List SymV → List SymV → List SymV
  | [],      []      => []
  | a :: as, b :: bs => mergeVal c a b :: mergeValList c as bs
  | _,       _       => []
end

/-- Merge two computation outcomes under symbolic condition `c`. -/
def symMerge (c : SExpr) (x y : SymR) : SymR :=
  ⟨sIte c x.inc y.inc, sIte c x.err y.err, mergeVal c x.val y.val⟩

/-! ## Environment lookup (1-based de Bruijn, mirroring `CekEnv.lookup`) -/

/-- Look up a de Bruijn index (`Var 1` = head). `none` = out of scope. -/
def symLookup : SymEnv → Nat → Option SymV
  | [],      _     => none
  | _ :: _,  0     => none
  | v :: _,  1     => some v
  | _ :: rest, n+1 => symLookup rest n

end Moist.Symbolic
