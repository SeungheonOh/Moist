import Moist.Symbolic.Compile
import Moist.Verified.BigStep

/-! # Stage 2 — a Lean denotational model of the SMT output (foundations)

The UPLC→SMT compiler (`Moist.Symbolic`) emits `SExpr` over the SMT-LIB datatypes
`D`/`DL`/`DM`/`V`/`VL`, `(Seq Int)` bytestrings, opaque sorts `G1`/`G2`/`MlResult`,
and the helper functions `moist_{fdiv,fmod,qdiv,qrem}`. To prove the compiler
**sound** — its SMT output behaves identically to the reference CEK — we give those
`SExpr`s a Lean denotation and prove the symbolic result agrees with `bigEval`
(which is already proven `≡ CEK` both ways, `Moist.Verified.BigStep.bigEval_iff_halt`).

## This file: the semantic universe

* `SemD`/`SemDL`/`SemDM` mirror the SMT `Data` datatypes; `SemV`/`SemVL` mirror the
  universal value sort `V`. They are the *term model* of z3's datatypes (datatypes
  are term-generated; under-specified selectors resolve to a fixed default — and the
  compiler only ever applies a selector under its matching `is-Con` guard, so the
  default is never observed where `¬err`).
* `(Seq Int)` is `List Int`; the opaque BLS sorts collapse to nullary `SemV.g1/g2/ml`.
  The compiler emits only BLS element constants; BLS operations are definite errors,
  matching the reference CEK.
* `Dyn` is the sort-tagged disjoint union of all these, the codomain of the single
  evaluator `evalDyn : Model → SExpr → Dyn` (next file section).

## Trust boundary (documented, to be minimized)

The only thing trusted is that **z3 is sound for the theories used** (algebraic
datatypes, linear integer arithmetic, the theory of sequences, and uninterpreted
functions) w.r.t. this term-model semantics. Everything from the `SExpr` denotation
down to the CEK is *proved* in Lean. No new Lean axioms beyond
`propext`/`Classical.choice`/`Quot.sound`.
-/

namespace Moist.Verified.Smt

open Moist.Symbolic
open Moist.Plutus (Data ByteString)

/-! ## Semantic `Data` (mirrors the SMT `D`/`DL`/`DM` datatypes) -/

mutual
/-- Semantic Plutus `Data` — the term model of the SMT `D` sort. Bytestrings are
`List Int` (`(Seq Int)`); `decodeD` maps this back to `Plutus.Data`. -/
inductive SemD where
  | constr : Int → SemDL → SemD
  | map    : SemDM → SemD
  | list   : SemDL → SemD
  | i      : Int → SemD
  | b      : List Int → SemD
/-- A list of `SemD` (the SMT `DL` sort). -/
inductive SemDL where
  | nil  : SemDL
  | cons : SemD → SemDL → SemDL
/-- A `SemD` association list (the SMT `DM` sort). -/
inductive SemDM where
  | nil  : SemDM
  | cons : SemD → SemD → SemDM → SemDM
end

/-! ## Semantic universal value (mirrors the SMT `V`/`VL` datatypes) -/

mutual
/-- Semantic first-order UPLC value — the term model of the SMT `V` sort. The three
`Const` list flavours (`ConstList`/`ConstDataList`/`ConstPairDataList`) and the two
pair flavours (`Pair`/`PairData`) are kept distinct, exactly as in `V`. The BLS
element sorts collapse to nullary constructors (only element constants are emitted). -/
inductive SemV where
  | int    : Int → SemV
  | bs     : List Int → SemV
  | bool   : Bool → SemV
  | unit   : SemV
  | str    : String → SemV
  | data   : SemD → SemV
  | list   : SemVL → SemV
  | dlist  : SemDL → SemV
  | pdlist : SemDM → SemV
  | pair   : SemV → SemV → SemV
  | pairD  : SemD → SemD → SemV
  | arr    : SemVL → SemV
  | constr : Int → SemVL → SemV
  | g1     : SemV
  | g2     : SemV
  | ml     : SemV
/-- A list of `SemV` (the SMT `VL` sort). -/
inductive SemVL where
  | nil  : SemVL
  | cons : SemV → SemVL → SemVL
end

deriving instance Repr, Inhabited, DecidableEq for SemD, SemDL, SemDM
deriving instance Repr, Inhabited, DecidableEq for SemV, SemVL

/-! ## The sort-tagged dynamic universe

`Dyn` is the codomain of the single SMT evaluator. Every SMT sort the compiler uses
maps to one constructor; projections recover the payload (a fixed default on a sort
mismatch — which never happens on guarded compiler output). -/

/-- A sort-tagged SMT value. -/
inductive Dyn where
  | i   : Int → Dyn
  | b   : Bool → Dyn
  | s   : String → Dyn
  | seq : List Int → Dyn
  | d   : SemD → Dyn
  | dl  : SemDL → Dyn
  | dm  : SemDM → Dyn
  | v   : SemV → Dyn
  | vl  : SemVL → Dyn
deriving Repr, Inhabited, DecidableEq

namespace Dyn

/-- Project an `Int` (default `0`). -/
def toInt : Dyn → Int        | .i n => n   | _ => 0
/-- Project a `Bool` (default `false`). -/
def toBool : Dyn → Bool      | .b x => x   | _ => false
/-- Project a `String` (default `""`). -/
def toStr : Dyn → String     | .s x => x   | _ => ""
/-- Project a `(Seq Int)` (default `[]`). -/
def toSeq : Dyn → List Int   | .seq x => x | _ => []
/-- Project a `SemD` (default junk). -/
def toD : Dyn → SemD         | .d x => x   | _ => default
/-- Project a `SemDL` (default `nil`). -/
def toDL : Dyn → SemDL       | .dl x => x  | _ => .nil
/-- Project a `SemDM` (default `nil`). -/
def toDM : Dyn → SemDM       | .dm x => x  | _ => .nil
/-- Project a `SemV` (default junk). -/
def toV : Dyn → SemV         | .v x => x   | _ => default
/-- Project a `SemVL` (default `nil`). -/
def toVL : Dyn → SemVL       | .vl x => x  | _ => .nil

end Dyn

/-! ## `SemV` / `SemD` projections (canonical datatype selectors)

These realise the SMT datatype selectors on the term model: the stored field when the
constructor matches, a fixed default otherwise. The compiler guards every selector
with its `is-Con` tester (folded into `err`), so the default is unobservable where
`¬err`. -/

namespace SemV
def getInt   : SemV → Int      | .int n => n   | _ => 0
def getSeq   : SemV → List Int | .bs s => s    | _ => []
def getBool  : SemV → Bool     | .bool b => b  | _ => false
def getStr   : SemV → String   | .str s => s   | _ => ""
def getData  : SemV → SemD     | .data d => d  | _ => default
def getList  : SemV → SemVL    | .list l => l  | _ => .nil
def getDList : SemV → SemDL    | .dlist l => l | _ => .nil
def getDM    : SemV → SemDM    | .pdlist m => m| _ => .nil
def getArr   : SemV → SemVL    | .arr l => l   | _ => .nil
def pFst     : SemV → SemV     | .pair a _ => a| _ => default
def pSnd     : SemV → SemV     | .pair _ b => b| _ => default
def pdFst    : SemV → SemD     | .pairD a _ => a | _ => default
def pdSnd    : SemV → SemD     | .pairD _ b => b | _ => default
def cTag     : SemV → Int      | .constr t _ => t | _ => 0
def cArgs    : SemV → SemVL    | .constr _ a => a | _ => .nil
/-- The `V`-constructor head name (matches `V.knownVCons` / the SMT testers). -/
def conName : SemV → String
  | .int _ => "VInt"   | .bs _ => "VBS"     | .bool _ => "VBool" | .unit => "VUnit"
  | .str _ => "VStr"   | .data _ => "VData" | .list _ => "VList" | .dlist _ => "VDList"
  | .pdlist _ => "VPDList" | .pair _ _ => "VPair" | .pairD _ _ => "VPairD"
  | .arr _ => "VArr"   | .constr _ _ => "VConstr"
  | .g1 => "VG1"       | .g2 => "VG2"       | .ml => "VMl"
end SemV

namespace SemD
def kTag  : SemD → Int      | .constr t _ => t | _ => 0
def kArgs : SemD → SemDL    | .constr _ a => a | _ => .nil
def kMap  : SemD → SemDM    | .map m => m      | _ => .nil
def kList : SemD → SemDL    | .list l => l     | _ => .nil
def kInt  : SemD → Int      | .i n => n        | _ => 0
def kBs   : SemD → List Int | .b s => s        | _ => []
/-- The `D`-constructor head name (matches the SMT `is-DConstr`/… testers). -/
def conName : SemD → String
  | .constr _ _ => "DConstr" | .map _ => "DMap" | .list _ => "DList"
  | .i _ => "DI"             | .b _ => "DB"
end SemD

def SemDL.isNil : SemDL → Bool | .nil => true | _ => false
def SemDL.hd : SemDL → SemD    | .cons h _ => h | _ => default
def SemDL.tl : SemDL → SemDL   | .cons _ t => t | _ => .nil
def SemVL.isNil : SemVL → Bool | .nil => true | _ => false
def SemVL.hd : SemVL → SemV    | .cons h _ => h | _ => default
def SemVL.tl : SemVL → SemVL   | .cons _ t => t | _ => .nil
def SemDM.isNil : SemDM → Bool | .nil => true | _ => false

/-! ## The model and the integer-division helpers

A `Model` is a valuation of the declared symbolic input atoms. The opaque `uf_*`
functions and BLS operations no longer appear in compiler output, so the model
carries nothing for them. The BLS element constants `bls_*_default` are nullary and
collapse to `SemV.g1/g2/ml`. -/

/-- A first-order structure for the SMT signature: just the input-atom valuation. -/
structure Model where
  /-- The value assigned to each declared symbolic constant (by name). -/
  atoms : String → Dyn

/-- SMT-LIB `div`/`mod` are Euclidean (Boute's), matching Lean's `Int.ediv`/`Int.emod`
(remainder always `≥ 0`). The four `moist_*` helpers below mirror the `define-fun`s in
`datatypePreamble` verbatim, so the denotation matches the SMT text by construction. -/
def smtEdiv (a b : Int) : Int := a.ediv b
def smtEmod (a b : Int) : Int := a.emod b

/-- `moist_fdiv` — Haskell `div` (floor), via the preamble's case split. -/
def smtFdiv (a b : Int) : Int :=
  if b = 0 then 0 else if b < 0 then smtEdiv (-a) (-b) else smtEdiv a b
/-- `moist_fmod` — Haskell `mod`. -/
def smtFmod (a b : Int) : Int :=
  if b = 0 then 0 else if b < 0 then -(smtEmod (-a) b) else smtEmod a b
/-- `moist_qdiv` — truncated (Haskell `quot`). -/
def smtQdiv (a b : Int) : Int :=
  if b = 0 then 0 else
    let q := smtEdiv (Int.ofNat a.natAbs) (Int.ofNat b.natAbs)
    if (decide (a ≥ 0)) = (decide (b ≥ 0)) then q else -q
/-- `moist_qrem` — truncated remainder (Haskell `rem`). -/
def smtQrem (a b : Int) : Int :=
  if b = 0 then 0 else a - b * smtQdiv a b

/-- `(seq.nth s i)` — the SMT semantics is under-specified out of range; we pick `0`
there (the compiler guards every `seq.nth` with the in-range `err` condition). -/
def seqNth (s : List Int) (i : Int) : Int :=
  if 0 ≤ i ∧ i < (s.length : Int) then s.getD i.toNat 0 else 0

/-! ## The SMT evaluator `evalDyn`

A single total interpreter over the fragment of `SExpr` the compiler emits: datatype
constructors/selectors/testers for `V`/`D`/`DL`/`DM`/`VL`, `(Seq Int)` ops, integer/
boolean operators, the `moist_*` helpers, polymorphic `=` (structural on `Dyn`), and
`ite`. Heads outside this fragment (e.g. the now-unused `uf_*`, or `forall` in a
side-condition) fall through to a fixed default — they never occur in a compiled
`inc`/`err`/`val`. -/

/-- Constants and nullary constructors that print as bare atoms. -/
def evalAtom (M : Model) (a : String) : Dyn :=
  match a with
  | "VUnit" => .v .unit
  | "vnil"  => .vl .nil
  | "dnil"  => .dl .nil
  | "mnil"  => .dm .nil
  | "true"  => .b true
  | "false" => .b false
  | "bls_g1_default" | "bls_g2_default" | "bls_ml_default" => .i 0  -- junk; only VG1/VG2/VMl wrap it
  | "(as seq.empty (Seq Int))" => .seq []
  | _ => M.atoms a

/-- Application/operator semantics on already-evaluated arguments. -/
def evalApp (head : String) (args : List Dyn) : Dyn :=
  match head, args with
  -- V constructors
  | "VInt",   [d] => .v (.int d.toInt)
  | "VBS",    [d] => .v (.bs d.toSeq)
  | "VBool",  [d] => .v (.bool d.toBool)
  | "VStr",   [d] => .v (.str d.toStr)
  | "VData",  [d] => .v (.data d.toD)
  | "VList",  [d] => .v (.list d.toVL)
  | "VDList", [d] => .v (.dlist d.toDL)
  | "VPDList",[d] => .v (.pdlist d.toDM)
  | "VPair",  [a, b] => .v (.pair a.toV b.toV)
  | "VPairD", [a, b] => .v (.pairD a.toD b.toD)
  | "VArr",   [d] => .v (.arr d.toVL)
  | "VConstr",[t, a] => .v (.constr t.toInt a.toVL)
  | "VG1", [_] => .v .g1 | "VG2", [_] => .v .g2 | "VMl", [_] => .v .ml
  -- V selectors
  | "viVal",  [d] => .i   (d.toV.getInt)
  | "vbsVal", [d] => .seq (d.toV.getSeq)
  | "vbVal",  [d] => .b   (d.toV.getBool)
  | "vsVal",  [d] => .s   (d.toV.getStr)
  | "vdVal",  [d] => .d   (d.toV.getData)
  | "vlElems",[d] => .vl  (d.toV.getList)
  | "vdlElems",[d] => .dl (d.toV.getDList)
  | "vpdlElems",[d] => .dm (d.toV.getDM)
  | "varrElems",[d] => .vl (d.toV.getArr)
  | "vpFst",  [d] => .v (d.toV.pFst)
  | "vpSnd",  [d] => .v (d.toV.pSnd)
  | "vpdFst", [d] => .d (d.toV.pdFst)
  | "vpdSnd", [d] => .d (d.toV.pdSnd)
  | "vcTag",  [d] => .i (d.toV.cTag)
  | "vcArgs", [d] => .vl (d.toV.cArgs)
  | "vg1Val", [_] | "vg2Val", [_] | "vmlVal", [_] => .i 0
  -- D constructors
  | "DConstr",[t, a] => .d (.constr t.toInt a.toDL)
  | "DMap",   [d] => .d (.map d.toDM)
  | "DList",  [d] => .d (.list d.toDL)
  | "DI",     [d] => .d (.i d.toInt)
  | "DB",     [d] => .d (.b d.toSeq)
  -- D selectors
  | "dcTag",    [d] => .i (d.toD.kTag)
  | "dcArgs",   [d] => .dl (d.toD.kArgs)
  | "dmEntries",[d] => .dm (d.toD.kMap)
  | "dlElems",  [d] => .dl (d.toD.kList)
  | "diVal",    [d] => .i (d.toD.kInt)
  | "dbVal",    [d] => .seq (d.toD.kBs)
  -- list constructors / selectors
  | "dcons", [h, t] => .dl (.cons h.toD t.toDL)
  | "dhd",   [d] => .d (d.toDL.hd)
  | "dtl",   [d] => .dl (d.toDL.tl)
  | "mcons", [k, v, t] => .dm (.cons k.toD v.toD t.toDM)
  | "vcons", [h, t] => .vl (.cons h.toV t.toVL)
  | "vhd",   [d] => .v (d.toVL.hd)
  | "vtl",   [d] => .vl (d.toVL.tl)
  -- testers
  | "is-VInt",   [d] => .b (d.toV.conName == "VInt")
  | "is-VBS",    [d] => .b (d.toV.conName == "VBS")
  | "is-VBool",  [d] => .b (d.toV.conName == "VBool")
  | "is-VUnit",  [d] => .b (d.toV.conName == "VUnit")
  | "is-VStr",   [d] => .b (d.toV.conName == "VStr")
  | "is-VData",  [d] => .b (d.toV.conName == "VData")
  | "is-VList",  [d] => .b (d.toV.conName == "VList")
  | "is-VDList", [d] => .b (d.toV.conName == "VDList")
  | "is-VPDList",[d] => .b (d.toV.conName == "VPDList")
  | "is-VPair",  [d] => .b (d.toV.conName == "VPair")
  | "is-VPairD", [d] => .b (d.toV.conName == "VPairD")
  | "is-VArr",   [d] => .b (d.toV.conName == "VArr")
  | "is-VConstr",[d] => .b (d.toV.conName == "VConstr")
  | "is-VG1",    [d] => .b (d.toV.conName == "VG1")
  | "is-VG2",    [d] => .b (d.toV.conName == "VG2")
  | "is-VMl",    [d] => .b (d.toV.conName == "VMl")
  | "is-DConstr",[d] => .b (d.toD.conName == "DConstr")
  | "is-DMap",   [d] => .b (d.toD.conName == "DMap")
  | "is-DList",  [d] => .b (d.toD.conName == "DList")
  | "is-DI",     [d] => .b (d.toD.conName == "DI")
  | "is-DB",     [d] => .b (d.toD.conName == "DB")
  | "is-dnil",   [d] => .b (d.toDL.isNil)
  | "is-vnil",   [d] => .b (d.toVL.isNil)
  | "is-mnil",   [d] => .b (d.toDM.isNil)
  -- integer / boolean operators
  | "+", [a, b] => .i (a.toInt + b.toInt)
  | "-", [a, b] => .i (a.toInt - b.toInt)
  | "-", [a]    => .i (-a.toInt)
  | "*", [a, b] => .i (a.toInt * b.toInt)
  | "<", [a, b] => .b (decide (a.toInt < b.toInt))
  | "<=",[a, b] => .b (decide (a.toInt ≤ b.toInt))
  | ">=",[a, b] => .b (decide (a.toInt ≥ b.toInt))
  | "moist_fdiv", [a, b] => .i (smtFdiv a.toInt b.toInt)
  | "moist_fmod", [a, b] => .i (smtFmod a.toInt b.toInt)
  | "moist_qdiv", [a, b] => .i (smtQdiv a.toInt b.toInt)
  | "moist_qrem", [a, b] => .i (smtQrem a.toInt b.toInt)
  -- sequence (bytestring) operators
  | "seq.unit", [a] => .seq [a.toInt]
  | "seq.len",  [a] => .i (Int.ofNat a.toSeq.length)
  | "seq.nth",  [s, i] => .i (seqNth s.toSeq i.toInt)
  | "seq.++",   [a, b] => .seq (a.toSeq ++ b.toSeq)
  | "str.++",   [a, b] => .s (a.toStr ++ b.toStr)
  -- logical / equality / ite
  | "not", [a] => .b (!a.toBool)
  | "and", [a, b] => .b (a.toBool && b.toBool)
  | "or",  [a, b] => .b (a.toBool || b.toBool)
  | "=>",  [a, b] => .b (!a.toBool || b.toBool)
  | "=",   [a, b] => .b (decide (a = b))
  | "ite", [c, t, e] => if c.toBool then t else e
  | _, _ => .i 0

mutual
/-- Denote an `SExpr` to a sort-tagged `Dyn` under model `M`. Total. -/
def evalDyn (M : Model) : SExpr → Dyn
  | .int n  => .i n
  | .bool b => .b b
  | .str s  => .s s
  | .atom a => evalAtom M a
  | .app head args => evalApp head (evalDynList M args)
/-- Denote a list of `SExpr`s pointwise. -/
def evalDynList (M : Model) : List SExpr → List Dyn
  | []      => []
  | e :: es => evalDyn M e :: evalDynList M es
end

end Moist.Verified.Smt
