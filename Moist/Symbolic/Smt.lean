import Moist.Plutus.Types

/-! # A small, self-contained SMT-LIB v2 AST + emitter

This module defines the target language of the UPLC→SMT *denotational* compiler:
a minimal S-expression AST (`SExpr`), smart constructors, the fixed datatype
preamble for the universal UPLC value sort `V` (and the Plutus `Data` sort `D`),
and a pretty-printer (`SExpr.render` / `SmtScript.toSMTLib`) producing real
SMT-LIB v2 text that runs on z3.

Design choices (validated against z3 4.13):

* **Universal value sort `V`** — a datatype covering every *first-order* UPLC
  value: `VInt`/`VBS`/`VBool`/`VUnit`/`VData`/`VList`/`VPair`/`VConstr`.
  Higher-order values (closures, thunks, partial builtins) are NOT in `V`; the
  compiler keeps them structural at Lean compile-time (see `Value.lean`).
* **Builtin lists are datatypes** (`VL` = `vnil`/`vcons`; `Data` lists `DL`,
  `Data` maps `DM`) rather than `Seq V`, so head/tail/null/chooseList are native
  datatype selectors/testers and recursion is well-supported by z3.
* **ByteStrings are `(Seq Int)`** (bytes 0..255), so length/index/append/slice/
  equality are real SMT. CEK-supported operations without a symbolic denotation
  are incomplete; crypto operations absent from the CEK are definite errors.
* Legacy uninterpreted declarations for crypto/BLS remain in the preamble, but
  the compiler does not call them: the reference CEK has no denotation for those
  builtins and therefore reports a definite error at saturation.

This AST is plain Lean (no `Lean.Meta`) precisely so it can be given a Lean-level
denotation in the Stage-2 soundness proof.
-/

namespace Moist.Symbolic

/-! ## The S-expression AST -/

/-- A minimal SMT-LIB term. `atom` is emitted verbatim (identifiers, nullary
constructors like `VUnit`/`vnil`, and the occasional sort-annotated literal);
`app head args` emits `(head args…)`. -/
inductive SExpr where
  /-- Integer literal (negatives rendered as `(- n)`). -/
  | int  : Int → SExpr
  /-- Boolean literal `true`/`false`. -/
  | bool : Bool → SExpr
  /-- String literal (rendered as an SMT-LIB string `"…"`). -/
  | str  : String → SExpr
  /-- A verbatim symbol: a variable, a nullary constructor, or a raw token. -/
  | atom : String → SExpr
  /-- An application `(head args…)`. -/
  | app  : String → List SExpr → SExpr
deriving Repr, Inhabited

namespace SExpr

/-- Render an `SExpr` to SMT-LIB v2 concrete syntax. -/
partial def render : SExpr → String
  | .int n     => if n ≥ 0 then toString n else s!"(- {toString (-n)})"
  | .bool b    => if b then "true" else "false"
  | .str s     => "\"" ++ s.replace "\"" "\"\"" ++ "\""
  | .atom s    => s
  | .app f []  => f
  | .app f as  => "(" ++ f ++ " " ++ String.intercalate " " (as.map render) ++ ")"

instance : ToString SExpr := ⟨render⟩

/-! ## Boolean / equality smart constructors (constant-folding) -/

/-- Smart `not`, folding boolean literals. -/
def sNot : SExpr → SExpr
  | .bool b => .bool (!b)
  | e       => .app "not" [e]

/-- Smart binary `and`, folding `true`/`false`. -/
def sAnd : SExpr → SExpr → SExpr
  | .bool true,  b => b
  | .bool false, _ => .bool false
  | a, .bool true  => a
  | _, .bool false => .bool false
  | a, b           => .app "and" [a, b]

/-- Smart binary `or`, folding `true`/`false`. -/
def sOr : SExpr → SExpr → SExpr
  | .bool true,  _ => .bool true
  | .bool false, b => b
  | _, .bool true  => .bool true
  | a, .bool false => a
  | a, b           => .app "or" [a, b]

/-- Smart `=>`. -/
def sImplies : SExpr → SExpr → SExpr
  | .bool false, _ => .bool true
  | .bool true,  b => b
  | a, b           => .app "=>" [a, b]

/- Structural equality of S-expressions, used for the `ite c a a ⇒ a` peephole.
Mutual-structural (not `partial`) so it carries equation lemmas for the Stage-2
soundness proof (`beq a b = true → a = b`). -/
mutual
/-- Structural equality of S-expressions (used for the `ite c a a ⇒ a` peephole). -/
def beq : SExpr → SExpr → Bool
  | .int a,    .int b    => a == b
  | .bool a,   .bool b   => a == b
  | .str a,    .str b    => a == b
  | .atom a,   .atom b   => a == b
  | .app f as, .app g bs => f == g && beqList as bs
  | _, _ => false
/-- Pointwise structural equality of `SExpr` lists (same length + elementwise `beq`). -/
def beqList : List SExpr → List SExpr → Bool
  | [],      []      => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _,       _       => false
end

/-- Smart `ite`, folding a literal condition and collapsing `ite c a a`. -/
def sIte (c t e : SExpr) : SExpr :=
  match c with
  | .bool true  => t
  | .bool false => e
  | _           => if beq t e then t else .app "ite" [c, t, e]

/-- Smart equality (folds two equal int/bool literals). -/
def sEq (a b : SExpr) : SExpr :=
  match a, b with
  | .int x,  .int y  => .bool (x == y)
  | .bool x, .bool y => .bool (x == y)
  | _, _             => .app "=" [a, b]

end SExpr

open SExpr (sNot sAnd sOr sImplies sIte sEq)

/-! ## Sort names -/

/-- SMT-LIB sort tokens used at declaration sites. -/
inductive SSort where
  | int | bool | string | seqInt
  | data | dataList | dataMap
  | val  | valList
  | g1 | g2 | mlResult
deriving Repr, BEq, DecidableEq, Inhabited

/-- The concrete SMT-LIB sort token. -/
def SSort.render : SSort → String
  | .int => "Int" | .bool => "Bool" | .string => "String" | .seqInt => "(Seq Int)"
  | .data => "D" | .dataList => "DL" | .dataMap => "DM"
  | .val => "V" | .valList => "VL"
  | .g1 => "G1" | .g2 => "G2" | .mlResult => "MlResult"

/-! ## `V` / `Data` constructor & selector builders

These name the datatype declared in `preamble`. Keeping them as named helpers
(rather than open-coding strings everywhere) makes the compiler readable and the
Stage-2 denotation a simple symbol table. -/

namespace V

/-- `(VInt e)` — wrap an `Int`-sorted expr into a value. -/
def int (e : SExpr) : SExpr := .app "VInt" [e]
/-- `(viVal e)` — project the `Int` out of a `VInt`. -/
def asInt (e : SExpr) : SExpr := .app "viVal" [e]
/-- `(VBool e)`. -/
def bool (e : SExpr) : SExpr := .app "VBool" [e]
/-- `(vbVal e)` — project the `Bool`. -/
def asBool (e : SExpr) : SExpr := .app "vbVal" [e]
/-- `(VBS e)` — wrap a `(Seq Int)` bytestring. -/
def bs (e : SExpr) : SExpr := .app "VBS" [e]
/-- `(vbsVal e)` — project the `(Seq Int)`. -/
def asBS (e : SExpr) : SExpr := .app "vbsVal" [e]
/-- `(VStr e)` — wrap an SMT `String`. -/
def str (e : SExpr) : SExpr := .app "VStr" [e]
/-- `(vsVal e)` — project the `String`. -/
def asStr (e : SExpr) : SExpr := .app "vsVal" [e]
/-- `VUnit`. -/
def unit : SExpr := .atom "VUnit"
/-- `(VG1 e)` / `(VG2 e)` / `(VMl e)` — wrap opaque BLS elements. -/
def g1 (e : SExpr) : SExpr := .app "VG1" [e]
def g2 (e : SExpr) : SExpr := .app "VG2" [e]
def ml (e : SExpr) : SExpr := .app "VMl" [e]
def asG1 (e : SExpr) : SExpr := .app "vg1Val" [e]
def asG2 (e : SExpr) : SExpr := .app "vg2Val" [e]
def asMl (e : SExpr) : SExpr := .app "vmlVal" [e]
/-- `(VData e)`. -/
def data (e : SExpr) : SExpr := .app "VData" [e]
/-- `(vdVal e)` — project the `D`. -/
def asData (e : SExpr) : SExpr := .app "vdVal" [e]
-- The three list flavours of `Const` are kept distinct (so the concretization
-- `V → Const` is a function and the flavour-sensitive builtins type-check exactly
-- like the CEK): `VList` = `ConstList` (`List Const`), `VDList` = `ConstDataList`
-- (`List Data`), `VPDList` = `ConstPairDataList` (`List (Data × Data)`).
/-- `(VList e)` — general list `ConstList`; `e : VL`. -/
def list (e : SExpr) : SExpr := .app "VList" [e]
/-- `(vlElems e)` — project the `VL`. -/
def asList (e : SExpr) : SExpr := .app "vlElems" [e]
/-- `(VDList e)` — `ConstDataList`; `e : DL`. -/
def dlist (e : SExpr) : SExpr := .app "VDList" [e]
/-- `(vdlElems e)` — project the `DL`. -/
def asDL (e : SExpr) : SExpr := .app "vdlElems" [e]
/-- `(VPDList e)` — `ConstPairDataList`; `e : DM`. -/
def pdlist (e : SExpr) : SExpr := .app "VPDList" [e]
/-- `(vpdlElems e)` — project the `DM`. -/
def asDM (e : SExpr) : SExpr := .app "vpdlElems" [e]
/-- `(VArr e)` — `ConstArray`; `e : VL`. -/
def arr (e : SExpr) : SExpr := .app "VArr" [e]
/-- `(varrElems e)` — project the `VL`. -/
def asArr (e : SExpr) : SExpr := .app "varrElems" [e]
/-- `(VPair a b)` — general pair `Pair` (`Const × Const`); `a b : V`. -/
def pair (a b : SExpr) : SExpr := .app "VPair" [a, b]
/-- `(vpFst e)`. -/
def fst (e : SExpr) : SExpr := .app "vpFst" [e]
/-- `(vpSnd e)`. -/
def snd (e : SExpr) : SExpr := .app "vpSnd" [e]
/-- `(VPairD a b)` — `PairData` (`Data × Data`); `a b : D`. -/
def pairD (a b : SExpr) : SExpr := .app "VPairD" [a, b]
/-- `(vpdFst e)`. -/
def fstD (e : SExpr) : SExpr := .app "vpdFst" [e]
/-- `(vpdSnd e)`. -/
def sndD (e : SExpr) : SExpr := .app "vpdSnd" [e]
/-- `(VConstr tag fields)` — SOP constructor (`CekValue.VConstr`); `fields : VL`. -/
def constr (tag fields : SExpr) : SExpr := .app "VConstr" [tag, fields]
/-- `(vcTag e)`. -/
def cTag (e : SExpr) : SExpr := .app "vcTag" [e]
/-- `(vcArgs e)`. -/
def cArgs (e : SExpr) : SExpr := .app "vcArgs" [e]

/-- A datatype discriminator `(is-Cstr e)`. -/
def isCon (con : String) (e : SExpr) : SExpr := .app s!"is-{con}" [e]

end V

namespace VL

/-- `vnil` — empty value list. -/
def nil : SExpr := .atom "vnil"
/-- `(vcons h t)`. -/
def cons (h t : SExpr) : SExpr := .app "vcons" [h, t]
/-- `(vhd e)`. -/
def hd (e : SExpr) : SExpr := .app "vhd" [e]
/-- `(vtl e)`. -/
def tl (e : SExpr) : SExpr := .app "vtl" [e]
/-- `(is-vnil e)`. -/
def isNil (e : SExpr) : SExpr := .app "is-vnil" [e]
/-- Build a `VL` from a Lean list of `V`-exprs. -/
def ofList : List SExpr → SExpr
  | []      => nil
  | x :: xs => cons x (ofList xs)

end VL

namespace D

/-- `(DConstr tag args)` — `args : DL` (a list of `D`). -/
def constr (tag args : SExpr) : SExpr := .app "DConstr" [tag, args]
/-- `(DMap e)` — `e : DM` (a list of `(D × D)`). -/
def map (e : SExpr) : SExpr := .app "DMap" [e]
/-- `(DList e)` — `e : DL`. -/
def list (e : SExpr) : SExpr := .app "DList" [e]
/-- `(DI e)`. -/
def i (e : SExpr) : SExpr := .app "DI" [e]
/-- `(DB e)` where `e : (Seq Int)`. -/
def b (e : SExpr) : SExpr := .app "DB" [e]
def dcTag (e : SExpr) : SExpr := .app "dcTag" [e]
def dcArgs (e : SExpr) : SExpr := .app "dcArgs" [e]
def dmEntries (e : SExpr) : SExpr := .app "dmEntries" [e]
def dlElems (e : SExpr) : SExpr := .app "dlElems" [e]
def diVal (e : SExpr) : SExpr := .app "diVal" [e]
def dbVal (e : SExpr) : SExpr := .app "dbVal" [e]

end D

/-! `DL` (a `dcons`-list of `Data`) builders. -/
namespace DL
def nil : SExpr := .atom "dnil"
def cons (h t : SExpr) : SExpr := .app "dcons" [h, t]
def hd (e : SExpr) : SExpr := .app "dhd" [e]
def tl (e : SExpr) : SExpr := .app "dtl" [e]
def isNil (e : SExpr) : SExpr := .app "is-dnil" [e]
def ofList : List SExpr → SExpr
  | []      => nil
  | x :: xs => cons x (ofList xs)
end DL

/-! `DM` (a `mcons`-list of `(Data × Data)`) builders. -/
namespace DM
def nil : SExpr := .atom "mnil"
def cons (k v t : SExpr) : SExpr := .app "mcons" [k, v, t]
def key (e : SExpr) : SExpr := .app "mkey" [e]
def val (e : SExpr) : SExpr := .app "mval" [e]
def tl (e : SExpr) : SExpr := .app "mtl" [e]
def isNil (e : SExpr) : SExpr := .app "is-mnil" [e]
def ofList : List (SExpr × SExpr) → SExpr
  | []           => nil
  | (k, v) :: xs => cons k v (ofList xs)
end DM

/-! ## `(Seq Int)` bytestring builders -/

namespace Seq

/-- The empty `(Seq Int)` — needs the `as` sort annotation in SMT-LIB. -/
def empty : SExpr := .atom "(as seq.empty (Seq Int))"
/-- `(seq.unit e)`. -/
def unit (e : SExpr) : SExpr := .app "seq.unit" [e]
/-- `(seq.len e)`. -/
def len (e : SExpr) : SExpr := .app "seq.len" [e]
/-- `(seq.nth s i)`. -/
def nth (s i : SExpr) : SExpr := .app "seq.nth" [s, i]
/-- `(seq.++ a b)`. -/
def append (a b : SExpr) : SExpr := .app "seq.++" [a, b]
/-- `(seq.extract s off len)`. -/
def extract (s off len : SExpr) : SExpr := .app "seq.extract" [s, off, len]
/-- Build a literal `(Seq Int)` from concrete bytes. -/
def ofBytes : List UInt8 → SExpr
  | []      => empty
  | [x]     => unit (.int (Int.ofNat x.toNat))
  | x :: xs => append (unit (.int (Int.ofNat x.toNat))) (ofBytes xs)

end Seq

/-! ## Integer / boolean operator builders (over the SMT `Int`/`Bool` sorts) -/

namespace Op

def add (a b : SExpr) : SExpr := .app "+" [a, b]
def sub (a b : SExpr) : SExpr := .app "-" [a, b]
def mul (a b : SExpr) : SExpr := .app "*" [a, b]
def lt  (a b : SExpr) : SExpr := .app "<" [a, b]
def le  (a b : SExpr) : SExpr := .app "<=" [a, b]
def ge  (a b : SExpr) : SExpr := .app ">=" [a, b]
def neg (a : SExpr) : SExpr := .app "-" [a]

end Op

/-! ## Legacy opaque (uninterpreted) builtin declarations

These declarations are retained for compatibility with previously emitted scripts.
The compiler no longer calls them: the reference CEK errors on those builtins, so
the symbolic compiler reports the same definite error. -/

/-- A single uninterpreted-function declaration: name, argument sorts, result sort. -/
structure UFDecl where
  name : String
  args : List SSort
  ret  : SSort
deriving Repr

/-- The retained roster of opaque builtins. Argument sorts are the *projected*
first-order sorts (e.g. a bytestring argument is `(Seq Int)`), not `V`. -/
def opaqueUFs : List UFDecl :=
  let bs := SSort.seqInt
  [ ⟨"uf_sha2_256",   [bs], bs⟩
  , ⟨"uf_sha3_256",   [bs], bs⟩
  , ⟨"uf_blake2b_256",[bs], bs⟩
  , ⟨"uf_blake2b_224",[bs], bs⟩
  , ⟨"uf_keccak_256", [bs], bs⟩
  , ⟨"uf_ripemd_160", [bs], bs⟩
  -- signature verification: (pubkey, message, sig) → Bool
  , ⟨"uf_verifyEd25519",  [bs, bs, bs], .bool⟩
  , ⟨"uf_verifyEcdsa",    [bs, bs, bs], .bool⟩
  , ⟨"uf_verifySchnorr",  [bs, bs, bs], .bool⟩
  -- serialisation: Data → bytestring
  , ⟨"uf_serializeData", [.data], bs⟩
  -- Retained BLS12-381 declarations (not emitted by the compiler)
  , ⟨"uf_bls_g1_add",         [.g1, .g1], .g1⟩
  , ⟨"uf_bls_g1_neg",         [.g1], .g1⟩
  , ⟨"uf_bls_g1_scalarMul",   [.int, .g1], .g1⟩
  , ⟨"uf_bls_g1_equal",       [.g1, .g1], .bool⟩
  , ⟨"uf_bls_g1_hashToGroup", [bs, bs], .g1⟩
  , ⟨"uf_bls_g1_compress",    [.g1], bs⟩
  , ⟨"uf_bls_g1_uncompress",  [bs], .g1⟩
  , ⟨"uf_bls_g2_add",         [.g2, .g2], .g2⟩
  , ⟨"uf_bls_g2_neg",         [.g2], .g2⟩
  , ⟨"uf_bls_g2_scalarMul",   [.int, .g2], .g2⟩
  , ⟨"uf_bls_g2_equal",       [.g2, .g2], .bool⟩
  , ⟨"uf_bls_g2_hashToGroup", [bs, bs], .g2⟩
  , ⟨"uf_bls_g2_compress",    [.g2], bs⟩
  , ⟨"uf_bls_g2_uncompress",  [bs], .g2⟩
  , ⟨"uf_bls_millerLoop",     [.g1, .g2], .mlResult⟩
  , ⟨"uf_bls_mulMlResult",    [.mlResult, .mlResult], .mlResult⟩
  , ⟨"uf_bls_finalVerify",    [.mlResult, .mlResult], .bool⟩
  ]

/-- Render a `declare-fun`. -/
def UFDecl.render (d : UFDecl) : String :=
  let argStr := String.intercalate " " (d.args.map SSort.render)
  s!"(declare-fun {d.name} ({argStr}) {d.ret.render})"

/-! ## The datatype preamble

A fixed block declaring `D`/`DL`/`DM` (Plutus `Data`) and `V`/`VL` (universal
value), the opaque BLS sorts, plus all opaque uninterpreted functions. Validated
to load on z3 4.13. -/

def datatypePreamble : String :=
  "; ===== Moist UPLC→SMT universal value & Data datatypes =====\n" ++
  "(declare-sort G1 0)\n(declare-sort G2 0)\n(declare-sort MlResult 0)\n" ++
  "; D (Plutus Data) and V (universal value) are mutually recursive.\n" ++
  "; DL = list of D, DM = list of (D,D), VL = list of V. The three Const list\n" ++
  "; flavours (ConstList/ConstDataList/ConstPairDataList) and pairs (Pair/PairData)\n" ++
  "; are kept distinct so V faithfully mirrors Const (for a functional concretization).\n" ++
  "(declare-datatypes ((D 0) (DL 0) (DM 0) (V 0) (VL 0))\n" ++
  " (\n" ++
  "  ((DConstr (dcTag Int) (dcArgs DL)) (DMap (dmEntries DM)) (DList (dlElems DL)) (DI (diVal Int)) (DB (dbVal (Seq Int))))\n" ++
  "  ((dnil) (dcons (dhd D) (dtl DL)))\n" ++
  "  ((mnil) (mcons (mkey D) (mval D) (mtl DM)))\n" ++
  "  ((VInt (viVal Int)) (VBS (vbsVal (Seq Int))) (VBool (vbVal Bool)) (VUnit) (VStr (vsVal String))\n" ++
  "   (VData (vdVal D)) (VList (vlElems VL)) (VDList (vdlElems DL)) (VPDList (vpdlElems DM))\n" ++
  "   (VPair (vpFst V) (vpSnd V)) (VPairD (vpdFst D) (vpdSnd D)) (VArr (varrElems VL))\n" ++
  "   (VConstr (vcTag Int) (vcArgs VL))\n" ++
  "   (VG1 (vg1Val G1)) (VG2 (vg2Val G2)) (VMl (vmlVal MlResult)))\n" ++
  "  ((vnil) (vcons (vhd V) (vtl VL)))\n" ++
  " ))\n" ++
  "; recursive well-formedness for values supplied directly by an SMT model\n" ++
  "(define-fun moist_wf_seq ((s (Seq Int))) Bool\n" ++
  " (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len s)))\n" ++
  "   (and (<= 0 (seq.nth s i)) (<= (seq.nth s i) 255)))))\n" ++
  "(define-funs-rec\n" ++
  " ((moist_wf_d ((x D)) Bool) (moist_wf_dl ((xs DL)) Bool) (moist_wf_dm ((xs DM)) Bool))\n" ++
  " ((ite (is-DConstr x) (moist_wf_dl (dcArgs x))\n" ++
  "    (ite (is-DMap x) (moist_wf_dm (dmEntries x))\n" ++
  "     (ite (is-DList x) (moist_wf_dl (dlElems x))\n" ++
  "      (ite (is-DB x) (moist_wf_seq (dbVal x)) true))))\n" ++
  "  (ite (is-dnil xs) true (and (moist_wf_d (dhd xs)) (moist_wf_dl (dtl xs))))\n" ++
  "  (ite (is-mnil xs) true (and (moist_wf_d (mkey xs))\n" ++
  "    (moist_wf_d (mval xs)) (moist_wf_dm (mtl xs))))))\n" ++
  "(define-funs-rec\n" ++
  " ((moist_const_v ((x V)) Bool) (moist_const_vl ((xs VL)) Bool))\n" ++
  " ((ite (is-VConstr x) false\n" ++
  "    (ite (is-VBS x) (moist_wf_seq (vbsVal x))\n" ++
  "     (ite (is-VData x) (moist_wf_d (vdVal x))\n" ++
  "      (ite (is-VList x) (moist_const_vl (vlElems x))\n" ++
  "       (ite (is-VArr x) (moist_const_vl (varrElems x))\n" ++
  "        (ite (is-VPair x) (and (moist_const_v (vpFst x)) (moist_const_v (vpSnd x)))\n" ++
  "         (ite (is-VDList x) (moist_wf_dl (vdlElems x))\n" ++
  "          (ite (is-VPDList x) (moist_wf_dm (vpdlElems x))\n" ++
  "           (ite (is-VPairD x) (and (moist_wf_d (vpdFst x))\n" ++
  "             (moist_wf_d (vpdSnd x))) true)))))))))\n" ++
  "  (ite (is-vnil xs) true (and (moist_const_v (vhd xs))\n" ++
  "    (moist_const_vl (vtl xs))))))\n" ++
  "; degenerate defaults for the (effectively unused) BLS element *constants*\n" ++
  "(declare-const bls_g1_default G1)\n(declare-const bls_g2_default G2)\n(declare-const bls_ml_default MlResult)\n" ++
  "; integer division helpers: floor (Haskell div/mod) and truncated (quot/rem)\n" ++
  "(define-fun moist_fdiv ((a Int)(b Int)) Int (ite (= b 0) 0 (ite (< b 0) (div (- a) (- b)) (div a b))))\n" ++
  "(define-fun moist_fmod ((a Int)(b Int)) Int (ite (= b 0) 0 (ite (< b 0) (- (mod (- a) b)) (mod a b))))\n" ++
  "(define-fun moist_qdiv ((a Int)(b Int)) Int (ite (= b 0) 0 (ite (= (>= a 0) (>= b 0)) (div (abs a) (abs b)) (- (div (abs a) (abs b))))))\n" ++
  "(define-fun moist_qrem ((a Int)(b Int)) Int (ite (= b 0) 0 (- a (* b (moist_qdiv a b)))))\n" ++
  "; list drop for batch-7 DropList over both ConstList and ConstDataList\n" ++
  "(define-funs-rec\n" ++
  " ((moist_vdrop ((n Int) (xs VL)) VL) (moist_ddrop ((n Int) (xs DL)) DL))\n" ++
  " ((ite (or (<= n 0) (is-vnil xs)) xs (moist_vdrop (- n 1) (vtl xs)))\n" ++
  "  (ite (or (<= n 0) (is-dnil xs)) xs (moist_ddrop (- n 1) (dtl xs)))))"

/-! ## Script assembly -/

/-- A declared symbolic constant: SMT name and its sort. -/
structure SymConst where
  name : String
  sort : SSort
deriving Repr

/-- A full SMT-LIB script: the symbolic constants to solve for, side
constraints (e.g. byte ranges, `is-VPair`), and the **labelled** goal assertions.

Every goal assertion is emitted as `(assert (! e :named label))` and
`:produce-unsat-cores` is on, so a `(get-unsat-core)` after an `unsat` reports
exactly which labels caused the failure. In particular, the `¬inc`
("determinate") guard is named separately: if it appears in the core, the
negative result is an artefact of the fuel bound (raise the fuel); if it does
not, the result is genuine and bound-independent. -/
structure SmtScript where
  consts  : List SymConst := []
  /-- Side conditions constraining the symbolic constants (well-formedness). -/
  side    : List SExpr := []
  /-- The goal assertions, each with a unique label for unsat-core diagnosis. -/
  asserts : List (String × SExpr) := []
deriving Inhabited

/-- Emit a complete, runnable SMT-LIB v2 document with named assertions, unsat
cores, and both `(get-model)`/`(get-unsat-core)` (z3 prints whichever applies). -/
def SmtScript.toSMTLib (s : SmtScript) : String :=
  let header := "(set-logic ALL)\n(set-option :produce-models true)\n(set-option :produce-unsat-cores true)\n"
  let pre := datatypePreamble ++ "\n"
  let ufs := String.intercalate "\n" (opaqueUFs.map UFDecl.render)
  let decls := String.intercalate "\n"
    (s.consts.map (fun c => s!"(declare-const {c.name} {c.sort.render})"))
  let sides := String.intercalate "\n"
    (s.side.mapIdx (fun i e => s!"(assert (! {e.render} :named wf{i}))"))
  let goals := String.intercalate "\n"
    (s.asserts.map (fun (l, e) => s!"(assert (! {e.render} :named {l}))"))
  let tail := "(check-sat)\n(get-unsat-core)\n(get-model)"
  String.intercalate "\n"
    ([header ++ pre ++ ufs] ++
     (if decls.isEmpty then [] else [decls]) ++
     (if sides.isEmpty then [] else [sides]) ++
     (if goals.isEmpty then [] else [goals]) ++
     [tail]) ++ "\n"

end Moist.Symbolic
