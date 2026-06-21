import Moist.SMT.Basic
import Moist.CEK.Builtins
import Moist.CEK.Machine

namespace Moist.SMT.UPLC

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs)

abbrev SExpr := Moist.SMT.Expr

namespace SExpr

abbrev trueE : SExpr := Moist.SMT.Expr.trueE
abbrev falseE : SExpr := Moist.SMT.Expr.falseE
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
def any (xs : List SExpr) : SExpr := Moist.SMT.Expr.any xs
def ite (c t e : SExpr) : SExpr := Moist.SMT.Expr.ite c t e
def isCtor (ctor : String) (e : SExpr) : SExpr := .app ("(_ is " ++ ctor ++ ")") [e]
def seqEmpty (sort : String) : SExpr := .sym ("(as seq.empty " ++ sort ++ ")")
def seqUnit (e : SExpr) : SExpr := .app "seq.unit" [e]
def seqAppend (a b : SExpr) : SExpr := .app "seq.++" [a, b]
def seqLen (a : SExpr) : SExpr := .app "seq.len" [a]
def seqNth (a i : SExpr) : SExpr := .app "seq.nth" [a, i]
def seqExtract (a start len : SExpr) : SExpr := .app "seq.extract" [a, start, len]
def strAppend (a b : SExpr) : SExpr := .app "str.++" [a, b]

end SExpr

/-! ## Fixed SMT prelude

`Val` is only the first-order SMT representation of encodable UPLC values.
Higher-order runtime values (closures, delays and partial builtins) stay in the
Lean-side symbolic domain and are eliminated by fueled symbolic evaluation before
the final query is emitted.
-/

def prelude : List Moist.SMT.Command :=
  [ .raw "(define-sort Bytes () (Seq Int))"
  , .raw "(declare-sort G1 0)"
  , .raw "(declare-sort G2 0)"
  , .raw "(declare-sort MlResult 0)"
  , .raw <|
      "(declare-datatypes ((Data 0) (DataList 0) (DataPairList 0) (Val 0) (ValList 0))\n" ++
      "  (((DConstr (dataConstrTag Int) (dataConstrFields DataList))\n" ++
      "    (DMap (dataMapEntries DataPairList))\n" ++
      "    (DList (dataListItems DataList))\n" ++
      "    (DI (dataInt Int))\n" ++
      "    (DB (dataBytes Bytes)))\n" ++
      "   ((DNil) (DCons (dhead Data) (dtail DataList)))\n" ++
      "   ((DPNil) (DPCons (dpKey Data) (dpValue Data) (dpTail DataPairList)))\n" ++
      "   ((VInt (unVInt Int))\n" ++
      "    (VBytes (unVBytes Bytes))\n" ++
      "    (VString (unVString String))\n" ++
      "    (VBool (unVBool Bool))\n" ++
      "    (VUnit)\n" ++
      "    (VList (unVList ValList))\n" ++
      "    (VDataList (unVDataList DataList))\n" ++
      "    (VPairDataList (unVPairDataList DataPairList))\n" ++
      "    (VPair (vfst Val) (vsnd Val))\n" ++
      "    (VPairData (pdfst Data) (pdsnd Data))\n" ++
      "    (VData (unVData Data))\n" ++
      "    (VArray (unVArray ValList))\n" ++
      "    (VG1 (unVG1 G1))\n" ++
      "    (VG2 (unVG2 G2))\n" ++
      "    (VMlResult (unVMlResult MlResult))\n" ++
      "    (VConstr (vConstrTag Int) (vConstrFields ValList)))\n" ++
      "   ((VNil) (VCons (vhead Val) (vtail ValList)))))"
  , .raw "(define-fun same_sign ((a Int) (b Int)) Bool (= (>= a 0) (>= b 0)))"
  , .raw "(define-fun abs_int ((a Int)) Int (ite (< a 0) (- 0 a) a))"
  , .raw "(define-fun-rec bytes_valid_at ((bs Bytes) (i Int)) Bool (ite (>= i (seq.len bs)) true (and (>= (seq.nth bs i) 0) (<= (seq.nth bs i) 255) (bytes_valid_at bs (+ i 1)))))"
  , .raw "(define-fun bytes_valid ((bs Bytes)) Bool (bytes_valid_at bs 0))"
  , .raw <|
      "(define-funs-rec\n" ++
      "  ((data_valid ((d Data)) Bool)\n" ++
      "   (dlist_valid ((xs DataList)) Bool)\n" ++
      "   (dplist_valid ((xs DataPairList)) Bool)\n" ++
      "   (val_valid ((v Val)) Bool)\n" ++
      "   (vlist_valid ((xs ValList)) Bool)\n" ++
      "   (const_val_valid ((v Val)) Bool)\n" ++
      "   (const_vlist_valid ((xs ValList)) Bool))\n" ++
      "  ((or (and ((_ is DConstr) d) (dlist_valid (dataConstrFields d)))\n" ++
      "       (and ((_ is DMap) d) (dplist_valid (dataMapEntries d)))\n" ++
      "       (and ((_ is DList) d) (dlist_valid (dataListItems d)))\n" ++
      "       ((_ is DI) d)\n" ++
      "       (and ((_ is DB) d) (bytes_valid (dataBytes d))))\n" ++
      "   (or ((_ is DNil) xs) (and ((_ is DCons) xs) (data_valid (dhead xs)) (dlist_valid (dtail xs))))\n" ++
      "   (or ((_ is DPNil) xs) (and ((_ is DPCons) xs) (data_valid (dpKey xs)) (data_valid (dpValue xs)) (dplist_valid (dpTail xs))))\n" ++
      "   (or ((_ is VInt) v)\n" ++
      "       (and ((_ is VBytes) v) (bytes_valid (unVBytes v)))\n" ++
      "       ((_ is VString) v)\n" ++
      "       ((_ is VBool) v)\n" ++
      "       ((_ is VUnit) v)\n" ++
      "       (and ((_ is VList) v) (const_vlist_valid (unVList v)))\n" ++
      "       (and ((_ is VDataList) v) (dlist_valid (unVDataList v)))\n" ++
      "       (and ((_ is VPairDataList) v) (dplist_valid (unVPairDataList v)))\n" ++
      "       (and ((_ is VPair) v) (const_val_valid (vfst v)) (const_val_valid (vsnd v)))\n" ++
      "       (and ((_ is VPairData) v) (data_valid (pdfst v)) (data_valid (pdsnd v)))\n" ++
      "       (and ((_ is VData) v) (data_valid (unVData v)))\n" ++
      "       (and ((_ is VArray) v) (const_vlist_valid (unVArray v)))\n" ++
      "       ((_ is VG1) v)\n" ++
      "       ((_ is VG2) v)\n" ++
      "       ((_ is VMlResult) v)\n" ++
      "       (and ((_ is VConstr) v) (>= (vConstrTag v) 0) (vlist_valid (vConstrFields v))))\n" ++
      "   (or ((_ is VNil) xs) (and ((_ is VCons) xs) (val_valid (vhead xs)) (vlist_valid (vtail xs))))\n" ++
      "   (or ((_ is VInt) v)\n" ++
      "       (and ((_ is VBytes) v) (bytes_valid (unVBytes v)))\n" ++
      "       ((_ is VString) v)\n" ++
      "       ((_ is VBool) v)\n" ++
      "       ((_ is VUnit) v)\n" ++
      "       (and ((_ is VList) v) (const_vlist_valid (unVList v)))\n" ++
      "       (and ((_ is VDataList) v) (dlist_valid (unVDataList v)))\n" ++
      "       (and ((_ is VPairDataList) v) (dplist_valid (unVPairDataList v)))\n" ++
      "       (and ((_ is VPair) v) (const_val_valid (vfst v)) (const_val_valid (vsnd v)))\n" ++
      "       (and ((_ is VPairData) v) (data_valid (pdfst v)) (data_valid (pdsnd v)))\n" ++
      "       (and ((_ is VData) v) (data_valid (unVData v)))\n" ++
      "       (and ((_ is VArray) v) (const_vlist_valid (unVArray v)))\n" ++
      "       ((_ is VG1) v)\n" ++
      "       ((_ is VG2) v)\n" ++
      "       ((_ is VMlResult) v))\n" ++
      "   (or ((_ is VNil) xs) (and ((_ is VCons) xs) (const_val_valid (vhead xs)) (const_vlist_valid (vtail xs))))))"
  , .raw "(define-fun uplc_tdiv ((a Int) (b Int)) Int (ite (same_sign a b) (div (abs_int a) (abs_int b)) (- 0 (div (abs_int a) (abs_int b)))))"
  , .raw "(define-fun uplc_tmod ((a Int) (b Int)) Int (- a (* b (uplc_tdiv a b))))"
  , .raw "(define-fun uplc_div ((a Int) (b Int)) Int (let ((q (uplc_tdiv a b)) (r (uplc_tmod a b))) (ite (or (= r 0) (same_sign a b)) q (- q 1))))"
  , .raw "(define-fun uplc_mod ((a Int) (b Int)) Int (- a (* b (uplc_div a b))))"
  , .raw "(define-fun-rec bytes_lt_at ((a Bytes) (b Bytes) (i Int) (n Int)) Bool (ite (>= i n) (< (seq.len a) (seq.len b)) (ite (< (seq.nth a i) (seq.nth b i)) true (ite (> (seq.nth a i) (seq.nth b i)) false (bytes_lt_at a b (+ i 1) n)))))"
  , .raw "(define-fun bytes_lt ((a Bytes) (b Bytes)) Bool (bytes_lt_at a b 0 (ite (< (seq.len a) (seq.len b)) (seq.len a) (seq.len b))))"
  , .raw "(define-fun bytes_le ((a Bytes) (b Bytes)) Bool (or (= a b) (bytes_lt a b)))"
  , .raw "(define-fun-rec vlist_length ((xs ValList)) Int (ite ((_ is VNil) xs) 0 (+ 1 (vlist_length (vtail xs)))))"
  , .raw "(define-fun-rec dlist_length ((xs DataList)) Int (ite ((_ is DNil) xs) 0 (+ 1 (dlist_length (dtail xs)))))"
  , .raw "(define-fun-rec vlist_drop ((n Int) (xs ValList)) ValList (ite (or (<= n 0) ((_ is VNil) xs)) xs (vlist_drop (- n 1) (vtail xs))))"
  , .raw "(define-fun-rec dlist_drop ((n Int) (xs DataList)) DataList (ite (or (<= n 0) ((_ is DNil) xs)) xs (dlist_drop (- n 1) (dtail xs))))"
  , .raw "(define-fun-rec vlist_index ((n Int) (xs ValList)) Val (ite (<= n 0) (vhead xs) (vlist_index (- n 1) (vtail xs))))"
  , .declareFun "valid_utf8" [.bytes] .bool
  , .declareFun "uplc_decodeUtf8" [.bytes] .string
  , .declareFun "uplc_encodeUtf8" [.string] .bytes
  , .declareFun "uplc_serializeData" [.data] .bytes
  , .declareFun "uplc_sha2_256" [.bytes] .bytes
  , .declareFun "uplc_sha3_256" [.bytes] .bytes
  , .declareFun "uplc_blake2b_256" [.bytes] .bytes
  , .declareFun "uplc_keccak_256" [.bytes] .bytes
  , .declareFun "uplc_blake2b_224" [.bytes] .bytes
  , .declareFun "uplc_ripemd_160" [.bytes] .bytes
  , .declareFun "uplc_verifyEd25519Signature" [.bytes, .bytes, .bytes] .bool
  , .declareFun "uplc_verifyEcdsaSecp256k1Signature" [.bytes, .bytes, .bytes] .bool
  , .declareFun "uplc_verifySchnorrSecp256k1Signature" [.bytes, .bytes, .bytes] .bool
  , .declareFun "uplc_integerToByteString" [.bool, .int, .int] .bytes
  , .declareFun "uplc_integerToByteString_defined" [.bool, .int, .int] .bool
  , .declareFun "uplc_byteStringToInteger" [.bool, .bytes] .int
  , .declareFun "uplc_andByteString" [.bool, .bytes, .bytes] .bytes
  , .declareFun "uplc_orByteString" [.bool, .bytes, .bytes] .bytes
  , .declareFun "uplc_xorByteString" [.bool, .bytes, .bytes] .bytes
  , .declareFun "uplc_complementByteString" [.bytes] .bytes
  , .declareFun "uplc_readBit" [.bytes, .int] .bool
  , .declareFun "uplc_writeBits" [.bytes, .valList, .bool] .bytes
  , .declareFun "uplc_writeBits_defined" [.bytes, .valList, .bool] .bool
  , .declareFun "uplc_replicateByte" [.int, .int] .bytes
  , .declareFun "uplc_shiftByteString" [.bytes, .int] .bytes
  , .declareFun "uplc_rotateByteString" [.bytes, .int] .bytes
  , .declareFun "uplc_countSetBits" [.bytes] .int
  , .declareFun "uplc_findFirstSetBit" [.bytes] .int
  , .declareFun "uplc_expModInteger" [.int, .int, .int] .int
  , .declareFun "uplc_expModInteger_defined" [.int, .int, .int] .bool
  , .declareFun "uplc_g1_add" [.g1, .g1] .g1
  , .declareFun "uplc_g1_neg" [.g1] .g1
  , .declareFun "uplc_g1_scalarMul" [.int, .g1] .g1
  , .declareFun "uplc_g1_equal" [.g1, .g1] .bool
  , .declareFun "uplc_g1_hashToGroup" [.bytes, .bytes] .g1
  , .declareFun "uplc_g1_compress" [.g1] .bytes
  , .declareFun "uplc_g1_uncompress" [.bytes] .g1
  , .declareFun "uplc_g2_add" [.g2, .g2] .g2
  , .declareFun "uplc_g2_neg" [.g2] .g2
  , .declareFun "uplc_g2_scalarMul" [.int, .g2] .g2
  , .declareFun "uplc_g2_equal" [.g2, .g2] .bool
  , .declareFun "uplc_g2_hashToGroup" [.bytes, .bytes] .g2
  , .declareFun "uplc_g2_compress" [.g2] .bytes
  , .declareFun "uplc_g2_uncompress" [.bytes] .g2
  , .declareFun "uplc_millerLoop" [.g1, .g2] .ml
  , .declareFun "uplc_mulMlResult" [.ml, .ml] .ml
  , .declareFun "uplc_finalVerify" [.ml, .ml] .bool
  , .declareFun "uplc_valueData" [.val] .data
  , .declareFun "uplc_unValueData" [.data] .val
  , .declareFun "uplc_insertCoin" [.bytes, .bytes, .int, .val] .val
  , .declareFun "uplc_lookupCoin" [.bytes, .bytes, .val] .int
  , .declareFun "uplc_scaleValue" [.int, .val] .val
  , .declareFun "uplc_unionValue" [.val, .val] .val
  , .declareFun "uplc_valueContains" [.val, .val] .bool
  , .declareFun "uplc_g1_multiScalarMul" [.valList, .valList] .g1
  , .declareFun "uplc_g2_multiScalarMul" [.valList, .valList] .g2
  ]

inductive SymConst where
  | integer : SExpr → SymConst
  | bytes : SExpr → SymConst
  | string : SExpr → SymConst
  | bool : SExpr → SymConst
  | unit : SymConst
  | data : SExpr → SymConst
  | constList : SExpr → SymConst
  | dataList : SExpr → SymConst
  | pairDataList : SExpr → SymConst
  | pairData : SExpr → SExpr → SymConst
  | array : SExpr → SymConst
  | g1 : SExpr → SymConst
  | g2 : SExpr → SymConst
  | ml : SExpr → SymConst
deriving Repr, BEq

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

def bindOut (xs : List Outcome) (k : SymVal → List Outcome) : List Outcome :=
  xs.flatMap fun
    | .ok pc v => (k v).map (Outcome.guard pc)
    | .error pc => [.error pc]
    | .timeout pc => [.timeout pc]

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

partial def encodeVal? : SymVal → Option SExpr
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
    | .constList xs => some (.app "VList" [xs])
    | .dataList xs => some (.app "VDataList" [xs])
    | .pairDataList xs => some (.app "VPairDataList" [xs])
    | .pairData a b => some (.app "VPairData" [a, b])
    | .array xs => some (.app "VArray" [xs])
    | .g1 g => some (.app "VG1" [g])
    | .g2 g => some (.app "VG2" [g])
    | .ml r => some (.app "VMlResult" [r])

structure Proj (α : Type) where
  guard : SExpr
  val : α
deriving Repr

namespace Proj

def pure (a : α) : Proj α := ⟨SExpr.trueE, a⟩
def fail (dummy : α) : Proj α := ⟨SExpr.falseE, dummy⟩
def map (f : α → β) (p : Proj α) : Proj β := ⟨p.guard, f p.val⟩

def map2 (f : α → β → γ) (a : Proj α) (b : Proj β) : Proj γ :=
  ⟨SExpr.and a.guard b.guard, f a.val b.val⟩

def map3 (f : α → β → γ → δ) (a : Proj α) (b : Proj β) (c : Proj γ) : Proj δ :=
  ⟨SExpr.all [a.guard, b.guard, c.guard], f a.val b.val c.val⟩

end Proj

def valueProj (ctor selector : String) (dummy : SExpr) : SymVal → Proj SExpr
  | .dyn v => ⟨SExpr.isCtor ctor v, .app selector [v]⟩
  | _ => Proj.fail dummy

def asInt : SymVal → Proj SExpr
  | .const (.integer i) => Proj.pure i
  | v => valueProj "VInt" "unVInt" (.int 0) v

def asBytes : SymVal → Proj SExpr
  | .const (.bytes b) => Proj.pure b
  | v => valueProj "VBytes" "unVBytes" (SExpr.seqEmpty "Bytes") v

def asString : SymVal → Proj SExpr
  | .const (.string s) => Proj.pure s
  | v => valueProj "VString" "unVString" (.str "") v

def asBool : SymVal → Proj SExpr
  | .const (.bool b) => Proj.pure b
  | v => valueProj "VBool" "unVBool" (.bool false) v

def asData : SymVal → Proj SExpr
  | .const (.data d) => Proj.pure d
  | v => valueProj "VData" "unVData" (.app "DI" [.int 0]) v

def asDataList : SymVal → Proj SExpr
  | .const (.dataList xs) => Proj.pure xs
  | .const (.constList _) => ⟨SExpr.falseE, .app "DNil" []⟩
  | v => valueProj "VDataList" "unVDataList" (.app "DNil" []) v

def asPairDataList : SymVal → Proj SExpr
  | .const (.pairDataList xs) => Proj.pure xs
  | v => valueProj "VPairDataList" "unVPairDataList" (.app "DPNil" []) v

def asConstList : SymVal → Proj SExpr
  | .const (.constList xs) => Proj.pure xs
  | v => valueProj "VList" "unVList" (.app "VNil" []) v

def asArray : SymVal → Proj SExpr
  | .const (.array xs) => Proj.pure xs
  | v => valueProj "VArray" "unVArray" (.app "VNil" []) v

def asG1 : SymVal → Proj SExpr
  | .const (.g1 g) => Proj.pure g
  | v => valueProj "VG1" "unVG1" (.sym "g1_default") v

def asG2 : SymVal → Proj SExpr
  | .const (.g2 g) => Proj.pure g
  | v => valueProj "VG2" "unVG2" (.sym "g2_default") v

def asMl : SymVal → Proj SExpr
  | .const (.ml r) => Proj.pure r
  | v => valueProj "VMlResult" "unVMlResult" (.sym "ml_default") v

def asPairData : SymVal → Proj (SExpr × SExpr)
  | .const (.pairData a b) => Proj.pure (a, b)
  | .dyn v => ⟨SExpr.isCtor "VPairData" v, (.app "pdfst" [v], .app "pdsnd" [v])⟩
  | _ => Proj.fail (.app "DI" [.int 0], .app "DI" [.int 0])

def asPair : SymVal → Proj (SymVal × SymVal)
  | .pair a b => Proj.pure (a, b)
  | .dyn v => ⟨SExpr.isCtor "VPair" v, (.dyn (.app "vfst" [v]), .dyn (.app "vsnd" [v]))⟩
  | _ => Proj.fail (.dyn (.app "VUnit" []), .dyn (.app "VUnit" []))

def asConstVal : SymVal → Proj SExpr
  | .const c =>
      match encodeVal? (.const c) with
      | some v => Proj.pure v
      | none => Proj.fail (.app "VUnit" [])
  | .dyn v => ⟨.app "const_val_valid" [v], v⟩
  | .pair a b =>
      let a' := asConstVal a
      let b' := asConstVal b
      ⟨SExpr.and a'.guard b'.guard, .app "VPair" [a'.val, b'.val]⟩
  | .constr _ _ | .lam _ _ | .delay _ _ | .builtin _ _ _ =>
      Proj.fail (.app "VUnit" [])

def unitGuard : SymVal → SExpr
  | .const .unit => SExpr.trueE
  | .dyn v => SExpr.isCtor "VUnit" v
  | _ => SExpr.falseE

def checked1 (p : Proj α) (mk : α → SymVal) : List Outcome :=
  [.ok p.guard (mk p.val), .error (SExpr.not p.guard)]

def checkedBool (p : Proj SExpr) : List Outcome :=
  checked1 p (fun b => .const (.bool b))

def checkedConst (p : Proj SExpr) (mk : SExpr → SymConst) : List Outcome :=
  checked1 p (fun e => .const (mk e))

def checked2 (p : Proj α) (mk : α → List Outcome) : List Outcome :=
  (mk p.val).map (Outcome.guard p.guard) ++ [.error (SExpr.not p.guard)]

def bytesLiteral (bs : ByteString) : SExpr :=
  bs.data.foldl (fun acc b => SExpr.seqAppend acc (SExpr.seqUnit (.int (Int.ofNat b.toNat))))
    (SExpr.seqEmpty "Bytes")

mutual
  def dataLiteral : Data → SExpr
    | .Constr tag fields => .app "DConstr" [.int tag, dataListLiteral fields]
    | .Map ps => .app "DMap" [dataPairListLiteral ps]
    | .List xs => .app "DList" [dataListLiteral xs]
    | .I i => .app "DI" [.int i]
    | .B bs => .app "DB" [bytesLiteral bs]

  def dataListLiteral : List Data → SExpr
    | [] => .app "DNil" []
    | x :: xs => .app "DCons" [dataLiteral x, dataListLiteral xs]

  def dataPairListLiteral : List (Data × Data) → SExpr
    | [] => .app "DPNil" []
    | (k, v) :: xs => .app "DPCons" [dataLiteral k, dataLiteral v, dataPairListLiteral xs]
end

partial def constLiteral : Const → SymVal
  | .Integer i => .const (.integer (.int i))
  | .ByteString bs => .const (.bytes (bytesLiteral bs))
  | .String s => .const (.string (.str s))
  | .Unit => .const .unit
  | .Bool b => .const (.bool (.bool b))
  | .ConstList xs =>
      let vals := xs.filterMap (fun c => encodeVal? (constLiteral c))
      .const (.constList (valListExpr vals))
  | .ConstDataList xs => .const (.dataList (dataListLiteral xs))
  | .ConstPairDataList xs => .const (.pairDataList (dataPairListLiteral xs))
  | .Pair (a, b) => .pair (constLiteral a) (constLiteral b)
  | .PairData (a, b) => .const (.pairData (dataLiteral a) (dataLiteral b))
  | .Data d => .const (.data (dataLiteral d))
  | .ConstArray xs =>
      let vals := xs.filterMap (fun c => encodeVal? (constLiteral c))
      .const (.array (valListExpr vals))
  | .Bls12_381_G1_element => .const (.g1 (.sym "g1_default"))
  | .Bls12_381_G2_element => .const (.g2 (.sym "g2_default"))
  | .Bls12_381_MlResult => .const (.ml (.sym "ml_default"))

def lookupEnv : List SymVal → Nat → Option SymVal
  | [], _ => none
  | _, 0 => none
  | v :: _, 1 => some v
  | _ :: ρ, n + 1 => lookupEnv ρ n

def extendEnv (ρ : List SymVal) (v : SymVal) : List SymVal := v :: ρ

def branchOutcomes (alts : List (SExpr × List Outcome)) (extraErrors : List SExpr := []) : List Outcome :=
  alts.flatMap (fun (g, os) => mapPc g os) ++ extraErrors.map Outcome.error

def enumerate (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

def fieldFromValList (xs : SExpr) : SymVal := .dyn (.app "vhead" [xs])
def tailFromValList (xs : SExpr) : SymVal := .const (.constList (.app "vtail" [xs]))
def fieldFromDataList (xs : SExpr) : SymVal := .const (.data (.app "dhead" [xs]))
def tailFromDataList (xs : SExpr) : SymVal := .const (.dataList (.app "dtail" [xs]))

def divisionGuard (b : SExpr) : SExpr := SExpr.ne b (.int 0)

def nonnegGuard (x : SExpr) : SExpr := SExpr.ge x (.int 0)

mutual
  def evalSym : Nat → List SymVal → Term → List Outcome
    | 0, _, _ => timeout
    | _ + 1, ρ, .Var k =>
        match lookupEnv ρ k with
        | some v => ok v
        | none => err
    | _ + 1, _, .Constant (c, _) => ok (constLiteral c)
    | _ + 1, _, .Builtin b => ok (.builtin b [] (expectedArgs b))
    | _ + 1, ρ, .Lam _ body => ok (.lam body ρ)
    | _ + 1, ρ, .Delay body => ok (.delay body ρ)
    | n + 1, ρ, .Apply f a =>
        bindOut (evalSym n ρ f) fun vf =>
        bindOut (evalSym n ρ a) fun va =>
        applySym n vf va
    | n + 1, ρ, .Force t =>
        bindOut (evalSym n ρ t) fun vt =>
        forceSym n vt
    | n + 1, ρ, .Constr tag fields =>
        bindOut (evalListSym n ρ fields) fun vals =>
          match vals with
          | .constr (.int (-1)) vs => ok (.constr (.int (Int.ofNat tag)) vs)
          | _ => err
    | n + 1, ρ, .Case scrut alts =>
        bindOut (evalSym n ρ scrut) fun v =>
        caseSym n ρ v alts
    | _ + 1, _, .Error => err
  termination_by n _ t => (n, (1, sizeOf t))

  def evalListSym : Nat → List SymVal → List Term → List Outcome
    | _, _, [] => ok (.constr (.int (-1)) [])
    | n, ρ, t :: ts =>
        bindOut (evalSym n ρ t) fun v =>
        bindOut (evalListSym n ρ ts) fun rest =>
          match rest with
          | .constr (.int (-1)) vs => ok (.constr (.int (-1)) (v :: vs))
          | _ => err
  termination_by n _ ts => (n, (2, sizeOf ts))

  def applySym : Nat → SymVal → SymVal → List Outcome
    | 0, _, _ => timeout
    | n + 1, .lam body ρ, va => evalSym n (extendEnv ρ va) body
    | _ + 1, .builtin b args ea, va =>
        match ea.head with
        | .argV =>
            match ea.tail with
            | some rest => ok (.builtin b (va :: args) rest)
            | none => evalBuiltinSym b (va :: args)
        | .argQ => err
    | _ + 1, _, _ => err
  termination_by n _ _ => (n, (0, 0))

  def forceSym : Nat → SymVal → List Outcome
    | 0, _ => timeout
    | n + 1, .delay body ρ => evalSym n ρ body
    | _ + 1, .builtin b args ea =>
        match ea.head with
        | .argQ =>
            match ea.tail with
            | some rest => ok (.builtin b args rest)
            | none => evalBuiltinSym b args
        | .argV => err
    | _ + 1, _ => err
  termination_by n _ => (n, (0, 0))

  def applyListSym : Nat → SymVal → List SymVal → List Outcome
    | _, vf, [] => ok vf
    | n, vf, a :: as =>
        bindOut (applySym n vf a) fun vf' =>
        applyListSym n vf' as
  termination_by n _ vs => (n, (2, sizeOf vs))

  def applyValListSym : Nat → SymVal → SExpr → List Outcome
    | 0, _, _ => timeout
    | n + 1, vf, xs =>
        let nilBranch := (SExpr.isCtor "VNil" xs, ok vf)
        let consBranch :=
          (SExpr.not (SExpr.isCtor "VNil" xs),
            bindOut (applySym n vf (.dyn (.app "vhead" [xs]))) fun vf' =>
              applyValListSym n vf' (.app "vtail" [xs]))
        branchOutcomes [nilBranch, consBranch]
  termination_by n _ _ => (n, (2, 0))

  def caseSym : Nat → List SymVal → SymVal → List Term → List Outcome
    | n, ρ, .constr tag fields, alts =>
        let branches := (enumerate alts).map fun (i, alt) =>
          (SExpr.eq tag (.int (Int.ofNat i)),
            bindOut (evalSym n ρ alt) fun vAlt => applyListSym n vAlt fields)
        let covered := SExpr.any ((enumerate alts).map fun (i, _) => SExpr.eq tag (.int (Int.ofNat i)))
        branchOutcomes branches [SExpr.not covered]
    | n, ρ, .const (.bool b), alts =>
        let tag := SExpr.ite b (.int 1) (.int 0)
        if alts.length > 2 then err
        else
          let branches := (enumerate alts).map fun (i, alt) =>
            (SExpr.eq tag (.int (Int.ofNat i)), evalSym n ρ alt)
          branchOutcomes branches [SExpr.not (SExpr.any ((enumerate alts).map fun (i, _) => SExpr.eq tag (.int (Int.ofNat i))))]
    | n, ρ, .const .unit, alts =>
        if alts.length > 1 then err
        else match alts[0]? with
          | some alt => evalSym n ρ alt
          | none => err
    | n, ρ, .const (.integer x), alts =>
        let branches := (enumerate alts).map fun (i, alt) =>
          (SExpr.and (nonnegGuard x) (SExpr.eq x (.int (Int.ofNat i))), evalSym n ρ alt)
        let covered := SExpr.and (nonnegGuard x)
          (SExpr.any ((enumerate alts).map fun (i, _) => SExpr.eq x (.int (Int.ofNat i))))
        branchOutcomes branches [SExpr.not covered]
    | n, ρ, .const (.constList xs), alts =>
        if alts.length > 2 then err
        else
          let nilBranch := match alts[1]? with
            | some alt => [(SExpr.isCtor "VNil" xs, evalSym n ρ alt)]
            | none => []
          let consBranch := match alts[0]? with
            | some alt =>
                [(SExpr.not (SExpr.isCtor "VNil" xs),
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [fieldFromValList xs, tailFromValList xs])]
            | none => []
          let branches := consBranch ++ nilBranch
          branchOutcomes branches [SExpr.not (SExpr.any (branches.map Prod.fst))]
    | n, ρ, .const (.dataList xs), alts =>
        if alts.length > 2 then err
        else
          let nilBranch := match alts[1]? with
            | some alt => [(SExpr.isCtor "DNil" xs, evalSym n ρ alt)]
            | none => []
          let consBranch := match alts[0]? with
            | some alt =>
                [(SExpr.not (SExpr.isCtor "DNil" xs),
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [fieldFromDataList xs, tailFromDataList xs])]
            | none => []
          let branches := consBranch ++ nilBranch
          branchOutcomes branches [SExpr.not (SExpr.any (branches.map Prod.fst))]
    | n, ρ, .pair a b, alts =>
        if alts.length > 1 then err
        else match alts[0]? with
          | some alt => bindOut (evalSym n ρ alt) fun vAlt => applyListSym n vAlt [a, b]
          | none => err
    | n, ρ, .const (.pairData a b), alts =>
        if alts.length > 1 then err
        else match alts[0]? with
          | some alt =>
              bindOut (evalSym n ρ alt) fun vAlt =>
                applyListSym n vAlt [.const (.data a), .const (.data b)]
          | none => err
    | n, ρ, .dyn v, alts =>
        let enum := enumerate alts
        let tagCovered (tag : SExpr) : SExpr :=
          SExpr.any (enum.map fun (i, _) => SExpr.eq tag (.int (Int.ofNat i)))
        let boolTag := SExpr.ite (.app "unVBool" [v]) (.int 1) (.int 0)
        let boolBranches :=
          if alts.length > 2 then []
          else enum.map fun (i, alt) =>
            (SExpr.all [SExpr.isCtor "VBool" v, SExpr.eq boolTag (.int (Int.ofNat i))], evalSym n ρ alt)
        let boolError :=
          if alts.length > 2 then SExpr.isCtor "VBool" v
          else SExpr.and (SExpr.isCtor "VBool" v) (SExpr.not (tagCovered boolTag))
        let unitBranches :=
          if alts.length > 1 then []
          else match alts[0]? with
            | some alt => [(SExpr.isCtor "VUnit" v, evalSym n ρ alt)]
            | none => []
        let unitError :=
          if alts.length > 1 then SExpr.isCtor "VUnit" v
          else SExpr.and (SExpr.isCtor "VUnit" v) (SExpr.not (SExpr.any (unitBranches.map Prod.fst)))
        let intVal := .app "unVInt" [v]
        let intBranches := enum.map fun (i, alt) =>
          (SExpr.all [SExpr.isCtor "VInt" v, nonnegGuard intVal, SExpr.eq intVal (.int (Int.ofNat i))], evalSym n ρ alt)
        let intError := SExpr.and (SExpr.isCtor "VInt" v)
          (SExpr.not (SExpr.and (nonnegGuard intVal) (tagCovered intVal)))
        let listVal := .app "unVList" [v]
        let listBranches :=
          if alts.length > 2 then []
          else
            let nilBranch := match alts[1]? with
              | some alt => [(SExpr.all [SExpr.isCtor "VList" v, SExpr.isCtor "VNil" listVal], evalSym n ρ alt)]
              | none => []
            let consBranch := match alts[0]? with
              | some alt =>
                  [(SExpr.all [SExpr.isCtor "VList" v, SExpr.not (SExpr.isCtor "VNil" listVal)],
                    bindOut (evalSym n ρ alt) fun vAlt =>
                      applyListSym n vAlt [fieldFromValList listVal, tailFromValList listVal])]
              | none => []
            consBranch ++ nilBranch
        let listError :=
          if alts.length > 2 then SExpr.isCtor "VList" v
          else SExpr.and (SExpr.isCtor "VList" v) (SExpr.not (SExpr.any (listBranches.map Prod.fst)))
        let dataListVal := .app "unVDataList" [v]
        let dataListBranches :=
          if alts.length > 2 then []
          else
            let nilBranch := match alts[1]? with
              | some alt => [(SExpr.all [SExpr.isCtor "VDataList" v, SExpr.isCtor "DNil" dataListVal], evalSym n ρ alt)]
              | none => []
            let consBranch := match alts[0]? with
              | some alt =>
                  [(SExpr.all [SExpr.isCtor "VDataList" v, SExpr.not (SExpr.isCtor "DNil" dataListVal)],
                    bindOut (evalSym n ρ alt) fun vAlt =>
                      applyListSym n vAlt [fieldFromDataList dataListVal, tailFromDataList dataListVal])]
              | none => []
            consBranch ++ nilBranch
        let dataListError :=
          if alts.length > 2 then SExpr.isCtor "VDataList" v
          else SExpr.and (SExpr.isCtor "VDataList" v) (SExpr.not (SExpr.any (dataListBranches.map Prod.fst)))
        let pairBranches :=
          if alts.length > 1 then []
          else match alts[0]? with
            | some alt =>
                [(SExpr.isCtor "VPair" v,
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [.dyn (.app "vfst" [v]), .dyn (.app "vsnd" [v])])]
            | none => []
        let pairError :=
          if alts.length > 1 then SExpr.isCtor "VPair" v
          else SExpr.and (SExpr.isCtor "VPair" v) (SExpr.not (SExpr.any (pairBranches.map Prod.fst)))
        let pairDataBranches :=
          if alts.length > 1 then []
          else match alts[0]? with
            | some alt =>
                [(SExpr.isCtor "VPairData" v,
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [.const (.data (.app "pdfst" [v])), .const (.data (.app "pdsnd" [v]))])]
            | none => []
        let pairDataError :=
          if alts.length > 1 then SExpr.isCtor "VPairData" v
          else SExpr.and (SExpr.isCtor "VPairData" v) (SExpr.not (SExpr.any (pairDataBranches.map Prod.fst)))
        let constrTag := .app "vConstrTag" [v]
        let constrBranches := enum.map fun (i, alt) =>
          (SExpr.all [SExpr.isCtor "VConstr" v, SExpr.eq constrTag (.int (Int.ofNat i))],
            bindOut (evalSym n ρ alt) fun vAlt =>
              applyValListSym n vAlt (.app "vConstrFields" [v]))
        let constrError := SExpr.and (SExpr.isCtor "VConstr" v) (SExpr.not (tagCovered constrTag))
        let unsupportedError := SExpr.any [
          SExpr.isCtor "VBytes" v, SExpr.isCtor "VString" v, SExpr.isCtor "VData" v,
          SExpr.isCtor "VPairDataList" v, SExpr.isCtor "VArray" v, SExpr.isCtor "VG1" v,
          SExpr.isCtor "VG2" v, SExpr.isCtor "VMlResult" v]
        let branches := boolBranches ++ unitBranches ++ intBranches ++ listBranches ++
          dataListBranches ++ pairBranches ++ pairDataBranches ++ constrBranches
        branchOutcomes branches [
          boolError, unitError, intError, listError, dataListError,
          pairError, pairDataError, constrError, unsupportedError]
    | _, _, _, _ => err
  termination_by n _ _ _ => (n, (3, 0))

  def evalBuiltinSym : BuiltinFun → List SymVal → List Outcome
    | .AddInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.add (asInt a) (asInt b)) .integer
    | .SubtractInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.sub (asInt a) (asInt b)) .integer
    | .MultiplyInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.mul (asInt a) (asInt b)) .integer
    | .DivideInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_div" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .QuotientInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_tdiv" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .RemainderInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_tmod" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .ModInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_mod" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .EqualsInteger, [b, a] => checkedBool (Proj.map2 SExpr.eq (asInt a) (asInt b))
    | .LessThanInteger, [b, a] => checkedBool (Proj.map2 SExpr.lt (asInt a) (asInt b))
    | .LessThanEqualsInteger, [b, a] => checkedBool (Proj.map2 SExpr.le (asInt a) (asInt b))

    | .AppendByteString, [b, a] => checkedConst (Proj.map2 SExpr.seqAppend (asBytes a) (asBytes b)) .bytes
    | .ConsByteString, [bs, n] =>
        let p := Proj.map2 (fun n bs => (n, bs)) (asInt n) (asBytes bs)
        checked2 p fun (n, bs) =>
          let inByte := SExpr.and (SExpr.ge n (.int 0)) (SExpr.le n (.int 255))
          [.ok inByte (.const (.bytes (SExpr.seqAppend (SExpr.seqUnit n) bs))),
           .error (SExpr.not inByte)]
    | .SliceByteString, [bs, len, start] =>
        let p := Proj.map3 (fun start len bs => (start, len, bs)) (asInt start) (asInt len) (asBytes bs)
        checkedConst (p.map fun (start, len, bs) =>
          let s := SExpr.ite (SExpr.lt start (.int 0)) (.int 0) start
          let l := SExpr.ite (SExpr.lt len (.int 0)) (.int 0) len
          SExpr.seqExtract bs s l) .bytes
    | .LengthOfByteString, [bs] => checkedConst ((asBytes bs).map SExpr.seqLen) .integer
    | .IndexByteString, [idx, bs] =>
        let p := Proj.map2 (fun bs idx => (bs, idx)) (asBytes bs) (asInt idx)
        checked2 p fun (bs, idx) =>
          let inRange := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (SExpr.seqLen bs))
          [.ok inRange (.const (.integer (SExpr.seqNth bs idx))), .error (SExpr.not inRange)]
    | .EqualsByteString, [b, a] => checkedBool (Proj.map2 SExpr.eq (asBytes a) (asBytes b))
    | .LessThanByteString, [b, a] => checkedBool (Proj.map2 (fun a b => .app "bytes_lt" [a, b]) (asBytes a) (asBytes b))
    | .LessThanEqualsByteString, [b, a] => checkedBool (Proj.map2 (fun a b => .app "bytes_le" [a, b]) (asBytes a) (asBytes b))

    | .Sha2_256, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_sha2_256" [b]) .bytes
    | .Sha3_256, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_sha3_256" [b]) .bytes
    | .Blake2b_256, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_blake2b_256" [b]) .bytes
    | .VerifyEd25519Signature, [msg, sig, key] =>
        checkedBool (Proj.map3 (fun key msg sig => .app "uplc_verifyEd25519Signature" [key, msg, sig])
          (asBytes key) (asBytes msg) (asBytes sig))

    | .AppendString, [b, a] => checkedConst (Proj.map2 SExpr.strAppend (asString a) (asString b)) .string
    | .EqualsString, [b, a] => checkedBool (Proj.map2 SExpr.eq (asString a) (asString b))
    | .EncodeUtf8, [s] => checkedConst ((asString s).map fun x => .app "uplc_encodeUtf8" [x]) .bytes
    | .DecodeUtf8, [bs] =>
        checked2 (asBytes bs) fun b =>
          [.ok (.app "valid_utf8" [b]) (.const (.string (.app "uplc_decodeUtf8" [b]))),
           .error (SExpr.not (.app "valid_utf8" [b]))]

    | .IfThenElse, [elseV, thenV, cond] =>
        let c := asBool cond
        [.ok (SExpr.and c.guard c.val) thenV,
         .ok (SExpr.and c.guard (SExpr.not c.val)) elseV,
         .error (SExpr.not c.guard)]
    | .ChooseUnit, [result, unitV] =>
        match unitV with
        | .const .unit => ok result
        | .dyn v => [.ok (SExpr.isCtor "VUnit" v) result, .error (SExpr.not (SExpr.isCtor "VUnit" v))]
        | _ => err
    | .Trace, [result, msg] =>
        checked2 (asString msg) fun _ => ok result
    | .FstPair, [p] =>
        let pp := asPair p
        let pd := asPairData p
        [.ok pp.guard pp.val.1,
         .ok pd.guard (.const (.data pd.val.1)),
         .error (SExpr.not (SExpr.or pp.guard pd.guard))]
    | .SndPair, [p] =>
        let pp := asPair p
        let pd := asPairData p
        [.ok pp.guard pp.val.2,
         .ok pd.guard (.const (.data pd.val.2)),
         .error (SExpr.not (SExpr.or pp.guard pd.guard))]

    | .ChooseList, [consCase, nilCase, xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        let dBranches :=
          [.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val)) nilCase,
           .ok (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val))) consCase]
        let vBranches :=
          [.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val)) nilCase,
           .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val))) consCase]
        dBranches ++ vBranches ++ [.error (SExpr.not (SExpr.or dl.guard vl.guard))]
    | .MkCons, [tail, head] =>
        let dl := asDataList tail
        let hd := asData head
        let vl := asConstList tail
        let hv := asConstVal head
        let dataOk := SExpr.and dl.guard hd.guard
        let constOk := SExpr.and vl.guard hv.guard
        [.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
         .ok constOk (.const (.constList (.app "VCons" [hv.val, vl.val]))),
         .error (SExpr.not (SExpr.or dataOk constOk))]
    | .HeadList, [xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        [.ok (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val))) (.const (.data (.app "dhead" [dl.val]))),
         .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val))) (.dyn (.app "vhead" [vl.val])),
         .error (SExpr.not (SExpr.or (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                                     (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]
    | .TailList, [xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        [.ok (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val))) (.const (.dataList (.app "dtail" [dl.val]))),
         .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val))) (.const (.constList (.app "vtail" [vl.val]))),
         .error (SExpr.not (SExpr.or (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                                     (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]
    | .NullList, [xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        [.ok dl.guard (.const (.bool (SExpr.isCtor "DNil" dl.val))),
         .ok vl.guard (.const (.bool (SExpr.isCtor "VNil" vl.val))),
         .error (SExpr.not (SExpr.or dl.guard vl.guard))]

    | .ChooseData, [bCase, iCase, listCase, mapCase, constrCase, dVal] =>
        let d := asData dVal
        [.ok (SExpr.and d.guard (SExpr.isCtor "DConstr" d.val)) constrCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DMap" d.val)) mapCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DList" d.val)) listCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DI" d.val)) iCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DB" d.val)) bCase,
         .error (SExpr.not d.guard)]
    | .ConstrData, [fields, tag] =>
        checkedConst (Proj.map2 (fun tag fields => .app "DConstr" [tag, fields]) (asInt tag) (asDataList fields)) .data
    | .MapData, [ps] => checkedConst ((asPairDataList ps).map fun ps => .app "DMap" [ps]) .data
    | .ListData, [xs] => checkedConst ((asDataList xs).map fun xs => .app "DList" [xs]) .data
    | .IData, [i] => checkedConst ((asInt i).map fun i => .app "DI" [i]) .data
    | .BData, [bs] => checkedConst ((asBytes bs).map fun bs => .app "DB" [bs]) .data
    | .UnConstrData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DConstr" d
          [.ok is (.const (.pairData (.app "DI" [.app "dataConstrTag" [d]]) (.app "DList" [.app "dataConstrFields" [d]]))),
           .error (SExpr.not is)]
    | .UnMapData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DMap" d
          [.ok is (.const (.pairDataList (.app "dataMapEntries" [d]))), .error (SExpr.not is)]
    | .UnListData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DList" d
          [.ok is (.const (.dataList (.app "dataListItems" [d]))), .error (SExpr.not is)]
    | .UnIData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DI" d
          [.ok is (.const (.integer (.app "dataInt" [d]))), .error (SExpr.not is)]
    | .UnBData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DB" d
          [.ok is (.const (.bytes (.app "dataBytes" [d]))), .error (SExpr.not is)]
    | .EqualsData, [b, a] => checkedBool (Proj.map2 SExpr.eq (asData a) (asData b))
    | .MkPairData, [b, a] => checked1 (Proj.map2 (fun a b => (a, b)) (asData a) (asData b)) (fun (a, b) => .const (.pairData a b))
    | .MkNilData, [u] =>
        let g := unitGuard u
        [.ok g (.const (.dataList (.app "DNil" []))), .error (SExpr.not g)]
    | .MkNilPairData, [u] =>
        let g := unitGuard u
        [.ok g (.const (.pairDataList (.app "DPNil" []))), .error (SExpr.not g)]

    | .SerializeData, [d] => checkedConst ((asData d).map fun d => .app "uplc_serializeData" [d]) .bytes
    | .VerifyEcdsaSecp256k1Signature, [msg, sig, key] =>
        checkedBool (Proj.map3 (fun key msg sig => .app "uplc_verifyEcdsaSecp256k1Signature" [key, msg, sig])
          (asBytes key) (asBytes msg) (asBytes sig))
    | .VerifySchnorrSecp256k1Signature, [msg, sig, key] =>
        checkedBool (Proj.map3 (fun key msg sig => .app "uplc_verifySchnorrSecp256k1Signature" [key, msg, sig])
          (asBytes key) (asBytes msg) (asBytes sig))

    | .Keccak_256, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_keccak_256" [b]) .bytes
    | .Blake2b_224, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_blake2b_224" [b]) .bytes
    | .IntegerToByteString, [n, width, endian] =>
        let p := Proj.map3 (fun endian width n => (endian, width, n)) (asBool endian) (asInt width) (asInt n)
        checked2 p fun (endian, width, n) =>
          let basic := SExpr.all [SExpr.ge n (.int 0), SExpr.ge width (.int 0), SExpr.le width (.int 8192)]
          let defined := SExpr.and basic (.app "uplc_integerToByteString_defined" [endian, width, n])
          [.ok defined (.const (.bytes (.app "uplc_integerToByteString" [endian, width, n]))),
           .error (SExpr.not defined)]
    | .ByteStringToInteger, [bs, endian] =>
        checkedConst (Proj.map2 (fun endian bs => .app "uplc_byteStringToInteger" [endian, bs])
          (asBool endian) (asBytes bs)) .integer

    | .AndByteString, [b, a, pad] =>
        checkedConst (Proj.map3 (fun pad a b => .app "uplc_andByteString" [pad, a, b]) (asBool pad) (asBytes a) (asBytes b)) .bytes
    | .OrByteString, [b, a, pad] =>
        checkedConst (Proj.map3 (fun pad a b => .app "uplc_orByteString" [pad, a, b]) (asBool pad) (asBytes a) (asBytes b)) .bytes
    | .XorByteString, [b, a, pad] =>
        checkedConst (Proj.map3 (fun pad a b => .app "uplc_xorByteString" [pad, a, b]) (asBool pad) (asBytes a) (asBytes b)) .bytes
    | .ComplementByteString, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_complementByteString" [b]) .bytes
    | .ReadBit, [idx, bs] =>
        let p := Proj.map2 (fun bs idx => (bs, idx)) (asBytes bs) (asInt idx)
        checked2 p fun (bs, idx) =>
          let inRange := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (SExpr.mul (SExpr.seqLen bs) (.int 8)))
          [.ok inRange (.const (.bool (.app "uplc_readBit" [bs, idx]))), .error (SExpr.not inRange)]
    | .WriteBits, [val, idxs, bs] =>
        let p := Proj.map3 (fun bs idxs val => (bs, idxs, val)) (asBytes bs) (asConstList idxs) (asBool val)
        checked2 p fun (bs, idxs, val) =>
          let defined := .app "uplc_writeBits_defined" [bs, idxs, val]
          [.ok defined (.const (.bytes (.app "uplc_writeBits" [bs, idxs, val]))), .error (SExpr.not defined)]
    | .ReplicateByte, [byte, count] =>
        let p := Proj.map2 (fun count byte => (count, byte)) (asInt count) (asInt byte)
        checked2 p fun (count, byte) =>
          let g := SExpr.all [SExpr.ge count (.int 0), SExpr.le count (.int 8192),
            SExpr.ge byte (.int 0), SExpr.le byte (.int 255)]
          [.ok g (.const (.bytes (.app "uplc_replicateByte" [count, byte]))), .error (SExpr.not g)]
    | .ShiftByteString, [n, bs] =>
        checkedConst (Proj.map2 (fun bs n => .app "uplc_shiftByteString" [bs, n]) (asBytes bs) (asInt n)) .bytes
    | .RotateByteString, [n, bs] =>
        checkedConst (Proj.map2 (fun bs n => .app "uplc_rotateByteString" [bs, n]) (asBytes bs) (asInt n)) .bytes
    | .CountSetBits, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_countSetBits" [b]) .integer
    | .FindFirstSetBit, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_findFirstSetBit" [b]) .integer
    | .Ripemd_160, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_ripemd_160" [b]) .bytes
    | .ExpModInteger, [m, e, b] =>
        let p := Proj.map3 (fun b e m => (b, e, m)) (asInt b) (asInt e) (asInt m)
        checked2 p fun (b, e, m) =>
          let defined := SExpr.and (SExpr.gt m (.int 0)) (.app "uplc_expModInteger_defined" [b, e, m])
          [.ok defined (.const (.integer (.app "uplc_expModInteger" [b, e, m]))), .error (SExpr.not defined)]

    | .DropList, [xs, n] =>
        let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs]) (asInt n) (asConstList xs)
        let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs]) (asInt n) (asDataList xs)
        [.ok vl.guard (.const (.constList vl.val)),
         .ok dl.guard (.const (.dataList dl.val)),
         .error (SExpr.not (SExpr.or vl.guard dl.guard))]
    | .IndexArray, [idx, arr] =>
        let p := Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx)
        checked2 p fun (arr, idx) =>
          let g := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (.app "vlist_length" [arr]))
          [.ok g (.dyn (.app "vlist_index" [idx, arr])), .error (SExpr.not g)]
    | .LengthOfArray, [arr] => checkedConst ((asArray arr).map fun xs => .app "vlist_length" [xs]) .integer
    | .ListToArray, [xs] => checkedConst (asConstList xs) .array
    | .InsertCoin, [value, amount, token, policy] =>
        checked1 (Proj.map3 (fun policy token amount => (policy, token, amount)) (asBytes policy) (asBytes token) (asInt amount))
          (fun (policy, token, amount) =>
            match encodeVal? value with
            | some v => .dyn (.app "uplc_insertCoin" [policy, token, amount, v])
            | none => .dyn (.app "VUnit" []))
    | .LookupCoin, [value, token, policy] =>
        checkedConst (Proj.map2 (fun policy token =>
          match encodeVal? value with
          | some v => .app "uplc_lookupCoin" [policy, token, v]
          | none => .int 0) (asBytes policy) (asBytes token)) .integer
    | .ScaleValue, [value, scale] =>
        checked1 (asInt scale) (fun scale =>
          match encodeVal? value with
          | some v => .dyn (.app "uplc_scaleValue" [scale, v])
          | none => .dyn (.app "VUnit" []))
    | .UnionValue, [b, a] =>
        match encodeVal? a, encodeVal? b with
        | some a, some b => ok (.dyn (.app "uplc_unionValue" [a, b]))
        | _, _ => err
    | .ValueContains, [b, a] =>
        match encodeVal? a, encodeVal? b with
        | some a, some b => ok (.const (.bool (.app "uplc_valueContains" [a, b])))
        | _, _ => err
    | .ValueData, [v] =>
        match encodeVal? v with
        | some v => ok (.const (.data (.app "uplc_valueData" [v])))
        | none => err
    | .UnValueData, [d] => checked1 ((asData d).map fun d => .app "uplc_unValueData" [d]) .dyn

    | .Bls12_381_G1_add, [b, a] => checkedConst (Proj.map2 (fun a b => .app "uplc_g1_add" [a, b]) (asG1 a) (asG1 b)) .g1
    | .Bls12_381_G1_neg, [a] => checkedConst ((asG1 a).map fun a => .app "uplc_g1_neg" [a]) .g1
    | .Bls12_381_G1_scalarMul, [g, n] => checkedConst (Proj.map2 (fun n g => .app "uplc_g1_scalarMul" [n, g]) (asInt n) (asG1 g)) .g1
    | .Bls12_381_G1_equal, [b, a] => checkedBool (Proj.map2 (fun a b => .app "uplc_g1_equal" [a, b]) (asG1 a) (asG1 b))
    | .Bls12_381_G1_hashToGroup, [dst, bs] => checkedConst (Proj.map2 (fun bs dst => .app "uplc_g1_hashToGroup" [bs, dst]) (asBytes bs) (asBytes dst)) .g1
    | .Bls12_381_G1_compress, [g] => checkedConst ((asG1 g).map fun g => .app "uplc_g1_compress" [g]) .bytes
    | .Bls12_381_G1_uncompress, [bs] => checkedConst ((asBytes bs).map fun bs => .app "uplc_g1_uncompress" [bs]) .g1
    | .Bls12_381_G2_add, [b, a] => checkedConst (Proj.map2 (fun a b => .app "uplc_g2_add" [a, b]) (asG2 a) (asG2 b)) .g2
    | .Bls12_381_G2_neg, [a] => checkedConst ((asG2 a).map fun a => .app "uplc_g2_neg" [a]) .g2
    | .Bls12_381_G2_scalarMul, [g, n] => checkedConst (Proj.map2 (fun n g => .app "uplc_g2_scalarMul" [n, g]) (asInt n) (asG2 g)) .g2
    | .Bls12_381_G2_equal, [b, a] => checkedBool (Proj.map2 (fun a b => .app "uplc_g2_equal" [a, b]) (asG2 a) (asG2 b))
    | .Bls12_381_G2_hashToGroup, [dst, bs] => checkedConst (Proj.map2 (fun bs dst => .app "uplc_g2_hashToGroup" [bs, dst]) (asBytes bs) (asBytes dst)) .g2
    | .Bls12_381_G2_compress, [g] => checkedConst ((asG2 g).map fun g => .app "uplc_g2_compress" [g]) .bytes
    | .Bls12_381_G2_uncompress, [bs] => checkedConst ((asBytes bs).map fun bs => .app "uplc_g2_uncompress" [bs]) .g2
    | .Bls12_381_millerLoop, [g2, g1] => checkedConst (Proj.map2 (fun g1 g2 => .app "uplc_millerLoop" [g1, g2]) (asG1 g1) (asG2 g2)) .ml
    | .Bls12_381_mulMlResult, [b, a] => checkedConst (Proj.map2 (fun a b => .app "uplc_mulMlResult" [a, b]) (asMl a) (asMl b)) .ml
    | .Bls12_381_finalVerify, [b, a] => checkedBool (Proj.map2 (fun a b => .app "uplc_finalVerify" [a, b]) (asMl a) (asMl b))
    | .Bls12_381_G1_multiScalarMul, [points, scalars] =>
        checkedConst (Proj.map2 (fun scalars points => .app "uplc_g1_multiScalarMul" [scalars, points]) (asConstList scalars) (asConstList points)) .g1
    | .Bls12_381_G2_multiScalarMul, [points, scalars] =>
        checkedConst (Proj.map2 (fun scalars points => .app "uplc_g2_multiScalarMul" [scalars, points]) (asConstList scalars) (asConstList points)) .g2
    | _, _ => err
end

structure SymDecl where
  name : String
  sort : Moist.SMT.SSort
  value : SymVal
  assumptions : List SExpr := []
deriving Repr

def symInt (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .int, .const (.integer (.sym n)), []⟩

def symBool (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .bool, .const (.bool (.sym n)), []⟩

def symBytes (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .bytes, .const (.bytes (.sym n)), [.app "bytes_valid" [.sym n]]⟩

def symString (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .string, .const (.string (.sym n)), []⟩

def symData (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .data, .const (.data (.sym n)), [.app "data_valid" [.sym n]]⟩

def symVal (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .val, .dyn (.sym n), [.app "val_valid" [.sym n]]⟩

def symConstr (name : String) (fields : List SymVal := []) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .int, .constr (.sym n) fields, [SExpr.ge (.sym n) (.int 0)]⟩

def envOf (decls : List SymDecl) : List SymVal :=
  decls.map SymDecl.value

def declCommands (decls : List SymDecl) : List Moist.SMT.Command :=
  decls.map (fun d => .declareConst d.name d.sort)

def assumptionCommands (decls : List SymDecl) : List Moist.SMT.Command :=
  decls.flatMap fun d => d.assumptions.map Moist.SMT.Command.assert

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

def scriptWith (decls : List SymDecl) (assertions : List SExpr) : Moist.SMT.Script :=
  ⟨prelude ++ declCommands decls ++ assumptionCommands decls ++
    assertions.map Moist.SMT.Command.assert ++ [.checkSat, .getModel]⟩

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
