import Moist.SMT.Optimize
import Moist.CEK.Builtins
import Moist.CEK.Machine
import Moist.Plutus.DecidableEq

namespace Moist.SMT.UPLC

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs)

abbrev SExpr := Moist.SMT.Expr

namespace SExpr

abbrev trueE : SExpr := Moist.SMT.Expr.trueE
abbrev falseE : SExpr := Moist.SMT.Expr.falseE

/- A positive equality result is carried in `Type`, so it survives executable
matching while its field is still checked by the kernel. -/
structure EqCert {α : Type} (a b : α) : Type where
  eq : a = b

/- Lift a proof-producing element matcher to lists.  Keeping this helper
separate avoids a nested-inductive mutual recursion in the executable code. -/
def sameListWith
    (same : (a b : SExpr) → Option (EqCert a b)) :
    (xs ys : List SExpr) → Option (EqCert xs ys)
  | [], [] => some ⟨rfl⟩
  | x :: xs, y :: ys =>
      match same x y with
      | none => none
      | some hxy =>
          match sameListWith same xs ys with
          | some hrest => some ⟨by cases hxy.eq; cases hrest.eq; rfl⟩
          | none => none
  | _, _ => none

/- Return a kernel-checked certificate when two SMT expressions have exactly
the same syntax.  Fuel bounds compiler work only: exhaustion merely forgoes
the optimization.  No lawfulness assumption about `BEq` enters soundness. -/
def same? : (fuel : Nat) → (a b : SExpr) → Option (EqCert a b)
  | 0, _, _ => none
  | _ + 1, .sym x, .sym y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .int x, .int y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .bytes x, .bytes y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .dataLit x, .dataLit y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .dataListLit x, .dataListLit y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .dataPairListLit x, .dataPairListLit y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .constListLit x, .constListLit y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .bool x, .bool y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | _ + 1, .str x, .str y =>
      if h : x = y then some ⟨by cases h; rfl⟩ else none
  | fuel + 1, .app f xs, .app g ys =>
      if hf : f = g then
        match sameListWith (same? fuel) xs ys with
        | some hargs => some ⟨by cases hf; cases hargs.eq; rfl⟩
        | none => none
      else none
  | fuel + 1, .ite c t e, .ite c' t' e' =>
      match same? fuel c c' with
      | none => none
      | some hc =>
          match same? fuel t t' with
          | none => none
          | some ht =>
              match same? fuel e e' with
              | some he => some ⟨by cases hc.eq; cases ht.eq; cases he.eq; rfl⟩
              | none => none
  | _ + 1, _, _ => none

/--
Equality specialized for values that are already protected by a successful
typed projection.  Equal syntax denotes the same projected value, so the
result can be emitted as `true`; the soundness lemmas in
`Moist.SMT.Soundness.Foundations` deliberately use this only after proving
both operands evaluate at the required SMT sort.
-/
def reflexiveEqFuel : Nat := 128

def reflexiveEq (a b : SExpr) : SExpr :=
  match same? reflexiveEqFuel a b with
  | some _ => trueE
  | none => Moist.SMT.Expr.eq a b

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

/-! ## Fixed SMT prelude

`Val` is only the first-order SMT representation of encodable UPLC values.
Higher-order runtime values (closures, delays and partial builtins) stay in the
Lean-side symbolic domain and are eliminated by fueled symbolic evaluation before
the final query is emitted.
-/

private def bytesCorePrelude : List Moist.SMT.Command :=
  [.raw "(define-sort Bytes () (Seq Int))"]

private def stringCorePrelude : List Moist.SMT.Command :=
  [.raw "(define-sort UString () (Seq Int))"]

private def datatypeCorePrelude : List Moist.SMT.Command :=
  [ .raw "(declare-sort G1 0)"
  , .raw "(declare-sort G2 0)"
  , .raw "(declare-sort MlResult 0)"
  , .declareConst "g1_default" .g1
  , .declareConst "g2_default" .g2
  , .declareConst "ml_default" .ml
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
      "    (VString (unVString UString))\n" ++
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
  ]

private def integerDivisionSupportPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun same_sign ((a Int) (b Int)) Bool (= (>= a 0) (>= b 0)))"
  , .raw "(define-fun abs_int ((a Int)) Int (ite (< a 0) (- 0 a) a))"
  ]

private def bytesValidationPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun-rec bytes_valid_at ((bs Bytes) (i Int)) Bool (ite (>= i (seq.len bs)) true (and (>= (seq.nth bs i) 0) (<= (seq.nth bs i) 255) (bytes_valid_at bs (+ i 1)))))"
  , .raw "(define-fun bytes_valid ((bs Bytes)) Bool (bytes_valid_at bs 0))"
  ]

private def stringValidationPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun unicode_scalar ((cp Int)) Bool (and (<= 0 cp) (<= cp 1114111) (or (< cp 55296) (> cp 57343))))"
  , .raw "(define-fun-rec ustring_valid_at ((s UString) (i Int)) Bool (ite (>= i (seq.len s)) true (and (unicode_scalar (seq.nth s i)) (ustring_valid_at s (+ i 1)))))"
  , .raw "(define-fun ustring_valid ((s UString)) Bool (ustring_valid_at s 0))"
  ]

private def dataValidationPrelude : List Moist.SMT.Command :=
  [ .raw <|
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
      "       (and ((_ is VString) v) (ustring_valid (unVString v)))\n" ++
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
      "       (and ((_ is VString) v) (ustring_valid (unVString v)))\n" ++
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
  ]

private def integerDivisionBodyPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun uplc_tdiv ((a Int) (b Int)) Int (ite (same_sign a b) (div (abs_int a) (abs_int b)) (- 0 (div (abs_int a) (abs_int b)))))"
  , .raw "(define-fun uplc_tmod ((a Int) (b Int)) Int (- a (* b (uplc_tdiv a b))))"
  , .raw "(define-fun uplc_div ((a Int) (b Int)) Int (let ((q (uplc_tdiv a b)) (r (uplc_tmod a b))) (ite (or (= r 0) (same_sign a b)) q (- q 1))))"
  , .raw "(define-fun uplc_mod ((a Int) (b Int)) Int (- a (* b (uplc_div a b))))"
  ]

private def bytesOrderingPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun-rec bytes_lt_at ((a Bytes) (b Bytes) (i Int) (n Int)) Bool (ite (>= i n) (< (seq.len a) (seq.len b)) (ite (< (seq.nth a i) (seq.nth b i)) true (ite (> (seq.nth a i) (seq.nth b i)) false (bytes_lt_at a b (+ i 1) n)))))"
  , .raw "(define-fun bytes_lt ((a Bytes) (b Bytes)) Bool (bytes_lt_at a b 0 (ite (< (seq.len a) (seq.len b)) (seq.len a) (seq.len b))))"
  , .raw "(define-fun bytes_le ((a Bytes) (b Bytes)) Bool (or (= a b) (bytes_lt a b)))"
  ]

private def listPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun-rec vlist_length ((xs ValList)) Int (ite ((_ is VNil) xs) 0 (+ 1 (vlist_length (vtail xs)))))"
  , .raw "(define-fun-rec dlist_length ((xs DataList)) Int (ite ((_ is DNil) xs) 0 (+ 1 (dlist_length (dtail xs)))))"
  , .raw "(define-fun-rec vlist_drop ((n Int) (xs ValList)) ValList (ite (or (<= n 0) ((_ is VNil) xs)) xs (vlist_drop (- n 1) (vtail xs))))"
  , .raw "(define-fun-rec dlist_drop ((n Int) (xs DataList)) DataList (ite (or (<= n 0) ((_ is DNil) xs)) xs (dlist_drop (- n 1) (dtail xs))))"
  , .raw "(define-fun-rec vlist_index ((n Int) (xs ValList)) Val (ite (<= n 0) (vhead xs) (vlist_index (- n 1) (vtail xs))))"
  ]

private def utf8Prelude : List Moist.SMT.Command :=
  [ .raw "(define-fun utf8_cont ((b Int)) Bool (and (<= 128 b) (<= b 191)))"
  , .raw <|
      "(define-fun-rec valid_utf8_at ((bs Bytes) (i Int)) Bool\n" ++
      "  (ite (>= i (seq.len bs)) true\n" ++
      "    (let ((b0 (seq.nth bs i)) (n (seq.len bs)))\n" ++
      "      (or\n" ++
      "        (and (<= 0 b0) (<= b0 127) (valid_utf8_at bs (+ i 1)))\n" ++
      "        (and (<= 194 b0) (<= b0 223) (< (+ i 1) n)\n" ++
      "             (utf8_cont (seq.nth bs (+ i 1))) (valid_utf8_at bs (+ i 2)))\n" ++
      "        (and (= b0 224) (< (+ i 2) n)\n" ++
      "             (<= 160 (seq.nth bs (+ i 1))) (<= (seq.nth bs (+ i 1)) 191)\n" ++
      "             (utf8_cont (seq.nth bs (+ i 2))) (valid_utf8_at bs (+ i 3)))\n" ++
      "        (and (or (and (<= 225 b0) (<= b0 236)) (and (<= 238 b0) (<= b0 239)))\n" ++
      "             (< (+ i 2) n) (utf8_cont (seq.nth bs (+ i 1)))\n" ++
      "             (utf8_cont (seq.nth bs (+ i 2))) (valid_utf8_at bs (+ i 3)))\n" ++
      "        (and (= b0 237) (< (+ i 2) n)\n" ++
      "             (<= 128 (seq.nth bs (+ i 1))) (<= (seq.nth bs (+ i 1)) 159)\n" ++
      "             (utf8_cont (seq.nth bs (+ i 2))) (valid_utf8_at bs (+ i 3)))\n" ++
      "        (and (= b0 240) (< (+ i 3) n)\n" ++
      "             (<= 144 (seq.nth bs (+ i 1))) (<= (seq.nth bs (+ i 1)) 191)\n" ++
      "             (utf8_cont (seq.nth bs (+ i 2))) (utf8_cont (seq.nth bs (+ i 3)))\n" ++
      "             (valid_utf8_at bs (+ i 4)))\n" ++
      "        (and (<= 241 b0) (<= b0 243) (< (+ i 3) n)\n" ++
      "             (utf8_cont (seq.nth bs (+ i 1))) (utf8_cont (seq.nth bs (+ i 2)))\n" ++
      "             (utf8_cont (seq.nth bs (+ i 3))) (valid_utf8_at bs (+ i 4)))\n" ++
      "        (and (= b0 244) (< (+ i 3) n)\n" ++
      "             (<= 128 (seq.nth bs (+ i 1))) (<= (seq.nth bs (+ i 1)) 143)\n" ++
      "             (utf8_cont (seq.nth bs (+ i 2))) (utf8_cont (seq.nth bs (+ i 3)))\n" ++
      "             (valid_utf8_at bs (+ i 4)))))))"
  , .raw "(define-fun valid_utf8 ((bs Bytes)) Bool (valid_utf8_at bs 0))"
  , .raw <|
      "(define-fun utf8_encode_scalar ((cp Int)) Bytes\n" ++
      "  (ite (<= cp 127) (seq.unit cp)\n" ++
      "    (ite (<= cp 2047)\n" ++
      "      (seq.++ (seq.unit (+ 192 (div cp 64))) (seq.unit (+ 128 (mod cp 64))))\n" ++
      "      (ite (<= cp 65535)\n" ++
      "        (seq.++ (seq.unit (+ 224 (div cp 4096)))\n" ++
      "          (seq.++ (seq.unit (+ 128 (mod (div cp 64) 64))) (seq.unit (+ 128 (mod cp 64)))))\n" ++
      "        (seq.++ (seq.unit (+ 240 (div cp 262144)))\n" ++
      "          (seq.++ (seq.unit (+ 128 (mod (div cp 4096) 64)))\n" ++
      "            (seq.++ (seq.unit (+ 128 (mod (div cp 64) 64))) (seq.unit (+ 128 (mod cp 64))))))))))"
  , .raw <|
      "(define-fun-rec uplc_encodeUtf8_at ((s UString) (i Int)) Bytes\n" ++
      "  (ite (>= i (seq.len s)) (as seq.empty Bytes)\n" ++
      "    (seq.++ (utf8_encode_scalar (seq.nth s i)) (uplc_encodeUtf8_at s (+ i 1)))))"
  , .raw "(define-fun uplc_encodeUtf8 ((s UString)) Bytes (uplc_encodeUtf8_at s 0))"
  , .raw <|
      "(define-fun utf8_decode_scalar ((bs Bytes) (i Int)) Int\n" ++
      "  (let ((b0 (seq.nth bs i)))\n" ++
      "    (ite (<= b0 127) b0\n" ++
      "      (ite (<= b0 223) (+ (* (- b0 192) 64) (- (seq.nth bs (+ i 1)) 128))\n" ++
      "        (ite (<= b0 239)\n" ++
      "          (+ (* (- b0 224) 4096) (* (- (seq.nth bs (+ i 1)) 128) 64) (- (seq.nth bs (+ i 2)) 128))\n" ++
      "          (+ (* (- b0 240) 262144) (* (- (seq.nth bs (+ i 1)) 128) 4096)\n" ++
      "             (* (- (seq.nth bs (+ i 2)) 128) 64) (- (seq.nth bs (+ i 3)) 128)))))))"
  , .raw "(define-fun utf8_width ((b0 Int)) Int (ite (<= b0 127) 1 (ite (<= b0 223) 2 (ite (<= b0 239) 3 4))))"
  , .raw <|
      "(define-fun-rec uplc_decodeUtf8_at ((bs Bytes) (i Int)) UString\n" ++
      "  (ite (>= i (seq.len bs)) (as seq.empty UString)\n" ++
      "    (seq.++ (seq.unit (utf8_decode_scalar bs i))\n" ++
      "      (uplc_decodeUtf8_at bs (+ i (utf8_width (seq.nth bs i)))))))"
  , .raw "(define-fun uplc_decodeUtf8 ((bs Bytes)) UString (uplc_decodeUtf8_at bs 0))"
  ]

/-- The Plutus V3 byte operations share power, bit, integer/byte conversion,
and traversal helpers heavily enough that one dependency-closed family is
both safer and smaller than the former unconditional prelude. -/
private def advancedBytesPrelude : List Moist.SMT.Command :=
  [ .raw "(define-fun-rec uplc_pow_nat ((base Int) (exponent Int)) Int (ite (<= exponent 0) 1 (* base (uplc_pow_nat base (- exponent 1)))))"
  , .raw "(define-fun uplc_pow2 ((exponent Int)) Int (uplc_pow_nat 2 exponent))"
  , .raw "(define-fun uplc_byte_bit ((byte Int) (bit Int)) Int (mod (div byte (uplc_pow2 bit)) 2))"
  , .raw <|
      "(define-fun uplc_byte_and ((a Int) (b Int)) Int " ++
      "(+ (* 1 (uplc_byte_bit a 0) (uplc_byte_bit b 0)) " ++
      "(* 2 (uplc_byte_bit a 1) (uplc_byte_bit b 1)) " ++
      "(* 4 (uplc_byte_bit a 2) (uplc_byte_bit b 2)) " ++
      "(* 8 (uplc_byte_bit a 3) (uplc_byte_bit b 3)) " ++
      "(* 16 (uplc_byte_bit a 4) (uplc_byte_bit b 4)) " ++
      "(* 32 (uplc_byte_bit a 5) (uplc_byte_bit b 5)) " ++
      "(* 64 (uplc_byte_bit a 6) (uplc_byte_bit b 6)) " ++
      "(* 128 (uplc_byte_bit a 7) (uplc_byte_bit b 7))))"
  , .raw <|
      "(define-fun uplc_byte_or ((a Int) (b Int)) Int " ++
      "(+ (* 1 (ite (> (+ (uplc_byte_bit a 0) (uplc_byte_bit b 0)) 0) 1 0)) " ++
      "(* 2 (ite (> (+ (uplc_byte_bit a 1) (uplc_byte_bit b 1)) 0) 1 0)) " ++
      "(* 4 (ite (> (+ (uplc_byte_bit a 2) (uplc_byte_bit b 2)) 0) 1 0)) " ++
      "(* 8 (ite (> (+ (uplc_byte_bit a 3) (uplc_byte_bit b 3)) 0) 1 0)) " ++
      "(* 16 (ite (> (+ (uplc_byte_bit a 4) (uplc_byte_bit b 4)) 0) 1 0)) " ++
      "(* 32 (ite (> (+ (uplc_byte_bit a 5) (uplc_byte_bit b 5)) 0) 1 0)) " ++
      "(* 64 (ite (> (+ (uplc_byte_bit a 6) (uplc_byte_bit b 6)) 0) 1 0)) " ++
      "(* 128 (ite (> (+ (uplc_byte_bit a 7) (uplc_byte_bit b 7)) 0) 1 0))))"
  , .raw <|
      "(define-fun uplc_byte_xor ((a Int) (b Int)) Int " ++
      "(+ (* 1 (mod (+ (uplc_byte_bit a 0) (uplc_byte_bit b 0)) 2)) " ++
      "(* 2 (mod (+ (uplc_byte_bit a 1) (uplc_byte_bit b 1)) 2)) " ++
      "(* 4 (mod (+ (uplc_byte_bit a 2) (uplc_byte_bit b 2)) 2)) " ++
      "(* 8 (mod (+ (uplc_byte_bit a 3) (uplc_byte_bit b 3)) 2)) " ++
      "(* 16 (mod (+ (uplc_byte_bit a 4) (uplc_byte_bit b 4)) 2)) " ++
      "(* 32 (mod (+ (uplc_byte_bit a 5) (uplc_byte_bit b 5)) 2)) " ++
      "(* 64 (mod (+ (uplc_byte_bit a 6) (uplc_byte_bit b 6)) 2)) " ++
      "(* 128 (mod (+ (uplc_byte_bit a 7) (uplc_byte_bit b 7)) 2))))"
  , .raw <|
      "(define-fun uplc_byte_binop ((op Int) (a Int) (b Int)) Int " ++
      "(ite (= op 0) (uplc_byte_and a b) (ite (= op 1) (uplc_byte_or a b) (uplc_byte_xor a b))))"
  , .raw <|
      "(define-fun-rec uplc_bitwise_go ((op Int) (pad Bool) (a Bytes) (b Bytes) (i Int) (n Int)) Bytes " ++
      "(ite (>= i n) (as seq.empty Bytes) " ++
      "(let ((pad-byte (ite (= op 0) 255 0))) " ++
      "(seq.++ (seq.unit (uplc_byte_binop op " ++
      "(ite (< i (seq.len a)) (seq.nth a i) pad-byte) " ++
      "(ite (< i (seq.len b)) (seq.nth b i) pad-byte))) " ++
      "(uplc_bitwise_go op pad a b (+ i 1) n)))))"
  , .raw <|
      "(define-fun uplc_bitwise ((op Int) (pad Bool) (a Bytes) (b Bytes)) Bytes " ++
      "(uplc_bitwise_go op pad a b 0 (ite pad " ++
      "(ite (> (seq.len a) (seq.len b)) (seq.len a) (seq.len b)) " ++
      "(ite (< (seq.len a) (seq.len b)) (seq.len a) (seq.len b)))))"
  , .raw "(define-fun uplc_andByteString ((pad Bool) (a Bytes) (b Bytes)) Bytes (uplc_bitwise 0 pad a b))"
  , .raw "(define-fun uplc_orByteString ((pad Bool) (a Bytes) (b Bytes)) Bytes (uplc_bitwise 1 pad a b))"
  , .raw "(define-fun uplc_xorByteString ((pad Bool) (a Bytes) (b Bytes)) Bytes (uplc_bitwise 2 pad a b))"
  , .raw <|
      "(define-fun-rec uplc_complement_go ((bs Bytes) (i Int)) Bytes " ++
      "(ite (>= i (seq.len bs)) (as seq.empty Bytes) " ++
      "(seq.++ (seq.unit (- 255 (seq.nth bs i))) (uplc_complement_go bs (+ i 1)))))"
  , .raw "(define-fun uplc_complementByteString ((bs Bytes)) Bytes (uplc_complement_go bs 0))"
  , .raw <|
      "(define-fun uplc_readBit ((bs Bytes) (index Int)) Bool " ++
      "(let ((byte-index (- (- (seq.len bs) 1) (div index 8))) (bit-index (mod index 8))) " ++
      "(= (uplc_byte_bit (seq.nth bs byte-index) bit-index) 1)))"
  , .raw <|
      "(define-fun uplc_readBit_defined ((bs Bytes) (index Int)) Bool " ++
      "(and (>= index 0) (< index (* (seq.len bs) 8))))"
  , .raw <|
      "(define-fun uplc_set_bit ((bs Bytes) (index Int) (value Bool)) Bytes " ++
      "(let ((byte-index (- (- (seq.len bs) 1) (div index 8))) (bit-index (mod index 8))) " ++
      "(let ((old (seq.nth bs byte-index)) (mask (uplc_pow2 bit-index))) " ++
      "(let ((updated (ite value " ++
      "(ite (= (uplc_byte_bit old bit-index) 0) (+ old mask) old) " ++
      "(ite (= (uplc_byte_bit old bit-index) 1) (- old mask) old)))) " ++
      "(seq.++ (seq.extract bs 0 byte-index) " ++
      "(seq.++ (seq.unit updated) " ++
      "(seq.extract bs (+ byte-index 1) (- (- (seq.len bs) byte-index) 1))))))))"
  , .raw <|
      "(define-fun-rec uplc_writeBits_defined_go ((bs Bytes) (indices ValList)) Bool " ++
      "(ite ((_ is VNil) indices) true " ++
      "(let ((head (vhead indices))) " ++
      "(ite ((_ is VInt) head) " ++
      "(let ((index (unVInt head))) " ++
      "(and (>= index 0) (< index (* (seq.len bs) 8)) " ++
      "(uplc_writeBits_defined_go bs (vtail indices)))) false))))"
  , .raw <|
      "(define-fun-rec uplc_writeBits_go ((bs Bytes) (indices ValList) (value Bool)) Bytes " ++
      "(ite ((_ is VNil) indices) bs " ++
      "(uplc_writeBits_go (uplc_set_bit bs (unVInt (vhead indices)) value) (vtail indices) value)))"
  , .raw <|
      "(define-fun uplc_writeBits_defined ((bs Bytes) (indices ValList) (value Bool)) Bool " ++
      "(uplc_writeBits_defined_go bs indices))"
  , .raw <|
      "(define-fun uplc_writeBits ((bs Bytes) (indices ValList) (value Bool)) Bytes " ++
      "(uplc_writeBits_go bs indices value))"
  , .raw <|
      "(define-fun-rec uplc_replicateByte ((count Int) (byte Int)) Bytes " ++
      "(ite (<= count 0) (as seq.empty Bytes) " ++
      "(seq.++ (seq.unit byte) (uplc_replicateByte (- count 1) byte))))"
  , .raw <|
      "(define-fun uplc_replicateByte_defined ((count Int) (byte Int)) Bool " ++
      "(and (>= count 0) (<= count 8192) (>= byte 0) (<= byte 255)))"
  , .raw <|
      "(define-fun-rec uplc_bytes_to_int_be_go ((bs Bytes) (i Int) (acc Int)) Int " ++
      "(ite (>= i (seq.len bs)) acc " ++
      "(uplc_bytes_to_int_be_go bs (+ i 1) (+ (* acc 256) (seq.nth bs i)))))"
  , .raw <|
      "(define-fun-rec uplc_bytes_to_int_le_go ((bs Bytes) (i Int) (base Int) (acc Int)) Int " ++
      "(ite (>= i (seq.len bs)) acc " ++
      "(uplc_bytes_to_int_le_go bs (+ i 1) (* base 256) (+ acc (* (seq.nth bs i) base)))))"
  , .raw <|
      "(define-fun uplc_byteStringToInteger ((endian Bool) (bs Bytes)) Int " ++
      "(ite endian (uplc_bytes_to_int_be_go bs 0 0) (uplc_bytes_to_int_le_go bs 0 1 0)))"
  , .raw <|
      "(define-fun-rec uplc_nat_byte_length ((n Int)) Int " ++
      "(ite (<= n 0) 0 (+ 1 (uplc_nat_byte_length (div n 256)))))"
  , .raw <|
      "(define-fun-rec uplc_int_fixed_be_go ((n Int) (width Int) (i Int)) Bytes " ++
      "(ite (>= i width) (as seq.empty Bytes) " ++
      "(seq.++ (seq.unit (mod (div n (uplc_pow_nat 256 (- (- width i) 1))) 256)) " ++
      "(uplc_int_fixed_be_go n width (+ i 1)))))"
  , .raw <|
      "(define-fun-rec uplc_reverse_go ((bs Bytes) (i Int)) Bytes " ++
      "(ite (>= i (seq.len bs)) (as seq.empty Bytes) " ++
      "(seq.++ (seq.unit (seq.nth bs (- (- (seq.len bs) 1) i))) (uplc_reverse_go bs (+ i 1)))))"
  , .raw <|
      "(define-fun uplc_integerToByteString_defined ((endian Bool) (width Int) (n Int)) Bool " ++
      "(and (>= n 0) (>= width 0) (<= width 8192) " ++
      "(<= (uplc_nat_byte_length n) (ite (= width 0) 8192 width))))"
  , .raw <|
      "(define-fun uplc_integerToByteString ((endian Bool) (width Int) (n Int)) Bytes " ++
      "(let ((actual-width (ite (= width 0) (uplc_nat_byte_length n) width))) " ++
      "(let ((be (uplc_int_fixed_be_go n actual-width 0))) " ++
      "(ite endian be (uplc_reverse_go be 0)))))"
  , .raw <|
      "(define-fun uplc_shiftByteString ((bs Bytes) (amount Int)) Bytes " ++
      "(ite (= (seq.len bs) 0) bs " ++
      "(let ((bits (* (seq.len bs) 8)) (absolute (ite (< amount 0) (- amount) amount))) " ++
      "(ite (>= absolute bits) (uplc_replicateByte (seq.len bs) 0) " ++
      "(ite (= amount 0) bs " ++
      "(let ((number (uplc_bytes_to_int_be_go bs 0 0)) (modulus (uplc_pow2 bits))) " ++
      "(uplc_int_fixed_be_go (ite (> amount 0) " ++
      "(mod (* number (uplc_pow2 amount)) modulus) " ++
      "(div number (uplc_pow2 (- amount)))) (seq.len bs) 0)))))))"
  , .raw <|
      "(define-fun uplc_rotateByteString ((bs Bytes) (amount Int)) Bytes " ++
      "(ite (= (seq.len bs) 0) bs " ++
      "(let ((bits (* (seq.len bs) 8))) " ++
      "(let ((rotation (mod amount bits))) " ++
      "(ite (= rotation 0) bs " ++
      "(let ((number (uplc_bytes_to_int_be_go bs 0 0)) (modulus (uplc_pow2 bits))) " ++
      "(uplc_int_fixed_be_go (mod (+ (* number (uplc_pow2 rotation)) " ++
      "(div number (uplc_pow2 (- bits rotation)))) modulus) (seq.len bs) 0)))))))"
  , .raw <|
      "(define-fun uplc_popcount_byte ((byte Int)) Int " ++
      "(+ (uplc_byte_bit byte 0) (uplc_byte_bit byte 1) (uplc_byte_bit byte 2) " ++
      "(uplc_byte_bit byte 3) (uplc_byte_bit byte 4) (uplc_byte_bit byte 5) " ++
      "(uplc_byte_bit byte 6) (uplc_byte_bit byte 7)))"
  , .raw <|
      "(define-fun-rec uplc_countSetBits_go ((bs Bytes) (i Int) (acc Int)) Int " ++
      "(ite (>= i (seq.len bs)) acc " ++
      "(uplc_countSetBits_go bs (+ i 1) (+ acc (uplc_popcount_byte (seq.nth bs i))))))"
  , .raw "(define-fun uplc_countSetBits ((bs Bytes)) Int (uplc_countSetBits_go bs 0 0))"
  , .raw <|
      "(define-fun-rec uplc_findFirstSetBit_go ((bs Bytes) (index Int) (total Int)) Int " ++
      "(ite (>= index total) (- 1) " ++
      "(ite (uplc_readBit bs index) index (uplc_findFirstSetBit_go bs (+ index 1) total))))"
  , .raw <|
      "(define-fun uplc_findFirstSetBit ((bs Bytes)) Int " ++
      "(uplc_findFirstSetBit_go bs 0 (* (seq.len bs) 8)))"
  ]

private def expModPrelude : List Moist.SMT.Command :=
  [ .raw <|
      "(define-fun-rec uplc_gcd ((a Int) (b Int)) Int " ++
      "(ite (= b 0) a (uplc_gcd b (mod a b))))"
  , .raw <|
      "(define-fun-rec uplc_inverse_coeff_go ((r Int) (new-r Int) (t Int) (new-t Int)) Int " ++
      "(ite (= new-r 0) t " ++
      "(uplc_inverse_coeff_go new-r (mod r new-r) new-t (- t (* (div r new-r) new-t)))))"
  , .raw <|
      "(define-fun uplc_normalize_mod ((value Int) (modulus Int)) Int " ++
      "(mod value modulus))"
  , .raw <|
      "(define-fun uplc_mod_inverse ((value Int) (modulus Int)) Int " ++
      "(mod (uplc_inverse_coeff_go modulus (uplc_normalize_mod value modulus) 0 1) modulus))"
  , .raw <|
      "(define-fun-rec uplc_mod_pow_go ((base Int) (exponent Int) (acc Int) (modulus Int)) Int " ++
      "(ite (<= exponent 0) (mod acc modulus) " ++
      "(uplc_mod_pow_go (mod (* base base) modulus) (div exponent 2) " ++
      "(ite (= (mod exponent 2) 1) (mod (* acc base) modulus) acc) modulus)))"
  , .raw <|
      "(define-fun uplc_mod_pow ((base Int) (exponent Int) (modulus Int)) Int " ++
      "(ite (= modulus 1) 0 " ++
      "(uplc_mod_pow_go (uplc_normalize_mod base modulus) exponent 1 modulus)))"
  , .raw <|
      "(define-fun uplc_expModInteger_defined ((base Int) (exponent Int) (modulus Int)) Bool " ++
      "(and (> modulus 0) (or (= modulus 1) (or (>= exponent 0) " ++
      "(= (uplc_gcd (uplc_normalize_mod base modulus) modulus) 1)))))"
  , .raw <|
      "(define-fun uplc_expModInteger ((base Int) (exponent Int) (modulus Int)) Int " ++
      "(ite (= modulus 1) 0 (ite (= exponent 0) 1 " ++
      "(ite (> exponent 0) (uplc_mod_pow base exponent modulus) " ++
      "(uplc_mod_pow (uplc_mod_inverse base modulus) (- exponent) modulus)))))"
  ]

/-! ## Demand-driven SMT prelude

The historical production renderer emitted every helper above for every
query.  Most refinement queries use only integer/Boolean operations, yet paid
the parsing and solver-registration cost of recursive UTF-8, byte-wise,
list, and modular-arithmetic definitions.

The named sections below replace positional slicing of one monolithic list.
`prelude` and `preludeForAssertions` both traverse the same canonical section
order, so adding or moving a helper cannot silently shift every later family.
The dependency selector requests a section exactly when an assertion mentions
one of its exported or internal symbols.  Base sorts are selected as well:
integer/Boolean-only refinements need no custom SMT sort, byte and string
formulas need only their respective aliases, while datatype operations
conservatively retain the full core declaration block.

Keep the length regression in `Test.SMT.PreludeSlicing` in sync when changing
the full prelude.  That test also submits every selected family to Z3; the
basic and advanced builtin differential suites exercise all production
builtin encodings through this selector.
-/

inductive PreludeSection where
  | bytesCore
  | stringCore
  | datatypeCore
  | integerDivisionSupport
  | bytesValidation
  | stringValidation
  | dataValidation
  | integerDivisionBody
  | bytesOrdering
  | list
  | utf8
  | advancedBytes
  | expMod
deriving Repr, BEq

namespace PreludeSection

def commands : PreludeSection → List Moist.SMT.Command
  | .bytesCore => bytesCorePrelude
  | .stringCore => stringCorePrelude
  | .datatypeCore => datatypeCorePrelude
  | .integerDivisionSupport => integerDivisionSupportPrelude
  | .bytesValidation => bytesValidationPrelude
  | .stringValidation => stringValidationPrelude
  | .dataValidation => dataValidationPrelude
  | .integerDivisionBody => integerDivisionBodyPrelude
  | .bytesOrdering => bytesOrderingPrelude
  | .list => listPrelude
  | .utf8 => utf8Prelude
  | .advancedBytes => advancedBytesPrelude
  | .expMod => expModPrelude

/-- The one reviewed declaration order used by both full and selected
preludes.  A section may refer only to an earlier section or to itself. -/
def ordered : List PreludeSection :=
  [ .bytesCore
  , .stringCore
  , .datatypeCore
  , .integerDivisionSupport
  , .bytesValidation
  , .stringValidation
  , .dataValidation
  , .integerDivisionBody
  , .bytesOrdering
  , .list
  , .utf8
  , .advancedBytes
  , .expMod
  ]

end PreludeSection

/-- Sort aliases, opaque group sorts/defaults, and the mutually recursive
`Data`/`Val` datatype declaration. -/
def corePrelude : List Moist.SMT.Command :=
  bytesCorePrelude ++ stringCorePrelude ++ datatypeCorePrelude

/-- The full prelude is assembled from the same named sections and order as
the demand-selected prelude. -/
def prelude : List Moist.SMT.Command :=
  PreludeSection.ordered.flatMap PreludeSection.commands

private def bytesValidationNames : List String :=
  ["bytes_valid_at", "bytes_valid"]

private def stringValidationNames : List String :=
  ["unicode_scalar", "ustring_valid_at", "ustring_valid"]

private def dataValidationNames : List String :=
  [ "data_valid", "dlist_valid", "dplist_valid"
  , "val_valid", "vlist_valid", "const_val_valid", "const_vlist_valid"
  ]

private def integerDivisionNames : List String :=
  ["same_sign", "abs_int", "uplc_tdiv", "uplc_tmod", "uplc_div", "uplc_mod"]

private def bytesOrderingNames : List String :=
  ["bytes_lt_at", "bytes_lt", "bytes_le"]

private def listNames : List String :=
  ["vlist_length", "dlist_length", "vlist_drop", "dlist_drop", "vlist_index"]

private def utf8Names : List String :=
  [ "utf8_cont", "valid_utf8_at", "valid_utf8", "utf8_encode_scalar"
  , "uplc_encodeUtf8_at", "uplc_encodeUtf8", "utf8_decode_scalar", "utf8_width"
  , "uplc_decodeUtf8_at", "uplc_decodeUtf8"
  ]

private def advancedBytesNames : List String :=
  [ "uplc_pow_nat", "uplc_pow2", "uplc_byte_bit", "uplc_byte_and"
  , "uplc_byte_or", "uplc_byte_xor", "uplc_byte_binop", "uplc_bitwise_go"
  , "uplc_bitwise", "uplc_andByteString", "uplc_orByteString"
  , "uplc_xorByteString", "uplc_complement_go", "uplc_complementByteString"
  , "uplc_readBit", "uplc_readBit_defined", "uplc_set_bit"
  , "uplc_writeBits_defined_go", "uplc_writeBits_go", "uplc_writeBits_defined"
  , "uplc_writeBits", "uplc_replicateByte", "uplc_replicateByte_defined"
  , "uplc_bytes_to_int_be_go", "uplc_bytes_to_int_le_go"
  , "uplc_byteStringToInteger", "uplc_nat_byte_length", "uplc_int_fixed_be_go"
  , "uplc_reverse_go", "uplc_integerToByteString_defined"
  , "uplc_integerToByteString", "uplc_shiftByteString", "uplc_rotateByteString"
  , "uplc_popcount_byte", "uplc_countSetBits_go", "uplc_countSetBits"
  , "uplc_findFirstSetBit_go", "uplc_findFirstSetBit"
  ]

private def expModNames : List String :=
  [ "uplc_gcd", "uplc_inverse_coeff_go", "uplc_normalize_mod"
  , "uplc_mod_inverse", "uplc_mod_pow_go", "uplc_mod_pow"
  , "uplc_expModInteger_defined", "uplc_expModInteger"
  ]

private def datatypeConstructors : List String :=
  [ "DConstr", "DMap", "DList", "DI", "DB", "DNil", "DCons", "DPNil"
  , "DPCons", "VInt", "VBytes", "VString", "VBool", "VUnit", "VList"
  , "VDataList", "VPairDataList", "VPair", "VPairData", "VData", "VArray"
  , "VG1", "VG2", "VMlResult", "VConstr", "VNil", "VCons"
  ]

private def datatypeCoreNames : List String :=
  datatypeConstructors ++
    [ "dataConstrTag", "dataConstrFields", "dataMapEntries", "dataListItems"
    , "dataInt", "dataBytes", "dhead", "dtail", "dpKey", "dpValue", "dpTail"
    , "unVInt", "unVBytes", "unVString", "unVBool", "unVList"
    , "unVDataList", "unVPairDataList", "vfst", "vsnd", "pdfst", "pdsnd"
    , "unVData", "unVArray", "unVG1", "unVG2", "unVMlResult"
    , "vConstrTag", "vConstrFields", "vhead", "vtail"
    , "g1_default", "g2_default", "ml_default"
    ]

private def isDatatypeTester (name : String) : Bool :=
  datatypeConstructors.any fun constructor =>
    name == "(_ is " ++ constructor ++ ")"
structure PreludeNeeds where
  bytesCore : Bool := false
  stringCore : Bool := false
  fullCore : Bool := false
  bytesValidation : Bool := false
  stringValidation : Bool := false
  dataValidation : Bool := false
  integerDivision : Bool := false
  bytesOrdering : Bool := false
  list : Bool := false
  utf8 : Bool := false
  advancedBytes : Bool := false
  expMod : Bool := false
deriving Repr, BEq

namespace PreludeNeeds

private def all : PreludeNeeds :=
  { bytesCore := true
    stringCore := true
    fullCore := true
    bytesValidation := true
    stringValidation := true
    dataValidation := true
    integerDivision := true
    bytesOrdering := true
    list := true
    utf8 := true
    advancedBytes := true
    expMod := true }

private def merge (left right : PreludeNeeds) : PreludeNeeds :=
  { bytesCore := left.bytesCore || right.bytesCore
    stringCore := left.stringCore || right.stringCore
    fullCore := left.fullCore || right.fullCore
    bytesValidation := left.bytesValidation || right.bytesValidation
    stringValidation := left.stringValidation || right.stringValidation
    dataValidation := left.dataValidation || right.dataValidation
    integerDivision := left.integerDivision || right.integerDivision
    bytesOrdering := left.bytesOrdering || right.bytesOrdering
    list := left.list || right.list
    utf8 := left.utf8 || right.utf8
    advancedBytes := left.advancedBytes || right.advancedBytes
    expMod := left.expMod || right.expMod }

/-- Translate logical dependencies into the physical sections they require.
Keeping this mapping beside `PreludeNeeds` makes dependency closure explicit;
the emission path itself only walks `PreludeSection.ordered`. -/
def includes (needs : PreludeNeeds) : PreludeSection → Bool
  | .bytesCore => needs.bytesCore || needs.fullCore
  | .stringCore => needs.stringCore || needs.fullCore
  | .datatypeCore => needs.fullCore
  | .integerDivisionSupport | .integerDivisionBody => needs.integerDivision
  | .bytesValidation => needs.bytesValidation
  | .stringValidation => needs.stringValidation
  | .dataValidation => needs.dataValidation
  | .bytesOrdering => needs.bytesOrdering
  | .list => needs.list
  | .utf8 => needs.utf8
  | .advancedBytes => needs.advancedBytes
  | .expMod => needs.expMod

private def ofName (name : String) : PreludeNeeds :=
  let bytesValidation := bytesValidationNames.contains name
  let stringValidation := stringValidationNames.contains name
  let dataValidation := dataValidationNames.contains name
  let integerDivision := integerDivisionNames.contains name
  let bytesOrdering := bytesOrderingNames.contains name
  let list := listNames.contains name
  let utf8 := utf8Names.contains name
  let advancedBytes := advancedBytesNames.contains name
  let expMod := expModNames.contains name
  { bytesCore := bytesValidation || bytesOrdering || utf8
    stringCore := stringValidation || utf8
    fullCore := dataValidation || list || advancedBytes
    bytesValidation := bytesValidation || dataValidation
    stringValidation := stringValidation || dataValidation
    dataValidation
    integerDivision
    bytesOrdering
    list
    utf8
    advancedBytes
    expMod }

private def corelessNames : List String :=
  [ "not", "and", "or", "=>", "=", "+", "-", "*", "div", "mod"
  , "<", "<=", ">", ">=", "seq.++", "seq.unit", "seq.len", "seq.nth"
  , "seq.extract"
  ]

private def ofUnclassifiedName (name : String) : PreludeNeeds :=
  let named := ofName name
  if named != {} then named
  else if corelessNames.contains name || name.startsWith "$u$" then {}
  else if datatypeCoreNames.contains name || isDatatypeTester name then
    { fullCore := true }
  else all

private def direct : SExpr → PreludeNeeds
  | .sym "(as seq.empty Bytes)" => { bytesCore := true }
  | .sym "(as seq.empty UString)" => { stringCore := true }
  | .sym name | .app name _ => ofUnclassifiedName name
  | .bytes _ => { bytesCore := true }
  | .str _ => { stringCore := true }
  | .dataLit _ | .dataListLit _ | .dataPairListLit _ | .constListLit _ =>
      { fullCore := true }
  | .int _ | .bool _ | .ite _ _ _ => {}

private def children : SExpr → List SExpr
  | .app _ args => args
  | .ite condition thenExpr elseExpr => [condition, thenExpr, elseExpr]
  | _ => []

/-- Work-list scan with an explicit visit budget.  Generated expressions are
runtime DAGs, and a structurally recursive traversal can revisit shared nodes
exponentially often.  Hitting the generous budget conservatively requests the
full prelude, so slicing can never trade output completeness for compiler
latency. -/
private def scanLoop : Nat → List SExpr → PreludeNeeds → PreludeNeeds
  | 0, _ :: _, _ => all
  | _, [], needs => needs
  | fuel + 1, expression :: work, needs =>
      scanLoop fuel (children expression ++ work) (merge needs (direct expression))

def ofExpressions (expressions : List SExpr) : PreludeNeeds :=
  scanLoop 100000 expressions {}

end PreludeNeeds

/-- The dependency-closed prelude required by a script's logical assertions.
The selection is syntactic and deterministic; it does not trust Z3 or alter
the expressions certified by the executable SMT semantics. -/
def preludeForAssertions (assertions : List SExpr) : List Moist.SMT.Command :=
  let needs := PreludeNeeds.ofExpressions assertions
  PreludeSection.ordered.flatMap fun part =>
    if needs.includes part then part.commands else []

/-! ## Certified constant-list lengths

`ChooseList` can avoid generating an impossible alternative when a constant
list's length is statically known.  The cached length is proof-carrying: an
arbitrary caller can supply an unknown hint, but cannot attach a length to an
unrelated SMT expression.  Keeping the certificate syntactic also keeps the
compiler independent of any particular SMT model.
-/

inductive ExactConstListLength : SExpr → Nat → Prop where
  | literal (xs : List Const) :
      ExactConstListLength (.constListLit xs) xs.length
  | cons (head : SExpr) {tail : SExpr} {n : Nat}
      (h : ExactConstListLength tail n) :
      ExactConstListLength (.app "VCons" [head, tail]) (n + 1)
  | tail {xs : SExpr} {n : Nat}
      (h : ExactConstListLength xs (n + 1)) :
      ExactConstListLength (.app "vtail" [xs]) n
  | ite (condition : SExpr) {thenExpr elseExpr : SExpr} {n : Nat}
      (hThen : ExactConstListLength thenExpr n)
      (hElse : ExactConstListLength elseExpr n) :
      ExactConstListLength (.ite condition thenExpr elseExpr) n

inductive ConstListLengthHint (expr : SExpr) where
  | unknown
  | exact (length : Nat) (certificate : ExactConstListLength expr length)
deriving Repr

instance {expr : SExpr} : BEq (ConstListLengthHint expr) where
  beq a b :=
    match a, b with
    | .unknown, .unknown => true
    | .exact an _, .exact bn _ => an == bn
    | _, _ => false

namespace ConstListLengthHint

def certificate? {expr : SExpr} (hint : ConstListLengthHint expr) :
    Option { n : Nat // ExactConstListLength expr n } :=
  match hint with
  | .unknown => none
  | .exact n certificate => some ⟨n, certificate⟩

def knownLength {expr : SExpr} (hint : ConstListLengthHint expr) : Option Nat :=
  hint.certificate?.map Subtype.val

def literal (xs : List Const) : ConstListLengthHint (.constListLit xs) :=
  .exact xs.length (.literal xs)

def cons (head : SExpr) {tail : SExpr} (hint : ConstListLengthHint tail) :
    ConstListLengthHint (.app "VCons" [head, tail]) :=
  match hint.certificate? with
  | none => .unknown
  | some ⟨n, certificate⟩ =>
      .exact (n + 1) (.cons head certificate)

def tail {xs : SExpr} (hint : ConstListLengthHint xs) :
    ConstListLengthHint (.app "vtail" [xs]) :=
  match hint.certificate? with
  | none => .unknown
  | some ⟨0, _⟩ => .unknown
  | some ⟨n + 1, certificate⟩ =>
      .exact n (.tail certificate)

def ite (condition : SExpr) {thenExpr elseExpr : SExpr}
    (thenHint : ConstListLengthHint thenExpr)
    (elseHint : ConstListLengthHint elseExpr) :
    ConstListLengthHint (.ite condition thenExpr elseExpr) :=
  match thenHint.certificate?, elseHint.certificate? with
  | some ⟨thenLength, thenCertificate⟩,
      some ⟨elseLength, elseCertificate⟩ =>
      if h : thenLength = elseLength then
        .exact thenLength
          (.ite condition thenCertificate (h ▸ elseCertificate))
      else
        .unknown
  | _, _ => .unknown

end ConstListLengthHint

inductive SymConst where
  | integer : SExpr → SymConst
  | bytes : SExpr → SymConst
  | string : SExpr → SymConst
  | bool : SExpr → SymConst
  | unit : SymConst
  | data : SExpr → SymConst
  /-- A builtin constant list together with a certified known-length hint. -/
  | constList : (expr : SExpr) → ConstListLengthHint expr → SymConst
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
        x == y && hx.knownLength == hy.knownLength
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

/-! ## Outcome compaction

Lazy UPLC conditionals select delays and are forced immediately by compiled
programs.  Without compaction, every force materializes one outcome for every
symbolic branch and later continuations duplicate once for each of them.

Successful values of the same first-order representation are packed with
nested `ite`s, guarded by the disjunction of their path conditions.  Native
list sorts remain native instead of being round-tripped through the generic
`Val` datatype.  Non-encodable (higher-order) values are left untouched.
Error and timeout paths carry no value and are coalesced by disjunction.
-/

abbrev EncodedOk := SExpr × SExpr

/-- The first-order representations that can be compacted at a force join.
Keeping their SMT sorts separate is operationally important: a list
that is packed through the generic `Val` datatype must otherwise be tested and
projected again at every subsequent list builtin.  The same native-sort rule
lets recursive predicates and folds join Boolean and integer branches without
rebuilding an exponentially large `List Outcome`. -/
inductive CompactKind where
  | integer
  | bool
  | unit
  | bytes
  | string
  | data
  | constList
  | dataList
  | pairDataList
  | array
  | dyn
deriving Repr, BEq

namespace CompactKind

def encode? : CompactKind → SymVal → Option SExpr
  | .integer, .const (.integer i) => some i
  | .bool, .const (.bool b) => some b
  | .unit, .const .unit => some .trueE
  | .bytes, .const (.bytes b) => some b
  | .string, .const (.string s) => some s
  | .data, .const (.data d) => some d
  | .constList, .const (.constList xs _) => some xs
  | .dataList, .const (.dataList xs) => some xs
  | .pairDataList, .const (.pairDataList xs) => some xs
  | .array, .const (.array xs) => some xs
  | .dyn, .dyn e => some e
  | _, _ => none

def decode : CompactKind → SExpr → SymVal
  | .integer, e => .const (.integer e)
  | .bool, e => .const (.bool e)
  | .unit, _ => .const .unit
  | .bytes, e => .const (.bytes e)
  | .string, e => .const (.string e)
  | .data, e => .const (.data e)
  | .constList, e => .const (.constList e .unknown)
  | .dataList, e => .const (.dataList e)
  | .pairDataList, e => .const (.pairDataList e)
  | .array, e => .const (.array e)
  | .dyn, e => .dyn e

end CompactKind

def compactKind? : SymVal → Option CompactKind
  | .const (.integer _) => some .integer
  | .const (.bool _) => some .bool
  | .const .unit => some .unit
  | .const (.bytes _) => some .bytes
  | .const (.string _) => some .string
  | .const (.data _) => some .data
  | .const (.constList _ _) => some .constList
  | .const (.dataList _) => some .dataList
  | .const (.pairDataList _) => some .pairDataList
  | .const (.array _) => some .array
  | .dyn _ => some .dyn
  | _ => none

def encodedOks (kind : CompactKind) : List Outcome → List EncodedOk
  | [] => []
  | .ok pc v :: outs =>
      match kind.encode? v with
      | some e => (pc, e) :: encodedOks kind outs
      | none => encodedOks kind outs
  | _ :: outs => encodedOks kind outs

def nonEncodedOks : List Outcome → List Outcome
  | [] => []
  | out@(.ok _ v) :: outs =>
      match compactKind? v with
      | some _ => nonEncodedOks outs
      | none => out :: nonEncodedOks outs
  | _ :: outs => nonEncodedOks outs

def errorPcs : List Outcome → List SExpr
  | [] => []
  | .error pc :: outs => pc :: errorPcs outs
  | _ :: outs => errorPcs outs

def timeoutPcs : List Outcome → List SExpr
  | [] => []
  | .timeout pc :: outs => pc :: timeoutPcs outs
  | _ :: outs => timeoutPcs outs

/-- Merge encoded successful outcomes.  The merged path says that at least one
source path is active; the nested `ite` picks the first active source value. -/
def mergeEncodedOks : List EncodedOk → Option EncodedOk
  | [] => none
  | (pc, value) :: oks =>
      match mergeEncodedOks oks with
      | none => some (pc, value)
      | some (restPc, restValue) =>
          -- Keep the merged path and value on the same lazy discriminator.
          -- This avoids observing underspecified values in inactive selector
          -- branches in the executable SMT semantics.  If both branches are
          -- the same atomic expression, retain it directly: selecting between
          -- identical values only grows the SMT decision tree.
          some (SExpr.ite pc SExpr.trueE restPc,
            if SExpr.sameAtom value restValue then value
            else SExpr.ite pc value restValue)

structure EncodedConstListOk where
  pc : SExpr
  value : SExpr
  hint : ConstListLengthHint value
deriving Repr

namespace EncodedConstListOk

def erase (ok : EncodedConstListOk) : EncodedOk := (ok.pc, ok.value)

end EncodedConstListOk

def encodedConstListOks : List Outcome → List EncodedConstListOk
  | [] => []
  | .ok pc (.const (.constList value hint)) :: outs =>
      ⟨pc, value, hint⟩ :: encodedConstListOks outs
  | _ :: outs => encodedConstListOks outs

/-- Merge constant-list outcomes while joining their proof-carrying length
certificates.  A certificate survives exactly when both sides have the same
known length. -/
def mergeEncodedConstListOks :
    List EncodedConstListOk → Option EncodedConstListOk
  | [] => none
  | ok :: oks =>
      match mergeEncodedConstListOks oks with
      | none => some ok
      | some rest =>
          if SExpr.sameAtom ok.value rest.value then
            some {
              pc := SExpr.ite ok.pc SExpr.trueE rest.pc
              value := ok.value
              hint := ok.hint
            }
          else
            some {
              pc := SExpr.ite ok.pc SExpr.trueE rest.pc
              value := .ite ok.pc ok.value rest.value
              hint := .ite ok.pc ok.hint rest.hint
            }

def mergedDecode (kind : CompactKind) (e : SExpr) : SymVal :=
  match kind with
  | .bool => .const (.bool e)
  | .integer => .const (.integer e)
  | .unit => .const .unit
  | .bytes => .const (.bytes e)
  | .string => .const (.string e)
  | .data => .const (.data e)
  | .constList => .const (.constList e .unknown)
  | .dataList => .const (.dataList e)
  | .pairDataList => .const (.pairDataList e)
  | .array => .const (.array e)
  | .dyn => .dyn e

def mergedOkOutcome (kind : CompactKind) (outs : List Outcome) : List Outcome :=
  match kind with
  | .constList =>
      match mergeEncodedConstListOks (encodedConstListOks outs) with
      | none => []
      | some ok => [.ok ok.pc (.const (.constList ok.value ok.hint))]
  | kind =>
      match mergeEncodedOks (encodedOks kind outs) with
      | none => []
      | some (pc, value) => [.ok pc (mergedDecode kind value)]

def compactKinds : List CompactKind :=
  [.integer, .bool, .unit, .bytes, .string, .data, .constList, .dataList,
   .pairDataList, .array, .dyn]

def compactedOkOutcomes (outs : List Outcome) : List Outcome :=
  compactKinds.flatMap (fun kind => mergedOkOutcome kind outs) ++
    nonEncodedOks outs

def mergedErrorOutcome (outs : List Outcome) : List Outcome :=
  match errorPcs outs with
  | [] => []
  | pcs => [.error (SExpr.any pcs)]

def mergedTimeoutOutcome (outs : List Outcome) : List Outcome :=
  match timeoutPcs outs with
  | [] => []
  | pcs => [.timeout (SExpr.any pcs)]

/-- Remove outcomes whose path condition is syntactically false before a join.
Such an outcome can never be active in any SMT model, while retaining its
value would make `mergeEncodedOks` embed that dead value into an `ite` branch. -/
def pruneFalseOutcomes (outs : List Outcome) : List Outcome :=
  outs.filter fun out => !out.pc.isFalse

/-- Collapse redundant first-order branches while retaining every higher-order
branch.  This is applied at both semantic join points: `Force` for compiled
lazy `if`s and `Case` for constructor/tag alternatives. -/
def compactOutcomes (outs : List Outcome) : List Outcome :=
  let live := pruneFalseOutcomes outs
  compactedOkOutcomes live ++
    mergedErrorOutcome live ++ mergedTimeoutOutcome live

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
  | .const (.constList _ _) => ⟨SExpr.falseE, .app "DNil" []⟩
  | v => valueProj "VDataList" "unVDataList" (.app "DNil" []) v

def asPairDataList : SymVal → Proj SExpr
  | .const (.pairDataList xs) => Proj.pure xs
  | v => valueProj "VPairDataList" "unVPairDataList" (.app "DPNil" []) v

def asConstList : SymVal → Proj SExpr
  | .const (.constList xs _) => Proj.pure xs
  | v => valueProj "VList" "unVList" (.app "VNil" []) v

def knownConstListLength : SymVal → Option Nat
  | .const (.constList _ hint) => hint.knownLength
  | _ => none

def consConstListValue (head : SExpr) : SymVal → SymVal
  | .const (.constList tail hint) =>
      .const (.constList (.app "VCons" [head, tail]) (.cons head hint))
  | value =>
      let tail := (asConstList value).val
      .const (.constList (.app "VCons" [head, tail]) .unknown)

def tailConstListValue : SymVal → SymVal
  | .const (.constList xs hint) =>
      .const (.constList (.app "vtail" [xs]) (.tail hint))
  | value =>
      let xs := (asConstList value).val
      .const (.constList (.app "vtail" [xs]) .unknown)

/-- Select the constant-list alternatives that can be reachable at a known
length.  This is intentionally only a selector: the outcomes themselves keep
their ordinary SMT constructor guards. -/
def constListBranches (hint : Option Nat) (nilOutcome consOutcome : Outcome) :
    List Outcome :=
  match hint with
  | some 0 => [nilOutcome]
  | some (_ + 1) => [consOutcome]
  | none => [nilOutcome, consOutcome]

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
  .bytes bs

mutual
  def dataLiteral : Data → SExpr
    | d => .dataLit d

  def dataListLiteral : List Data → SExpr
    | xs => .dataListLit xs

  def dataPairListLiteral : List (Data × Data) → SExpr
    | xs => .dataPairListLit xs
end

def constLiteral : Const → SymVal
  | .Integer i => .const (.integer (.int i))
  | .ByteString bs => .const (.bytes (bytesLiteral bs))
  | .String s => .const (.string (.str s))
  | .Unit => .const .unit
  | .Bool b => .const (.bool (.bool b))
  | .ConstList xs => .const (.constList (.constListLit xs) (.literal xs))
  | .ConstDataList xs => .const (.dataList (dataListLiteral xs))
  | .ConstPairDataList xs => .const (.pairDataList (dataPairListLiteral xs))
  | .Pair (a, b) => .pair (constLiteral a) (constLiteral b)
  | .PairData (a, b) => .const (.pairData (dataLiteral a) (dataLiteral b))
  | .Data d => .const (.data (dataLiteral d))
  | .ConstArray xs => .const (.array (.constListLit xs))
  | .Bls12_381_G1_element => .const (.g1 (.sym "g1_default"))
  | .Bls12_381_G2_element => .const (.g2 (.sym "g2_default"))
  | .Bls12_381_MlResult => .const (.ml (.sym "ml_default"))

/-! ## CEK-backed ground evaluation

`SymConst` records an SMT expression, so being in the `.const` constructor does
not by itself mean an expression is ground.  This recognizer is deliberately
strict: it succeeds only for literal syntax emitted from a UPLC constant.
When every saturated argument is literal, use the executable CEK builtin
implementation as the single source of truth and re-embed its result.  This
both avoids unnecessary SMT and prevents the ground case from drifting away
from CEK while a symbolic encoding is optimized.
-/

def symValLiteral? : SymVal → Option Const
  | .const (.integer (.int i)) => some (.Integer i)
  | .const (.bytes (.bytes bs)) => some (.ByteString bs)
  | .const (.string (.str s)) => some (.String s)
  | .const (.bool (.bool b)) => some (.Bool b)
  | .const .unit => some .Unit
  | .const (.data (.dataLit d)) => some (.Data d)
  | .const (.constList (.constListLit xs) _) => some (.ConstList xs)
  | .const (.dataList (.dataListLit xs)) => some (.ConstDataList xs)
  | .const (.pairDataList (.dataPairListLit xs)) => some (.ConstPairDataList xs)
  | .const (.pairData (.dataLit a) (.dataLit b)) => some (.PairData (a, b))
  | .const (.array (.constListLit xs)) => some (.ConstArray xs)
  | .pair a b => do
      let ca ← symValLiteral? a
      let cb ← symValLiteral? b
      some (.Pair (ca, cb))
  | _ => none

def evalBuiltinStatic? (b : BuiltinFun) (args : List SymVal) : Option (List Outcome) := do
  let constArgs ← args.mapM symValLiteral?
  let cekArgs := constArgs.map Moist.CEK.CekValue.VCon
  match Moist.CEK.evalBuiltin b cekArgs with
  | some (.VCon c) => some (ok (constLiteral c))
  | some _ => none
  | none => some err

def staticOrSymbolic (b : BuiltinFun) (args : List SymVal)
    (symbolic : Unit → List Outcome) : List Outcome :=
  match evalBuiltinStatic? b args with
  | some outs => outs
  | none => symbolic ()

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
def tailFromValList (xs : SExpr) : SymVal :=
  .const (.constList (.app "vtail" [xs]) .unknown)
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
        -- An application is a first-order join after a symbolic function
        -- choice.  Compact its result before an enclosing application can
        -- multiply every function branch by every argument branch.
        compactOutcomes <| bindOut (evalSym n ρ f) fun vf =>
          bindOut (evalSym n ρ a) fun va =>
          applySym n vf va
    | n + 1, ρ, .Force t =>
        compactOutcomes <| bindOut (evalSym n ρ t) fun vt =>
          forceSym n vt
    | n + 1, ρ, .Constr tag fields =>
        bindOut (evalListSym n ρ fields) fun vals =>
          match vals with
          | .constr (.int (-1)) vs => ok (.constr (.int (Int.ofNat tag)) vs)
          | _ => err
    | n + 1, ρ, .Case scrut alts =>
        -- `Case` is a semantic join point just like forcing a lazy branch.
        -- Compact first-order alternatives before a surrounding continuation
        -- can duplicate once for every constructor/tag alternative.
        compactOutcomes <| bindOut (evalSym n ρ scrut) fun v =>
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
            | none => evalBuiltinSaturated b (va :: args)
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
            | none => evalBuiltinSaturated b args
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
    | n, ρ, .const (.constList xs _), alts =>
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
        checkedConst (Proj.map2 SExpr.intAdd (asInt a) (asInt b)) .integer
    | .SubtractInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.intSub (asInt a) (asInt b)) .integer
    | .MultiplyInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.intMul (asInt a) (asInt b)) .integer
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
    | .EqualsInteger, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asInt a) (asInt b))
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
    | .EqualsByteString, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asBytes a) (asBytes b))
    | .LessThanByteString, [b, a] => checkedBool (Proj.map2 (fun a b => .app "bytes_lt" [a, b]) (asBytes a) (asBytes b))
    | .LessThanEqualsByteString, [b, a] => checkedBool (Proj.map2 (fun a b => .app "bytes_le" [a, b]) (asBytes a) (asBytes b))

    | .Sha2_256, _ => timeout
    | .Sha3_256, _ => timeout
    | .Blake2b_256, _ => timeout
    | .VerifyEd25519Signature, _ => timeout

    | .AppendString, [b, a] => checkedConst (Proj.map2 SExpr.strAppend (asString a) (asString b)) .string
    | .EqualsString, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asString a) (asString b))
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
        let nilOutcome := .ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val)) nilCase
        let consOutcome :=
          .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val))) consCase
        let vBranches := constListBranches (knownConstListLength xs) nilOutcome consOutcome
        dBranches ++ vBranches ++ [.error (SExpr.not (SExpr.or dl.guard vl.guard))]
    | .MkCons, [tail, head] =>
        let dl := asDataList tail
        let hd := asData head
        let vl := asConstList tail
        let hv := asConstVal head
        let dataOk := SExpr.and dl.guard hd.guard
        let constOk := SExpr.and vl.guard hv.guard
        [.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
         .ok constOk (consConstListValue hv.val tail),
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
         .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
           (tailConstListValue xs),
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
    | .EqualsData, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asData a) (asData b))
    | .MkPairData, [b, a] => checked1 (Proj.map2 (fun a b => (a, b)) (asData a) (asData b)) (fun (a, b) => .const (.pairData a b))
    | .MkNilData, [u] =>
        let g := unitGuard u
        [.ok g (.const (.dataList (.app "DNil" []))), .error (SExpr.not g)]
    | .MkNilPairData, [u] =>
        let g := unitGuard u
        [.ok g (.const (.pairDataList (.app "DPNil" []))), .error (SExpr.not g)]

    | .SerializeData, _ => timeout
    | .VerifyEcdsaSecp256k1Signature, _ => timeout
    | .VerifySchnorrSecp256k1Signature, _ => timeout

    | .Keccak_256, _ => timeout
    | .Blake2b_224, _ => timeout
    | .IntegerToByteString, [n, width, endian] =>
        let p := Proj.map3 (fun endian width n => (endian, width, n)) (asBool endian) (asInt width) (asInt n)
        checked2 p fun (endian, width, n) =>
          let defined := .app "uplc_integerToByteString_defined" [endian, width, n]
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
          let defined := .app "uplc_readBit_defined" [bs, idx]
          [.ok defined (.const (.bool (.app "uplc_readBit" [bs, idx]))),
           .error (SExpr.not defined)]
    | .WriteBits, [val, idxs, bs] =>
        let p := Proj.map3 (fun bs idxs val => (bs, idxs, val)) (asBytes bs) (asConstList idxs) (asBool val)
        checked2 p fun (bs, idxs, val) =>
          let defined := .app "uplc_writeBits_defined" [bs, idxs, val]
          [.ok defined (.const (.bytes (.app "uplc_writeBits" [bs, idxs, val]))), .error (SExpr.not defined)]
    | .ReplicateByte, [byte, count] =>
        let p := Proj.map2 (fun count byte => (count, byte)) (asInt count) (asInt byte)
        checked2 p fun (count, byte) =>
          let defined := .app "uplc_replicateByte_defined" [count, byte]
          [.ok defined (.const (.bytes (.app "uplc_replicateByte" [count, byte]))),
           .error (SExpr.not defined)]
    | .ShiftByteString, [n, bs] =>
        checkedConst
          (Proj.map2 (fun bs n => .app "uplc_shiftByteString" [bs, n])
            (asBytes bs) (asInt n)) .bytes
    | .RotateByteString, [n, bs] =>
        checkedConst
          (Proj.map2 (fun bs n => .app "uplc_rotateByteString" [bs, n])
            (asBytes bs) (asInt n)) .bytes
    | .CountSetBits, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_countSetBits" [b]) .integer
    | .FindFirstSetBit, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_findFirstSetBit" [b]) .integer
    | .Ripemd_160, _ => timeout
    | .ExpModInteger, [m, e, b] =>
        let p := Proj.map3 (fun b e m => (b, e, m)) (asInt b) (asInt e) (asInt m)
        checked2 p fun (b, e, m) =>
          let defined := .app "uplc_expModInteger_defined" [b, e, m]
          [.ok defined (.const (.integer (.app "uplc_expModInteger" [b, e, m]))), .error (SExpr.not defined)]

    | .DropList, [xs, n] =>
        let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs]) (asInt n) (asConstList xs)
        let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs]) (asInt n) (asDataList xs)
        [.ok vl.guard (.const (.constList vl.val .unknown)),
         .ok dl.guard (.const (.dataList dl.val)),
         .error (SExpr.not (SExpr.or vl.guard dl.guard))]
    | .IndexArray, [idx, arr] =>
        let p := Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx)
        checked2 p fun (arr, idx) =>
          let g := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (.app "vlist_length" [arr]))
          [.ok g (.dyn (.app "vlist_index" [idx, arr])), .error (SExpr.not g)]
    | .LengthOfArray, [arr] => checkedConst ((asArray arr).map fun xs => .app "vlist_length" [xs]) .integer
    | .ListToArray, [xs] => checkedConst (asConstList xs) .array
    | .InsertCoin, _ => timeout
    | .LookupCoin, _ => timeout
    | .ScaleValue, _ => timeout
    | .UnionValue, _ => timeout
    | .ValueContains, _ => timeout
    | .ValueData, _ => timeout
    | .UnValueData, _ => timeout

    | .Bls12_381_G1_add, _ => timeout
    | .Bls12_381_G1_neg, _ => timeout
    | .Bls12_381_G1_scalarMul, _ => timeout
    | .Bls12_381_G1_equal, _ => timeout
    | .Bls12_381_G1_hashToGroup, _ => timeout
    | .Bls12_381_G1_compress, _ => timeout
    | .Bls12_381_G1_uncompress, _ => timeout
    | .Bls12_381_G2_add, _ => timeout
    | .Bls12_381_G2_neg, _ => timeout
    | .Bls12_381_G2_scalarMul, _ => timeout
    | .Bls12_381_G2_equal, _ => timeout
    | .Bls12_381_G2_hashToGroup, _ => timeout
    | .Bls12_381_G2_compress, _ => timeout
    | .Bls12_381_G2_uncompress, _ => timeout
    | .Bls12_381_millerLoop, _ => timeout
    | .Bls12_381_mulMlResult, _ => timeout
    | .Bls12_381_finalVerify, _ => timeout
    | .Bls12_381_G1_multiScalarMul, _ => timeout
    | .Bls12_381_G2_multiScalarMul, _ => timeout
    | _, _ => err

  /-- General saturated-builtin boundary.  Every fully applied builtin takes
  the same CEK-backed ground fast path; the handwritten encoding is used only
  when at least one argument is genuinely symbolic. -/
  def evalBuiltinSaturated (b : BuiltinFun) (args : List SymVal) : List Outcome :=
    staticOrSymbolic b args fun _ => evalBuiltinSym b args
end

def symDeclRequired? (name : String) (sort : Moist.SMT.SSort)
    (value : SymVal) : Option (List SExpr) :=
  match sort, value with
  | .int, .const (.integer (.sym n)) =>
      if n == name then some [] else none
  | .bool, .const (.bool (.sym n)) =>
      if n == name then some [] else none
  | .bytes, .const (.bytes (.sym n)) =>
      if n == name then some [.app "bytes_valid" [.sym n]] else none
  | .string, .const (.string (.sym n)) =>
      if n == name then some [.app "ustring_valid" [.sym n]] else none
  | .data, .const (.data (.sym n)) =>
      if n == name then some [.app "data_valid" [.sym n]] else none
  | .val, .dyn (.sym n) =>
      if n == name then some [.app "val_valid" [.sym n]] else none
  | .int, .constr (.sym n) _ =>
      if n == name then some [SExpr.ge (.sym n) (.int 0)] else none
  | _, _ => none

/-- A symbolic declaration has a sort/value shape produced by one of the
public smart constructors and contains every validity assumption needed to
decode a Z3 value into CEK. -/
def SymDeclWellFormed (name : String) (sort : Moist.SMT.SSort)
    (value : SymVal) (assumptions : List SExpr) : Prop :=
  ∃ required, symDeclRequired? name sort value = some required ∧
    ∀ e, e ∈ required → e ∈ assumptions

structure SymDecl where
  name : String
  sort : Moist.SMT.SSort
  value : SymVal
  assumptions : List SExpr := []
  wellFormed : SymDeclWellFormed name sort value assumptions
deriving Repr

namespace SymDecl

/-- Add user constraints without changing the certified declaration
sort/value shape or removing mandatory decoding assumptions. -/
def withAssumptions (d : SymDecl) (extra : List SExpr) : SymDecl :=
  { name := d.name
    sort := d.sort
    value := d.value
    assumptions := d.assumptions ++ extra
    wellFormed := by
      rcases d.wellFormed with ⟨required, hrequired, hmem⟩
      exact ⟨required, hrequired, fun e he => List.mem_append_left _ (hmem e he)⟩ }

end SymDecl

def symInt (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .int, .const (.integer (.sym n)), [], by
    exact ⟨[], by simp [symDeclRequired?], by simp⟩⟩

def symBool (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .bool, .const (.bool (.sym n)), [], by
    exact ⟨[], by simp [symDeclRequired?], by simp⟩⟩

def symBytes (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .bytes, .const (.bytes (.sym n)), [.app "bytes_valid" [.sym n]], by
    exact ⟨[.app "bytes_valid" [.sym n]], by simp [symDeclRequired?], by simp⟩⟩

def symString (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .string, .const (.string (.sym n)), [.app "ustring_valid" [.sym n]], by
    exact ⟨[.app "ustring_valid" [.sym n]], by simp [symDeclRequired?], by simp⟩⟩

def symData (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .data, .const (.data (.sym n)), [.app "data_valid" [.sym n]], by
    exact ⟨[.app "data_valid" [.sym n]], by simp [symDeclRequired?], by simp⟩⟩

def symVal (name : String) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .val, .dyn (.sym n), [.app "val_valid" [.sym n]], by
    exact ⟨[.app "val_valid" [.sym n]], by simp [symDeclRequired?], by simp⟩⟩

def symConstr (name : String) (fields : List SymVal := []) : SymDecl :=
  let n := Moist.SMT.sanitize name
  ⟨n, .int, .constr (.sym n) fields, [SExpr.ge (.sym n) (.int 0)], by
    exact ⟨[SExpr.ge (.sym n) (.int 0)], by simp [symDeclRequired?], by simp⟩⟩

def envOf (decls : List SymDecl) : List SymVal :=
  decls.map SymDecl.value

def declCommands (decls : List SymDecl) : List Moist.SMT.Command :=
  decls.map (fun d => .declareConst d.name d.sort)

def assumptionCommands (decls : List SymDecl) : List Moist.SMT.Command :=
  decls.flatMap fun d => d.assumptions.map Moist.SMT.Command.assert

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
The product compiler uses only the fixed, reviewed `z3QueryTactic`; callers of
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
