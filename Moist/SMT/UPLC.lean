import Moist.SMT.Optimize
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
def strAppend (a b : SExpr) : SExpr := .app "seq.++" [a, b]

end SExpr

/-! ## Fixed SMT prelude

`Val` is only the first-order SMT representation of encodable UPLC values.
Higher-order runtime values (closures, delays and partial builtins) stay in the
Lean-side symbolic domain and are eliminated by fueled symbolic evaluation before
the final query is emitted.
-/

def prelude : List Moist.SMT.Command :=
  [ .raw "(define-sort Bytes () (Seq Int))"
  , .raw "(define-sort UString () (Seq Int))"
  , .raw "(declare-sort G1 0)"
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
  , .raw "(define-fun same_sign ((a Int) (b Int)) Bool (= (>= a 0) (>= b 0)))"
  , .raw "(define-fun abs_int ((a Int)) Int (ite (< a 0) (- 0 a) a))"
  , .raw "(define-fun-rec bytes_valid_at ((bs Bytes) (i Int)) Bool (ite (>= i (seq.len bs)) true (and (>= (seq.nth bs i) 0) (<= (seq.nth bs i) 255) (bytes_valid_at bs (+ i 1)))))"
  , .raw "(define-fun bytes_valid ((bs Bytes)) Bool (bytes_valid_at bs 0))"
  , .raw "(define-fun unicode_scalar ((cp Int)) Bool (and (<= 0 cp) (<= cp 1114111) (or (< cp 55296) (> cp 57343))))"
  , .raw "(define-fun-rec ustring_valid_at ((s UString) (i Int)) Bool (ite (>= i (seq.len s)) true (and (unicode_scalar (seq.nth s i)) (ustring_valid_at s (+ i 1)))))"
  , .raw "(define-fun ustring_valid ((s UString)) Bool (ustring_valid_at s 0))"
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
  , .raw "(define-fun utf8_cont ((b Int)) Bool (and (<= 128 b) (<= b 191)))"
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
  , .raw "(define-fun-rec uplc_pow_nat ((base Int) (exponent Int)) Int (ite (<= exponent 0) 1 (* base (uplc_pow_nat base (- exponent 1)))))"
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
  , .raw <|
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
  | constList
  | dataList
  | dyn
deriving Repr, BEq

namespace CompactKind

def encode? : CompactKind → SymVal → Option SExpr
  | .integer, .const (.integer i) => some i
  | .bool, .const (.bool b) => some b
  | .constList, .const (.constList xs _) => some xs
  | .dataList, .const (.dataList xs) => some xs
  | .dyn, .dyn e => some e
  | _, _ => none

def decode : CompactKind → SExpr → SymVal
  | .integer, e => .const (.integer e)
  | .bool, e => .const (.bool e)
  | .constList, e => .const (.constList e .unknown)
  | .dataList, e => .const (.dataList e)
  | .dyn, e => .dyn e

end CompactKind

def compactKind? : SymVal → Option CompactKind
  | .const (.integer _) => some .integer
  | .const (.bool _) => some .bool
  | .const (.constList _ _) => some .constList
  | .const (.dataList _) => some .dataList
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
          -- branches in the executable SMT semantics.
          some (SExpr.ite pc SExpr.trueE restPc,
            SExpr.ite pc value restValue)

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
          some {
            pc := SExpr.ite ok.pc SExpr.trueE rest.pc
            value := .ite ok.pc ok.value rest.value
            hint := .ite ok.pc ok.hint rest.hint
          }

def mergedDecode (kind : CompactKind) (e : SExpr) : SymVal :=
  match kind with
  | .bool => .const (.bool e)
  | .integer => .const (.integer e)
  | .constList => .const (.constList e .unknown)
  | .dataList => .const (.dataList e)
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

def compactedOkOutcomes (outs : List Outcome) : List Outcome :=
  mergedOkOutcome .integer outs ++
    mergedOkOutcome .bool outs ++
    mergedOkOutcome .constList outs ++
    mergedOkOutcome .dataList outs ++
    mergedOkOutcome .dyn outs ++
    nonEncodedOks outs

def mergedErrorOutcome (outs : List Outcome) : List Outcome :=
  match errorPcs outs with
  | [] => []
  | pcs => [.error (SExpr.any pcs)]

def mergedTimeoutOutcome (outs : List Outcome) : List Outcome :=
  match timeoutPcs outs with
  | [] => []
  | pcs => [.timeout (SExpr.any pcs)]

/-- Collapse redundant first-order branches while retaining every higher-order
branch.  This is applied at `Force`, the join point for compiled lazy `if`s. -/
def compactOutcomes (outs : List Outcome) : List Outcome :=
  compactedOkOutcomes outs ++
    mergedErrorOutcome outs ++ mergedTimeoutOutcome outs

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
        bindOut (evalSym n ρ f) fun vf =>
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

    | .Sha2_256, _ => timeout
    | .Sha3_256, _ => timeout
    | .Blake2b_256, _ => timeout
    | .VerifyEd25519Signature, _ => timeout

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
    | .EqualsData, [b, a] => checkedBool (Proj.map2 SExpr.eq (asData a) (asData b))
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

private def symDeclRequired? (name : String) (sort : Moist.SMT.SSort)
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

/-- The declaration invariant exposes the nonnegative-tag assertion required
by an integer declaration whose value is a symbolic constructor. -/
theorem constrTagNonnegative_mem (declaration : SymDecl)
    {tag : String} {fields : List SymVal}
    (hsort : declaration.sort = .int)
    (hvalue : declaration.value = .constr (.sym tag) fields)
    (hname : tag = declaration.name) :
    SExpr.ge (.sym tag) (.int 0) ∈ declaration.assumptions := by
  rcases declaration with ⟨name, sort, value, assumptions, hwellFormed⟩
  simp only at hsort hvalue hname ⊢
  subst sort
  subst value
  subst name
  rcases hwellFormed with ⟨required, hrequired, hcontains⟩
  simp [symDeclRequired?] at hrequired
  subst required
  exact hcontains _ (by simp)

/-- Every declaration at SMT sort `Val` carries the exact validity assertion
needed to decode its model value into a CEK value. -/
theorem valValid_mem_of_sort (declaration : SymDecl)
    (hsort : declaration.sort = .val) :
    (.app "val_valid" [.sym declaration.name] : SExpr) ∈
      declaration.assumptions := by
  rcases declaration with ⟨name, sort, value, assumptions, hwellFormed⟩
  simp only at hsort ⊢
  subst sort
  rcases hwellFormed with ⟨required, hrequired, hcontains⟩
  cases value <;> simp [symDeclRequired?] at hrequired
  case dyn expression =>
    cases expression <;> simp at hrequired
    case sym symbol =>
      rcases hrequired with ⟨rfl, hrequired⟩
      subst required
      exact hcontains _ (.head _)

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

/-- Run Z3's context-aware datatype simplification and its direct SMT search
as a two-way portfolio.  Symbolic list queries vary sharply: model-producing
queries often favor the former while counterexample queries favor the latter.
This changes only solver strategy; assertions and returned models retain their
ordinary SMT meaning. -/
def z3QueryTactic : String :=
  "(par-or (then simplify ctx-solver-simplify smt) smt)"

def scriptWith (decls : List SymDecl) (assertions : List SExpr) : Moist.SMT.Script :=
  ⟨prelude ++ declCommands decls ++ assumptionCommands decls ++
    assertions.map Moist.SMT.Command.assert ++
      [.checkSatUsing z3QueryTactic, .getModel]⟩

private theorem assertions_prelude :
    prelude.filterMap Moist.SMT.Command.assertion? = [] := by
  rfl

private theorem assertions_declCommands (decls : List SymDecl) :
    (declCommands decls).filterMap Moist.SMT.Command.assertion? = [] := by
  induction decls with
  | nil => rfl
  | cons _ decls _ => simp [declCommands, Moist.SMT.Command.assertion?]

private theorem assertions_assertCommands (assertions : List SExpr) :
    (assertions.map Moist.SMT.Command.assert).filterMap
      Moist.SMT.Command.assertion? = assertions := by
  induction assertions with
  | nil => rfl
  | cons _ assertions ih =>
      simp [Moist.SMT.Command.assertion?, ih]

private theorem assertions_assumptionCommands (decls : List SymDecl) :
    (assumptionCommands decls).filterMap Moist.SMT.Command.assertion? =
      decls.flatMap SymDecl.assumptions := by
  induction decls with
  | nil => rfl
  | cons decl decls ih =>
      change
        (decl.assumptions.map Moist.SMT.Command.assert ++
          assumptionCommands decls).filterMap Moist.SMT.Command.assertion? =
        decl.assumptions ++ decls.flatMap SymDecl.assumptions
      rw [List.filterMap_append, assertions_assertCommands, ih]

/-- Purely syntactic accounting for typed assertion commands.  This theorem
does not claim that Z3 returned a model, that the model satisfies the
assertions, or that raw prelude commands have any particular semantics; those
facts belong to `Soundness.CertifiedZ3Model`. -/
theorem scriptWith_assertions (decls : List SymDecl) (assertions : List SExpr) :
    (scriptWith decls assertions).assertions =
      decls.flatMap SymDecl.assumptions ++ assertions := by
  simp only [scriptWith, Moist.SMT.Script.assertions, List.filterMap_append]
  rw [assertions_prelude, assertions_declCommands,
    assertions_assumptionCommands, assertions_assertCommands]
  simp [Moist.SMT.Command.assertion?]

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

theorem scriptForBoolTrue_assertions (fuel : Nat) (decls : List SymDecl) (t : Term) :
    (scriptForBoolTrue fuel decls t).assertions =
      decls.flatMap SymDecl.assumptions ++
        [okBoolTrueCond (evalSym fuel (envOf decls) t)] := by
  simp [scriptForBoolTrue, scriptWith_assertions]

theorem scriptForIntEq_assertions (fuel : Nat) (decls : List SymDecl)
    (t : Term) (rhs : SExpr) :
    (scriptForIntEq fuel decls t rhs).assertions =
      decls.flatMap SymDecl.assumptions ++
        [okIntEqCond (evalSym fuel (envOf decls) t) rhs] := by
  simp [scriptForIntEq, scriptWith_assertions]

theorem scriptForError_assertions (fuel : Nat) (decls : List SymDecl) (t : Term) :
    (scriptForError fuel decls t).assertions =
      decls.flatMap SymDecl.assumptions ++
        [errorCond (evalSym fuel (envOf decls) t)] := by
  simp [scriptForError, scriptWith_assertions]

end Moist.SMT.UPLC
