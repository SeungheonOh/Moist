import Moist.SMT.Compiler.UPLC.Expressions

/-!
# UPLC compiler prelude

The reviewed SMT helper definitions and the demand-driven, dependency-closed
prelude selector.  This module contains emitted compiler data only; semantic
justification remains in the soundness tree.
-/

namespace Moist.SMT.UPLC

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


end Moist.SMT.UPLC

