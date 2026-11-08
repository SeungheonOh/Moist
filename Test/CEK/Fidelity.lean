import Test.Framework
import Moist.CEK.Machine
import Moist.CEK.UplcParser
import Moist.CEK.Readback

/-! # CEK model fidelity

Programs whose outcome on the plutus-core 1.65 CEK machine is known, evaluated by
the model under both builtin semantics variants (C: PlutusV3 before PV11, E: from
PV11). Each case states the expected outcome per variant: failure, or a constant
whose value and exact type must match. The `mkcons/*` cases are the
disagreements found by the real-machine fuzzer before lists carried their
element type.
-/

namespace Test.CEK.Fidelity

open Moist.CEK Moist.CEK.UplcParser
open Moist.Plutus.Term
open Test.Framework

/-- An expected outcome: failure, or the constant of a program text. -/
inductive Outcome where
  | failure
  | value (expected : String)

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def variantName : SemVariant → String
  | .C => "C"
  | .E => "E"

private def constantOf (text : String) : IO (Const × BuiltinType) := do
  match parseUplcProgram text with
  | .ok (.Constant (c, ty)) => pure (c, ty)
  | .ok _ => throw (IO.userError s!"expected a constant program: {text}")
  | .error e => throw (IO.userError s!"parse error in expectation: {e}")

private def run (variant : SemVariant) (label program : String) (outcome : Outcome) : IO Unit := do
  let term ← match parseUplcProgram program with
    | .ok term => pure term
    | .error e => throw (IO.userError s!"{label}: parse error: {e}")
  let result := (eval (sv := variant) term (2 ^ 80) (2 ^ 80)).result
  let name := s!"{label}/{variantName variant}"
  match outcome, result with
  | .failure, .failure => pure ()
  | .failure, .success v => check s!"{name}: expected failure, got {v}" false
  | .value text, .success (.VCon c) =>
    let (expected, ty) ← constantOf text
    check s!"{name}: value {repr c} expected {repr expected}" (c == expected)
    check s!"{name}: type {repr (constType c)} expected {repr ty}" (constType c == ty)
  | .value _, .success v => check s!"{name}: expected a constant, got {v}" false
  | .value _, .failure => check s!"{name}: expected success, got failure" false
  | _, .outOfBudget => check s!"{name}: out of budget" false

/-- A case with the same outcome under both variants. -/
private def both (label program : String) (outcome : Outcome) : IO Unit := do
  run .C label program outcome
  run .E label program outcome

/-- `2^262144`, just above the `CInteger` bound, built by squaring `2^64` twelve times. -/
private def huge : String :=
  let square (t : String) := s!"[(lam x [(builtin multiplyInteger) x x]) {t}]"
  (List.range 12).foldl (fun t _ => square t) "(con integer 18446744073709551616)"

/-- A bytestring of 65537 bytes, one above the `CByteString` bound. -/
private def longBytes : String :=
  let block := "[(builtin replicateByte) (con integer 8192) (con integer 97)]"
  let twice (t : String) := s!"[(lam b [(builtin appendByteString) b b]) {t}]"
  s!"[(builtin consByteString) (con integer 98) {twice (twice (twice block))}]"

private def prog (body : String) : String := s!"(program 1.1.0 {body})"

def tests : TestTree := suite "cek-fidelity" do
  test "mkCons_checks_element_types" do
    both "mkcons/int-on-intlist"
      (prog "[(force (builtin mkCons)) (con integer 1) (con (list integer) [2])]")
      (.value (prog "(con (list integer) [1, 2])"))
    both "mkcons/int-on-intnil"
      (prog "[(force (builtin mkCons)) (con integer 1) (con (list integer) [])]")
      (.value (prog "(con (list integer) [1])"))
    both "mkcons/bool-on-intlist"
      (prog "[(force (builtin mkCons)) (con bool True) (con (list integer) [2])]") .failure
    both "mkcons/bool-on-intnil"
      (prog "[(force (builtin mkCons)) (con bool True) (con (list integer) [])]") .failure
    both "mkcons/data-on-intnil"
      (prog "[(force (builtin mkCons)) (con data (I 1)) (con (list integer) [])]") .failure
    both "mkcons/int-on-boolnil"
      (prog "[(force (builtin mkCons)) (con integer 1) (con (list bool) [])]") .failure
    both "mkcons/int-on-datanil"
      (prog "[(force (builtin mkCons)) (con integer 1) (con (list data) [])]") .failure
    both "mkcons/data-on-datanil"
      (prog "[(force (builtin mkCons)) (con data (I 1)) (con (list data) [])]")
      (.value (prog "(con (list data) [I 1])"))
    both "mkcons/pair-on-pairnil"
      (prog "[(force (builtin mkCons)) [(builtin mkPairData) (con data (I 1)) (con data (I 2))] [(builtin mkNilPairData) (con unit ())]]")
      (.value (prog "(con (list (pair data data)) [(I 1, I 2)])"))
    both "mkcons/data-on-pairnil"
      (prog "[(force (builtin mkCons)) (con data (I 1)) [(builtin mkNilPairData) (con unit ())]]")
      .failure
    both "mkcons/list-on-nested"
      (prog "[(force (builtin mkCons)) (con (list integer) []) (con (list (list integer)) [])]")
      (.value (prog "(con (list (list integer)) [[]])"))
    both "mkcons/boollist-on-nested"
      (prog "[(force (builtin mkCons)) (con (list bool) []) (con (list (list integer)) [])]")
      .failure
  test "list_types_survive" do
    both "head/nested-empty"
      (prog "[(force (builtin headList)) (con (list (list integer)) [[]])]")
      (.value (prog "(con (list integer) [])"))
    both "tail/integer"
      (prog "[(force (builtin tailList)) (con (list integer) [1])]")
      (.value (prog "(con (list integer) [])"))
    both "unMapData"
      (prog "[(builtin unMapData) (con data (Map [(I 0, I 1)]))]")
      (.value (prog "(con (list (pair data data)) [(I 0, I 1)])"))
    both "mkNilPairData"
      (prog "[(builtin mkNilPairData) (con unit ())]")
      (.value (prog "(con (list (pair data data)) [])"))
    both "case/list-tail-type"
      (prog "(case (con (list bool) [True]) (lam h (lam t t)) (con unit ()))")
      (.value (prog "(con (list bool) [])"))
    both "listToArray"
      (prog "[(force (builtin lengthOfArray)) [(force (builtin listToArray)) (con (list bool) [])]]")
      (.value (prog "(con integer 0)"))
    both "indexArray"
      (prog "[(force (builtin indexArray)) (con (array integer) [1, 2, 3]) (con integer 1)]")
      (.value (prog "(con integer 2)"))
  test "data_builtins_require_data_lists" do
    both "constrData/intnil"
      (prog "[(builtin constrData) (con integer 0) (con (list integer) [])]") .failure
    both "listData/intlist" (prog "[(builtin listData) (con (list integer) [1])]") .failure
    both "mapData/datalist" (prog "[(builtin mapData) (con (list data) [I 1])]") .failure
    both "constrData/data"
      (prog "[(builtin constrData) (con integer 7) (con (list data) [I 1])]")
      (.value (prog "(con data (Constr 7 [I 1]))"))
    run .C "constrData/negative-tag"
      (prog "[(builtin constrData) (con integer -1) (con (list data) [])]")
      (.value (prog "(con data (Constr -1 []))"))
    run .E "constrData/negative-tag"
      (prog "[(builtin constrData) (con integer -1) (con (list data) [])]") .failure
    both "serialiseData/constr"
      (prog "[(builtin serialiseData) (con data (Constr 0 []))]")
      (.value (prog "(con bytestring #d87980)"))
    both "serialiseData/list"
      (prog "[(builtin serialiseData) (con data (List [I 1, B #00]))]")
      (.value (prog "(con bytestring #9f014100ff)"))
  test "variant_E_bounds" do
    run .C "add/beyond-bound" (prog s!"[(builtin lessThanInteger) {huge} (con integer 0)]")
      (.value (prog "(con bool False)"))
    run .E "add/beyond-bound" (prog s!"[(builtin lessThanInteger) {huge} (con integer 0)]") .failure
    both "equalsInteger/beyond-bound" (prog s!"[(builtin equalsInteger) {huge} (con integer 0)]")
      (.value (prog "(con bool False)"))
    run .C "equalsByteString/long" (prog s!"[(builtin equalsByteString) {longBytes} (con bytestring #)]")
      (.value (prog "(con bool False)"))
    run .E "equalsByteString/long" (prog s!"[(builtin equalsByteString) {longBytes} (con bytestring #)]")
      .failure
    both "equalsData/long" (prog s!"[(builtin equalsData) [(builtin bData) {longBytes}] (con data (B #))]")
      (.value (prog "(con bool False)"))
    run .C "shift/beyond-int64"
      (prog "[(builtin shiftByteString) (con bytestring #ff) (con integer 18446744073709551616)]")
      (.value (prog "(con bytestring #00)"))
    run .E "shift/beyond-int64"
      (prog "[(builtin shiftByteString) (con bytestring #ff) (con integer 18446744073709551616)]")
      .failure
    both "rotate/minBound"
      (prog "[(builtin rotateByteString) (con bytestring #0102) (con integer -9223372036854775808)]")
      (.value (prog "(con bytestring #0102)"))
    both "shift/byte-multiple"
      (prog "[(builtin shiftByteString) (con bytestring #0102) (con integer 8)]")
      (.value (prog "(con bytestring #0200)"))
    both "consByteString/256"
      (prog "[(builtin consByteString) (con integer 256) (con bytestring #)]") .failure
    both "slice/beyond-int64"
      (prog "[(builtin sliceByteString) (con integer 18446744073709551616) (con integer 1) (con bytestring #01)]")
      .failure
  test "case_on_constants" do
    both "case/list-three-branches"
      (prog "(case (con (list integer) []) (con integer 0) (con integer 1) (con integer 2))") .failure
    both "case/true-one-branch" (prog "(case (con bool True) (con integer 0))") .failure
    both "case/false-one-branch" (prog "(case (con bool False) (con integer 0))")
      (.value (prog "(con integer 0)"))
    both "case/data" (prog "(case (con data (I 0)) (con integer 0))") .failure

end Test.CEK.Fidelity
