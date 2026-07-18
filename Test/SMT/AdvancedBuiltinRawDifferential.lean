import Moist.SMT.Compiler

namespace Test.SMT.AdvancedBuiltinRawDifferential

open Moist.SMT
open Moist.SMT.UPLC
open Moist.Plutus.Term

def bytes (xs : List UInt8) : SExpr :=
  .bytes (ByteArray.mk xs.toArray)

def ints : List Int → SExpr
  | [] => .app "VNil" []
  | i :: is => .app "VCons" [.app "VInt" [.int i], ints is]

def constExpr? : Const → Option SExpr
  | .Integer i => some (.int i)
  | .ByteString bs => some (.bytes bs)
  | .Bool b => some (.bool b)
  | _ => none

structure Case where
  label : String
  builtin : BuiltinFun
  rawName : String
  /-- Arguments in ordinary source order (the raw SMT function order). -/
  sourceConsts : List Const
  rawArgs : List SExpr
  definedName? : Option String := none
  definedArgs? : Option (List SExpr) := none

def Case.formula (test : Case) : SExpr :=
  let result := Moist.CEK.evalBuiltinConst test.builtin test.sourceConsts.reverse
  let call : SExpr := .app test.rawName test.rawArgs
  let defined? := test.definedName?.map (fun name =>
    (.app name (test.definedArgs?.getD test.rawArgs) : SExpr))
  match result, defined? with
  | some constant, some defined =>
      match constExpr? constant with
      | some expected => SExpr.all [defined, SExpr.eq call expected]
      | none => .bool false
  | none, some defined => SExpr.not defined
  | some constant, none =>
      match constExpr? constant with
      | some expected => SExpr.eq call expected
      | none => .bool false
  | none, none => .bool false

def byteSamples : List (List UInt8) :=
  [[], [0], [1], [0x55], [0xff], [0, 0xff], [0x12, 0x34], [0xff, 0, 0x81]]

def intToCases : List Case :=
  ([-1, 0, 1, 255, 256, 257, 65535, 65536] : List Int).flatMap fun n =>
    ([-1, 0, 1, 2, 3, 8, 8193] : List Int).flatMap fun width =>
      [false, true].map fun endian =>
        { label := s!"itobs-{endian}-{width}-{n}"
          builtin := .IntegerToByteString
          rawName := "uplc_integerToByteString"
          sourceConsts := [.Bool endian, .Integer width, .Integer n]
          rawArgs := [.bool endian, .int width, .int n]
          definedName? := some "uplc_integerToByteString_defined" }

def bsToCases : List Case :=
  byteSamples.flatMap fun xs => [false, true].map fun endian =>
    let ba := ByteArray.mk xs.toArray
    { label := s!"bstoi-{endian}-{xs.length}"
      builtin := .ByteStringToInteger
      rawName := "uplc_byteStringToInteger"
      sourceConsts := [.Bool endian, .ByteString ba]
      rawArgs := [.bool endian, .bytes ba] }

def binCases (builtin : BuiltinFun) (rawName : String) : List Case :=
  byteSamples.flatMap fun ax => byteSamples.flatMap fun bx =>
    [false, true].map fun pad =>
      let a := ByteArray.mk ax.toArray
      let b := ByteArray.mk bx.toArray
      { label := s!"{rawName}-{pad}-{ax.length}-{bx.length}"
        builtin := builtin
        rawName := rawName
        sourceConsts := [.Bool pad, .ByteString a, .ByteString b]
        rawArgs := [.bool pad, .bytes a, .bytes b] }

def unaryBytesCases (builtin : BuiltinFun) (rawName : String) : List Case :=
  byteSamples.map fun xs =>
    let bs := ByteArray.mk xs.toArray
    { label := s!"{rawName}-{xs.length}"
      builtin := builtin
      rawName := rawName
      sourceConsts := [.ByteString bs]
      rawArgs := [.bytes bs] }

def readCases : List Case :=
  byteSamples.flatMap fun xs =>
    ([-2, -1, 0, 1, 7, 8, 15, 16, 23, 24] : List Int).map fun idx =>
      let bs := ByteArray.mk xs.toArray
      { label := s!"read-{xs.length}-{idx}"
        builtin := .ReadBit
        rawName := "uplc_readBit"
        sourceConsts := [.ByteString bs, .Integer idx]
        rawArgs := [.bytes bs, .int idx]
        definedName? := some "uplc_readBit_defined" }

def writeIndexSamples : List (List Int) :=
  [[], [0], [7], [8], [15], [-1], [0, 7], [0, 15], [7, 7], [0, -1]]

def writeCases : List Case :=
  byteSamples.flatMap fun xs => writeIndexSamples.flatMap fun indices =>
    [false, true].map fun value =>
      let bs := ByteArray.mk xs.toArray
      { label := s!"write-{xs.length}-{indices.length}-{value}"
        builtin := .WriteBits
        rawName := "uplc_writeBits"
        sourceConsts := [.ByteString bs, .ConstList (indices.map Const.Integer), .Bool value]
        rawArgs := [.bytes bs, ints indices, .bool value]
        definedName? := some "uplc_writeBits_defined" }

def malformedWriteCases : List Case :=
  [ { label := "write-non-integer-index"
      builtin := .WriteBits
      rawName := "uplc_writeBits"
      sourceConsts :=
        [.ByteString (ByteArray.mk #[0]), .ConstList [.Unit], .Bool true]
      rawArgs :=
        [bytes [0], .app "VCons" [.app "VUnit" [], .app "VNil" []],
         .bool true]
      definedName? := some "uplc_writeBits_defined" }
  , { label := "write-mixed-index-list"
      builtin := .WriteBits
      rawName := "uplc_writeBits"
      sourceConsts :=
        [.ByteString (ByteArray.mk #[0]),
         .ConstList [.Integer 0, .ByteString ByteArray.empty], .Bool false]
      rawArgs :=
        [bytes [0],
         .app "VCons"
           [.app "VInt" [.int 0],
            .app "VCons"
              [.app "VBytes" [bytes []], .app "VNil" []]],
         .bool false]
      definedName? := some "uplc_writeBits_defined" }
  ]

def replicateCases : List Case :=
  ([-1, 0, 1, 2, 8, 8192, 8193] : List Int).flatMap fun count =>
    ([-1, 0, 1, 127, 255, 256] : List Int).map fun byte =>
      { label := s!"rep-{count}-{byte}"
        builtin := .ReplicateByte
        rawName := "uplc_replicateByte"
        sourceConsts := [.Integer count, .Integer byte]
        rawArgs := [.int count, .int byte]
        definedName? := some "uplc_replicateByte_defined" }

def shiftCases (builtin : BuiltinFun) (rawName : String) : List Case :=
  byteSamples.flatMap fun xs =>
    ([-9223372036854775809, -9223372036854775808, -25, -24, -17, -16, -9, -8,
      -7, -1, 0, 1, 7, 8, 9, 15, 16, 17, 24, 25,
      9223372036854775807, 9223372036854775808] : List Int).map fun amount =>
      let bs := ByteArray.mk xs.toArray
      { label := s!"{rawName}-{xs.length}-{amount}"
        builtin := builtin
        rawName := rawName
        sourceConsts := [.ByteString bs, .Integer amount]
        rawArgs := [.bytes bs, .int amount] }

def expCases : List Case :=
  ([-8, -3, -1, 0, 1, 2, 3, 7, 8] : List Int).flatMap fun base =>
    ([-5, -3, -1, 0, 1, 2, 3, 5] : List Int).flatMap fun exponent =>
      ([-1, 0, 1, 2, 3, 4, 5, 7, 8, 11] : List Int).map fun modulus =>
        { label := s!"exp-{base}-{exponent}-{modulus}"
          builtin := .ExpModInteger
          rawName := "uplc_expModInteger"
          sourceConsts := [.Integer base, .Integer exponent, .Integer modulus]
          rawArgs := [.int base, .int exponent, .int modulus]
          definedName? := some "uplc_expModInteger_defined" }

def groups : List (String × List Case) :=
  [ ("integerToByteString", intToCases)
  , ("byteStringToInteger", bsToCases)
  , ("andByteString", binCases .AndByteString "uplc_andByteString")
  , ("orByteString", binCases .OrByteString "uplc_orByteString")
  , ("xorByteString", binCases .XorByteString "uplc_xorByteString")
  , ("complementByteString", unaryBytesCases .ComplementByteString "uplc_complementByteString")
  , ("readBit", readCases)
  , ("writeBits", writeCases)
  , ("replicateByte", replicateCases)
  , ("shiftByteString", shiftCases .ShiftByteString "uplc_shiftByteString")
  , ("rotateByteString", shiftCases .RotateByteString "uplc_rotateByteString")
  , ("countSetBits", unaryBytesCases .CountSetBits "uplc_countSetBits")
  , ("findFirstSetBit", unaryBytesCases .FindFirstSetBit "uplc_findFirstSetBit")
  , ("expModInteger", expCases)
  ]

def caseCount : Nat :=
  (groups.map fun group => group.2.length).sum

example : caseCount = 1890 := by native_decide

def firstLine (s : String) : String := (s.splitOn "\n").head?.getD ""

def runOne (name suffix expected : String) (formula : SExpr) : IO Unit := do
  let path := s!"/tmp/moist-advanced-{name}-{suffix}.smt2"
  let production := scriptWith [] [formula]
  let solverCommands ←
    match production.commands.reverse with
    | .getModel :: reversed => pure reversed.reverse
    | _ => throw <| IO.userError s!"{name}/{suffix}: production script no longer ends in get-model"
  IO.FS.writeFile path (Script.mk solverCommands).render
  let result ← IO.Process.output { cmd := "z3", args := #["-T:120", path] }
  let status := firstLine result.stdout
  unless result.exitCode == 0 && result.stderr.isEmpty &&
      (result.stdout.splitOn "(error").length == 1 && status == expected do
    throw <| IO.userError s!"{name}/{suffix}: expected {expected}, got {status}\n{result.stdout}\n{result.stderr}"
  IO.FS.removeFile path

unsafe def main : IO Unit := do
  unless caseCount == 1890 do
    throw <| IO.userError s!"advanced raw case coverage changed: {caseCount}"
  for (name, cases) in groups do
    let formula := SExpr.all (cases.map Case.formula)
    runOne name "positive" "sat" formula
    runOne name "negative" "unsat" (SExpr.not formula)
    IO.println s!"{name}: CEK agrees with raw SMT on {cases.length} cases"
  let malformedFormula := SExpr.all (malformedWriteCases.map Case.formula)
  runOne "writeBitsMalformed" "positive" "sat" malformedFormula
  runOne "writeBitsMalformed" "negative" "unsat"
    (SExpr.not malformedFormula)
  IO.println
    s!"writeBitsMalformed: CEK agrees with raw SMT on {malformedWriteCases.length} cases"

end Test.SMT.AdvancedBuiltinRawDifferential

unsafe def main : IO Unit := Test.SMT.AdvancedBuiltinRawDifferential.main
