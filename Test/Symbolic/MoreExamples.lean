import Moist.Symbolic.Compile

namespace Test.Symbolic.MoreExamples

open Moist.Plutus.Term (Term Const BuiltinType AtomicType BuiltinFun TypeOperator)
open Moist.Symbolic
open SExpr (sEq)

abbrev intT : BuiltinType := .AtomicType .TypeInteger
abbrev boolT : BuiltinType := .AtomicType .TypeBool
abbrev unitT : BuiltinType := .AtomicType .TypeUnit
abbrev bytesT : BuiltinType := .AtomicType .TypeByteString
abbrev dataT : BuiltinType := .AtomicType .TypeData
abbrev listT (t : BuiltinType) : BuiltinType := .TypeOperator (.TypeList t)
abbrev arrayT (t : BuiltinType) : BuiltinType := .TypeOperator (.TypeArray t)
abbrev pairT (a b : BuiltinType) : BuiltinType := .TypeOperator (.TypePair a b)

abbrev intC (n : Int) : Term := .Constant (.Integer n, intT)
abbrev boolC (b : Bool) : Term := .Constant (.Bool b, boolT)
abbrev unitC : Term := .Constant (.Unit, unitT)
abbrev bsC (bytes : List UInt8) : Term :=
  .Constant (.ByteString ⟨bytes.toArray⟩, bytesT)
abbrev nilIntC : Term := .Constant (.ConstList [], listT intT)
def intListC (xs : List Int) : Term :=
  .Constant (.ConstList (xs.map (fun x => Const.Integer x)), listT intT)
abbrev emptyArrayIntC : Term := .Constant (.ConstArray [], arrayT intT)
abbrev pairC (a : Const) (aTy : BuiltinType) (b : Const) (bTy : BuiltinType) : Term :=
  .Constant (.Pair (a, b), pairT aTy bTy)

def b1 (b : BuiltinFun) (a : Term) : Term := .Apply (.Builtin b) a
def b2 (b : BuiltinFun) (x y : Term) : Term := .Apply (.Apply (.Builtin b) x) y
def b1F (b : BuiltinFun) (a : Term) : Term := .Apply (.Force (.Builtin b)) a
def b1FF (b : BuiltinFun) (a : Term) : Term := .Apply (.Force (.Force (.Builtin b))) a

def mkNilD : Term := b1 .MkNilData unitC
def mkConsT (head tail : Term) : Term :=
  .Apply (.Apply (.Force (.Builtin .MkCons)) head) tail
def headT (xs : Term) : Term := b1F .HeadList xs
def tailT (xs : Term) : Term := b1F .TailList xs
def nullT (xs : Term) : Term := b1F .NullList xs
def fstT (p : Term) : Term := b1FF .FstPair p

def ite3 (c t e : Term) : Term :=
  .Apply (.Apply (.Apply (.Force (.Builtin .IfThenElse)) c) t) e

def chooseListT (xs nilCase consCase : Term) : Term :=
  .Apply (.Apply (.Apply (.Force (.Force (.Builtin .ChooseList))) xs) nilCase) consCase

def dropListT (n xs : Term) : Term :=
  .Apply (.Apply (.Force (.Builtin .DropList)) n) xs

def lengthArrayT (xs : Term) : Term := b1F .LengthOfArray xs

def mkPairDataT (a b : Term) : Term := b2 .MkPairData a b

/-- A compact z3-backed example. `needle`s are substrings expected in the model/output. -/
structure Example where
  name : String
  expect : String
  compiled : Compiled
  goal : Goal
  needles : List String := []

private def contains? (s t : String) : Bool := (s.splitOn t).length ≥ 2

private def answerLine (out : String) : String :=
  let lines := (out.splitOn "\n").map String.trim
  if lines.contains "sat" then "sat"
  else if lines.contains "unsat" then "unsat"
  else if lines.contains "unknown" then "unknown"
  else "<no-answer>"

private def runZ3 (name smt : String) : IO String := do
  let path := s!"/tmp/moist_more_examples_{name}.smt2"
  IO.FS.writeFile path smt
  let out ← IO.Process.output { cmd := "z3", args := #["-T:10", path] }
  pure (out.stdout ++ out.stderr)

private def runExample (ex : Example) : IO Unit := do
  let out ← runZ3 ex.name (ex.compiled.toSMTLib ex.goal)
  let answer := answerLine out
  let missing := ex.needles.filter (fun n => !contains? out n)
  if answer == ex.expect && missing.isEmpty then
    IO.println s!"✓ {ex.name}: {answer}"
  else
    IO.println s!"✗ {ex.name}: got {answer}, expected {ex.expect}"
    unless missing.isEmpty do
      IO.println s!"  missing expected output fragments: {missing}"
    IO.println out
    throw <| IO.userError s!"example {ex.name} failed"

/-! ## Works today: precise, determinate SMT. -/

def workHeadMkConsInt : Example :=
  { name := "works_head-mkCons-typed-int-solves-x-42"
    expect := "sat"
    compiled := compile 20 [("x", .integer)] (headT (mkConsT (.Var 1) nilIntC))
    goal := (goalReturnsInt · 42)
    needles := ["(define-fun x () Int", "42"] }

def workHeadMkConsAnyV : Example :=
  { name := "works_head-mkCons-anyV-solves-VInt-42"
    expect := "sat"
    compiled := compile 20 [("x", .anyV)] (headT (mkConsT (.Var 1) nilIntC))
    goal := (goalReturnsInt · 42)
    needles := ["(define-fun x () V", "(VInt 42)"] }

def workTailNullAfterCons : Example :=
  { name := "works_null-tail-mkCons-is-true"
    expect := "sat"
    compiled := compile 20 [("x", .anyV)] (nullT (tailT (mkConsT (.Var 1) nilIntC)))
    goal := (goalReturnsBool · true) }

def workDataListHead : Example :=
  { name := "works_head-mkCons-iData-onto-mkNilData-solves-x-7"
    expect := "sat"
    compiled := compile 20 [("x", .integer)] (headT (mkConsT (b1 .IData (.Var 1)) mkNilD))
    goal := fun r => goalEqualsV r (V.data (D.i (.int 7)))
    needles := ["(define-fun x () Int", "7"] }

def workFstPairConcretePair : Example :=
  { name := "works_fstPair-concrete-pair-returns-first"
    expect := "sat"
    compiled := compile 20 [] (fstT (pairC (.Integer 5) intT (.Bool true) boolT))
    goal := (goalReturnsInt · 5) }

/-! ## Genuine CEK errors: determinate failures, not `inc`. -/

def errorHeadEmptyList : Example :=
  { name := "error_head-empty-const-list-is-definite-error"
    expect := "sat"
    compiled := compile 20 [] (headT nilIntC)
    goal := goalErrors }

def impossibleHeadEmptySucceeds : Example :=
  { name := "error_head-empty-const-list-cannot-succeed"
    expect := "unsat"
    compiled := compile 20 [] (headT nilIntC)
    goal := goalSucceeds }

def errorLengthArrayAbsentFromCEK : Example :=
  { name := "error_non-crypto-lengthOfArray-is-definite-CEK-absent-error"
    expect := "sat"
    compiled := compile 20 [] (lengthArrayT emptyArrayIntC)
    goal := goalErrors }

/-! ## More CEK-supported non-crypto builtins that now have determinate SMT. -/

def workDivideInteger : Example :=
  { name := "works_divideInteger-symbolic-solves-x"
    expect := "sat"
    compiled := compile 20 [("x", .integer)] (b2 .DivideInteger (.Var 1) (intC 2))
    goal := (goalReturnsInt · 21)
    needles := ["(define-fun x () Int", "42"] }

def workEqualsByteString : Example :=
  { name := "works_equalsByteString-constant-is-true"
    expect := "sat"
    compiled := compile 20 [] (b2 .EqualsByteString (bsC [1, 2]) (bsC [1, 2]))
    goal := (goalReturnsBool · true) }

def workUnIData : Example :=
  { name := "works_unIData-after-iData-solves-x"
    expect := "sat"
    compiled := compile 20 [("x", .integer)] (b1 .UnIData (b1 .IData (.Var 1)))
    goal := (goalReturnsInt · 9)
    needles := ["(define-fun x () Int", "9"] }

def errorUnBDataHeadIDataList : Example :=
  { name := "error_unBData-head-mkCons-iData-onto-mkNilData-is-definite-error"
    expect := "sat"
    compiled := compile 20 [("x", .integer)]
      (b1 .UnBData (headT (mkConsT (b1 .IData (.Var 1)) mkNilD)))
    goal := goalErrors }

def impossibleUnBDataHeadIDataListSucceeds : Example :=
  { name := "error_unBData-head-mkCons-iData-onto-mkNilData-cannot-succeed"
    expect := "unsat"
    compiled := compile 20 [("x", .integer)]
      (b1 .UnBData (headT (mkConsT (b1 .IData (.Var 1)) mkNilD)))
    goal := goalSucceeds }

def workMkPairData : Example :=
  { name := "works_mkPairData-fstPair-solves-x"
    expect := "sat"
    compiled := compile 20 [("x", .integer), ("y", .integer)]
      (fstT (mkPairDataT (b1 .IData (.Var 1)) (b1 .IData (.Var 2))))
    goal := fun r => goalEqualsV r (V.data (D.i (.int 11)))
    needles := ["(define-fun x () Int", "11"] }

def workIfThenElseBuiltin : Example :=
  { name := "works_ifThenElse-builtin-pass-through"
    expect := "sat"
    compiled := compile 20 [] (ite3 (boolC true) (intC 1) (intC 2))
    goal := (goalReturnsInt · 1) }

def workChooseListBuiltin : Example :=
  { name := "works_chooseList-builtin-pass-through"
    expect := "sat"
    compiled := compile 20 [] (chooseListT nilIntC (intC 0) (intC 1))
    goal := (goalReturnsInt · 0) }

def workDropList : Example :=
  { name := "works_dropList-then-head"
    expect := "sat"
    compiled := compile 20 [] (headT (dropListT (intC 1) (intListC [41, 42])))
    goal := (goalReturnsInt · 42) }

def examples : List Example := [
  workHeadMkConsInt,
  workHeadMkConsAnyV,
  workTailNullAfterCons,
  workDataListHead,
  workFstPairConcretePair,
  errorHeadEmptyList,
  impossibleHeadEmptySucceeds,
  errorLengthArrayAbsentFromCEK,
  workDivideInteger,
  workEqualsByteString,
  workUnIData,
  errorUnBDataHeadIDataList,
  impossibleUnBDataHeadIDataListSucceeds,
  workMkPairData,
  workIfThenElseBuiltin,
  workChooseListBuiltin,
  workDropList
]

def main : IO Unit := examples.forM runExample

#eval! main

end Test.Symbolic.MoreExamples
