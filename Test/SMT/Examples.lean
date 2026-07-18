import Moist.SMT.Compiler.Operational

namespace Test.SMT.Examples

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC

abbrev tyInt : BuiltinType := .AtomicType .TypeInteger
abbrev tyBool : BuiltinType := .AtomicType .TypeBool
abbrev tyListInt : BuiltinType := .TypeOperator (.TypeList tyInt)

def int (n : Int) : Term := .Constant (.Integer n, tyInt)
def bool (b : Bool) : Term := .Constant (.Bool b, tyBool)
def app (f x : Term) : Term := .Apply f x
def app1 (b : BuiltinFun) (x : Term) : Term := app (.Builtin b) x
def app2 (b : BuiltinFun) (x y : Term) : Term := app (app (.Builtin b) x) y
def forceBuiltin (b : BuiltinFun) : Term := .Force (.Builtin b)

def ifThenElse (c t e : Term) : Term :=
  app (app (app (forceBuiltin .IfThenElse) c) t) e

def lazyIf (c t e : Term) : Term :=
  .Force (ifThenElse c (.Delay t) (.Delay e))

def equalsIntegerAddExample : Term :=
  app2 .EqualsInteger (int 10) (app2 .AddInteger (int 5) (.Var 1))

def caseIntegerExample : Term :=
  .Case (.Var 1) [.Error, .Error, bool true]

def caseIfConstrExample : Term :=
  let cond := app2 .EqualsInteger (.Var 1) (int 10)
  -- This is the satisfiable-by-x=10 orientation of the example:
  -- if x == 10 then Constr 1 [] else Constr 0 [], with branch 1 returning true.
  .Case (ifThenElse cond (.Constr 1 []) (.Constr 0 [])) [.Error, bool true]

def forceDelayExample : Term :=
  app2 .EqualsInteger (int 42) (.Force (.Delay (.Var 1)))

def caseEmptyConstListMissingNilExample : Term :=
  .Case (.Constant (.ConstList [], tyListInt)) [bool true]

def mkConsRejectsRuntimeConstrExample : Term :=
  app (app (forceBuiltin .MkCons) (.Constr 0 [])) (.Constant (.ConstList [], tyListInt))

def recursiveSumTerm : Term :=
  let body :=
    let x := .Var 1
    let self := .Var 2
    let cond := app2 .LessThanInteger x (int 0)
    let xMinusOne := app2 .SubtractInteger x (int 1)
    let recCall := app (app self self) xMinusOne
    let step := app2 .AddInteger x recCall
    lazyIf cond (int 0) step
  let sumF := .Lam 0 (.Lam 0 body)
  app (app sumF sumF) (.Var 1)

def xInt : SymDecl := symInt "x"
def scriptEqualsIntegerAdd : Script :=
  scriptForBoolTrue 20 [xInt] equalsIntegerAddExample

def scriptCaseInteger : Script :=
  scriptForBoolTrue 20 [xInt] caseIntegerExample

def scriptCaseIfConstr : Script :=
  scriptForBoolTrue 30 [xInt] caseIfConstrExample

def scriptForceDelay : Script :=
  scriptForBoolTrue 20 [xInt] forceDelayExample

def scriptCaseEmptyConstListMissingNilError : Script :=
  scriptForError 20 [] caseEmptyConstListMissingNilExample

def scriptMkConsRejectsRuntimeConstrError : Script :=
  scriptForError 20 [] mkConsRejectsRuntimeConstrExample

def scriptRecursiveSum55 : Script :=
  scriptForIntEq 100 [xInt] recursiveSumTerm (.int 55)

def examples : List (String × Script) :=
  [ ("equals_integer_add.smt2", scriptEqualsIntegerAdd)
  , ("case_integer.smt2", scriptCaseInteger)
  , ("case_if_constr.smt2", scriptCaseIfConstr)
  , ("force_delay.smt2", scriptForceDelay)
  , ("case_empty_const_list_missing_nil_error.smt2", scriptCaseEmptyConstListMissingNilError)
  , ("mkcons_rejects_runtime_constr_error.smt2", scriptMkConsRejectsRuntimeConstrError)
  , ("recursive_sum_55.smt2", scriptRecursiveSum55)
  ]

def outputDir : System.FilePath := "Test/generated/smt"

unsafe def writeExamples : IO Unit := do
  IO.FS.createDirAll outputDir
  for (name, script) in examples do
    IO.FS.writeFile (outputDir / name) script.renderDag

unsafe def main : IO Unit := do
  writeExamples
  IO.println s!"wrote {examples.length} SMTLib examples to {outputDir}"

end Test.SMT.Examples

unsafe def main : IO Unit := Test.SMT.Examples.main
