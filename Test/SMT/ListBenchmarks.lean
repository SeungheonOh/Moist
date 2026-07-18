import Test.SMT.Compaction
import Moist.SMT.DagRender

/-!
# Symbolic-list solver benchmarks

These workloads exercise different parts of the SMT compiler's list encoding:

* `sortedInputScript` asks for a model whose fixed-length symbolic list is
  sorted.  A satisfying model composes directly with the public
  `evalSym_okBoolTrueCond_sound` CEK endpoint.
* `sortSortednessCounterexampleScript` searches for an input on which insertion
  sort returns a list that fails the recursive sortedness checker.
* `insertSortednessCounterexampleScript` assumes a sorted input and searches
  for a key whose insertion makes it unsorted.
* `sortSumCounterexampleScript` searches for a failure of sum preservation.
* `sortIdempotenceCounterexampleScript` compares one and two applications of
  insertion sort as list values.

Every query asserts `okBoolTrueCond` for a UPLC Boolean term.  Consequently, a
satisfying counterexample query composes with the public
`evalSym_okBoolTrueCond_sound` endpoint to a genuine CEK-level witness.  An
unsatisfiable result remains a solver benchmark rather than a completeness
claim, as required by the public one-way soundness API.
-/

namespace Test.SMT.ListBenchmarks

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC
open Test.SMT.Examples (app app2 bool int ifThenElse lazyIf)
open Test.SMT.Compaction

/-- Recursive adjacent-pair sortedness for builtin constant lists. -/
def isSortedF : Term :=
  let xs := .Var 1
  let self := .Var 2
  let tail := tailList xs
  let recurse := app (app self self) tail
  let compareRest :=
    lazyIf (app2 .LessThanEqualsInteger (headList xs) (headList tail))
      recurse (bool false)
  let consCase := lazyChooseList tail (bool true) compareRest
  .Lam 0 (.Lam 0 (lazyChooseList xs (bool true) consCase))

def isSorted (xs : Term) : Term :=
  app (app isSortedF isSortedF) xs

/-- Recursive integer sum for builtin constant lists. -/
def sumListF : Term :=
  let xs := .Var 1
  let self := .Var 2
  let recurse := app (app self self) (tailList xs)
  let consCase := app2 .AddInteger (headList xs) recurse
  .Lam 0 (.Lam 0 (lazyChooseList xs (int 0) consCase))

def sumList (xs : Term) : Term :=
  app (app sumListF sumListF) xs

/-- Recursive elementwise equality for builtin integer lists. -/
def listEqF : Term :=
  let ys := .Var 1
  let xs := .Var 2
  let self := .Var 3
  let recurse := app (app (app self self) (tailList xs)) (tailList ys)
  let bothCons := lazyIf (app2 .EqualsInteger (headList xs) (headList ys))
    recurse (bool false)
  let body := lazyChooseList xs
    (lazyChooseList ys (bool true) (bool false))
    (lazyChooseList ys (bool false) bothCons)
  .Lam 0 (.Lam 0 (.Lam 0 body))

def listEq (xs ys : Term) : Term :=
  app (app (app listEqF listEqF) xs) ys

/-- Boolean negation inside UPLC, so a satisfying compiled query witnesses a
CEK evaluation of the negated property rather than merely absence of a
symbolic success path. -/
def boolNot (term : Term) : Term :=
  ifThenElse term (bool false) (bool true)

def boolTrueCondition (fuel : Nat) (decls : List SymDecl) (term : Term) : SExpr :=
  okBoolTrueCond (evalSym fuel (envOf decls) term)

/-- Satisfiable model-generation query: choose `n` integers in nondecreasing
order. -/
def sortedInputScript (n : Nat) : Script :=
  let decls := symbolicInts n
  scriptWith decls
    [boolTrueCondition (sortFuel n) decls (isSorted (symbolicIntList n))]

/-- Counterexample query for insertion-sort sortedness. -/
def sortSortednessCounterexampleScript (n : Nat) : Script :=
  let decls := symbolicInts n
  let sorted := isSorted (insertionSort (symbolicIntList n))
  scriptWith decls [boolTrueCondition (sortFuel n + 80) decls (boolNot sorted)]

/-- Counterexample query for inserting a symbolic key into an already sorted
fixed-length symbolic list. -/
def insertSortednessCounterexampleScript (n : Nat) : Script :=
  let decls := symbolicInts (n + 1)
  let xs := symbolicIntList n
  let key := .Var (n + 1)
  let counterexample := lazyIf (isSorted xs)
    (boolNot (isSorted (insert key xs))) (bool false)
  scriptWith decls
    [boolTrueCondition (sortFuel n + 80) decls counterexample]

/-- Counterexample query for preservation of the integer sum by insertion
sort. -/
def sortSumCounterexampleScript (n : Nat) : Script :=
  let decls := symbolicInts n
  let xs := symbolicIntList n
  let sameSum := app2 .EqualsInteger (sumList xs) (sumList (insertionSort xs))
  scriptWith decls
    [boolTrueCondition (sortFuel n + 80) decls (boolNot sameSum)]

/-- Counterexample query for idempotence of insertion sort.  The lambda shares
the first sorted list at the UPLC level before comparing it with a second
application. -/
def sortIdempotenceCounterexampleScript (n : Nat) : Script :=
  let decls := symbolicInts n
  let once := insertionSort (symbolicIntList n)
  let sameTwice := app (.Lam 0 (listEq (.Var 1) (insertionSort (.Var 1)))) once
  scriptWith decls
    [boolTrueCondition (sortFuel n + 120) decls (boolNot sameTwice)]

def benchmarkScripts (n : Nat) : List (String × (Unit → Script)) :=
  [ (s!"sorted-input-{n}.smt2", fun _ => sortedInputScript n)
  , (s!"insertion-sort-sorted-{n}.smt2", fun _ => sortSortednessCounterexampleScript n)
  , (s!"insert-preserves-sorted-{n}.smt2", fun _ => insertSortednessCounterexampleScript n)
  , (s!"insertion-sort-sum-{n}.smt2", fun _ => sortSumCounterexampleScript n)
  , (s!"insertion-sort-idempotent-{n}.smt2", fun _ => sortIdempotenceCounterexampleScript n)
  ]

-- Every asserted benchmark condition is a CEK-level Boolean witness term;
-- these are the exact assertion-neutral and actual-machine endpoints it uses.
#check scriptWith_assertions
#check Moist.SMT.UPLC.Soundness.evalSym_okBoolTrueCond_sound

def outputDir : System.FilePath := "Test/generated/smt/list-benchmarks"

unsafe def writeBenchmarks (sizes : List Nat) : IO Unit := do
  IO.FS.createDirAll outputDir
  for n in sizes do
    for (name, makeScript) in benchmarkScripts n do
      let start ← IO.monoMsNow
      let script := makeScript ()
      let rendered := script.renderDag
      IO.FS.writeFile (outputDir / name) rendered
      let stop ← IO.monoMsNow
      IO.println s!"{name}: bytes={rendered.length} generation-ms={stop - start}"

unsafe def writeDefaultBenchmarks : IO Unit :=
  writeBenchmarks [4, 6, 8]

end Test.SMT.ListBenchmarks
