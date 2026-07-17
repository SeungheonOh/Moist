import Test.SMT.Examples
import Moist.SMT.Soundness

/-!
# Symbolic outcome compaction regressions

The workload below is deliberately written as ordinary UPLC.  It insertion
sorts a constant list whose elements are independent symbolic integers.  Every
comparison therefore forks a lazy `if`, and every recursive list match forks a
lazy `chooseList`; this is the shape that previously made `List Outcome` grow
too quickly to compile useful input sizes.
-/

namespace Test.SMT.Compaction

open Moist.Plutus.Term
open Moist.SMT
open Moist.SMT.UPLC
open Test.SMT.Examples (tyListInt app app2 lazyIf)

def forceN : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .Force (forceN n t)

def forcedBuiltin (n : Nat) (b : BuiltinFun) : Term :=
  forceN n (.Builtin b)

def chooseList (xs nilCase consCase : Term) : Term :=
  app (app (app (forcedBuiltin 2 .ChooseList) xs) nilCase) consCase

def lazyChooseList (xs nilCase consCase : Term) : Term :=
  .Force (chooseList xs (.Delay nilCase) (.Delay consCase))

def mkCons (x xs : Term) : Term :=
  app (app (forcedBuiltin 1 .MkCons) x) xs

def headList (xs : Term) : Term :=
  app (forcedBuiltin 1 .HeadList) xs

def tailList (xs : Term) : Term :=
  app (forcedBuiltin 1 .TailList) xs

def emptyIntList : Term :=
  .Constant (.ConstList [], tyListInt)

/-- A closed self-applied insertion function.  In its body, variables 1, 2,
and 3 are respectively the tail, inserted element, and recursive self. -/
def insertF : Term :=
  let xs := .Var 1
  let x := .Var 2
  let self := .Var 3
  let recurse := app (app (app self self) x) (tailList xs)
  let insertTail := mkCons (headList xs) recurse
  let body := lazyChooseList xs
    (mkCons x xs)
    (lazyIf (app2 .LessThanEqualsInteger x (headList xs))
      (mkCons x xs)
      insertTail)
  .Lam 0 (.Lam 0 (.Lam 0 body))

def insert (x xs : Term) : Term :=
  app (app (app insertF insertF) x) xs

/-- A closed self-applied insertion sort.  Its body sees the input list at
variable 1 and recursive self at variable 2. -/
def insertionSortF : Term :=
  let xs := .Var 1
  let self := .Var 2
  let sortedTail := app (app self self) (tailList xs)
  let body := lazyChooseList xs xs (insert (headList xs) sortedTail)
  .Lam 0 (.Lam 0 body)

def insertionSort (xs : Term) : Term :=
  app (app insertionSortF insertionSortF) xs

def symbolicInts (n : Nat) : List SymDecl :=
  (List.range n).map fun i => symInt s!"sort_{i}"

def symbolicIntList (n : Nat) : Term :=
  (List.range n).foldr (fun i xs => mkCons (.Var (i + 1)) xs) emptyIntList

def sortFuel (n : Nat) : Nat := 80 + 24 * n

def insertionSortOutcomes (n : Nat) : List Outcome :=
  evalSym (sortFuel n) (envOf (symbolicInts n))
    (insertionSort (symbolicIntList n))

def successCount (outs : List Outcome) : Nat :=
  outs.countP fun | .ok _ _ => true | _ => false

def errorCount (outs : List Outcome) : Nat :=
  outs.countP fun | .error _ => true | _ => false

def timeoutCount (outs : List Outcome) : Nat :=
  outs.countP fun | .timeout _ => true | _ => false

-- The optimization itself has a small, deterministic unit regression: all
-- encodable successes and all errors/timeouts are represented once.
private def sampleOutcomes : List Outcome :=
  [ .ok (.sym "a") (.const (.constList (.sym "xs")))
  , .ok (.sym "b") (.dyn (.sym "v"))
  , .ok (.sym "data") (.const (.dataList (.sym "ds")))
  , .ok (.sym "higher") (.delay (.Var 1) [])
  , .error (.sym "e1")
  , .error (.sym "e2")
  , .timeout (.sym "t1")
  , .timeout (.sym "t2")
  ]

#guard (compactOutcomes sampleOutcomes).length == 4
#guard successCount (compactOutcomes sampleOutcomes) == 2
#guard errorCount (compactOutcomes sampleOutcomes) == 1
#guard timeoutCount (compactOutcomes sampleOutcomes) == 1

-- End-to-end regression beyond the former six-element practical limit.  All
-- successful orderings are packed into one value; only the linearly many
-- outer call-site errors and the single exhausted symbolic-recursion path
-- remain as separate outcome kinds.
#guard
  let outs := insertionSortOutcomes 7
  outs.length == 10 && successCount outs == 1 &&
    errorCount outs == 8 && timeoutCount outs == 1

-- These are the public kernel-checked CEK endpoints exercised by generated
-- success and error assertions.
#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound

def benchmarkSize (n : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  let outs := insertionSortOutcomes n
  let total := outs.length
  let oks := successCount outs
  let errors := errorCount outs
  let timeouts := timeoutCount outs
  -- Printing the result forces the pure evaluator before the stop timestamp;
  -- Lean otherwise keeps the whole symbolic computation as a thunk.
  IO.print s!"n={n} outcomes={total} ok={oks} error={errors} timeout={timeouts}"
  let stop ← IO.monoMsNow
  IO.println s!" ms={stop - start}"

def main : IO Unit := do
  for n in [4, 5, 6, 7, 8] do
    benchmarkSize n

end Test.SMT.Compaction
