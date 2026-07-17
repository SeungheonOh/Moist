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
open Test.SMT.Examples (tyListInt app app2 lazyIf bool int)

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

/-- A recursive nondecreasing-order predicate.  Composing this with insertion
sort exercises native Boolean joins after a native-list-producing program. -/
def sortedF : Term :=
  let xs := .Var 1
  let self := .Var 2
  let tail := tailList xs
  let recurse := app (app self self) tail
  let consTail := lazyIf
    (app2 .LessThanEqualsInteger (headList xs) (headList tail))
    recurse (bool false)
  let consXs := lazyChooseList tail (bool true) consTail
  let body := lazyChooseList xs (bool true) consXs
  .Lam 0 (.Lam 0 body)

def sorted (xs : Term) : Term :=
  app (app sortedF sortedF) xs

/-- A recursive integer fold.  `sum (sort xs) = sum xs` exercises native
integer joins and is independent of the sortedness predicate benchmark. -/
def sumF : Term :=
  let xs := .Var 1
  let self := .Var 2
  let recurse := app (app self self) (tailList xs)
  let body := lazyChooseList xs (int 0)
    (app2 .AddInteger (headList xs) recurse)
  .Lam 0 (.Lam 0 body)

def sumList (xs : Term) : Term :=
  app (app sumF sumF) xs

def symbolicInts (n : Nat) : List SymDecl :=
  (List.range n).map fun i => symInt s!"sort_{i}"

def symbolicIntList (n : Nat) : Term :=
  (List.range n).foldr (fun i xs => mkCons (.Var (i + 1)) xs) emptyIntList

def sortFuel (n : Nat) : Nat := 80 + 24 * n

def insertionSortOutcomes (n : Nat) : List Outcome :=
  evalSym (sortFuel n) (envOf (symbolicInts n))
    (insertionSort (symbolicIntList n))

/-- Fully symbolic sortedness workload: every list element is an independent
SMT integer. -/
def sortedAfterInsertionOutcomes (n : Nat) : List Outcome :=
  evalSym (sortFuel n + 80) (envOf (symbolicInts n))
    (sorted (insertionSort (symbolicIntList n)))

/-- Independent fold-preservation workload over the same symbolic input. -/
def sumAfterInsertionOutcomes (n : Nat) : List Outcome :=
  evalSym (sortFuel n + 80) (envOf (symbolicInts n))
    (sumList (insertionSort (symbolicIntList n)))

def symbolicSum (n : Nat) : SExpr :=
  (List.range n).foldl (fun acc i =>
    SExpr.add acc (.sym (sanitize s!"sort_{i}"))) (.int 0)

/-- Constraint workload for a generated, already-sorted symbolic list. -/
def adjacentOrdered (n : Nat) : SExpr :=
  SExpr.all ((List.range (n - 1)).map fun i =>
    SExpr.le (.sym (sanitize s!"sort_{i}"))
      (.sym (sanitize s!"sort_{i + 1}")))

def presortedCheckScript (n : Nat) : Script :=
  let decls := symbolicInts n
  let outs := evalSym (sortFuel n + 80) (envOf decls)
    (sorted (symbolicIntList n))
  scriptWith decls [SExpr.all [adjacentOrdered n, okBoolTrueCond outs]]

def sortedAfterInsertionScript (n : Nat) : Script :=
  scriptWith (symbolicInts n) [okBoolTrueCond (sortedAfterInsertionOutcomes n)]

def sumAfterInsertionScript (n : Nat) : Script :=
  scriptWith (symbolicInts n)
    [okIntEqCond (sumAfterInsertionOutcomes n) (symbolicSum n)]

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
  , .ok (.sym "i1") (.const (.integer (.sym "x")))
  , .ok (.sym "i2") (.const (.integer (.sym "y")))
  , .ok (.sym "p") (.const (.bool (.sym "p")))
  , .ok (.sym "q") (.const (.bool (.sym "q")))
  , .ok (.sym "higher") (.delay (.Var 1) [])
  , .error (.sym "e1")
  , .error (.sym "e2")
  , .timeout (.sym "t1")
  , .timeout (.sym "t2")
  ]

#guard (compactOutcomes sampleOutcomes).length == 8
#guard successCount (compactOutcomes sampleOutcomes) == 6
#guard errorCount (compactOutcomes sampleOutcomes) == 1
#guard timeoutCount (compactOutcomes sampleOutcomes) == 1

-- Recursive Boolean and integer results are each joined at their native sort.
#guard
  let outs := sortedAfterInsertionOutcomes 3
  outs.length == 10 && successCount outs == 2 &&
    errorCount outs == 6 && timeoutCount outs == 2

#guard
  let outs := sumAfterInsertionOutcomes 3
  outs.length == 11 && successCount outs == 2 &&
    errorCount outs == 6 && timeoutCount outs == 3

-- End-to-end regression beyond the former six-element practical limit.  Each
-- successful representation is packed once; only the linearly many
-- outer call-site errors and the single exhausted symbolic-recursion path
-- remain as separate outcome kinds.
#guard
  let outs := insertionSortOutcomes 7
  outs.length == 11 && successCount outs == 2 &&
    errorCount outs == 8 && timeoutCount outs == 1

-- These are the public kernel-checked CEK endpoints exercised by generated
-- success and error assertions.
#check Moist.SMT.UPLC.Soundness.evalSym_errorCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_okBoolTrueCond_sound
#check Moist.SMT.UPLC.Soundness.compactOutcomes_active_timeout

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
