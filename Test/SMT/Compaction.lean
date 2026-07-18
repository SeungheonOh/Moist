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

/-- Keep application compaction at the production evaluator boundary. -/
theorem evalSym_apply_compacts (n : Nat) (ρ : List SymVal) (f a : Term) :
    evalSym (n + 1) ρ (.Apply f a) =
      compactOutcomes
        (bindOut (evalSym n ρ f) fun vf =>
          bindOut (evalSym n ρ a) fun va => applySym n vf va) := by
  simp [evalSym]

-- The optimization itself has a small, deterministic unit regression: all
-- encodable successes and all errors/timeouts are represented once.
private def sampleOutcomes : List Outcome :=
  [ .ok (.sym "a") (.const (.constList (.sym "xs") .unknown))
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

/- Identical atomic values do not need a value-selector tree.  The path still
records both alternatives, but the merged value remains the literal itself.
This is the exact shape produced by conditionals whose branches compute the
same first-order result. -/
private def identicalIntegerOutcomes : List Outcome :=
  [ .ok (.sym "same-left") (.const (.integer (.int 7)))
  , .ok (.sym "same-right") (.const (.integer (.int 7)))
  ]

#guard SExpr.sameAtom (.int 7) (.int 7)
#guard !SExpr.sameAtom (.int 7) (.int 8)
#guard
  match mergedOkOutcome .integer identicalIntegerOutcomes with
  | [.ok _ (.const (.integer (.int 7)))] => true
  | _ => false

private def expressionDepth : SExpr → Nat
  | .app _ args =>
      args.foldl (fun depth arg => max depth (expressionDepth arg + 1)) 1
  | .ite condition thenExpr elseExpr =>
      max (expressionDepth condition)
        (max (expressionDepth thenExpr) (expressionDepth elseExpr)) + 1
  | _ => 1

private def manySymbolicErrors (count : Nat) : List Outcome :=
  (List.range count).map fun i => .error (.sym s!"error_path_{i}")

-- Wide disjunctions are balanced at every compiler call site.  This protects
-- both the renderer and Z3 from a linear recursion spine without adding SMT
-- operator nodes.
#guard
  match compactOutcomes (manySymbolicErrors 256) with
  | [.error pc] => expressionDepth pc ≤ 10
  | _ => false

/- The native-sort extension must cover every newly supported representation,
not merely the integer/list cases exercised by insertion sort.  Two paths of
each kind collapse to one result of that same kind. -/
private def nativeSampleOutcomes : List Outcome :=
  [ .ok (.sym "unit-a") (.const .unit)
  , .ok (.sym "unit-b") (.const .unit)
  , .ok (.sym "bytes-a") (.const (.bytes (.sym "bytes-x")))
  , .ok (.sym "bytes-b") (.const (.bytes (.sym "bytes-y")))
  , .ok (.sym "string-a") (.const (.string (.sym "string-x")))
  , .ok (.sym "string-b") (.const (.string (.sym "string-y")))
  , .ok (.sym "data-a") (.const (.data (.sym "data-x")))
  , .ok (.sym "data-b") (.const (.data (.sym "data-y")))
  , .ok (.sym "pairs-a") (.const (.pairDataList (.sym "pairs-x")))
  , .ok (.sym "pairs-b") (.const (.pairDataList (.sym "pairs-y")))
  , .ok (.sym "array-a") (.const (.array (.sym "array-x")))
  , .ok (.sym "array-b") (.const (.array (.sym "array-y")))
  ]

private def outcomeCompactKinds : List Outcome → List CompactKind
  | [] => []
  | .ok _ value :: outs =>
      match compactKind? value with
      | some kind => kind :: outcomeCompactKinds outs
      | none => outcomeCompactKinds outs
  | _ :: outs => outcomeCompactKinds outs

#guard (compactOutcomes nativeSampleOutcomes).length == 6
#guard outcomeCompactKinds (compactOutcomes nativeSampleOutcomes) ==
  [.unit, .bytes, .string, .data, .pairDataList, .array]

-- Recursive Boolean and integer results are each joined at their native sort.
#guard
  let outs := sortedAfterInsertionOutcomes 3
  outs.length == 2 && successCount outs == 1 &&
    errorCount outs == 1 && timeoutCount outs == 0

#guard
  let outs := sumAfterInsertionOutcomes 3
  outs.length == 2 && successCount outs == 1 &&
    errorCount outs == 1 && timeoutCount outs == 0

-- Syntactically impossible paths disappear before their values can be packed
-- into nested selector terms.  Live outcomes of every kind are retained.
#guard
  match pruneFalseOutcomes
      [.ok (.bool false) (.const (.integer (.sym "dead"))),
       .ok (.sym "live") (.const (.integer (.sym "value"))),
       .error (.bool false), .error (.sym "error"),
       .timeout (.bool false), .timeout (.sym "timeout")] with
  | [.ok (.sym "live") (.const (.integer (.sym "value"))),
      .error (.sym "error"), .timeout (.sym "timeout")] => true
  | _ => false

/-! `Case` is the other general UPLC join point.  A symbolic constructor can
select every alternative, so using several independent cases in a surrounding
computation used to multiply equivalent first-order outcomes. -/

private def caseJoinIntAlts (width : Nat) : List Term :=
  (List.range width).map fun i => int (Int.ofNat i)

private def caseJoinInt (width : Nat) : Term :=
  .Case (.Var 1) (caseJoinIntAlts width)

private def caseJoinSum : Nat → Nat → Term
  | 0, _ => int 0
  | count + 1, width =>
      app2 .AddInteger (caseJoinInt width) (caseJoinSum count width)

private def caseJoinOutcomes (count width : Nat) : List Outcome :=
  evalSym (80 + 20 * count) (envOf [symConstr "case_join_tag"])
    (caseJoinSum count width)

/-- Keep the optimizer at the production `Case` join itself. -/
theorem evalSym_case_join_compacts (n : Nat) (ρ : List SymVal)
    (scrut : Term) (alts : List Term) :
    evalSym (n + 1) ρ (.Case scrut alts) =
      compactOutcomes
        (bindOut (evalSym n ρ scrut) fun v => caseSym n ρ v alts) := by
  simp [evalSym]

-- Eight alternatives across four symbolic case joins still have exactly one
-- packed integer success and one joined possible error.
#guard
  let outs := caseJoinOutcomes 4 8
  outs.length == 2 && successCount outs == 1 &&
    errorCount outs == 1 && timeoutCount outs == 0

private def nilOutcome : Outcome := .ok (.sym "nil-pc") (.const .unit)
private def consOutcome : Outcome := .ok (.sym "cons-pc") (.const .unit)

private def branchNames : List Outcome → List String
  | [] => []
  | .ok (.sym name) _ :: outs => name :: branchNames outs
  | _ :: outs => branchNames outs

#guard branchNames (constListBranches (some 0) nilOutcome consOutcome) == ["nil-pc"]
#guard branchNames (constListBranches (some 3) nilOutcome consOutcome) == ["cons-pc"]
#guard branchNames (constListBranches none nilOutcome consOutcome) == ["nil-pc", "cons-pc"]
#guard knownConstListLength (constLiteral (.ConstList [])) == some 0

private def certifiedNilOutcomes : List Outcome :=
  [ .ok (.sym "left")
      (.const (.constList (.constListLit []) (.literal [])))
  , .ok (.sym "right")
      (.const (.constList (.constListLit []) (.literal [])))
  ]

-- Same-length joins retain a certificate for the newly built `ite`, rather
-- than copying forgeable metadata from either input.
#guard
  match mergedOkOutcome .constList certifiedNilOutcomes with
  | [.ok _ value] => knownConstListLength value == some 0
  | _ => false

-- End-to-end regression beyond the former six-element practical limit.  Each
-- successful representation is packed once, and all possible runtime errors
-- are represented by one merged outcome; impossible carried failures and
-- timeouts are absent.
#guard
  let outs := insertionSortOutcomes 7
  outs.length == 2 && successCount outs == 1 &&
    errorCount outs == 1 && timeoutCount outs == 0

-- These are the public kernel-checked CEK endpoints exercised by generated
-- success and error assertions.
#check Moist.SMT.UPLC.Soundness.evalSym_errorCond_sound
#check Moist.SMT.UPLC.Soundness.evalSym_okBoolTrueCond_sound
#check Moist.SMT.UPLC.Soundness.compactOutcomes_active_ok
#check Moist.SMT.UPLC.SExpr.sameAtom_eq_true
#check Moist.SMT.UPLC.Soundness.mergeEncodedOks_active
#check Moist.SMT.UPLC.Soundness.compactDecode_encode_toCek
#check Moist.SMT.UPLC.Soundness.compactDecode_encode_noOpaque
#check Moist.SMT.UPLC.Soundness.compactOutcomes_active_error
#check Moist.SMT.UPLC.Soundness.compactOutcomes_active_timeout
#check Moist.SMT.UPLC.Soundness.evalBoolIs_any_true
#check Moist.SMT.UPLC.Soundness.evalBoolIs_any_true_of_mem
#check
  Moist.SMT.UPLC.Soundness.evalBoolIs_any_true_iff_referenceLinearAny_true_of_bools
#check Moist.SMT.UPLC.Soundness.evalBool?_any_eq_referenceLinearAny
#check Moist.SMT.UPLC.Soundness.evalBoolIs_any_eq_referenceLinearAny
#check
  Moist.SMT.UPLC.Soundness.evalBoolIs_any_true_iff_referenceLinearAny_true
#check Moist.SMT.UPLC.Soundness.mem_pruneFalseOutcomes_iff_of_active
#check Moist.SMT.UPLC.Soundness.constListBranches_sublist
#check Moist.SMT.UPLC.Soundness.exactConstListLength_eval_length
#check Moist.SMT.UPLC.Soundness.constListBranches_complete_for_toCek

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
