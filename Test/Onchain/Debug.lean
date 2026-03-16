import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude
import Moist.Plutus.Eval

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude
open Moist.Plutus.Eval
open Moist.Cardano.V3
open Moist.Onchain.PlutusData
namespace Test.Debug

@[plutus_sop]
inductive Foo where
  | foo : Int → Int → Int → Int → Int → Int → Int → Foo

def Plus (x y : Int) : Int := addInteger x y

@[onchain]
def factorial (n : Int) : Int :=
  ifThenElse (equalsInteger n 0) 1 (n * (factorial (n - 1)))
decreasing_by sorry

@[onchain]
def aaa (x : Foo) : Int :=
  match x with
  | .foo a b c d e f g =>
    a + g + e + c

#evaluatePrettyTerm factorial (1 : Int)

#show_mir aaa
#show_beta_mir aaa
#show_optimized_mir aaa

@[onchain]
def bbb : Foo := Foo.foo 1 2 3 4 5 6 42

def aaaa : Term := compile! aaa

def bbbb : Term := compile! bbb

@[plutus_data]
structure Bar where
  (x : Int)
  (y : Int)
  (z : Int)

@[onchain]
def ccc : Bar := { x := 1, y := 2, z := 3 }

@[plutus_data]
inductive Baz where
  | baz : Int → Int → Int → Baz
  | bar : Int -> Int → Baz
  | aaa : Int -> Int -> Baz
  | foo : Int → Baz
  | qux : Baz

@[plutus_data]
inductive SOPHi where
  | sophi : Int → SOPHi
  | sopbye : SOPHi
  | fooooo : Int → SOPHi
  deriving Repr

@[plutus_sop]
inductive Maybe (α : Type) where
  | none : Maybe α
  | some : α → Maybe α

@[onchain]
def fff : Int :=
  let bad (x : Maybe SOPHi) : Int :=
    match x with
    | Maybe.none => 0
    | Maybe.some (.sophi a) => a
    | _ => 42
  bad .none

@[onchain]
def ddd (x : Baz) : Int :=
  match x with
    | Baz.baz a b c => a + b + c
    | Baz.bar a b => a + b
    | Baz.aaa a b => a + b
    | Baz.foo a => a + 1
    | Baz.qux => 0

def testMaybe : Maybe Int :=
  .some 42

#print SOPHi.instPlutusData
#print SOPHi.instBEq
-- #eval (fromData (.I 14) : Maybe SOPHi)  -- needs PlutusData (Maybe SOPHi), but Maybe is @[plutus_sop]
-- #eval (toData (.some (.sophi 42) : Maybe SOPHi))
#show_mir testMaybe

#show_beta_mir ddd

#show_optimized_mir ddd

def dddd : Term := compile! ddd

@[plutus_data]
structure A where
  x : Int
  y : Int
  z : Int
  a : Int

@[onchain]
def testing (x : A) (y : A): Int := x.y + x.a + y.y + y.x

def testing2 (x : A) (k : A) : Int :=
  match x with
    | { x, y, z, a } => y + a + k.y + k.x
      -- match k with
      --   | { x:=xa, y:=ya, z:=za, a:=aa } => y + a + ya + aa

@[onchain]
def eee : Baz := Baz.bar 1 2

def eeee : Term := compile! eee

#show_mir eee

#show_mir testing2

#show_opt_trace testing

#show_beta_mir testing

#show_beta_mir testing2

#show_optimized_mir testing

#show_optimized_mir testing2

#show_beta_mir testing

#evaluatePrettyTerm testing ({ x := 1, y := 2, z := 3, a := 4 } : A) ({ x := 5, y := 6, z := 7, a := 8 } : A)

#evaluatePrettyTerm testing

#show_pretty_uplc testing

#evaluatePrettyTerm testing2 ({ x := 1, y := 2, z := 3, a := 4 } : A) ({ x := 5, y := 6, z := 7, a := 8 } : A)

#evaluatePrettyTerm ([1,2,3] : List Int)

#eval ((compile! ddd).Apply eeee).evaluatePretty

#evaluatePrettyTerm (Baz.aaa 1 123)

#evaluatePrettyTerm (ifThenElse (equalsInteger 1 1) (42: Int) 0)

#evaluatePrettyTerm ([(), (), ()] : List Unit)

@[onchain]
def a : List Unit := [(), (), ()]

#show_optimized_mir a

#show_optimized_mir ccc

#eval (aaaa.Apply bbbb).evaluatePretty

#show_mir bbb

#show_optimized_mir aaa

/-! ## Explicit recursion via recursors -/

@[onchain] noncomputable def listSumRecOn (xs : List Int) : Int :=
  List.recOn xs 0 fun x _ ih => x + ih

@[onchain] noncomputable def listSumBrecOn (xs : List Int) : Int :=
  List.brecOn xs fun xs below =>
    match xs with
    | [] => 0
    | x :: _ => x + below.1

@[onchain] noncomputable def listSumRecOnViaHelper (xs : List Int) : Int :=
  listSumRecOn xs

@[onchain] noncomputable def listSumBrecOnViaHelper (xs : List Int) : Int :=
  listSumBrecOn xs

/--
error: compilation of Test.Debug.listSumRecOn failed: translation error: cannot compile Test.Debug.listSumRecOn: explicit recursor List.recOn is unsupported in `compile!` when Lean did not generate Test.Debug.listSumRecOn._sunfold; write recursive equations and let Lean generate `_sunfold`, or use well-founded recursion
-/
#guard_msgs(error) in
#check (compile! listSumRecOn : Term)

/--
error: compilation of Test.Debug.listSumBrecOn failed: translation error: cannot compile Test.Debug.listSumBrecOn: explicit recursor List.brecOn is unsupported in `compile!` when Lean did not generate Test.Debug.listSumBrecOn._sunfold; write recursive equations and let Lean generate `_sunfold`, or use well-founded recursion
-/
#guard_msgs(error) in
#check (compile! listSumBrecOn : Term)

/--
error: compilation of Test.Debug.listSumRecOnViaHelper failed: translation error: cannot compile Test.Debug.listSumRecOn: explicit recursor List.recOn is unsupported in `compile!` when Lean did not generate Test.Debug.listSumRecOn._sunfold; write recursive equations and let Lean generate `_sunfold`, or use well-founded recursion
-/
#guard_msgs(error) in
#check (compile! listSumRecOnViaHelper : Term)

/--
error: compilation of Test.Debug.listSumBrecOnViaHelper failed: translation error: cannot compile Test.Debug.listSumBrecOn: explicit recursor List.brecOn is unsupported in `compile!` when Lean did not generate Test.Debug.listSumBrecOn._sunfold; write recursive equations and let Lean generate `_sunfold`, or use well-founded recursion
-/
#guard_msgs(error) in
#check (compile! listSumBrecOnViaHelper : Term)

/-! ## Recursive SOP type (structural recursion) -/

inductive Tree where
  | leaf : Int → Tree
  | node : Tree → Tree → Tree

@[onchain]
def treeSum (t : Tree) : Int :=
  match t with
  | .leaf n => n
  | .node l r => treeSum l + treeSum r

@[onchain]
def treeLeaf5 : Tree := .leaf 5

@[onchain]
def treeSmall : Tree := .node (.leaf 2) (.leaf 3)

@[onchain]
def treeBig : Tree := .node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))


@[onchain]
def eqTxOutRef (a b : TxOutRef) : Bool :=
  ifThenElse (equalsByteString a.id b.id)
    (equalsInteger a.idx b.idx)
    false

@[onchain]
def findInputByOutRef (inputs : List TxInInfo) (ref : TxOutRef) : Maybe TxInInfo :=
  match inputs with
  | [] => .none
  | x :: xs =>
    if x.outRef == ref
    then .some x
    else findInputByOutRef xs ref

#show_optimized_mir findInputByOutRef

#show_pretty_uplc findInputByOutRef

@[onchain]
def testingIns : List TxInInfo := [{ outRef := { id := "12312123", idx := 0 }, resolved := { address := { credential := .scriptCredential "aaaa", stakingCredential := .nothingData}, value := .mk [], datum := .noOutputDatum, referenceScript := .nothingData } }]
@[onchain]
def testingRef : TxOutRef := { id := "abc", idx := 0 }

#show_mir testingIns
#show_optimized_mir testingIns
#evaluatePrettyTerm testingIns

@[onchain]
def addall (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: xs => x + addall xs

#show_optimized_mir addall

@[onchain]
def hello (x : Bool) : Int :=
  if x then 42 else 0
  -- match x with
  -- | true => 42
  -- | false => 0

#show_optimized_mir hello
#evaluatePrettyTerm hello false

/-! ## PlutusData fromData safety -/

/-! ## Abbrev field test types for PlutusData -/

-- Structure with Int abbrev fields (Lovelace, POSIXTime)
@[plutus_data]
structure TestPayment where
  amount : Lovelace
  time   : POSIXTime

-- Multi-constructor with mixed abbrev fields
@[plutus_data]
inductive TestAction where
  | pay      : Lovelace → TestAction
  | certify  : Int → TestAction
  | empty    : TestAction

-- Nested @[plutus_data] type as a field
@[plutus_data]
structure TestNested where
  inner : Bar
  tag   : Int

-- Structure with POSIXTime abbrev fields
@[plutus_data]
structure TestTime where
  start : POSIXTime
  end_  : POSIXTime

-- Onchain construction functions for abbrev types
@[onchain]
def mkTestPayment : TestPayment :=
  { amount := 1000000, time := 42 }

@[onchain]
def mkTestActionPay : TestAction :=
  .pay 500

@[onchain]
def mkTestActionEmpty : TestAction :=
  .empty

@[onchain]
def mkTestNested : TestNested :=
  { inner := { x := 10, y := 20, z := 30 }, tag := 7 }

@[onchain]
def mkTestTime : TestTime :=
  { start := 1000, end_ := 2000 }

-- Onchain match on abbrev fields
@[onchain]
def extractLovelace (p : TestPayment) : Int := p.amount

@[onchain]
def matchTestAction (a : TestAction) : Int :=
  match a with
  | .pay amt => amt
  | .certify _ => -1
  | .empty => 0

@[onchain]
def extractPOSIXTime (t : TestTime) : Int := t.start + t.end_

/-! ## BEq on @[plutus_data] types -/

@[onchain]
def eqBar (a b : Bar) : Bool := a == b

@[onchain]
def eqBaz (a b : Baz) : Bool := a == b

#show_optimized_mir eqBar
#show_optimized_mir eqBaz

end Test.Debug


/-
MIR for Test.Debug.findInputByOutRef:
fix Test.Debug.findInputByOutRef_0 =
  λinputs_1 ref_2.
    force ((force (force chooseList)) inputs_1 (delay
      constr(0)) (delay
      let head_3 = (force headList) inputs_1
      let tail_4 = (force tailList) inputs_1
      in
        force ((force ifThenElse) ((case constr(0 (λa_9 b_10.
          let fields_14 = (force (force sndPair)) (unConstrData a_9)
          let fields_24 = (force (force sndPair)) (unConstrData b_10)
          in
            equalsData constr(0 0 ((force mkCons) constr(4 (unBData ((force headList) fields_14))) ((force mkCons) constr(3 (unIData ((force headList) ((force tailList) fields_14)))) []))) constr(0 0 ((force mkCons) constr(4 (unBData ((force headList) fields_24))) ((force mkCons) constr(3 (unIData ((force headList) ((force tailList) fields_24)))) []))))) of
          | λsf0_8.
            sf0_8) ((force headList) ((force (force sndPair)) (unConstrData head_3))) ref_2) (delay
          constr(1 head_3)) (delay Test.Debug.findInputByOutRef_0 tail_4 ref_2))))
-/

#show_expr Moist.Cardano.V3.TxOutRef.instBEq
