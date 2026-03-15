import Moist.Onchain
import Moist.Plutus.Pretty
import Moist.Onchain.Prelude
import Moist.Plutus.Eval

open Moist.Plutus.Term
open Moist.Plutus.Pretty (prettyTerm)
open Moist.Onchain.Prelude
open Moist.Plutus.Eval
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

@[plutus_data]
inductive Maybe α where
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

#show_mir ddd

#show_beta_mir ddd

#show_optimized_mir ddd

def dddd : Term := compile! ddd

@[plutus_sop]
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

#show_mir testing

#show_mir testing2

#show_opt_trace testing

#show_beta_mir testing

#show_beta_mir testing2

#show_optimized_mir testing

#show_optimized_mir testing2

#show_beta_mir testing

#evaluatePrettyTerm testing ({ x := 1, y := 2, z := 3, a := 4 } : A) ({ x := 5, y := 6, z := 7, a := 8 } : A)

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

@[onchain]
def intListNil : List Int := []

@[onchain]
def intList123 : List Int := [1, 2, 3]

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

end Test.Debug


/-
let anf_1001 = force (force sndPair)
let anf_1002 = force tailList
let anf_1003 = force headList
in
  λx_0.
    let pair_2 = unConstrData x_0
    in
      addInteger
        (unIData (anf_1003 (anf_1002 (anf_1001 pair_2))))
        (unIData (anf_1003 (anf_1002 (anf_1002 (anf_1002 (anf_1001 pair_2))))))
-/
