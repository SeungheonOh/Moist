import Moist.Onchain
import PlutusCore.UPLC.CekMachine
import Moist.Plutus.Convert
import Blaster

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! ## Builtin spec axioms (state what Plutus builtins actually compute) -/

axiom subtractInteger_eq (x y : Int) : subtractInteger x y = x - y
axiom lessThanEqInteger_iff (x y : Int) : lessThanEqInteger x y = decide (x ≤ y)

/-- Standard termination tactic for Plutus-builtin recursive functions. -/
macro "plutus_decreasing" : tactic =>
  `(tactic| first
    | (simp only [subtractInteger_eq]; rename_i h; simp only [lessThanEqInteger_iff, decide_eq_true_eq] at h; omega)
    | (rename_i h; simp only [lessThanEqInteger_iff, decide_eq_true_eq] at h; omega))

/-! ## CEK result extraction -/

def integerToBuiltin (x : Int) : Term := .Const (.Integer x)

def fromFrameToInt : State → Option Int
  | .Halt (.VCon (.Integer n)) => some n
  | _ => none

def getIntResult (prog : Program) (args : List Term) (fuel : Nat := 500) : Int :=
  match fromFrameToInt (cekExecuteProgram prog args fuel) with
  | some n => n
  | none => 0

def mkProg (t : Term) : Program := .Program (.Version 1 1 0) t

/-! -----------------------------------------------------------
    § 1  Factorial — compiled UPLC = Lean reference
    ----------------------------------------------------------- -/

@[onchain] noncomputable def factorial (n : Int) : Int :=
  if lessThanEqInteger n 1 then 1
  else multiplyInteger n (factorial (subtractInteger n 1))
termination_by n.toNat
decreasing_by plutus_decreasing

def factorialUPLC : Term := compile! factorial
def factorialProg : Program := mkProg factorialUPLC

def leanFactorial (n : Int) : Int :=
  if n ≤ 1 then 1 else n * leanFactorial (n - 1)
termination_by n.toNat
decreasing_by omega

#blaster (unfold-depth: 600) (timeout: 120)
  [∀ x : Int,
    (fromFrameToInt $ cekExecuteProgram factorialProg [integerToBuiltin x] 500).isSome →
    getIntResult factorialProg [integerToBuiltin x] 500 = leanFactorial x]

/-! -----------------------------------------------------------
    § 2  Fibonacci — compiled UPLC = Lean reference
    ----------------------------------------------------------- -/

@[onchain] def fib (n : Int) : Int :=
  if lessThanEqInteger n 1
  then n
  else fib (n - 1) + fib (n - 2)
termination_by n.toNat
decreasing_by all_goals plutus_decreasing

def fibUPLC : Term := compile! fib
def fibProg : Program := mkProg fibUPLC

def referenceFib (n : Int) : Int :=
  if n ≤ 1 then n else referenceFib (n - 1) + referenceFib (n - 2)
termination_by n.toNat
decreasing_by all_goals omega

-- Shows that result from UPLC evaluation matches result of Lean evaluation
#blaster (unfold-depth: 600) (timeout: 120)
  [∀ x : Int,
    (fromFrameToInt $ cekExecuteProgram fibProg [integerToBuiltin x] 500).isSome →
    getIntResult fibProg [integerToBuiltin x] 500 = fib x]

-- Shows that UPLC matches the behavior of reference fib function identically
#blaster (unfold-depth: 600) (timeout: 120)
  [∀ x : Int,
    (fromFrameToInt $ cekExecuteProgram fibProg [integerToBuiltin x] 500).isSome →
    getIntResult fibProg [integerToBuiltin x] 500 = referenceFib x]

/-! -----------------------------------------------------------
    § 3  Sum to N — compiled UPLC = Lean reference + Gauss
    ----------------------------------------------------------- -/

@[onchain] noncomputable def sumTo (n : Int) : Int :=
  if lessThanEqInteger n 0 then 0
  else addInteger n (sumTo (subtractInteger n 1))
termination_by n.toNat
decreasing_by plutus_decreasing

def sumToUPLC : Term := compile! sumTo
def sumToProg : Program := mkProg sumToUPLC

def leanSumTo (n : Int) : Int :=
  if n ≤ 0 then 0 else n + leanSumTo (n - 1)
termination_by n.toNat
decreasing_by omega

#blaster (unfold-depth: 600) (timeout: 120)
  [∀ x : Int,
    (fromFrameToInt $ cekExecuteProgram sumToProg [integerToBuiltin x] 500).isSome →
    getIntResult sumToProg [integerToBuiltin x] 500 = leanSumTo x]

-- Gauss formula: for 0 ≤ n ≤ 5, compiled sumTo(n) = n*(n+1)/2
#blaster (unfold-depth: 600) (timeout: 120)
  [∀ x : Int, 0 ≤ x → x ≤ 5 →
    (fromFrameToInt $ cekExecuteProgram sumToProg [integerToBuiltin x] 500).isSome →
    getIntResult sumToProg [integerToBuiltin x] 500 = x * (x + 1) / 2]

/-! -----------------------------------------------------------
    § 4  Arithmetic — ∀ inputs
    ----------------------------------------------------------- -/

@[onchain] noncomputable def double (x : Int) : Int := addInteger x x
@[onchain] noncomputable def square (x : Int) : Int := multiplyInteger x x
@[onchain] noncomputable def mulAdd (x y z : Int) : Int := addInteger (multiplyInteger x y) z

def doubleProg := mkProg (compile! double)
def squareProg := mkProg (compile! square)
def mulAddProg := mkProg (compile! mulAdd)

#blaster (unfold-depth: 80)
  [∀ x : Int, getIntResult doubleProg [integerToBuiltin x] = 2 * x]

#blaster (unfold-depth: 80)
  [∀ x : Int, getIntResult squareProg [integerToBuiltin x] = x * x]

#blaster (unfold-depth: 100)
  [∀ x y z : Int,
    getIntResult mulAddProg [integerToBuiltin x, integerToBuiltin y, integerToBuiltin z] 100 = x * y + z]

-- Cross-function: double(x) = mulAdd(2, x, 0)
#blaster (unfold-depth: 100)
  [∀ x : Int,
    getIntResult doubleProg [integerToBuiltin x] 100 =
    getIntResult mulAddProg [integerToBuiltin 2, integerToBuiltin x, integerToBuiltin 0] 100]

-- Distributivity through compilation: 2(x+y) = 2x + 2y
@[onchain] noncomputable def distL (x y : Int) : Int := multiplyInteger 2 (addInteger x y)
@[onchain] noncomputable def distR (x y : Int) : Int := addInteger (multiplyInteger 2 x) (multiplyInteger 2 y)

#blaster (unfold-depth: 120)
  [∀ x y : Int,
    getIntResult (mkProg (compile! distL)) [integerToBuiltin x, integerToBuiltin y] 120 =
    getIntResult (mkProg (compile! distR)) [integerToBuiltin x, integerToBuiltin y] 120]

/-! -----------------------------------------------------------
    § 5  findInputByOutRef — Data-encoded, ∀-quantified
    ----------------------------------------------------------- -/

@[plutus_sop]
inductive Maybe (α : Type) where
  | none : Maybe α
  | some : α → Maybe α

@[onchain]
def findInputByOutRef (inputs : List TxInInfo) (ref : TxOutRef) : Maybe TxInInfo :=
  match inputs with
  | [] => .none
  | x :: xs =>
    if x.outRef == ref then .some x
    else findInputByOutRef xs ref

def findUPLC := compile! findInputByOutRef

def mkRef (txId : ByteString) (idx : Int) : Data := .Constr 0 [.B txId, .I idx]
def stubTxOut : Data :=
  .Constr 0 [.Constr 0 [.Constr 0 [.B ⟨""⟩], .Constr 1 []], .Map [], .Constr 0 [], .Constr 1 []]
def mkInput (txId : ByteString) (idx : Int) : Data := .Constr 0 [mkRef txId idx, stubTxOut]

def exec (t : Term) (n : Nat := 200) : State :=
  cekExecuteProgram (.Program (.Version 1 1 0) t) [] n
def app (t : Term) (args : List Term) : Term := args.foldl .Apply t

-- ∀ ref, find [] ref = None
#blaster (unfold-depth: 200) (timeout: 30)
  [∀ (txId : ByteString) (idx : Int),
    exec (app findUPLC [.Const (.ConstDataList []), .Const (.Data (mkRef txId idx))]) 300 =
    .Halt (.VConstr 0 [])]

-- ∀ ref, find [ref] ref = Some(ref)
#blaster (unfold-depth: 300) (timeout: 60)
  [∀ (txId : ByteString) (idx : Int),
    let ref   := mkRef txId idx
    let input := mkInput txId idx
    exec (app findUPLC [.Const (.ConstDataList [input]), .Const (.Data ref)]) 500 =
    .Halt (.VConstr 1 [.VCon (.Data input)])]

-- ∀ ref₁ ≠ ref₂, find [input₂] ref₁ = None
#blaster (unfold-depth: 300) (timeout: 60)
  [∀ (id1 : ByteString) (i1 : Int) (id2 : ByteString) (i2 : Int),
    mkRef id1 i1 ≠ mkRef id2 i2 →
    exec (app findUPLC [.Const (.ConstDataList [mkInput id2 i2]), .Const (.Data (mkRef id1 i1))]) 500 =
    .Halt (.VConstr 0 [])]

@[plutus_sop]
structure Eras where
  Byron : Int
  Shelley : Int
  Allegra : Int
  Mary : Int
  Alonzo : Int
  Babbage : Int
  Conway : Int

@[onchain]
def foo (e : Eras) (f : Eras) : Int := e.Byron + e.Shelley + f.Mary + f.Conway

#show_optimized_mir foo
