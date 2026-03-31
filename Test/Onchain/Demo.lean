import Moist.Onchain
import Test.Onchain.CompileFvt
import PlutusCore.UPLC.CekMachine
import Blaster

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.Data (Data)
open PlutusCore.ByteString (ByteString)
open Moist.Onchain.Prelude
open Moist.Cardano.V3

/-! ## Builtin spec axioms (state what Plutus builtins actually compute) -/

opaque subtractInteger_eq (x y : Int) : subtractInteger x y = x - y := sorry
opaque lessThanEqInteger_iff (x y : Int) : lessThanEqInteger x y = decide (x ≤ y) := sorry

/-- Standard termination tactic for Plutus-builtin recursive functions. -/
macro "plutus_decreasing" : tactic =>
  `(tactic| first
    | (simp only [subtractInteger_eq]; rename_i h; simp only [lessThanEqInteger_iff, decide_eq_true_eq] at h; omega)
    | (rename_i h; simp only [lessThanEqInteger_iff, decide_eq_true_eq] at h; omega))

/-! ## CEK result extraction helpers -/

def integerToBuiltin (x : Int) : Term := .Const (.Integer x)

def fromFrameToInt : State → Option Int
  | .Halt (.VCon (.Integer n)) => some n
  | _ => none

def getIntResult (prog : Program) (args : List Term) (fuel : Nat := 500) : Int :=
  match fromFrameToInt (cekExecuteProgram prog args fuel) with
  | some n => n
  | none => 0

def mkProg (t : Term) : Program := .Program (.Version 1 1 0) t

def mkRef (txId : ByteString) (idx : Int) : Data := .Constr 0 [.B txId, .I idx]
def stubTxOut : Data :=
  .Constr 0 [.Constr 0 [.Constr 0 [.B ⟨""⟩], .Constr 1 []], .Map [], .Constr 0 [], .Constr 1 []]
def mkInput (txId : ByteString) (idx : Int) : Data := .Constr 0 [mkRef txId idx, stubTxOut]

def exec (t : Term) (n : Nat := 200) : State :=
  cekExecuteProgram (.Program (.Version 1 1 0) t) [] n
def app (t : Term) (args : List Term) : Term := args.foldl .Apply t



















@[plutus_data]
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

@[plutus_sop]
inductive Maybe (α : Type) where
  | none : Maybe α
  | some : α → Maybe α

@[onchain]
def findInputByOutRef (inputs : List TxInInfo) (ref : TxOutRef) : Maybe TxInInfo :=
  match inputs with
  | [x] => .some x -- now, let's make it always return first element
  | _ => .none

def findUPLC := compile_fvt! findInputByOutRef

#show_optimized_mir findInputByOutRef
#show_pretty_uplc findInputByOutRef
#show_opt_trace findInputByOutRef

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
-- NOTE: Expected to fail — current impl ignores ref, always returns Some for singleton
#blaster (unfold-depth: 300) (timeout: 60)
  [∀ (id1 : ByteString) (i1 : Int) (id2 : ByteString) (i2 : Int),
    mkRef id1 i1 ≠ mkRef id2 i2 →
    exec (app findUPLC [.Const (.ConstDataList [mkInput id2 i2]), .Const (.Data (mkRef id1 i1))]) 500 =
    .Halt (.VConstr 0 [])]
