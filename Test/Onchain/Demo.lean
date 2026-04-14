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
  | x :: xs => if x.outRef == ref then .some x else findInputByOutRef xs ref
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

















/-! ## Demo: k-of-n multisig with monotonicity proofs

Count how many of the `required` signers appear in the actual `signers`
list, and check it meets the `threshold`. We prove two safety properties
*directly on the Lean definition* — the same definition that compiles
down to UPLC. -/

@[onchain]
def isMember (k : PubKeyHash) (ks : List PubKeyHash) : Bool :=
  match ks with
  | [] => false
  | x :: xs =>
    match equalsByteString k x with
    | true => true
    | false => isMember k xs

@[onchain]
def countSigners (required signers : List PubKeyHash) : Int :=
  match required with
  | [] => 0
  | r :: rs =>
    match isMember r signers with
    | true => addInteger 1 (countSigners rs signers)
    | false => countSigners rs signers

@[onchain]
def hasEnoughSigs (required signers : List PubKeyHash) (threshold : Int) : Bool :=
  lessThanEqInteger threshold (countSigners required signers)

def hasEnoughSigsUPLC := compile_fvt! hasEnoughSigs
#show_pretty_uplc hasEnoughSigs

-- Sanity: 2-of-3 multisig, two signers present → accepted.
#eval hasEnoughSigs
  [ByteArray.mk #[1], ByteArray.mk #[2], ByteArray.mk #[3]]
  [ByteArray.mk #[1], ByteArray.mk #[2]]
  2
-- Same keys, threshold 3 → rejected.
#eval hasEnoughSigs
  [ByteArray.mk #[1], ByteArray.mk #[2], ByteArray.mk #[3]]
  [ByteArray.mk #[1], ByteArray.mk #[2]]
  3

-- Run the compiled UPLC on the CEK machine: 2-of-3 passes.
#evaluatePrettyTerm
  (hasEnoughSigs
    ([ByteArray.mk #[1], ByteArray.mk #[2], ByteArray.mk #[3]] : List PubKeyHash)
    ([ByteArray.mk #[1], ByteArray.mk #[2]] : List PubKeyHash)
    (2 : Int))
-- Same signers, threshold 3 → the CEK machine returns false.
#evaluatePrettyTerm
  (hasEnoughSigs
    ([ByteArray.mk #[1], ByteArray.mk #[2], ByteArray.mk #[3]] : List PubKeyHash)
    ([ByteArray.mk #[1], ByteArray.mk #[2]] : List PubKeyHash)
    (3 : Int))


/-- Extending the signer list can only make membership *more* true. -/
theorem isMember_cons (k s : PubKeyHash) (sigs : List PubKeyHash) :
    isMember k sigs = true → isMember k (s :: sigs) = true := by
  intro h
  show (match equalsByteString k s with
        | true => true
        | false => isMember k sigs) = true
  generalize equalsByteString k s = b
  cases b
  · exact h
  · rfl

/-- Adding a signer never decreases how many required keys we count. -/
theorem countSigners_le_cons (req sigs : List PubKeyHash) (s : PubKeyHash) :
    countSigners req sigs ≤ countSigners req (s :: sigs) := by
  induction req with
  | nil =>
    show (0 : Int) ≤ 0
    omega
  | cons r rs ih =>
    show (match isMember r sigs with
          | true => (1 : Int) + countSigners rs sigs
          | false => countSigners rs sigs) ≤
         (match isMember r (s :: sigs) with
          | true => (1 : Int) + countSigners rs (s :: sigs)
          | false => countSigners rs (s :: sigs))
    generalize hb1 : isMember r sigs = b1
    generalize hb2 : isMember r (s :: sigs) = b2
    cases b1 with
    | false =>
      cases b2 with
      | false => exact ih
      | true =>
        show countSigners rs sigs ≤ (1 : Int) + countSigners rs (s :: sigs)
        omega
    | true =>
      have hcons := isMember_cons r s sigs hb1
      cases b2 with
      | false => rw [hb2] at hcons; contradiction
      | true =>
        show (1 : Int) + countSigners rs sigs ≤ (1 : Int) + countSigners rs (s :: sigs)
        omega

/-- **Threshold monotonicity.** Lowering `threshold` can only keep a
valid signer set valid — you never lose validity by asking for fewer
signatures. -/
theorem hasEnoughSigs_mono_threshold
    (req sig : List PubKeyHash) (t t' : Int) :
    t' ≤ t →
    hasEnoughSigs req sig t = true →
    hasEnoughSigs req sig t' = true := by
  intro ht h
  simp only [hasEnoughSigs, lessThanEqInteger, decide_eq_true_eq] at h ⊢
  omega

/-- **Subset closure.** Adding an extra signer can only keep a valid
signer set valid — no one can invalidate a passing tx by showing up. -/
theorem hasEnoughSigs_mono_signers
    (req sig : List PubKeyHash) (s : PubKeyHash) (t : Int) :
    hasEnoughSigs req sig t = true →
    hasEnoughSigs req (s :: sig) t = true := by
  intro h
  have step := countSigners_le_cons req sig s
  simp only [hasEnoughSigs, lessThanEqInteger, decide_eq_true_eq] at h ⊢
  omega


















/-! ## Demo: AMM constant-product swap with invariant proofs

A fee-less Uniswap-style swap: deposit `dx` of token X, withdraw `dy`
of token Y. The swap is valid iff the constant-product invariant
`(x+dx) * (y-dy) ≥ x*y` is preserved. We prove:
  • The no-op swap is always valid.
  • Sequential composition: two valid swaps preserve the invariant
    from the original starting state. -/

@[onchain]
def validSwap (x y dx dy : Int) : Bool :=
  lessThanEqInteger (x * y) ((x + dx) * (y - dy))

def validSwapUPLC := compile_fvt! validSwap
#show_pretty_uplc validSwap

-- Sanity: put in 10, take out 9 on a 100/100 pool: 110*91 = 10010 ≥ 10000.
#eval validSwap 100 100 10 9
-- Put in 10, take out 11: 110*89 = 9790 < 10000 → rejected.
#eval validSwap 100 100 10 11

-- Run the compiled UPLC on the CEK machine (honest swap accepted).
#evaluatePrettyTerm validSwap (100 : Int) (100 : Int) (10 : Int) (9 : Int)
-- CEK rejects the over-withdraw that breaks the invariant.
#evaluatePrettyTerm validSwap (100 : Int) (100 : Int) (10 : Int) (11 : Int)

-- Concrete: 110 × 91 = 10010 ≥ 10000 so the CEK accepts this swap.
#blaster (unfold-depth: 300) (timeout: 60)
  [exec (app validSwapUPLC
            [.Const (.Integer 100), .Const (.Integer 100),
             .Const (.Integer 10),  .Const (.Integer 9)]) 500 =
    .Halt (.VCon (.Bool true))]

-- Concrete: 110 × 89 = 9790 < 10000, invariant broken, CEK rejects.
#blaster (unfold-depth: 300) (timeout: 60)
  [exec (app validSwapUPLC
            [.Const (.Integer 100), .Const (.Integer 100),
             .Const (.Integer 10),  .Const (.Integer 11)]) 500 =
    .Halt (.VCon (.Bool false))]

-- ∀ pool, the no-op swap (0 in, 0 out) runs through the CEK and
-- always returns true. This is the `validSwap_noop` theorem as a
-- symbolic execution test.
#blaster (unfold-depth: 300) (timeout: 60)
  [∀ (x y : Int),
    exec (app validSwapUPLC
              [.Const (.Integer x), .Const (.Integer y),
               .Const (.Integer 0), .Const (.Integer 0)]) 500 =
    .Halt (.VCon (.Bool true))]

-- Whenever the constant-product invariant is preserved, the CEK
-- accepts the swap — symbolic counterpart to `validSwap_unfold.mpr`.
#blaster (unfold-depth: 300) (timeout: 60)
  [∀ (x y dx dy : Int),
    x * y ≤ (x + dx) * (y - dy) →
    exec (app validSwapUPLC
              [.Const (.Integer x),  .Const (.Integer y),
               .Const (.Integer dx), .Const (.Integer dy)]) 500 =
    .Halt (.VCon (.Bool true))]

-- And whenever the invariant is broken, the CEK rejects it.
#blaster (unfold-depth: 300) (timeout: 60)
  [∀ (x y dx dy : Int),
    (x + dx) * (y - dy) < x * y →
    exec (app validSwapUPLC
              [.Const (.Integer x),  .Const (.Integer y),
               .Const (.Integer dx), .Const (.Integer dy)]) 500 =
    .Halt (.VCon (.Bool false))]

/-- The swap check unfolds to the constant-product inequality. -/
theorem validSwap_unfold (x y dx dy : Int) :
    validSwap x y dx dy = true ↔ x * y ≤ (x + dx) * (y - dy) := by
  simp only [validSwap, lessThanEqInteger_iff, decide_eq_true_eq]

/-- **No-op safety.** Swapping nothing is always valid. -/
theorem validSwap_noop (x y : Int) : validSwap x y 0 0 = true := by
  rw [validSwap_unfold]; simp

/-- **Sequential composition.** Two consecutive valid swaps preserve
the constant-product invariant relative to the *original* pool state. -/
theorem validSwap_compose
    (x y dx1 dy1 dx2 dy2 : Int) :
    validSwap x y dx1 dy1 = true →
    validSwap (x + dx1) (y - dy1) dx2 dy2 = true →
    x * y ≤ (x + dx1 + dx2) * (y - dy1 - dy2) := by
  intro h1 h2
  rw [validSwap_unfold] at h1 h2
  calc x * y
      ≤ (x + dx1) * (y - dy1) := h1
    _ ≤ (x + dx1 + dx2) * (y - dy1 - dy2) := h2
