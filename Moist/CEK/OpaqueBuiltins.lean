import Moist.CEK.SemVariant

/-! # Uninterpreted cryptographic builtins

The model does not implement hashing, signature verification or BLS12-381
arithmetic. Instead, the semantics of those builtins is given by the `opaque`
constants below. The kernel cannot unfold an `opaque` constant, so a theorem
about the model holds for *every* function of the stated type — in particular
for the real one. No proof can rely on a particular result (or on a failure) of
these builtins; it can only rely on their types (e.g. a signature check returns
a `Bool` when it succeeds) and on determinism.

Each constant takes the builtin semantics variant, so results may differ per
variant (variant E bounds the size of some arguments).

At runtime (`#eval`, the conformance runner, the test executables) each constant
runs the implementation named by `@[implemented_by]`, which calls the Zig FFI in
`ffi/ffi.zig` (Zig `std.crypto` and blst). Introducing an `opaque` constant adds
no axiom.

BLS12-381 points are represented by their canonical compressed encodings (48
bytes for G1, 96 for G2); Miller-loop results by an implementation-defined byte
serialisation.
-/

namespace Moist.CEK.Opaque

open Moist.Plutus (ByteString)

/-- The hash builtins. -/
inductive HashFun
  | sha2_256 | sha3_256 | blake2b_224 | blake2b_256 | keccak_256 | ripemd_160
deriving DecidableEq, Repr

/-- The signature-verification builtins. -/
inductive SigScheme
  | ed25519 | ecdsaSecp256k1 | schnorrSecp256k1
deriving DecidableEq, Repr

/-- The two BLS12-381 groups. -/
inductive Group
  | g1 | g2
deriving DecidableEq, Repr

/-! ## Runtime implementations (never seen by the kernel) -/

/-- FFI codes. -/
def HashFun.code : HashFun → UInt8
  | .sha2_256 => 0 | .sha3_256 => 1 | .blake2b_224 => 2
  | .blake2b_256 => 3 | .keccak_256 => 4 | .ripemd_160 => 5

def SigScheme.code : SigScheme → UInt8
  | .ed25519 => 0 | .ecdsaSecp256k1 => 1 | .schnorrSecp256k1 => 2

def Group.base : Group → UInt8
  | .g1 => 0 | .g2 => 10


namespace Runtime

@[extern "moist_crypto_hash"]
opaque ffiHash (code : UInt8) (input : @& ByteArray) : ByteArray

@[extern "moist_crypto_verify"]
opaque ffiVerify (code : UInt8) (pk : @& ByteArray) (msg : @& ByteArray) (sig : @& ByteArray) : ByteArray

@[extern "moist_crypto_bls"]
opaque ffiBls (op : UInt8) (a : @& ByteArray) (b : @& ByteArray) : ByteArray

/-- Decode the FFI status byte: `0` = failure, `1` = success followed by the result. -/
def status (r : ByteArray) : Option ByteArray :=
  if r.size ≥ 1 && r.get! 0 == 1 then some (r.extract 1 r.size) else none

def statusBool (r : ByteArray) : Option Bool :=
  (status r).map fun b => b.size == 1 && b.get! 0 == 1

/-- The order of the BLS12-381 groups G1 and G2. -/
def groupOrder : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- `msmScalarLb ≤ s ≤ msmScalarUb` (PlutusCore.Crypto.BLS12_381.Bounds). -/
def msmScalarInBounds (s : Int) : Bool :=
  decide (-((2 ^ 4095 : Nat) : Int) ≤ s) && decide (s ≤ ((2 ^ 4095 : Nat) : Int) - 1)

/-- A scalar reduced modulo the group order, as 32 little-endian bytes.
Every point lies in the prime-order subgroup, so `[k]P = [k mod r]P`. -/
def scalarBytes (k : Int) : ByteArray := Id.run do
  let mut n := (k % (groupOrder : Int)).toNat
  let mut out := ByteArray.emptyWithCapacity 32
  for _ in [:32] do
    out := out.push n.toUInt8
    n := n / 256
  return out

/-- The compressed encoding of the identity point. -/
def identity : Group → ByteArray
  | .g1 => ByteArray.mk (#[0xc0] ++ Array.replicate 47 0)
  | .g2 => ByteArray.mk (#[0xc0] ++ Array.replicate 95 0)

def hash [sv : SemVariant] (f : HashFun) (input : ByteString) : Option ByteString :=
  -- every hash builtin unlifts its argument as `CByteString` in ensurable variants
  if cByteStringOk sv input then status (ffiHash f.code input) else none

def verifySignature [sv : SemVariant] (scheme : SigScheme) (pk msg sig : ByteString) : Option Bool :=
  -- Ed25519 and Schnorr unlift the message as `CByteString` in ensurable variants
  let msgOk := match scheme with
    | .ecdsaSecp256k1 => true
    | _ => cByteStringOk sv msg
  if msgOk then statusBool (ffiVerify scheme.code pk msg sig) else none

def blsAdd [SemVariant] (g : Group) (p q : ByteString) : Option ByteString :=
  status (ffiBls (g.base + 0) p q)

def blsNeg [SemVariant] (g : Group) (p : ByteString) : Option ByteString :=
  status (ffiBls (g.base + 1) p ByteArray.empty)

def blsScalarMul [sv : SemVariant] (g : Group) (k : Int) (p : ByteString) : Option ByteString :=
  -- `scalarMulE` (ensurable variants) rejects scalars beyond the 512-byte bound
  if sv.ensurable && !msmScalarInBounds k then none
  else status (ffiBls (g.base + 2) (scalarBytes k) p)

def blsEqual [SemVariant] (g : Group) (p q : ByteString) : Option Bool :=
  statusBool (ffiBls (g.base + 3) p q)

def blsHashToGroup [sv : SemVariant] (g : Group) (msg dst : ByteString) : Option ByteString :=
  if cByteStringOk sv msg then status (ffiBls (g.base + 4) msg dst) else none

def blsCompress [SemVariant] (_ : Group) (p : ByteString) : Option ByteString :=
  some p

def blsUncompress [SemVariant] (g : Group) (bytes : ByteString) : Option ByteString :=
  status (ffiBls (g.base + 5) bytes ByteArray.empty)

def blsMultiScalarMul [sv : SemVariant] (g : Group) (scalars : List Int) (points : List ByteString) :
    Option ByteString :=
  if scalars.any (fun s => !msmScalarInBounds s) then none
  else (scalars.zip points).foldlM (init := identity g) fun acc (s, p) => do
    let term ← blsScalarMul (sv := sv) g s p
    blsAdd g acc term

def millerLoop [SemVariant] (p q : ByteString) : Option ByteString :=
  status (ffiBls 20 p q)

def mulMlResult [SemVariant] (a b : ByteString) : Option ByteString :=
  status (ffiBls 21 a b)

def finalVerify [SemVariant] (a b : ByteString) : Option Bool :=
  statusBool (ffiBls 22 a b)

end Runtime

/-! ## The uninterpreted semantics -/

/-- `sha2_256`, `sha3_256`, `blake2b_224`, `blake2b_256`, `keccak_256`, `ripemd_160`. -/
@[implemented_by Runtime.hash]
opaque hash [sv : SemVariant] (f : HashFun) (input : ByteString) : Option ByteString

/-- `verifyEd25519Signature`, `verifyEcdsaSecp256k1Signature`,
`verifySchnorrSecp256k1Signature` applied to key, message and signature. -/
@[implemented_by Runtime.verifySignature]
opaque verifySignature [sv : SemVariant] (scheme : SigScheme) (pk msg sig : ByteString) : Option Bool

/-- `bls12_381_G*_add`. -/
@[implemented_by Runtime.blsAdd]
opaque blsAdd [sv : SemVariant] (g : Group) (p q : ByteString) : Option ByteString

/-- `bls12_381_G*_neg`. -/
@[implemented_by Runtime.blsNeg]
opaque blsNeg [sv : SemVariant] (g : Group) (p : ByteString) : Option ByteString

/-- `bls12_381_G*_scalarMul`. -/
@[implemented_by Runtime.blsScalarMul]
opaque blsScalarMul [sv : SemVariant] (g : Group) (k : Int) (p : ByteString) : Option ByteString

/-- `bls12_381_G*_equal`. -/
@[implemented_by Runtime.blsEqual]
opaque blsEqual [sv : SemVariant] (g : Group) (p q : ByteString) : Option Bool

/-- `bls12_381_G*_hashToGroup` applied to message and domain separation tag. -/
@[implemented_by Runtime.blsHashToGroup]
opaque blsHashToGroup [sv : SemVariant] (g : Group) (msg dst : ByteString) : Option ByteString

/-- `bls12_381_G*_compress`. -/
@[implemented_by Runtime.blsCompress]
opaque blsCompress [sv : SemVariant] (g : Group) (p : ByteString) : Option ByteString

/-- `bls12_381_G*_uncompress`; also used to validate point literals. -/
@[implemented_by Runtime.blsUncompress]
opaque blsUncompress [sv : SemVariant] (g : Group) (bytes : ByteString) : Option ByteString

/-- `bls12_381_G*_multiScalarMul`. -/
@[implemented_by Runtime.blsMultiScalarMul]
opaque blsMultiScalarMul [sv : SemVariant] (g : Group) (scalars : List Int) (points : List ByteString) :
    Option ByteString

/-- `bls12_381_millerLoop`. -/
@[implemented_by Runtime.millerLoop]
opaque millerLoop [sv : SemVariant] (p q : ByteString) : Option ByteString

/-- `bls12_381_mulMlResult`. -/
@[implemented_by Runtime.mulMlResult]
opaque mulMlResult [sv : SemVariant] (a b : ByteString) : Option ByteString

/-- `bls12_381_finalVerify`. -/
@[implemented_by Runtime.finalVerify]
opaque finalVerify [sv : SemVariant] (a b : ByteString) : Option Bool

end Moist.CEK.Opaque
