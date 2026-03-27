import Lean
import Moist.Plutus.Term

namespace Moist.Onchain

open Lean
open Moist.Plutus.Term

/-- Map from Lean fully-qualified names to Plutus builtins. -/
def builtinMap : NameMap BuiltinFun := Id.run do
  let mut m : NameMap BuiltinFun := {}
  for (n, b) in entries do
    m := m.insert n b
  pure m
where
  entries : List (Name × BuiltinFun) :=
    [ -- Integer arithmetic
      (`Int.add,                     .AddInteger)
    , (`Int.sub,                     .SubtractInteger)
    , (`Int.mul,                     .MultiplyInteger)
    , (`Int.div,                     .DivideInteger)
    , (`Int.mod,                     .ModInteger)
    , (`Int.natAbs,                  .EqualsInteger) -- placeholder; see below
    -- ifThenElse: NOT mapped here. It unfolds to Bool.casesOn, which
    -- translateCasesOn handles via Force(IfThenElse(Delay t)(Delay f)).
    -- Direct Plutus builtins (for manual usage)
    , (`Moist.Onchain.Prelude.addInteger,         .AddInteger)
    , (`Moist.Onchain.Prelude.subtractInteger,    .SubtractInteger)
    , (`Moist.Onchain.Prelude.multiplyInteger,    .MultiplyInteger)
    , (`Moist.Onchain.Prelude.divideInteger,      .DivideInteger)
    , (`Moist.Onchain.Prelude.modInteger,         .ModInteger)
    , (`Moist.Onchain.Prelude.equalsInteger,      .EqualsInteger)
    , (`Moist.Onchain.Prelude.lessThanInteger,    .LessThanInteger)
    , (`Moist.Onchain.Prelude.lessThanEqInteger,  .LessThanEqualsInteger)
    , (`Moist.Onchain.Prelude.trace,              .Trace)
    -- Data operations
    , (`Moist.Onchain.Prelude.constrData,     .ConstrData)
    , (`Moist.Onchain.Prelude.unConstrData,   .UnConstrData)
    , (`Moist.Onchain.Prelude.iData,          .IData)
    , (`Moist.Onchain.Prelude.unIData,        .UnIData)
    , (`Moist.Onchain.Prelude.bData,          .BData)
    , (`Moist.Onchain.Prelude.unBData,        .UnBData)
    , (`Moist.Onchain.Prelude.listData,       .ListData)
    , (`Moist.Onchain.Prelude.unListData,     .UnListData)
    , (`Moist.Onchain.Prelude.mapData,        .MapData)
    , (`Moist.Onchain.Prelude.unMapData,      .UnMapData)
    , (`Moist.Onchain.Prelude.equalsData,     .EqualsData)
    -- List operations
    , (`Moist.Onchain.Prelude.headList,       .HeadList)
    , (`Moist.Onchain.Prelude.tailList,       .TailList)
    , (`Moist.Onchain.Prelude.nullList,       .NullList)
    , (`Moist.Onchain.Prelude.mkCons,         .MkCons)
    -- Pair operations
    , (`Moist.Onchain.Prelude.fstPair,        .FstPair)
    , (`Moist.Onchain.Prelude.sndPair,        .SndPair)
    -- ByteString operations
    , (`Moist.Onchain.Prelude.appendByteString,          .AppendByteString)
    , (`Moist.Onchain.Prelude.lengthOfByteString,        .LengthOfByteString)
    , (`Moist.Onchain.Prelude.indexByteString,           .IndexByteString)
    , (`Moist.Onchain.Prelude.sliceByteString,           .SliceByteString)
    , (`Moist.Onchain.Prelude.equalsByteString,          .EqualsByteString)
    , (`Moist.Onchain.Prelude.lessThanByteString,        .LessThanByteString)
    , (`Moist.Onchain.Prelude.lessThanEqualsByteString,  .LessThanEqualsByteString)
    , (`Moist.Onchain.Prelude.consByteString,            .ConsByteString)
    -- Crypto
    , (`Moist.Onchain.Prelude.sha2_256,       .Sha2_256)
    , (`Moist.Onchain.Prelude.blake2b_256,    .Blake2b_256)
    , (`Moist.Onchain.Prelude.blake2b_224,    .Blake2b_224)
    , (`Moist.Onchain.Prelude.verifyEd25519Signature,           .VerifyEd25519Signature)
    , (`Moist.Onchain.Prelude.verifyEcdsaSecp256k1Signature,    .VerifyEcdsaSecp256k1Signature)
    , (`Moist.Onchain.Prelude.verifySchnorrSecp256k1Signature,  .VerifySchnorrSecp256k1Signature)
    , (`Moist.Onchain.Prelude.keccak_256,     .Keccak_256)
    -- String operations
    , (`Moist.Onchain.Prelude.encodeUtf8,     .EncodeUtf8)
    , (`Moist.Onchain.Prelude.decodeUtf8,     .DecodeUtf8)
    , (`Moist.Onchain.Prelude.appendString,   .AppendString)
    , (`Moist.Onchain.Prelude.equalsString,   .EqualsString)
    -- Unit / Error
    , (`Moist.Onchain.Prelude.chooseUnit,     .ChooseUnit)
    -- Pair operations
    , (`Moist.Onchain.Prelude.mkPairData,     .MkPairData)
    ]

/-- Number of Force nodes required to fully instantiate a polymorphic builtin.
    Monomorphic builtins need 0; each type quantifier in the Plutus type scheme
    adds 1. -/
def builtinForceCount : BuiltinFun → Nat
  | .FstPair | .SndPair | .ChooseList => 2
  | .IfThenElse | .ChooseUnit | .ChooseData
  | .HeadList | .TailList | .NullList | .MkCons | .Trace => 1
  | .DropList | .IndexArray | .ListToArray => 1
  | .Bls12_381_G1_multiScalarMul | .Bls12_381_G2_multiScalarMul => 0
  | _ => 0

/-! ## Builtin Arity

Value arity: number of `App` nodes required after all `Force` nodes
have been applied. Sourced from `plutuz/src/ast/builtin.zig`. -/

def builtinArity : BuiltinFun → Nat
  -- Integer
  | .AddInteger => 2
  | .SubtractInteger => 2
  | .MultiplyInteger => 2
  | .DivideInteger => 2
  | .QuotientInteger => 2
  | .RemainderInteger => 2
  | .ModInteger => 2
  | .EqualsInteger => 2
  | .LessThanInteger => 2
  | .LessThanEqualsInteger => 2
  -- ByteString
  | .AppendByteString => 2
  | .ConsByteString => 2
  | .SliceByteString => 3
  | .LengthOfByteString => 1
  | .IndexByteString => 2
  | .EqualsByteString => 2
  | .LessThanByteString => 2
  | .LessThanEqualsByteString => 2
  -- Cryptography
  | .Sha2_256 => 1
  | .Sha3_256 => 1
  | .Blake2b_256 => 1
  | .VerifyEd25519Signature => 3
  -- Strings
  | .AppendString => 2
  | .EqualsString => 2
  | .EncodeUtf8 => 1
  | .DecodeUtf8 => 1
  -- Bool
  | .IfThenElse => 3
  -- Unit
  | .ChooseUnit => 2
  -- Tracing
  | .Trace => 2
  -- Pairs
  | .FstPair => 1
  | .SndPair => 1
  -- Lists
  | .ChooseList => 3
  | .MkCons => 2
  | .HeadList => 1
  | .TailList => 1
  | .NullList => 1
  -- Data
  | .ChooseData => 6
  | .ConstrData => 2
  | .MapData => 1
  | .ListData => 1
  | .IData => 1
  | .BData => 1
  | .UnConstrData => 1
  | .UnMapData => 1
  | .UnListData => 1
  | .UnIData => 1
  | .UnBData => 1
  | .EqualsData => 2
  -- Misc constructors
  | .MkPairData => 2
  | .MkNilData => 1
  | .MkNilPairData => 1
  -- Batch 2
  | .SerializeData => 1
  -- Batch 3
  | .VerifyEcdsaSecp256k1Signature => 3
  | .VerifySchnorrSecp256k1Signature => 3
  -- BLS
  | .Bls12_381_G1_add => 2
  | .Bls12_381_G1_neg => 1
  | .Bls12_381_G1_scalarMul => 2
  | .Bls12_381_G1_equal => 2
  | .Bls12_381_G1_hashToGroup => 2
  | .Bls12_381_G1_compress => 1
  | .Bls12_381_G1_uncompress => 1
  | .Bls12_381_G2_add => 2
  | .Bls12_381_G2_neg => 1
  | .Bls12_381_G2_scalarMul => 2
  | .Bls12_381_G2_equal => 2
  | .Bls12_381_G2_hashToGroup => 2
  | .Bls12_381_G2_compress => 1
  | .Bls12_381_G2_uncompress => 1
  | .Bls12_381_millerLoop => 2
  | .Bls12_381_mulMlResult => 2
  | .Bls12_381_finalVerify => 2
  -- Crypto
  | .Keccak_256 => 1
  | .Blake2b_224 => 1
  | .IntegerToByteString => 3
  | .ByteStringToInteger => 2
  -- Batch 5
  | .AndByteString => 3
  | .OrByteString => 3
  | .XorByteString => 3
  | .ComplementByteString => 1
  | .ReadBit => 2
  | .WriteBits => 3
  | .ReplicateByte => 2
  | .ShiftByteString => 2
  | .RotateByteString => 2
  | .CountSetBits => 1
  | .FindFirstSetBit => 1
  | .Ripemd_160 => 1
  -- Batch 6
  | .ExpModInteger => 3
  -- Batch 7
  | .DropList => 2
  | .IndexArray => 2
  | .LengthOfArray => 1
  | .ListToArray => 1
  | .InsertCoin => 4
  | .LookupCoin => 3
  | .ScaleValue => 2
  | .UnionValue => 2
  | .ValueContains => 2
  | .ValueData => 1
  | .UnValueData => 1
  | .Bls12_381_G1_multiScalarMul => 2
  | .Bls12_381_G2_multiScalarMul => 2

/-! ## Builtin Totality

A builtin is **total** when its saturated application always succeeds,
regardless of argument values. Fallible builtins can error at runtime
(e.g. division by zero, empty list, wrong Data constructor). -/

def builtinIsTotal : BuiltinFun → Bool
  -- Integer: division can fail
  | .DivideInteger | .QuotientInteger | .RemainderInteger | .ModInteger => false
  -- ByteString: ConsByteString (byte out of range), IndexByteString (OOB)
  | .ConsByteString | .IndexByteString => false
  -- Crypto: signature verification can fail on malformed inputs
  | .VerifyEd25519Signature
  | .VerifyEcdsaSecp256k1Signature
  | .VerifySchnorrSecp256k1Signature => false
  -- Strings: DecodeUtf8 can fail on invalid UTF-8
  | .DecodeUtf8 => false
  -- Lists: HeadList/TailList fail on empty, MkCons can fail on type mismatch
  | .HeadList | .TailList | .MkCons => false
  -- Data: Un* fail on wrong Data constructor.
  | .UnConstrData | .UnMapData | .UnListData | .UnIData | .UnBData => false
  -- BLS: uncompress/hashToGroup can fail on invalid input
  | .Bls12_381_G1_uncompress | .Bls12_381_G1_hashToGroup => false
  | .Bls12_381_G2_uncompress | .Bls12_381_G2_hashToGroup => false
  -- IntegerToByteString can fail (negative size, too large)
  | .IntegerToByteString => false
  -- Bitwise: ReadBit/WriteBits (OOB), ReplicateByte (negative size)
  | .ReadBit | .WriteBits | .ReplicateByte => false
  -- Batch 6: ExpModInteger (modulus <= 0, etc.)
  | .ExpModInteger => false
  -- Batch 7: value builtins can fail on key size / decoding
  | .LookupCoin | .InsertCoin => false
  | .UnValueData => false
  -- Everything else is total
  | _ => true

def isBuiltinName (name : Name) : Bool :=
  builtinMap.contains name

def lookupBuiltin (name : Name) : Option BuiltinFun :=
  builtinMap.find? name

end Moist.Onchain
