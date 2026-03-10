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

def isBuiltinName (name : Name) : Bool :=
  builtinMap.contains name

def lookupBuiltin (name : Name) : Option BuiltinFun :=
  builtinMap.find? name

end Moist.Onchain
