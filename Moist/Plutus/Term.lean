import Moist.Plutus.Types

namespace Moist.Plutus.Term

open Moist.Plutus (Data ByteString Integer)

-- TODO: Need to check if BLS12 are considered as atomic types in spec
inductive AtomicType
  | TypeInteger
  | TypeByteString
  | TypeString
  | TypeBool
  | TypeUnit
  | TypeData
deriving BEq

instance : Repr AtomicType where
  reprPrec t _ :=
    match t with
    | AtomicType.TypeInteger => "Integer"
    | AtomicType.TypeByteString => "ByteString"
    | AtomicType.TypeString => "String"
    | AtomicType.TypeBool => "Bool"
    | AtomicType.TypeUnit => "Unit"
    | AtomicType.TypeData => "Data"

mutual
  inductive BuiltinType
    | AtomicType : AtomicType → BuiltinType
    | TypeOperator : TypeOperator → BuiltinType
  deriving Repr

  inductive TypeOperator
    | TypeList : BuiltinType → TypeOperator
    | TypePair : BuiltinType → BuiltinType → TypeOperator
  deriving Repr
end

mutual
  def beqBuiltinType : BuiltinType → BuiltinType → Bool
    | .AtomicType a, .AtomicType b => a == b
    | .TypeOperator a, .TypeOperator b => beqTypeOperator a b
    | _, _ => false

  def beqTypeOperator : TypeOperator → TypeOperator → Bool
    | .TypeList a, .TypeList b => beqBuiltinType a b
    | .TypePair a1 a2, .TypePair b1 b2 => beqBuiltinType a1 b1 && beqBuiltinType a2 b2
    | _, _ => false
end

instance : BEq BuiltinType where beq := beqBuiltinType
instance : BEq TypeOperator where beq := beqTypeOperator


inductive Const
  | Integer               : Integer → Const
  | ByteString            : ByteString → Const
  | String                : String → Const
  | Unit                  : Const
  | Bool                  : Bool → Const
  | ConstList             : List Const → Const
  | ConstDataList         : List Data → Const
    -- NOTE: Added to properly implement builtins evaluation and to avoid using List.map
  | ConstPairDataList     : List (Data × Data) → Const
    -- NOTE: Added to properly implement builtins evaluation and to avoid using List.map
  | Pair                  : Const × Const → Const
  | PairData              : Data × Data → Const
    -- NOTE: Added to properly implement builtins evaluation and to avoid using List.map
  | Data                  : Data → Const
  | Bls12_381_G1_element  : Const
    -- NOTE: missing value here (need to check in spec)
  | Bls12_381_G2_element  : Const
    -- NOTE: missing value here (need to check in spec)
  | Bls12_381_MlResult    : Const
    -- NOTE: missing value here (need to check in spec)
deriving Repr

private def beqConst : Const → Const → Bool
  | .Integer a, .Integer b => a == b
  | .ByteString a, .ByteString b => a == b
  | .String a, .String b => a == b
  | .Unit, .Unit => true
  | .Bool a, .Bool b => a == b
  | .ConstList as, .ConstList bs => beqConstList as bs
  | .ConstDataList as, .ConstDataList bs => as == bs
  | .ConstPairDataList as, .ConstPairDataList bs => as == bs
  | .Pair (a1, a2), .Pair (b1, b2) => beqConst a1 b1 && beqConst a2 b2
  | .PairData a, .PairData b => a == b
  | .Data a, .Data b => a == b
  | .Bls12_381_G1_element, .Bls12_381_G1_element => true
  | .Bls12_381_G2_element, .Bls12_381_G2_element => true
  | .Bls12_381_MlResult, .Bls12_381_MlResult => true
  | _, _ => false
where
  beqConstList : List Const → List Const → Bool
    | [], [] => true
    | a :: as, b :: bs => beqConst a b && beqConstList as bs
    | _, _ => false

instance : BEq Const where beq := beqConst

inductive BuiltinFun
-- Batch 1
-- Integer
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger
  | RemainderInteger
  | ModInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
-- ByteString
  | AppendByteString
  | ConsByteString
  | SliceByteString
  | LengthOfByteString
  | IndexByteString
  | EqualsByteString
  | LessThanByteString
  | LessThanEqualsByteString
-- Cryptography
  | Sha2_256
  | Sha3_256
  | Blake2b_256
  | VerifyEd25519Signature
-- Strings
  | AppendString
  | EqualsString
  | EncodeUtf8
  | DecodeUtf8
-- Bool
  | IfThenElse
-- Unit
  | ChooseUnit
-- Tracing
  | Trace
-- Pairs
  | FstPair
  | SndPair
-- Lists
  | ChooseList
  | MkCons
  | HeadList
  | TailList
  | NullList
-- Data
  | ChooseData
  | ConstrData
  | MapData
  | ListData
  | IData
  | BData
  | UnConstrData
  | UnMapData
  | UnListData
  | UnIData
  | UnBData
  | EqualsData
-- Misc constructors
  | MkPairData
  | MkNilData
  | MkNilPairData
-- Batch 2
  | SerializeData
-- Batch 3
  | VerifyEcdsaSecp256k1Signature
  | VerifySchnorrSecp256k1Signature
-- Batch 4 = Chang
-- Bls curve
  | Bls12_381_G1_add
  | Bls12_381_G1_neg
  | Bls12_381_G1_scalarMul
  | Bls12_381_G1_equal
  | Bls12_381_G1_hashToGroup
  | Bls12_381_G1_compress
  | Bls12_381_G1_uncompress
  | Bls12_381_G2_add
  | Bls12_381_G2_neg
  | Bls12_381_G2_scalarMul
  | Bls12_381_G2_equal
  | Bls12_381_G2_hashToGroup
  | Bls12_381_G2_compress
  | Bls12_381_G2_uncompress
  | Bls12_381_millerLoop
  | Bls12_381_mulMlResult
  | Bls12_381_finalVerify
-- Cryptography
  | Keccak_256
  | Blake2b_224
  | IntegerToByteString
  | ByteStringToInteger

-- Not live yet
-- Batch 5
-- ByteString
  | AndByteString
  | OrByteString
  | XorByteString
  | ComplementByteString
  | ReadBit
  | WriteBits
  | ReplicateByte
  | ShiftByteString
  | RotateByteString
  | CountSetBits
  | FindFirstSetBit
-- Cryptography
  | Ripemd_160
-- Batch 6
  | ExpModInteger
deriving Repr, BEq

end Moist.Plutus.Term
