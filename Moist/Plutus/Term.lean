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
  | TypeBls12_381_G1_element
  | TypeBls12_381_G2_element
  | TypeBls12_381_MlResult
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
    | AtomicType.TypeBls12_381_G1_element => "Bls12_381_G1_element"
    | AtomicType.TypeBls12_381_G2_element => "Bls12_381_G2_element"
    | AtomicType.TypeBls12_381_MlResult => "Bls12_381_MlResult"

mutual
  inductive BuiltinType
    | AtomicType : AtomicType → BuiltinType
    | TypeOperator : TypeOperator → BuiltinType
  deriving Repr

  inductive TypeOperator
    | TypeList : BuiltinType → TypeOperator
    | TypePair : BuiltinType → BuiltinType → TypeOperator
    | TypeArray : BuiltinType → TypeOperator
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
    | .TypeArray a, .TypeArray b => beqBuiltinType a b
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
  | ConstArray            : List Const → Const
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
  | .ConstArray as, .ConstArray bs => beqConstList as bs
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
-- Batch 7
  | DropList | IndexArray | LengthOfArray | ListToArray
  | InsertCoin | LookupCoin | ScaleValue | UnionValue | ValueContains | ValueData | UnValueData
  | Bls12_381_G1_multiScalarMul | Bls12_381_G2_multiScalarMul
deriving Repr, BEq

inductive Term
| Var : Nat → Term
| Constant : Const × BuiltinType → Term
| Builtin : BuiltinFun → Term
| Lam : Nat → Term → Term
| Apply : Term → Term → Term
| Delay : Term → Term
| Force : Term → Term
| Constr : Nat → List Term → Term
| Case : Term → List Term → Term
| Error : Term
deriving Repr

inductive Version
| Version : Nat → Nat → Nat → Version

instance : Repr Version where
  reprPrec v _ :=
    "Version " ++ repr v.1 ++ "." ++ repr v.2 ++ "." ++ repr v.3

instance {α β} [LT α] [LT β] : LT (Prod α β) where
  lt | (a₁, b₁), (a₂, b₂) => (a₁ < a₂) ∨ (a₁ = a₂ ∧ b₁ < b₂)

instance {α β} [LT α] [LT β] [DecidableLT α] [DecidableEq α] [dltb : DecidableLT β] : DecidableRel (LT.lt : Prod α β → Prod α β → Prop) :=
  λ (a₁, b₁) (a₂, b₂) =>
    if h : a₁ < a₂
      then isTrue (Or.inl h)
    else if heq : a₁ = a₂ then
      match dltb b₁ b₂ with
      | isTrue  hlt  => isTrue (Or.inr ⟨heq, hlt⟩)
      | isFalse hnlt => isFalse (fun h => by
          cases h
          · contradiction
          · have hl : a₁ = a₂ ∧ b₁ < b₂ := by assumption
            obtain ⟨_, _⟩ := hl
            contradiction
        )
    else isFalse (fun h => by
           cases h
           · contradiction
           · have hl : a₁ = a₂ ∧ b₁ < b₂ := by assumption
             obtain ⟨_, _⟩ := hl
             contradiction
         )

instance : LT Version where
  lt | .Version a₁ b₁ c₁, .Version a₂ b₂ c₂ => (a₁, b₁, c₁) < (a₂, b₂, c₂)

instance [dltp : DecidableLT (Nat × Nat × Nat)] : DecidableRel (LT.lt : Version → Version → Prop) :=
  λ (.Version a₁ b₁ c₁) (.Version a₂ b₂ c₂) => dltp (a₁, b₁, c₁) (a₂, b₂, c₂)

inductive Program
| Program : Version → Term → Program
deriving Repr

instance : Inhabited Program where
  default := .Program (.Version 1 1 0) (.Error)

/-- Map a constant to its builtin type. -/
def constType : Const → BuiltinType
  | Const.Integer _            => BuiltinType.AtomicType AtomicType.TypeInteger
  | Const.ByteString _         => BuiltinType.AtomicType AtomicType.TypeByteString
  | Const.String _             => BuiltinType.AtomicType AtomicType.TypeString
  | Const.Unit                 => BuiltinType.AtomicType AtomicType.TypeUnit
  | Const.Bool _               => BuiltinType.AtomicType AtomicType.TypeBool
  | Const.ConstList _          => BuiltinType.TypeOperator (TypeOperator.TypeList (BuiltinType.AtomicType AtomicType.TypeData))
  | Const.ConstDataList _      => BuiltinType.TypeOperator (TypeOperator.TypeList (BuiltinType.AtomicType AtomicType.TypeData))
  | Const.ConstPairDataList _  => BuiltinType.TypeOperator (TypeOperator.TypePair (BuiltinType.AtomicType AtomicType.TypeData) (BuiltinType.AtomicType AtomicType.TypeData))
  | Const.Pair _               => BuiltinType.TypeOperator (TypeOperator.TypePair (BuiltinType.AtomicType AtomicType.TypeData) (BuiltinType.AtomicType AtomicType.TypeData))
  | Const.PairData _           => BuiltinType.TypeOperator (TypeOperator.TypePair (BuiltinType.AtomicType AtomicType.TypeData) (BuiltinType.AtomicType AtomicType.TypeData)) -- This is wrong : ( fix .
  | Const.Data _               => BuiltinType.AtomicType AtomicType.TypeData
  | Const.ConstArray _         => BuiltinType.TypeOperator (TypeOperator.TypeArray (BuiltinType.AtomicType AtomicType.TypeData))
  | Const.Bls12_381_G1_element => BuiltinType.AtomicType AtomicType.TypeBls12_381_G1_element
  | Const.Bls12_381_G2_element => BuiltinType.AtomicType AtomicType.TypeBls12_381_G2_element
  | Const.Bls12_381_MlResult   => BuiltinType.AtomicType AtomicType.TypeBls12_381_MlResult

end Moist.Plutus.Term
