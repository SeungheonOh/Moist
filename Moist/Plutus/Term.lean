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
  | TypeValue
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
    | AtomicType.TypeValue => "Value"

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


/-- A Plutus constant. Every Plutus value has exactly one encoding: lists and arrays
carry their element type (as `DefaultUniList t` / `DefaultUniArray t` do in plutus-core),
a list of data is `ConstList (data) [.Data d, ...]` and a pair of data is
`Pair (.Data a, .Data b)`. -/
inductive Const
  | Integer               : Integer → Const
  | ByteString            : ByteString → Const
  | String                : String → Const
  | Unit                  : Const
  | Bool                  : Bool → Const
  | ConstList             : BuiltinType → List Const → Const
  | Pair                  : Const × Const → Const
  | Data                  : Data → Const
  | ConstArray            : BuiltinType → List Const → Const
  /-- A G1 point, carried as its canonical 48-byte compressed encoding. Distinct
  points have distinct encodings, so distinct points are distinct model values. -/
  | Bls12_381_G1_element  : ByteString → Const
  /-- A G2 point, carried as its canonical 96-byte compressed encoding. -/
  | Bls12_381_G2_element  : ByteString → Const
  /-- A Miller-loop result (an element of the target field). The payload is an
  implementation-defined serialisation; programs can only consume it through
  `bls12_381_mulMlResult` and `bls12_381_finalVerify`. -/
  | Bls12_381_MlResult    : ByteString → Const
  /-- A multi-asset value: currency symbol ↦ (token name ↦ quantity). Well-formed
  values (the only ones the parser, decoder and builtins produce) have strictly
  ascending keys of at most 32 bytes, no empty inner map, and nonzero quantities
  in the signed 128-bit range, so equal values have equal payloads. -/
  | Value                 : List (ByteString × List (ByteString × Integer)) → Const
deriving Repr

private def beqConst : Const → Const → Bool
  | .Integer a, .Integer b => a == b
  | .ByteString a, .ByteString b => a == b
  | .String a, .String b => a == b
  | .Unit, .Unit => true
  | .Bool a, .Bool b => a == b
  | .ConstList ta as, .ConstList tb bs => ta == tb && beqConstList as bs
  | .Pair (a1, a2), .Pair (b1, b2) => beqConst a1 b1 && beqConst a2 b2
  | .Data a, .Data b => a == b
  | .ConstArray ta as, .ConstArray tb bs => ta == tb && beqConstList as bs
  | .Bls12_381_G1_element a, .Bls12_381_G1_element b => a == b
  | .Bls12_381_G2_element a, .Bls12_381_G2_element b => a == b
  | .Bls12_381_MlResult a, .Bls12_381_MlResult b => a == b
  | .Value a, .Value b => a == b
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

/-- The builtin type of a constant (exact: lists and arrays carry their element type). -/
def constType : Const → BuiltinType
  | Const.Integer _            => .AtomicType .TypeInteger
  | Const.ByteString _         => .AtomicType .TypeByteString
  | Const.String _             => .AtomicType .TypeString
  | Const.Unit                 => .AtomicType .TypeUnit
  | Const.Bool _               => .AtomicType .TypeBool
  | Const.ConstList ty _       => .TypeOperator (.TypeList ty)
  | Const.Pair (first, second) => .TypeOperator (.TypePair (constType first) (constType second))
  | Const.Data _               => .AtomicType .TypeData
  | Const.ConstArray ty _      => .TypeOperator (.TypeArray ty)
  | Const.Bls12_381_G1_element _ => .AtomicType .TypeBls12_381_G1_element
  | Const.Bls12_381_G2_element _ => .AtomicType .TypeBls12_381_G2_element
  | Const.Bls12_381_MlResult _   => .AtomicType .TypeBls12_381_MlResult
  | Const.Value _              => .AtomicType .TypeValue

/-- The builtin type `data`. -/
abbrev dataType : BuiltinType := .AtomicType .TypeData
/-- The builtin type `pair data data`. -/
abbrev pairDataType : BuiltinType := .TypeOperator (.TypePair dataType dataType)

/-- The constant `list data` holding the given data items. -/
def Const.dataList (ds : List Moist.Plutus.Data) : Const := .ConstList dataType (ds.map .Data)
/-- The constant `pair data data`. -/
def Const.pairData (p : Moist.Plutus.Data × Moist.Plutus.Data) : Const := .Pair (.Data p.1, .Data p.2)
/-- The constant `list (pair data data)` holding the given entries. -/
def Const.pairDataList (ps : List (Moist.Plutus.Data × Moist.Plutus.Data)) : Const := .ConstList pairDataType (ps.map Const.pairData)

end Moist.Plutus.Term
