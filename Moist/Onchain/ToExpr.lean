import Lean.ToExpr
import Moist.Plutus.Term

namespace Moist.Onchain.ToExprInstances

open Lean
open Moist.Plutus.Term

/-! ## ToExpr for external types -/

instance : ToExpr ByteArray where
  toExpr ba := mkApp (.const ``ByteArray.mk []) (toExpr ba.data)
  toTypeExpr := .const ``ByteArray []

/-! Data is recursive and from an external package. We write a fully
    self-contained implementation that handles List/Prod recursion manually. -/

open Moist.Plutus in
private partial def dataToExpr : Data → Lean.Expr
  | .Constr n ds =>
    mkApp2 (.const ``Data.Constr []) (toExpr n) (listDataToExpr ds)
  | .Map ps =>
    mkApp (.const ``Data.Map []) (listPairDataToExpr ps)
  | .List ds =>
    mkApp (.const ``Data.List []) (listDataToExpr ds)
  | .I n =>
    mkApp (.const ``Data.I []) (toExpr n)
  | .B bs =>
    mkApp (.const ``Data.B []) (toExpr bs)
where
  listDataToExpr : List Moist.Plutus.Data → Lean.Expr
    | [] => mkApp (.const ``List.nil [.zero]) (.const ``Moist.Plutus.Data [])
    | d :: ds => mkApp3 (.const ``List.cons [.zero]) (.const ``Moist.Plutus.Data [])
        (dataToExpr d) (listDataToExpr ds)
  listPairDataToExpr : List (Moist.Plutus.Data × Moist.Plutus.Data) → Lean.Expr
    | [] =>
      let pairTy := mkApp2 (.const ``Prod [.zero, .zero]) (.const ``Moist.Plutus.Data []) (.const ``Moist.Plutus.Data [])
      mkApp (.const ``List.nil [.zero]) pairTy
    | (a, b) :: rest =>
      let pairTy := mkApp2 (.const ``Prod [.zero, .zero]) (.const ``Moist.Plutus.Data []) (.const ``Moist.Plutus.Data [])
      let pair := mkApp4 (.const ``Prod.mk [.zero, .zero]) (.const ``Moist.Plutus.Data []) (.const ``Moist.Plutus.Data [])
        (dataToExpr a) (dataToExpr b)
      mkApp3 (.const ``List.cons [.zero]) pairTy pair (listPairDataToExpr rest)

open Moist.Plutus in
instance : ToExpr Data where
  toExpr := dataToExpr
  toTypeExpr := .const ``Data []

/-! ## ToExpr for UPLC types -/

instance : ToExpr AtomicType where
  toExpr
    | .TypeInteger    => .const ``AtomicType.TypeInteger []
    | .TypeByteString => .const ``AtomicType.TypeByteString []
    | .TypeString     => .const ``AtomicType.TypeString []
    | .TypeBool       => .const ``AtomicType.TypeBool []
    | .TypeUnit       => .const ``AtomicType.TypeUnit []
    | .TypeData       => .const ``AtomicType.TypeData []
  toTypeExpr := .const ``AtomicType []

mutual
  private def builtinTypeToExpr : BuiltinType → Lean.Expr
    | .AtomicType t => mkApp (.const ``BuiltinType.AtomicType []) (toExpr t)
    | .TypeOperator t => mkApp (.const ``BuiltinType.TypeOperator []) (typeOperatorToExpr t)

  private def typeOperatorToExpr : TypeOperator → Lean.Expr
    | .TypeList t => mkApp (.const ``TypeOperator.TypeList []) (builtinTypeToExpr t)
    | .TypePair a b => mkApp2 (.const ``TypeOperator.TypePair []) (builtinTypeToExpr a) (builtinTypeToExpr b)
end

instance : ToExpr BuiltinType where
  toExpr := builtinTypeToExpr
  toTypeExpr := .const ``BuiltinType []

instance : ToExpr TypeOperator where
  toExpr := typeOperatorToExpr
  toTypeExpr := .const ``TypeOperator []

private partial def constToExpr : Const → Lean.Expr
  | .Integer n            => mkApp (.const ``Const.Integer []) (toExpr n)
  | .ByteString bs        => mkApp (.const ``Const.ByteString []) (toExpr bs)
  | .String s             => mkApp (.const ``Const.String []) (toExpr s)
  | .Unit                 => .const ``Const.Unit []
  | .Bool b               => mkApp (.const ``Const.Bool []) (toExpr b)
  | .ConstList cs         => mkApp (.const ``Const.ConstList []) (listConstToExpr cs)
  | .ConstDataList ds     => mkApp (.const ``Const.ConstDataList []) (toExpr ds)
  | .ConstPairDataList ps => mkApp (.const ``Const.ConstPairDataList []) (toExpr ps)
  | .Pair p               => mkApp (.const ``Const.Pair []) (pairConstToExpr p)
  | .PairData p           => mkApp (.const ``Const.PairData []) (toExpr p)
  | .Data d               => mkApp (.const ``Const.Data []) (toExpr d)
  | .Bls12_381_G1_element => .const ``Const.Bls12_381_G1_element []
  | .Bls12_381_G2_element => .const ``Const.Bls12_381_G2_element []
  | .Bls12_381_MlResult   => .const ``Const.Bls12_381_MlResult []
where
  listConstToExpr : List Const → Lean.Expr
    | [] => mkApp (.const ``List.nil [.zero]) (.const ``Const [])
    | c :: cs => mkApp3 (.const ``List.cons [.zero]) (.const ``Const []) (constToExpr c) (listConstToExpr cs)
  pairConstToExpr : Const × Const → Lean.Expr
    | (a, b) => mkApp4 (.const ``Prod.mk [.zero, .zero]) (.const ``Const []) (.const ``Const []) (constToExpr a) (constToExpr b)

instance : ToExpr Const where
  toExpr := constToExpr
  toTypeExpr := .const ``Const []

instance : ToExpr BuiltinFun where
  toExpr b :=
    let name := match b with
    | .AddInteger => ``BuiltinFun.AddInteger
    | .SubtractInteger => ``BuiltinFun.SubtractInteger
    | .MultiplyInteger => ``BuiltinFun.MultiplyInteger
    | .DivideInteger => ``BuiltinFun.DivideInteger
    | .QuotientInteger => ``BuiltinFun.QuotientInteger
    | .RemainderInteger => ``BuiltinFun.RemainderInteger
    | .ModInteger => ``BuiltinFun.ModInteger
    | .EqualsInteger => ``BuiltinFun.EqualsInteger
    | .LessThanInteger => ``BuiltinFun.LessThanInteger
    | .LessThanEqualsInteger => ``BuiltinFun.LessThanEqualsInteger
    | .AppendByteString => ``BuiltinFun.AppendByteString
    | .ConsByteString => ``BuiltinFun.ConsByteString
    | .SliceByteString => ``BuiltinFun.SliceByteString
    | .LengthOfByteString => ``BuiltinFun.LengthOfByteString
    | .IndexByteString => ``BuiltinFun.IndexByteString
    | .EqualsByteString => ``BuiltinFun.EqualsByteString
    | .LessThanByteString => ``BuiltinFun.LessThanByteString
    | .LessThanEqualsByteString => ``BuiltinFun.LessThanEqualsByteString
    | .Sha2_256 => ``BuiltinFun.Sha2_256
    | .Sha3_256 => ``BuiltinFun.Sha3_256
    | .Blake2b_256 => ``BuiltinFun.Blake2b_256
    | .VerifyEd25519Signature => ``BuiltinFun.VerifyEd25519Signature
    | .AppendString => ``BuiltinFun.AppendString
    | .EqualsString => ``BuiltinFun.EqualsString
    | .EncodeUtf8 => ``BuiltinFun.EncodeUtf8
    | .DecodeUtf8 => ``BuiltinFun.DecodeUtf8
    | .IfThenElse => ``BuiltinFun.IfThenElse
    | .ChooseUnit => ``BuiltinFun.ChooseUnit
    | .Trace => ``BuiltinFun.Trace
    | .FstPair => ``BuiltinFun.FstPair
    | .SndPair => ``BuiltinFun.SndPair
    | .ChooseList => ``BuiltinFun.ChooseList
    | .MkCons => ``BuiltinFun.MkCons
    | .HeadList => ``BuiltinFun.HeadList
    | .TailList => ``BuiltinFun.TailList
    | .NullList => ``BuiltinFun.NullList
    | .ChooseData => ``BuiltinFun.ChooseData
    | .ConstrData => ``BuiltinFun.ConstrData
    | .MapData => ``BuiltinFun.MapData
    | .ListData => ``BuiltinFun.ListData
    | .IData => ``BuiltinFun.IData
    | .BData => ``BuiltinFun.BData
    | .UnConstrData => ``BuiltinFun.UnConstrData
    | .UnMapData => ``BuiltinFun.UnMapData
    | .UnListData => ``BuiltinFun.UnListData
    | .UnIData => ``BuiltinFun.UnIData
    | .UnBData => ``BuiltinFun.UnBData
    | .EqualsData => ``BuiltinFun.EqualsData
    | .MkPairData => ``BuiltinFun.MkPairData
    | .MkNilData => ``BuiltinFun.MkNilData
    | .MkNilPairData => ``BuiltinFun.MkNilPairData
    | .SerializeData => ``BuiltinFun.SerializeData
    | .VerifyEcdsaSecp256k1Signature => ``BuiltinFun.VerifyEcdsaSecp256k1Signature
    | .VerifySchnorrSecp256k1Signature => ``BuiltinFun.VerifySchnorrSecp256k1Signature
    | .Bls12_381_G1_add => ``BuiltinFun.Bls12_381_G1_add
    | .Bls12_381_G1_neg => ``BuiltinFun.Bls12_381_G1_neg
    | .Bls12_381_G1_scalarMul => ``BuiltinFun.Bls12_381_G1_scalarMul
    | .Bls12_381_G1_equal => ``BuiltinFun.Bls12_381_G1_equal
    | .Bls12_381_G1_hashToGroup => ``BuiltinFun.Bls12_381_G1_hashToGroup
    | .Bls12_381_G1_compress => ``BuiltinFun.Bls12_381_G1_compress
    | .Bls12_381_G1_uncompress => ``BuiltinFun.Bls12_381_G1_uncompress
    | .Bls12_381_G2_add => ``BuiltinFun.Bls12_381_G2_add
    | .Bls12_381_G2_neg => ``BuiltinFun.Bls12_381_G2_neg
    | .Bls12_381_G2_scalarMul => ``BuiltinFun.Bls12_381_G2_scalarMul
    | .Bls12_381_G2_equal => ``BuiltinFun.Bls12_381_G2_equal
    | .Bls12_381_G2_hashToGroup => ``BuiltinFun.Bls12_381_G2_hashToGroup
    | .Bls12_381_G2_compress => ``BuiltinFun.Bls12_381_G2_compress
    | .Bls12_381_G2_uncompress => ``BuiltinFun.Bls12_381_G2_uncompress
    | .Bls12_381_millerLoop => ``BuiltinFun.Bls12_381_millerLoop
    | .Bls12_381_mulMlResult => ``BuiltinFun.Bls12_381_mulMlResult
    | .Bls12_381_finalVerify => ``BuiltinFun.Bls12_381_finalVerify
    | .Keccak_256 => ``BuiltinFun.Keccak_256
    | .Blake2b_224 => ``BuiltinFun.Blake2b_224
    | .IntegerToByteString => ``BuiltinFun.IntegerToByteString
    | .ByteStringToInteger => ``BuiltinFun.ByteStringToInteger
    | .AndByteString => ``BuiltinFun.AndByteString
    | .OrByteString => ``BuiltinFun.OrByteString
    | .XorByteString => ``BuiltinFun.XorByteString
    | .ComplementByteString => ``BuiltinFun.ComplementByteString
    | .ReadBit => ``BuiltinFun.ReadBit
    | .WriteBits => ``BuiltinFun.WriteBits
    | .ReplicateByte => ``BuiltinFun.ReplicateByte
    | .ShiftByteString => ``BuiltinFun.ShiftByteString
    | .RotateByteString => ``BuiltinFun.RotateByteString
    | .CountSetBits => ``BuiltinFun.CountSetBits
    | .FindFirstSetBit => ``BuiltinFun.FindFirstSetBit
    | .Ripemd_160 => ``BuiltinFun.Ripemd_160
    | .ExpModInteger => ``BuiltinFun.ExpModInteger
    .const name []
  toTypeExpr := .const ``BuiltinFun []

/-! ## ToExpr for Term (UPLC AST)

Use fully qualified names to avoid ambiguity with Lean.Term. -/

partial def uplcTermToExpr : Moist.Plutus.Term.Term → Lean.Expr
  | .Var n => mkApp (.const ``Moist.Plutus.Term.Term.Var []) (toExpr n)
  | .Constant (c, ty) =>
    mkApp (.const ``Moist.Plutus.Term.Term.Constant [])
      (mkApp4 (.const ``Prod.mk [.zero, .zero])
        (.const ``Const []) (.const ``BuiltinType [])
        (toExpr c) (toExpr ty))
  | .Builtin b => mkApp (.const ``Moist.Plutus.Term.Term.Builtin []) (toExpr b)
  | .Lam n body => mkApp2 (.const ``Moist.Plutus.Term.Term.Lam []) (toExpr n) (uplcTermToExpr body)
  | .Apply f a => mkApp2 (.const ``Moist.Plutus.Term.Term.Apply []) (uplcTermToExpr f) (uplcTermToExpr a)
  | .Delay e => mkApp (.const ``Moist.Plutus.Term.Term.Delay []) (uplcTermToExpr e)
  | .Force e => mkApp (.const ``Moist.Plutus.Term.Term.Force []) (uplcTermToExpr e)
  | .Constr tag args =>
    mkApp2 (.const ``Moist.Plutus.Term.Term.Constr []) (toExpr tag) (listUplcTermToExpr args)
  | .Case scrut alts =>
    mkApp2 (.const ``Moist.Plutus.Term.Term.Case []) (uplcTermToExpr scrut) (listUplcTermToExpr alts)
  | .Error => .const ``Moist.Plutus.Term.Term.Error []
where
  listUplcTermToExpr : List Moist.Plutus.Term.Term → Lean.Expr
    | [] => mkApp (.const ``List.nil [.zero]) (.const ``Moist.Plutus.Term.Term [])
    | t :: ts => mkApp3 (.const ``List.cons [.zero]) (.const ``Moist.Plutus.Term.Term [])
        (uplcTermToExpr t) (listUplcTermToExpr ts)

instance : ToExpr Moist.Plutus.Term.Term where
  toExpr := uplcTermToExpr
  toTypeExpr := .const ``Moist.Plutus.Term.Term []

instance : ToExpr Version where
  toExpr
    | .Version a b c => mkApp3 (.const ``Version.Version []) (toExpr a) (toExpr b) (toExpr c)
  toTypeExpr := .const ``Version []

instance : ToExpr Program where
  toExpr
    | .Program v t => mkApp2 (.const ``Program.Program []) (toExpr v) (toExpr t)
  toTypeExpr := .const ``Program []

end Moist.Onchain.ToExprInstances
