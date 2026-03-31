import Lean
import Moist.Onchain.Compile
import PlutusCore.UPLC.Term.ToExpr

/-! # compile_fvt! — Compile @[onchain] defs to PlutusCore.UPLC.Term.Term

Like `compile!` but produces `PlutusCore.UPLC.Term.Term` (named variables)
instead of `Moist.Plutus.Term.Term` (de Bruijn indexed). The conversion
happens at elaboration time so the result is a concrete literal — no
runtime conversion needed for `#blaster` proofs.
-/

namespace Test.CompileFvt

open Lean Elab Meta
open Moist.Onchain (compileToUPLC onchainAttr)

/-! ## MetaM-level conversion: Moist de Bruijn → sc-fvt named -/

open PlutusCore.Data in
instance : Inhabited Data := ⟨.I 0⟩
instance : Inhabited PlutusCore.UPLC.Term.Const := ⟨.Unit⟩
instance : Inhabited PlutusCore.UPLC.Term.Term := ⟨.Error⟩

private def mkName (n : Nat) : String :=
  String.singleton (Char.ofNat (97 + n % 26))

private def convertByteString (ba : ByteArray) : PlutusCore.ByteString.ByteString :=
  ⟨String.mk (ba.toList.map (fun b => Char.ofNat b.toNat))⟩

private partial def convertData : Moist.Plutus.Data → PlutusCore.Data.Data
  | .Constr i ds => .Constr i (ds.map convertData)
  | .Map ps => .Map (ps.map fun (a, b) => (convertData a, convertData b))
  | .List ds => .List (ds.map convertData)
  | .I n => .I n
  | .B bs => .B (convertByteString bs)

private partial def convertConst : Moist.Plutus.Term.Const → PlutusCore.UPLC.Term.Const
  | .Integer n => .Integer n
  | .ByteString bs => .ByteString (convertByteString bs)
  | .String s => .String s
  | .Unit => .Unit
  | .Bool b => .Bool b
  | .ConstList cs => .ConstList (cs.map convertConst)
  | .ConstDataList ds => .ConstDataList (ds.map convertData)
  | .ConstPairDataList ps => .ConstPairDataList (ps.map fun (a, b) => (convertData a, convertData b))
  | .Pair (a, b) => .Pair (convertConst a, convertConst b)
  | .PairData (a, b) => .PairData (convertData a, convertData b)
  | .Data d => .Data (convertData d)
  | .ConstArray cs => .ConstList (cs.map convertConst)
  | .Bls12_381_G1_element => .Bls12_381_G1_element
  | .Bls12_381_G2_element => .Bls12_381_G2_element
  | .Bls12_381_MlResult => .Bls12_381_MlResult

private def convertBuiltinFun : Moist.Plutus.Term.BuiltinFun → PlutusCore.UPLC.Term.BuiltinFun
  | .AddInteger => .AddInteger
  | .SubtractInteger => .SubtractInteger
  | .MultiplyInteger => .MultiplyInteger
  | .DivideInteger => .DivideInteger
  | .QuotientInteger => .QuotientInteger
  | .RemainderInteger => .RemainderInteger
  | .ModInteger => .ModInteger
  | .EqualsInteger => .EqualsInteger
  | .LessThanInteger => .LessThanInteger
  | .LessThanEqualsInteger => .LessThanEqualsInteger
  | .AppendByteString => .AppendByteString
  | .ConsByteString => .ConsByteString
  | .SliceByteString => .SliceByteString
  | .LengthOfByteString => .LengthOfByteString
  | .IndexByteString => .IndexByteString
  | .EqualsByteString => .EqualsByteString
  | .LessThanByteString => .LessThanByteString
  | .LessThanEqualsByteString => .LessThanEqualsByteString
  | .Sha2_256 => .Sha2_256
  | .Sha3_256 => .Sha3_256
  | .Blake2b_256 => .Blake2b_256
  | .VerifyEd25519Signature => .VerifyEd25519Signature
  | .AppendString => .AppendString
  | .EqualsString => .EqualsString
  | .EncodeUtf8 => .EncodeUtf8
  | .DecodeUtf8 => .DecodeUtf8
  | .IfThenElse => .IfThenElse
  | .ChooseUnit => .ChooseUnit
  | .Trace => .Trace
  | .FstPair => .FstPair
  | .SndPair => .SndPair
  | .ChooseList => .ChooseList
  | .MkCons => .MkCons
  | .HeadList => .HeadList
  | .TailList => .TailList
  | .NullList => .NullList
  | .ChooseData => .ChooseData
  | .ConstrData => .ConstrData
  | .MapData => .MapData
  | .ListData => .ListData
  | .IData => .IData
  | .BData => .BData
  | .UnConstrData => .UnConstrData
  | .UnMapData => .UnMapData
  | .UnListData => .UnListData
  | .UnIData => .UnIData
  | .UnBData => .UnBData
  | .EqualsData => .EqualsData
  | .MkPairData => .MkPairData
  | .MkNilData => .MkNilData
  | .MkNilPairData => .MkNilPairData
  | .SerializeData => .SerializeData
  | .VerifyEcdsaSecp256k1Signature => .VerifyEcdsaSecp256k1Signature
  | .VerifySchnorrSecp256k1Signature => .VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add => .Bls12_381_G1_add
  | .Bls12_381_G1_neg => .Bls12_381_G1_neg
  | .Bls12_381_G1_scalarMul => .Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal => .Bls12_381_G1_equal
  | .Bls12_381_G1_hashToGroup => .Bls12_381_G1_hashToGroup
  | .Bls12_381_G1_compress => .Bls12_381_G1_compress
  | .Bls12_381_G1_uncompress => .Bls12_381_G1_uncompress
  | .Bls12_381_G2_add => .Bls12_381_G2_add
  | .Bls12_381_G2_neg => .Bls12_381_G2_neg
  | .Bls12_381_G2_scalarMul => .Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal => .Bls12_381_G2_equal
  | .Bls12_381_G2_hashToGroup => .Bls12_381_G2_hashToGroup
  | .Bls12_381_G2_compress => .Bls12_381_G2_compress
  | .Bls12_381_G2_uncompress => .Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop => .Bls12_381_millerLoop
  | .Bls12_381_mulMlResult => .Bls12_381_mulMlResult
  | .Bls12_381_finalVerify => .Bls12_381_finalVerify
  | .Keccak_256 => .Keccak_256
  | .Blake2b_224 => .Blake2b_224
  | .IntegerToByteString => .IntegerToByteString
  | .ByteStringToInteger => .ByteStringToInteger
  | .AndByteString => .AndByteString
  | .OrByteString => .OrByteString
  | .XorByteString => .XorByteString
  | .ComplementByteString => .ComplementByteString
  | .ReadBit => .ReadBit
  | .WriteBits => .WriteBits
  | .ReplicateByte => .ReplicateByte
  | .ShiftByteString => .ShiftByteString
  | .RotateByteString => .RotateByteString
  | .CountSetBits => .CountSetBits
  | .FindFirstSetBit => .FindFirstSetBit
  | .Ripemd_160 => .Ripemd_160
  | .ExpModInteger => .ExpModInteger
  | .DropList | .IndexArray | .LengthOfArray | .ListToArray
  | .InsertCoin | .LookupCoin | .ScaleValue | .UnionValue
  | .ValueContains | .ValueData | .UnValueData
  | .Bls12_381_G1_multiScalarMul | .Bls12_381_G2_multiScalarMul => .ExpModInteger

/-- Convert Moist Term (de Bruijn, 1-based) to sc-fvt Term (named).
    `depth` tracks binding depth for unique name assignment. -/
private partial def convertTerm (depth : Nat) : Moist.Plutus.Term.Term → PlutusCore.UPLC.Term.Term
  | .Var n => .Var (mkName (depth - n))
  | .Constant (c, _) => .Const (convertConst c)
  | .Builtin b => .Builtin (convertBuiltinFun b)
  | .Lam _ body => .Lam (mkName depth) (convertTerm (depth + 1) body)
  | .Apply f x => .Apply (convertTerm depth f) (convertTerm depth x)
  | .Delay t => .Delay (convertTerm depth t)
  | .Force t => .Force (convertTerm depth t)
  | .Constr tag fields => .Constr tag (fields.map (convertTerm depth))
  | .Case scrut alts => .Case (convertTerm depth scrut) (alts.map (convertTerm depth))
  | .Error => .Error

private def moistToFvt (t : Moist.Plutus.Term.Term) : PlutusCore.UPLC.Term.Term :=
  convertTerm 0 t

/-! ## compile_fvt! elaborator -/

/-- Compile an @[onchain] definition to `PlutusCore.UPLC.Term.Term`.
    Conversion from de Bruijn to named variables happens at elaboration time. -/
elab "compile_fvt!" id:ident : term => do
  let name ← resolveGlobalConstNoOverload id
  let env ← getEnv
  unless onchainAttr.hasTag env name do
    throwError "{name} is not marked @[onchain]"
  let result ← compileToUPLC name
  match result with
  | .ok moistTerm =>
    let fvtTerm := moistToFvt moistTerm
    return toExpr fvtTerm
  | .error e => throwError "compilation of {name} failed: {e}"

end Test.CompileFvt
