import Moist.Plutus.Term

namespace Moist.Plutus.Pretty

open Moist.Plutus.Term
open Std (Format)

/-! # UPLC Pretty Printer

Renders UPLC Terms in the standard Plutus textual format:
- Application uses square brackets: `[f x]`
- Everything else uses parentheses
- De Bruijn indexed variables
-/

private def fmtBuiltin : BuiltinFun → String
  | .AddInteger => "addInteger"
  | .SubtractInteger => "subtractInteger"
  | .MultiplyInteger => "multiplyInteger"
  | .DivideInteger => "divideInteger"
  | .QuotientInteger => "quotientInteger"
  | .RemainderInteger => "remainderInteger"
  | .ModInteger => "modInteger"
  | .EqualsInteger => "equalsInteger"
  | .LessThanInteger => "lessThanInteger"
  | .LessThanEqualsInteger => "lessThanEqualsInteger"
  | .AppendByteString => "appendByteString"
  | .ConsByteString => "consByteString"
  | .SliceByteString => "sliceByteString"
  | .LengthOfByteString => "lengthOfByteString"
  | .IndexByteString => "indexByteString"
  | .EqualsByteString => "equalsByteString"
  | .LessThanByteString => "lessThanByteString"
  | .LessThanEqualsByteString => "lessThanEqualsByteString"
  | .Sha2_256 => "sha2_256"
  | .Sha3_256 => "sha3_256"
  | .Blake2b_256 => "blake2b_256"
  | .VerifyEd25519Signature => "verifyEd25519Signature"
  | .AppendString => "appendString"
  | .EqualsString => "equalsString"
  | .EncodeUtf8 => "encodeUtf8"
  | .DecodeUtf8 => "decodeUtf8"
  | .IfThenElse => "ifThenElse"
  | .ChooseUnit => "chooseUnit"
  | .Trace => "trace"
  | .FstPair => "fstPair"
  | .SndPair => "sndPair"
  | .ChooseList => "chooseList"
  | .MkCons => "mkCons"
  | .HeadList => "headList"
  | .TailList => "tailList"
  | .NullList => "nullList"
  | .ChooseData => "chooseData"
  | .ConstrData => "constrData"
  | .MapData => "mapData"
  | .ListData => "listData"
  | .IData => "iData"
  | .BData => "bData"
  | .UnConstrData => "unConstrData"
  | .UnMapData => "unMapData"
  | .UnListData => "unListData"
  | .UnIData => "unIData"
  | .UnBData => "unBData"
  | .EqualsData => "equalsData"
  | .MkPairData => "mkPairData"
  | .MkNilData => "mkNilData"
  | .MkNilPairData => "mkNilPairData"
  | .SerializeData => "serializeData"
  | .VerifyEcdsaSecp256k1Signature => "verifyEcdsaSecp256k1Signature"
  | .VerifySchnorrSecp256k1Signature => "verifySchnorrSecp256k1Signature"
  | .Bls12_381_G1_add => "bls12_381_G1_add"
  | .Bls12_381_G1_neg => "bls12_381_G1_neg"
  | .Bls12_381_G1_scalarMul => "bls12_381_G1_scalarMul"
  | .Bls12_381_G1_equal => "bls12_381_G1_equal"
  | .Bls12_381_G1_hashToGroup => "bls12_381_G1_hashToGroup"
  | .Bls12_381_G1_compress => "bls12_381_G1_compress"
  | .Bls12_381_G1_uncompress => "bls12_381_G1_uncompress"
  | .Bls12_381_G2_add => "bls12_381_G2_add"
  | .Bls12_381_G2_neg => "bls12_381_G2_neg"
  | .Bls12_381_G2_scalarMul => "bls12_381_G2_scalarMul"
  | .Bls12_381_G2_equal => "bls12_381_G2_equal"
  | .Bls12_381_G2_hashToGroup => "bls12_381_G2_hashToGroup"
  | .Bls12_381_G2_compress => "bls12_381_G2_compress"
  | .Bls12_381_G2_uncompress => "bls12_381_G2_uncompress"
  | .Bls12_381_millerLoop => "bls12_381_millerLoop"
  | .Bls12_381_mulMlResult => "bls12_381_mulMlResult"
  | .Bls12_381_finalVerify => "bls12_381_finalVerify"
  | .Keccak_256 => "keccak_256"
  | .Blake2b_224 => "blake2b_224"
  | .IntegerToByteString => "integerToByteString"
  | .ByteStringToInteger => "byteStringToInteger"
  | .AndByteString => "andByteString"
  | .OrByteString => "orByteString"
  | .XorByteString => "xorByteString"
  | .ComplementByteString => "complementByteString"
  | .ReadBit => "readBit"
  | .WriteBits => "writeBits"
  | .ReplicateByte => "replicateByte"
  | .ShiftByteString => "shiftByteString"
  | .RotateByteString => "rotateByteString"
  | .CountSetBits => "countSetBits"
  | .FindFirstSetBit => "findFirstSetBit"
  | .Ripemd_160 => "ripemd_160"
  | .ExpModInteger => "expModInteger"

private def fmtAtomicType : AtomicType → String
  | .TypeInteger => "integer"
  | .TypeByteString => "bytestring"
  | .TypeString => "string"
  | .TypeBool => "bool"
  | .TypeUnit => "unit"
  | .TypeData => "data"

mutual
  private def fmtByteString : ByteString → String
    | bs =>
        let hex := bs.data.toList.map fun b =>
          let hi := b.toNat / 16
          let lo := b.toNat % 16
          let hexChar n := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
          s!"{hexChar hi}{hexChar lo}"
        "#" ++ String.join hex

  private def fmtData : Moist.Plutus.Data → String
    | .Constr idx fields => s!"(Constr {idx} {fmtDataList fields})"
    | .Map entries => s!"(Map {fmtDataPairList entries})"
    | .List xs => s!"(List {fmtDataList xs})"
    | .I n => s!"(I {n})"
    | .B bs => s!"(B {fmtByteString bs})"

  private def fmtDataList : List Moist.Plutus.Data → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map fmtData) ++ "]"

  private def fmtDataPair : Moist.Plutus.Data × Moist.Plutus.Data → String
    | (a, b) => s!"({fmtData a}, {fmtData b})"

  private def fmtDataPairList : List (Moist.Plutus.Data × Moist.Plutus.Data) → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map fmtDataPair) ++ "]"

  private def fmtConstList : List Const → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map fmtConst) ++ "]"

  private def fmtConstPair : Const × Const → String
    | (a, b) => s!"({fmtConst a}, {fmtConst b})"

  private def fmtConst : Const → String
    | .Integer n => toString n
    | .ByteString bs => fmtByteString bs
    | .String s => s!"\"{s}\""
    | .Unit => "()"
    | .Bool b => if b then "True" else "False"
    | .Data d => fmtData d
    | .ConstList xs => fmtConstList xs
    | .ConstDataList xs => fmtDataList xs
    | .ConstPairDataList xs => fmtDataPairList xs
    | .Pair p => fmtConstPair p
    | .PairData p => fmtDataPair p
    | .Bls12_381_G1_element => "<G1>"
    | .Bls12_381_G2_element => "<G2>"
    | .Bls12_381_MlResult => "<MlResult>"
end

mutual
  private def fmtBuiltinType : BuiltinType → String
    | .AtomicType t => fmtAtomicType t
    | .TypeOperator op => fmtTypeOp op

  private def fmtTypeOp : TypeOperator → String
    | .TypeList t => s!"(list {fmtBuiltinType t})"
    | .TypePair a b => s!"(pair {fmtBuiltinType a} {fmtBuiltinType b})"
end

partial def fmtTerm : Term → Format
  | .Var n =>
    .text s!"(var {n})"

  | .Constant (c, ty) =>
    .text s!"(con {fmtBuiltinType ty} {fmtConst c})"

  | .Builtin b =>
    .text s!"(builtin {fmtBuiltin b})"

  | .Error =>
    .text "(error)"

  | .Lam _ body =>
    Format.group
      (.text "(lam" ++
        Format.nest 2 (Format.line ++ fmtTerm body) ++
        .text ")")

  | .Apply f x =>
    Format.group
      (.text "[" ++
        Format.nest 2 (fmtTerm f ++ Format.line ++ fmtTerm x) ++
        .text "]")

  | .Force e =>
    Format.group
      (.text "(force" ++
        Format.nest 2 (Format.line ++ fmtTerm e) ++
        .text ")")

  | .Delay e =>
    Format.group
      (.text "(delay" ++
        Format.nest 2 (Format.line ++ fmtTerm e) ++
        .text ")")

  | .Constr tag args =>
    let argFmts := args.map fmtTerm
    Format.group
      (.text s!"(constr {tag}" ++
        (if args.isEmpty then .nil
         else Format.nest 2 (argFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil)) ++
        .text ")")

  | .Case scrut alts =>
    let altFmts := alts.map fmtTerm
    Format.group
      (.text "(case" ++
        Format.nest 2 (Format.line ++ fmtTerm scrut ++
          altFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil) ++
        .text ")")

def fmtProgram : Program → Format
  | .Program (.Version a b c) t =>
    Format.group
      (.text s!"(program {a}.{b}.{c}" ++
        Format.nest 2 (Format.line ++ fmtTerm t) ++
        .text ")")

def prettyTerm (t : Term) (width : Nat := 100) : String :=
  (fmtTerm t).pretty width

def prettyProgram (p : Program) (width : Nat := 100) : String :=
  (fmtProgram p).pretty width

instance : ToString Term where
  toString := prettyTerm

instance : ToString Program where
  toString := prettyProgram

instance : Std.ToFormat Term where
  format := fmtTerm

instance : Std.ToFormat Program where
  format := fmtProgram

end Moist.Plutus.Pretty
