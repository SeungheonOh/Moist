import Moist.MIR.Expr

namespace Moist.MIR

open Moist.Plutus.Term
open Moist.Plutus (ByteString)
open Std (Format)

/-! # MIR Pretty Printer

Uses Lean's built-in Wadler-style Format for smart layout.
Short expressions stay on one line; long ones break with proper indentation.
-/

def builtinName : BuiltinFun → String
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

private def fmtConst : Const → Format
  | c => .text <| go c
where
  fmtByteString (bs : ByteString) : String :=
    let hex := bs.data.toList.map fun b =>
      let hi := b.toNat / 16
      let lo := b.toNat % 16
      let hexChar n := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
      s!"{hexChar hi}{hexChar lo}"
    "#" ++ String.join hex

  fmtData : Moist.Plutus.Data → String
    | .Constr idx fields => s!"(Constr {idx} {fmtDataList fields})"
    | .Map entries => s!"(Map {fmtDataPairList entries})"
    | .List xs => s!"(List {fmtDataList xs})"
    | .I n => s!"(I {n})"
    | .B bs => s!"(B {fmtByteString bs})"

  fmtDataList : List Moist.Plutus.Data → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map fmtData) ++ "]"

  fmtDataPair : Moist.Plutus.Data × Moist.Plutus.Data → String
    | (a, b) => s!"({fmtData a}, {fmtData b})"

  fmtDataPairList : List (Moist.Plutus.Data × Moist.Plutus.Data) → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map fmtDataPair) ++ "]"

  fmtConstList : List Const → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map go) ++ "]"

  fmtConstPair : Const × Const → String
    | (a, b) => s!"({go a}, {go b})"

  go : Const → String
    | .Integer n => toString n
    | .ByteString bs => fmtByteString bs
    | .String s => s!"\"{s}\""
    | .Unit => "()"
    | .Bool b => if b then "True" else "False"
    | .ConstList xs => fmtConstList xs
    | .ConstDataList xs => fmtDataList xs
    | .ConstPairDataList xs => fmtDataPairList xs
    | .Pair p => fmtConstPair p
    | .PairData p => fmtDataPair p
    | .Data d => fmtData d
    | .Bls12_381_G1_element => "<G1>"
    | .Bls12_381_G2_element => "<G2>"
    | .Bls12_381_MlResult => "<MlResult>"

private def fmtVar (v : VarId) : Format := .text (toString v)

private def parensIf (cond : Bool) (f : Format) : Format :=
  if cond then .text "(" ++ f ++ .text ")" else f

private def needsParens : Expr → Bool
  | .App _ _ | .Lam _ _ | .Fix _ _ | .Let _ _ | .Force _ | .Delay _ | .Case _ _ => true
  | _ => false

private def collectLamParams : Expr → List VarId × Expr
  | .Lam x body =>
    let (params, inner) := collectLamParams body
    (x :: params, inner)
  | e => ([], e)

private def collectLetBinds : Expr → List (VarId × Expr) × Expr
  | .Let binds body =>
    let (moreBinds, innerBody) := collectLetBinds body
    (binds ++ moreBinds, innerBody)
  | e => ([], e)

private def uncurryAppFmt : Expr → Expr × List Expr
  | .App f x =>
    let (head, args) := uncurryAppFmt f
    (head, args ++ [x])
  | e => (e, [])

partial def fmtExpr : Expr → Format
  | .Var v => fmtVar v
  | .Lit (c, _) => fmtConst c
  | .Builtin b => .text (builtinName b)
  | .Error => .text "error"

  | .Lam x body =>
    let (params, inner) := collectLamParams body
    let allParams := x :: params
    let paramsFmt := Format.joinSep (allParams.map fmtVar) (.text " ")
    Format.group
      (.text "λ" ++ paramsFmt ++ .text "." ++
        Format.nest 2 (Format.line ++ fmtExpr inner))

  | .Fix f body =>
    Format.group
      (.text "fix " ++ fmtVar f ++ .text " =" ++
        Format.nest 2 (Format.line ++ fmtExpr body))

  | .App f x =>
    let (head, args) := uncurryAppFmt (.App f x)
    let parts := head :: args
    let fmts := parts.map fun e => parensIf (needsParens e) (fmtExpr e)
    Format.group (Format.joinSep fmts (.text " "))

  | .Force e =>
    Format.group
      (.text "force " ++ parensIf (needsParens e) (fmtExpr e))

  | .Delay e =>
    Format.group
      (.text "delay" ++ Format.nest 2 (Format.line ++ fmtExpr e))

  | .Constr tag args =>
    let argFmts := args.map fun e => parensIf (needsParens e) (fmtExpr e)
    Format.group
      (.text s!"constr({tag}" ++
        (if args.isEmpty then .nil
         else .text " " ++ Format.joinSep argFmts (.text " ")) ++
        .text ")")

  | .Case scrut alts =>
    let scrutFmt := parensIf (needsParens scrut) (fmtExpr scrut)
    let altFmts := alts.map fun e => .text "| " ++ fmtExpr e
    let altsDoc := altFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil
    .text "case " ++ scrutFmt ++ .text " of" ++
      Format.nest 2 altsDoc

  | .Let binds body =>
    let (extraBinds, innerBody) := collectLetBinds body
    let allBinds := binds ++ extraBinds
    let fmtBind (v : VarId) (rhs : Expr) : Format :=
      Format.group
        (.text "let " ++ fmtVar v ++ .text " =" ++
          Format.nest 2 (Format.line ++ fmtExpr rhs))
    match allBinds with
    | [] => fmtExpr innerBody
    | (v, rhs) :: rest =>
      let bindsDoc := rest.foldl
        (fun acc (v, rhs) => acc ++ Format.line ++ fmtBind v rhs)
        (fmtBind v rhs)
      bindsDoc ++ Format.line ++
        Format.group (.text "in" ++ Format.nest 2 (Format.line ++ fmtExpr innerBody))

def pretty (e : Expr) (width : Nat := 100) : String :=
  (fmtExpr e).pretty width

instance : ToString Expr where
  toString e := pretty e

instance : Std.ToFormat Expr where
  format := fmtExpr

end Moist.MIR
