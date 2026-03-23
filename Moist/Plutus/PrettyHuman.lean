import PlutusCore.UPLC.Term
import Moist.Plutus.Convert

namespace Moist.Plutus.PrettyHuman

open PlutusCore.UPLC.Term
open Std (Format)

/-! # Human-Readable UPLC Pretty Printer

Renders UPLC terms in a readable, high-level format:
- `Apply (Lam name body) arg` is shown as `let name = arg in body`
- Variables show their actual names from the term
- Applications are uncurried: `f x y z`
- Builtins shown by name without wrapper
- Minimal parenthesization
-/

private def builtinName : BuiltinFun → String
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

mutual
  private def fmtByteString (bs : PlutusCore.ByteString.ByteString) : String :=
    let hex := bs.data.data.map fun c =>
      let b := c.toNat
      let hi := b / 16
      let lo := b % 16
      let hexChar n := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
      s!"{hexChar hi}{hexChar lo}"
    "#" ++ String.join hex

  private def fmtData : PlutusCore.Data.Data → String
    | .Constr idx fields => s!"(Constr {idx} {fmtDataList fields})"
    | .Map entries => s!"(Map {fmtDataPairList entries})"
    | .List xs => s!"(List {fmtDataList xs})"
    | .I n => s!"(I {n})"
    | .B bs => s!"(B {fmtByteString bs})"

  private def fmtDataList : List PlutusCore.Data.Data → String
    | [] => "[]"
    | xs => "[" ++ String.intercalate ", " (xs.map fmtData) ++ "]"

  private def fmtDataPair : PlutusCore.Data.Data × PlutusCore.Data.Data → String
    | (a, b) => s!"({fmtData a}, {fmtData b})"

  private def fmtDataPairList : List (PlutusCore.Data.Data × PlutusCore.Data.Data) → String
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

/-- Does this term need parentheses when used as an argument? -/
private def needsParens : Term → Bool
  | .Var _ | .Const _ | .Builtin _ | .Error => false
  | .Constr _ _ => false
  | _ => true

private def parensIf (cond : Bool) (f : Format) : Format :=
  if cond then .text "(" ++ f ++ .text ")" else f

/-- Does this term require multiline rendering?
    Used to avoid wrapping in `Format.group` which would flatten line breaks. -/
private def forcesMultiline : Term → Bool
  | .Case _ _ => true
  | .Apply (.Lam _ _) _ => true
  | _ => false

/-- Uncurry an application spine, stopping at let patterns (`Apply (Lam _ _) _`). -/
private def uncurryApp : Term → Term × List Term
  | .Apply f x =>
    match f with
    | .Apply (.Lam _ _) _ =>
      -- f is a let-binding; treat as head, don't uncurry through it
      (f, [x])
    | _ =>
      let (head, args) := uncurryApp f
      (head, args ++ [x])
  | other => (other, [])

/-- Render a UPLC term in human-readable format.
    Since terms carry their own variable names, no environment is needed. -/
partial def fmtHuman (t : Term) : Format :=
  match t with
  | .Var name => .text name

  | .Const cv => .text (fmtConst cv)

  | .Builtin b => .text (builtinName b)

  | .Error => .text "error"

  -- Let binding: Apply (Lam name body) arg -> let name = arg in body
  | t@(.Apply (.Lam _ _) _) =>
    let (binds, inner) := collectLets t
    let bodyFmt := fmtHuman inner
    let bindsFmt := binds.map fun (name, val) =>
      Format.group
        (.text s!"let {name} =" ++ Format.nest 2 (Format.line ++ val))
    match bindsFmt with
    | [] => bodyFmt
    | first :: rest =>
      let bindsDoc := rest.foldl (fun acc b => acc ++ Format.line ++ b) first
      bindsDoc ++ Format.line ++
        Format.group (.text "in" ++ Format.nest 2 (Format.line ++ bodyFmt))

  -- Lambda: collect multi-param lambdas
  | t@(.Lam _ _) =>
    let (names, inner) := collectLams t
    let bodyFmt := fmtHuman inner
    let paramStr := String.intercalate " " names
    let fmt := .text s!"λ{paramStr}." ++ Format.nest 2 (Format.line ++ bodyFmt)
    if forcesMultiline inner then fmt else Format.group fmt

  -- Application: uncurry into f x y z
  | t@(.Apply _ _) =>
    let (head, args) := uncurryApp t
    let headFmt := fmtHuman head
    let argFmts := fmtArgs args
    let headFmt' := parensIf (needsParens head) headFmt
    let argsDoc := argFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil
    Format.group (headFmt' ++ Format.nest 2 argsDoc)

  | .Force e =>
    let eFmt := fmtHuman e
    Format.group
      (.text "force " ++ parensIf (needsParens e) eFmt)

  | .Delay e =>
    let eFmt := fmtHuman e
    Format.group
      (.text "delay" ++ Format.nest 2 (Format.line ++ parensIf (needsParens e) eFmt))

  | .Constr tag args =>
    let argFmts := fmtArgs args
    Format.group
      (.text s!"constr({tag}" ++
        (if args.isEmpty then .nil
         else .text " " ++ Format.joinSep argFmts (.text " ")) ++
        .text ")")

  | .Case scrut alts =>
    let scrutFmt := fmtHuman scrut
    let altFmts := fmtCaseAlts alts
    let altsDoc := altFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil
    .text "case " ++ parensIf (needsParens scrut) scrutFmt ++ .text " of" ++
      Format.nest 2 altsDoc

where
  /-- Collect a chain of let bindings (Apply (Lam name body) arg). -/
  collectLets (t : Term) : List (String × Format) × Term :=
    match t with
    | .Apply (.Lam name body) arg =>
      let argFmt := fmtHuman arg
      let (moreBinds, inner) := collectLets body
      ((name, argFmt) :: moreBinds, inner)
    | other => ([], other)

  /-- Collect consecutive lambdas into a multi-param lambda. -/
  collectLams (t : Term) : List String × Term :=
    match t with
    | .Lam name body =>
      let (moreNames, inner) := collectLams body
      (name :: moreNames, inner)
    | other => ([], other)

  /-- Format a list of argument terms, wrapping non-atoms in parens. -/
  fmtArgs (args : List Term) : List Format :=
    args.map fun arg =>
      let fmt := fmtHuman arg
      parensIf (needsParens arg) fmt

  /-- Format a single case alternative.
      If the alt is a lambda, render as `λparams. body` with body on next line. -/
  fmtCaseAlt (alt : Term) : Format :=
    match alt with
    | .Lam _ _ =>
      let (names, inner) := collectLams alt
      let bodyFmt := fmtHuman inner
      let paramStr := String.intercalate " " names
      .text s!"λ{paramStr}." ++ Format.nest 2 (Format.line ++ bodyFmt)
    | other =>
      fmtHuman other

  /-- Format case alternatives. -/
  fmtCaseAlts (alts : List Term) : List Format :=
    alts.map fun alt => .text "| " ++ fmtCaseAlt alt

def fmtHumanProgram : Program → Format
  | .Program (.Version a b c) t =>
    let termFmt := fmtHuman t
    Format.group
      (.text s!"(program {a}.{b}.{c}" ++
        Format.nest 2 (Format.line ++ termFmt) ++
        .text ")")

def prettyHuman (t : Term) (width : Nat := 100) : String :=
  (fmtHuman t).pretty width

def prettyHumanProgram (p : Program) (width : Nat := 100) : String :=
  (fmtHumanProgram p).pretty width

end Moist.Plutus.PrettyHuman

def PlutusCore.UPLC.Term.Term.prettyTerm (t : PlutusCore.UPLC.Term.Term) (width : Nat := 100) : String :=
  Moist.Plutus.PrettyHuman.prettyHuman t width

def PlutusCore.UPLC.Term.Term.printPrettyTerm (t : PlutusCore.UPLC.Term.Term) (width : Nat := 100) : IO Unit :=
  IO.println (Moist.Plutus.PrettyHuman.prettyHuman t width)
