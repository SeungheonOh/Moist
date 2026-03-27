import Moist.Plutus.Term

namespace Moist.Plutus.PrettyHuman

open Moist.Plutus.Term
open Std (Format)

/-! # Human-Readable UPLC Pretty Printer

Renders UPLC terms in a readable, high-level format:
- `Apply (Lam _ body) arg` is shown as `let x = arg in body`
- Lambdas get generated names (`i0`, `i1`, ...)
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
  | .DropList => "dropList"
  | .IndexArray => "indexArray"
  | .LengthOfArray => "lengthOfArray"
  | .ListToArray => "listToArray"
  | .InsertCoin => "insertCoin"
  | .LookupCoin => "lookupCoin"
  | .ScaleValue => "scaleValue"
  | .UnionValue => "unionValue"
  | .ValueContains => "valueContains"
  | .ValueData => "valueData"
  | .UnValueData => "unValueData"
  | .Bls12_381_G1_multiScalarMul => "bls12_381_G1_multiScalarMul"
  | .Bls12_381_G2_multiScalarMul => "bls12_381_G2_multiScalarMul"

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
    | .ConstArray xs => fmtConstList xs
    | .Bls12_381_G1_element => "<G1>"
    | .Bls12_381_G2_element => "<G2>"
    | .Bls12_381_MlResult => "<MlResult>"
end

/-- Generate a readable variable name from a counter.
    0→a, 1→b, ..., 25→z, 26→a1, 27→b1, ..., 51→z1, 52→a2, ... -/
private def freshName (n : Nat) : String :=
  let letter := Char.ofNat (97 + n % 26)  -- 'a' + offset
  let cycle := n / 26
  if cycle == 0 then s!"{letter}" else s!"{letter}{cycle}"

/-- Look up a De Bruijn variable in the name environment.
    `env` has outermost binder at index 0, innermost at the end.
    De Bruijn index 1 = innermost binder. -/
private def lookupVar (env : Array String) (idx : Nat) : String :=
  if idx == 0 || idx > env.size then s!"?{idx}"
  else env[env.size - idx]!

/-- Does this term need parentheses when used as an argument? -/
private def needsParens : Term → Bool
  | .Var _ | .Constant _ | .Builtin _ | .Error => false
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
    `env` tracks generated names for De Bruijn variables.
    `c` is the fresh name counter.
    Returns `(Format, updated counter)`. -/
partial def fmtHuman (t : Term) (env : Array String) (c : Nat) : Format × Nat :=
  match t with
  | .Var n => (.text (lookupVar env n), c)

  | .Constant (cv, _) => (.text (fmtConst cv), c)

  | .Builtin b => (.text (builtinName b), c)

  | .Error => (.text "error", c)

  -- Let binding: Apply (Lam _ body) arg → let name = arg in body
  | t@(.Apply (.Lam _ _) _) =>
    let (binds, inner, env', c') := collectLets t env c
    let (bodyFmt, c'') := fmtHuman inner env' c'
    let bindsFmt := binds.map fun (name, val) =>
      Format.group
        (.text s!"let {name} =" ++ Format.nest 2 (Format.line ++ val))
    match bindsFmt with
    | [] => (bodyFmt, c'')
    | first :: rest =>
      let bindsDoc := rest.foldl (fun acc b => acc ++ Format.line ++ b) first
      (bindsDoc ++ Format.line ++
        Format.group (.text "in" ++ Format.nest 2 (Format.line ++ bodyFmt)), c'')

  -- Lambda: collect multi-param lambdas
  | t@(.Lam _ _) =>
    let (names, inner, env', c') := collectLams t env c
    let (bodyFmt, c'') := fmtHuman inner env' c'
    let paramStr := String.intercalate " " names
    let fmt := .text s!"λ{paramStr}." ++ Format.nest 2 (Format.line ++ bodyFmt)
    (if forcesMultiline inner then fmt else Format.group fmt, c'')

  -- Application: uncurry into f x y z
  | t@(.Apply _ _) =>
    let (head, args) := uncurryApp t
    let (headFmt, c1) := fmtHuman head env c
    let (argFmts, c2) := fmtArgs args env c1
    let headFmt' := parensIf (needsParens head) headFmt
    let argsDoc := argFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil
    (Format.group (headFmt' ++ Format.nest 2 argsDoc), c2)

  | .Force e =>
    let (eFmt, c') := fmtHuman e env c
    (Format.group
      (.text "force " ++ parensIf (needsParens e) eFmt), c')

  | .Delay e =>
    let (eFmt, c') := fmtHuman e env c
    (Format.group
      (.text "delay" ++ Format.nest 2 (Format.line ++ parensIf (needsParens e) eFmt)), c')

  | .Constr tag args =>
    let (argFmts, c') := fmtArgs args env c
    (Format.group
      (.text s!"constr({tag}" ++
        (if args.isEmpty then .nil
         else .text " " ++ Format.joinSep argFmts (.text " ")) ++
        .text ")"), c')

  | .Case scrut alts =>
    let (scrutFmt, c1) := fmtHuman scrut env c
    let (altFmts, c2) := fmtCaseAlts alts env c1
    let altsDoc := altFmts.foldl (fun acc a => acc ++ Format.line ++ a) .nil
    (.text "case " ++ parensIf (needsParens scrut) scrutFmt ++ .text " of" ++
      Format.nest 2 altsDoc, c2)

where
  /-- Collect a chain of let bindings (Apply (Lam _ body) arg). -/
  collectLets (t : Term) (env : Array String) (c : Nat)
      : List (String × Format) × Term × Array String × Nat :=
    match t with
    | .Apply (.Lam _ body) arg =>
      let (argFmt, c1) := fmtHuman arg env c
      let name := freshName c1
      let c2 := c1 + 1
      let env' := env.push name
      let (moreBinds, inner, env'', c3) := collectLets body env' c2
      ((name, argFmt) :: moreBinds, inner, env'', c3)
    | other => ([], other, env, c)

  /-- Collect consecutive lambdas into a multi-param lambda. -/
  collectLams (t : Term) (env : Array String) (c : Nat)
      : List String × Term × Array String × Nat :=
    match t with
    | .Lam _ body =>
      let name := freshName c
      let c1 := c + 1
      let env' := env.push name
      let (moreNames, inner, env'', c2) := collectLams body env' c1
      (name :: moreNames, inner, env'', c2)
    | other => ([], other, env, c)

  /-- Format a list of argument terms, wrapping non-atoms in parens. -/
  fmtArgs (args : List Term) (env : Array String) (c : Nat)
      : List Format × Nat :=
    args.foldl (fun (acc, ci) arg =>
      let (fmt, ci') := fmtHuman arg env ci
      (acc ++ [parensIf (needsParens arg) fmt], ci'))
      ([], c)

  /-- Format a single case alternative.
      If the alt is a lambda, render as `λparams. body` with body on next line. -/
  fmtCaseAlt (alt : Term) (env : Array String) (c : Nat)
      : Format × Nat :=
    match alt with
    | .Lam _ _ =>
      let (names, inner, env', c') := collectLams alt env c
      let (bodyFmt, c'') := fmtHuman inner env' c'
      let paramStr := String.intercalate " " names
      (.text s!"λ{paramStr}." ++ Format.nest 2 (Format.line ++ bodyFmt), c'')
    | other =>
      let (fmt, c') := fmtHuman other env c
      (fmt, c')

  /-- Format case alternatives. -/
  fmtCaseAlts (alts : List Term) (env : Array String) (c : Nat)
      : List Format × Nat :=
    alts.foldl (fun (acc, ci) alt =>
      let (fmt, ci') := fmtCaseAlt alt env ci
      (acc ++ [.text "| " ++ fmt], ci'))
      ([], c)

def fmtHumanProgram : Program → Format
  | .Program (.Version a b c) t =>
    let (termFmt, _) := fmtHuman t #[] 0
    Format.group
      (.text s!"(program {a}.{b}.{c}" ++
        Format.nest 2 (Format.line ++ termFmt) ++
        .text ")")

def prettyHuman (t : Term) (width : Nat := 100) : String :=
  (fmtHuman t #[] 0).1.pretty width

def prettyHumanProgram (p : Program) (width : Nat := 100) : String :=
  (fmtHumanProgram p).pretty width

end Moist.Plutus.PrettyHuman

def Moist.Plutus.Term.Term.prettyTerm (t : Moist.Plutus.Term.Term) (width : Nat := 100) : String :=
  Moist.Plutus.PrettyHuman.prettyHuman t width

def Moist.Plutus.Term.Term.printPrettyTerm (t : Moist.Plutus.Term.Term) (width : Nat := 100) : IO Unit :=
  IO.println (Moist.Plutus.PrettyHuman.prettyHuman t width)
