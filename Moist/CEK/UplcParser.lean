import Moist.Plutus.Term
import Moist.Plutus.Types

namespace Moist.CEK.UplcParser

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString Integer)

/-! # UPLC Textual Syntax Parser

Parses the Plutus conformance test format:
```
(program <major>.<minor>.<patch> <term>)
```

Named variables are converted to 1-based de Bruijn indices during parsing.
-/

/-! ## Parser Monad -/

structure ParseState where
  input : String
  pos   : String.Pos
deriving Inhabited

abbrev Parser := EStateM String ParseState

private def remaining (s : ParseState) : Substring :=
  ⟨s.input, s.pos, s.input.endPos⟩

private def peek? : Parser (Option Char) := do
  let s ← get
  if s.pos < s.input.endPos then
    pure (some (s.input.get s.pos))
  else
    pure none

private def next : Parser Char := do
  let s ← get
  if s.pos < s.input.endPos then
    let c := s.input.get s.pos
    set { s with pos := s.input.next s.pos }
    pure c
  else
    throw "unexpected end of input"

private def expect (c : Char) : Parser Unit := do
  let got ← next
  if got != c then throw s!"expected '{c}', got '{got}'"

private def skipWhitespaceAndComments : Parser Unit := do
  let mut continue_ := true
  while continue_ do
    let c? ← peek?
    match c? with
    | some ' ' | some '\n' | some '\r' | some '\t' => discard next
    | some '-' =>
      let s ← get
      let nextPos := s.input.next s.pos
      if nextPos < s.input.endPos && s.input.get nextPos == '-' then
        -- Skip line comment
        discard next; discard next
        let mut inComment := true
        while inComment do
          let c? ← peek?
          match c? with
          | some '\n' => discard next; inComment := false
          | some _ => discard next
          | none => inComment := false
      else
        continue_ := false
    | _ => continue_ := false

private def ws : Parser Unit := skipWhitespaceAndComments

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '\''

private def parseIdent : Parser String := do
  ws
  let s ← get
  let start := s.pos
  let c? ← peek?
  match c? with
  | none => throw "expected identifier, got end of input"
  | some c =>
    if !c.isAlpha && c != '_' then throw s!"expected identifier, got '{c}'"
    else pure ()
  let mut done := false
  while !done do
    let c? ← peek?
    match c? with
    | some c => if isIdentChar c then discard next else done := true
    | none => done := true
  let s' ← get
  let ident := s.input.extract start s'.pos
  if ident.isEmpty then throw "expected identifier"
  pure ident

private def parseNat : Parser Nat := do
  ws
  let c? ← peek?
  match c? with
  | none => throw "expected number"
  | some c => if !c.isDigit then throw s!"expected digit, got '{c}'" else pure ()
  let mut n : Nat := 0
  let mut done := false
  while !done do
    let c? ← peek?
    match c? with
    | some c =>
      if c.isDigit then
        n := n * 10 + (c.toNat - '0'.toNat)
        discard next
      else done := true
    | none => done := true
  pure n

private def parseHexByte (hi lo : Char) : Option UInt8 :=
  let hexVal (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  match hexVal hi, hexVal lo with
  | some h, some l => some (UInt8.ofNat (h * 16 + l))
  | _, _ => none

private def parseByteString : Parser ByteArray := do
  ws
  expect '#'
  let mut bytes : ByteArray := ByteArray.empty
  let mut done := false
  while !done do
    let c? ← peek?
    match c? with
    | some c =>
      if (c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) then
        let hi ← next
        let lo ← next
        match parseHexByte hi lo with
        | some b => bytes := bytes.push b
        | none => throw s!"invalid hex byte: {hi}{lo}"
      else done := true
    | none => done := true
  pure bytes

private def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def hexDigitVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

private def parseHexNat : Parser Nat := do
  let mut n : Nat := 0
  let mut count : Nat := 0
  let mut done := false
  while !done do
    let c? ← peek?
    match c? with
    | some c =>
      if isHexDigit c then
        n := n * 16 + hexDigitVal c
        discard next
        count := count + 1
      else done := true
    | none => done := true
  if count == 0 then throw "expected hex digit"
  pure n

private def parseInt : Parser Int := do
  ws
  let c? ← peek?
  let neg ← match c? with
    | some '-' => discard next; pure true
    | some '+' => discard next; pure false
    | _ => pure false
  -- Check for 0x hex prefix
  let c? ← peek?
  if c? == some '0' then
    let saved ← get
    discard next
    let c2? ← peek?
    if c2? == some 'x' || c2? == some 'X' then
      discard next
      let n ← parseHexNat
      pure (if neg then -(Int.ofNat n) else Int.ofNat n)
    else
      set saved
      let n ← parseNat
      pure (if neg then -(Int.ofNat n) else Int.ofNat n)
  else
    let n ← parseNat
    pure (if neg then -(Int.ofNat n) else Int.ofNat n)

/-- Parse consecutive hex digit pairs into a ByteArray (for 0x... literals). -/
private def parseHexBytes : Parser ByteArray := do
  let mut bytes : ByteArray := ByteArray.empty
  let mut done := false
  while !done do
    let c? ← peek?
    match c? with
    | some c =>
      if isHexDigit c then
        let hi ← next
        let lo ← next
        match parseHexByte hi lo with
        | some b => bytes := bytes.push b
        | none => throw s!"invalid hex byte: {hi}{lo}"
      else done := true
    | none => done := true
  pure bytes

private def isOctDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

/-- Parse consecutive hex digits and return the accumulated value. -/
private def parseHexCode : Parser Nat := do
  let mut code : Nat := 0
  let mut done := false
  while !done do
    let d? ← peek?
    match d? with
    | some d =>
      if isHexDigit d then
        code := code * 16 + hexDigitVal d
        discard next
      else done := true
    | none => done := true
  pure code

/-- Parse consecutive octal digits and return the accumulated value. -/
private def parseOctCode : Parser Nat := do
  let mut code : Nat := 0
  let mut done := false
  while !done do
    let d? ← peek?
    match d? with
    | some d =>
      if isOctDigit d then
        code := code * 8 + (d.toNat - '0'.toNat)
        discard next
      else done := true
    | none => done := true
  pure code

/-- Parse consecutive decimal digits and return the accumulated value. -/
private def parseDecCode : Parser Nat := do
  let mut code : Nat := 0
  let mut done := false
  while !done do
    let d? ← peek?
    match d? with
    | some d =>
      if d.isDigit then
        code := code * 10 + (d.toNat - '0'.toNat)
        discard next
      else done := true
    | none => done := true
  pure code

private def parseString : Parser String := do
  ws
  expect '"'
  let mut s := ""
  let mut done := false
  while !done do
    let c ← next
    if c == '"' then done := true
    else if c == '\\' then
      let esc ← peek?
      match esc with
      | some 'n' => discard next; s := s.push '\n'
      | some 't' => discard next; s := s.push '\t'
      | some '\\' => discard next; s := s.push '\\'
      | some '"' => discard next; s := s.push '"'
      | some 'a' => discard next; s := s.push '\x07'
      | some 'b' => discard next; s := s.push '\x08'
      | some 'f' => discard next; s := s.push '\x0C'
      | some 'r' => discard next; s := s.push '\r'
      | some 'v' => discard next; s := s.push '\x0B'
      | some 'x' =>
        discard next
        let code ← parseHexCode
        s := s.push (Char.ofNat code)
      | some 'o' =>
        discard next
        let code ← parseOctCode
        s := s.push (Char.ofNat code)
      | some d =>
        if d.isDigit then
          let code ← parseDecCode
          s := s.push (Char.ofNat code)
        else
          discard next
          s := s.push d
      | none => throw "unexpected end of input after backslash"
    else s := s.push c
  pure s

/-! ## Builtin Name Parsing -/

private def parseBuiltinName : Parser BuiltinFun := do
  let name ← parseIdent
  match name with
  | "addInteger" => pure .AddInteger
  | "subtractInteger" => pure .SubtractInteger
  | "multiplyInteger" => pure .MultiplyInteger
  | "divideInteger" => pure .DivideInteger
  | "quotientInteger" => pure .QuotientInteger
  | "remainderInteger" => pure .RemainderInteger
  | "modInteger" => pure .ModInteger
  | "equalsInteger" => pure .EqualsInteger
  | "lessThanInteger" => pure .LessThanInteger
  | "lessThanEqualsInteger" => pure .LessThanEqualsInteger
  | "appendByteString" => pure .AppendByteString
  | "consByteString" => pure .ConsByteString
  | "sliceByteString" => pure .SliceByteString
  | "lengthOfByteString" => pure .LengthOfByteString
  | "indexByteString" => pure .IndexByteString
  | "equalsByteString" => pure .EqualsByteString
  | "lessThanByteString" => pure .LessThanByteString
  | "lessThanEqualsByteString" => pure .LessThanEqualsByteString
  | "sha2_256" => pure .Sha2_256
  | "sha3_256" => pure .Sha3_256
  | "blake2b_256" => pure .Blake2b_256
  | "blake2b_224" => pure .Blake2b_224
  | "verifyEd25519Signature" => pure .VerifyEd25519Signature
  | "verifyEcdsaSecp256k1Signature" => pure .VerifyEcdsaSecp256k1Signature
  | "verifySchnorrSecp256k1Signature" => pure .VerifySchnorrSecp256k1Signature
  | "appendString" => pure .AppendString
  | "equalsString" => pure .EqualsString
  | "encodeUtf8" => pure .EncodeUtf8
  | "decodeUtf8" => pure .DecodeUtf8
  | "ifThenElse" => pure .IfThenElse
  | "chooseUnit" => pure .ChooseUnit
  | "trace" => pure .Trace
  | "fstPair" => pure .FstPair
  | "sndPair" => pure .SndPair
  | "chooseList" => pure .ChooseList
  | "mkCons" => pure .MkCons
  | "headList" => pure .HeadList
  | "tailList" => pure .TailList
  | "nullList" => pure .NullList
  | "chooseData" => pure .ChooseData
  | "constrData" => pure .ConstrData
  | "mapData" => pure .MapData
  | "listData" => pure .ListData
  | "iData" => pure .IData
  | "bData" => pure .BData
  | "unConstrData" => pure .UnConstrData
  | "unMapData" => pure .UnMapData
  | "unListData" => pure .UnListData
  | "unIData" => pure .UnIData
  | "unBData" => pure .UnBData
  | "equalsData" => pure .EqualsData
  | "mkPairData" => pure .MkPairData
  | "mkNilData" => pure .MkNilData
  | "mkNilPairData" => pure .MkNilPairData
  | "serialiseData" => pure .SerializeData
  | "serializeData" => pure .SerializeData
  | "keccak_256" => pure .Keccak_256
  | "integerToByteString" => pure .IntegerToByteString
  | "byteStringToInteger" => pure .ByteStringToInteger
  | "bls12_381_G1_add" => pure .Bls12_381_G1_add
  | "bls12_381_G1_neg" => pure .Bls12_381_G1_neg
  | "bls12_381_G1_scalarMul" => pure .Bls12_381_G1_scalarMul
  | "bls12_381_G1_equal" => pure .Bls12_381_G1_equal
  | "bls12_381_G1_hashToGroup" => pure .Bls12_381_G1_hashToGroup
  | "bls12_381_G1_compress" => pure .Bls12_381_G1_compress
  | "bls12_381_G1_uncompress" => pure .Bls12_381_G1_uncompress
  | "bls12_381_G2_add" => pure .Bls12_381_G2_add
  | "bls12_381_G2_neg" => pure .Bls12_381_G2_neg
  | "bls12_381_G2_scalarMul" => pure .Bls12_381_G2_scalarMul
  | "bls12_381_G2_equal" => pure .Bls12_381_G2_equal
  | "bls12_381_G2_hashToGroup" => pure .Bls12_381_G2_hashToGroup
  | "bls12_381_G2_compress" => pure .Bls12_381_G2_compress
  | "bls12_381_G2_uncompress" => pure .Bls12_381_G2_uncompress
  | "bls12_381_millerLoop" => pure .Bls12_381_millerLoop
  | "bls12_381_mulMlResult" => pure .Bls12_381_mulMlResult
  | "bls12_381_finalVerify" => pure .Bls12_381_finalVerify
  | "andByteString" => pure .AndByteString
  | "orByteString" => pure .OrByteString
  | "xorByteString" => pure .XorByteString
  | "complementByteString" => pure .ComplementByteString
  | "readBit" => pure .ReadBit
  | "writeBits" => pure .WriteBits
  | "replicateByte" => pure .ReplicateByte
  | "shiftByteString" => pure .ShiftByteString
  | "rotateByteString" => pure .RotateByteString
  | "countSetBits" => pure .CountSetBits
  | "findFirstSetBit" => pure .FindFirstSetBit
  | "ripemd_160" => pure .Ripemd_160
  | "expModInteger" => pure .ExpModInteger
  | "dropList" => pure .DropList
  | "indexArray" => pure .IndexArray
  | "lengthOfArray" => pure .LengthOfArray
  | "listToArray" => pure .ListToArray
  | "insertCoin" => pure .InsertCoin
  | "lookupCoin" => pure .LookupCoin
  | "scaleValue" => pure .ScaleValue
  | "unionValue" => pure .UnionValue
  | "valueContains" => pure .ValueContains
  | "valueData" => pure .ValueData
  | "unValueData" => pure .UnValueData
  | "bls12_381_G1_multiScalarMul" => pure .Bls12_381_G1_multiScalarMul
  | "bls12_381_G2_multiScalarMul" => pure .Bls12_381_G2_multiScalarMul
  | _ => throw s!"unknown builtin: {name}"

/-! ## Type Parsing -/

private partial def parseType : Parser BuiltinType := do
  ws
  let c? ← peek?
  match c? with
  | some '(' => do
    discard next; ws
    let kw ← parseIdent
    match kw with
    | "list" =>
      let inner ← parseType
      ws; expect ')'
      pure (.TypeOperator (.TypeList inner))
    | "pair" =>
      let t1 ← parseType
      let t2 ← parseType
      ws; expect ')'
      pure (.TypeOperator (.TypePair t1 t2))
    | "array" =>
      let inner ← parseType
      ws; expect ')'
      pure (.TypeOperator (.TypeArray inner))
    | _ => throw s!"unknown type constructor: {kw}"
  | _ =>
    let name ← parseIdent
    match name with
    | "integer" => pure (.AtomicType .TypeInteger)
    | "bytestring" => pure (.AtomicType .TypeByteString)
    | "string" => pure (.AtomicType .TypeString)
    | "bool" => pure (.AtomicType .TypeBool)
    | "unit" => pure (.AtomicType .TypeUnit)
    | "data" => pure (.AtomicType .TypeData)
    | "bls12_381_G1_element" => pure (.AtomicType .TypeBls12_381_G1_element)
    | "bls12_381_G2_element" => pure (.AtomicType .TypeBls12_381_G2_element)
    | "bls12_381_MlResult" => pure (.AtomicType .TypeBls12_381_MlResult)
    | "value" => pure (.AtomicType .TypeData)
    | _ => throw s!"unknown type: {name}"

/-! ## Data Literal Parsing -/

partial def parseDataLit : Parser Data := do
  ws
  let c? ← peek?
  -- Handle optional parentheses around data literals: (Constr 1 [...]) or Constr 1 [...]
  let parens ← match c? with
    | some '(' => discard next; pure true
    | _ => pure false
  let kw ← parseIdent
  let result ← match kw with
  | "Constr" => do
    let tag ← parseInt
    ws
    let fields ← parseDataList
    pure (.Constr tag fields)
  | "Map" => do
    ws; expect '['
    let pairs ← parseDataPairList
    ws; expect ']'
    pure (.Map pairs)
  | "List" => do
    ws
    let items ← parseDataList
    pure (.List items)
  | "I" => do
    let i ← parseInt
    pure (.I i)
  | "B" => do
    let bs ← parseByteString
    pure (.B bs)
  | _ => throw s!"unknown data constructor: {kw}"
  if parens then
    ws; expect ')'
  pure result
where
  parseDataList : Parser (List Data) := do
    ws; expect '['
    let mut items : List Data := []
    let mut done := false
    while !done do
      ws
      let c? ← peek?
      match c? with
      | some ']' => discard next; done := true
      | _ =>
        -- Skip comma if present
        let c? ← peek?
        if c? == some ',' then discard next
        ws
        let d ← parseDataLit
        items := items ++ [d]
    pure items
  parseDataPairList : Parser (List (Data × Data)) := do
    let mut pairs : List (Data × Data) := []
    let mut done := false
    while !done do
      ws
      let c? ← peek?
      match c? with
      | some ']' => done := true
      | _ =>
        if c? == some ',' then discard next
        ws; expect '('
        let k ← parseDataLit
        ws; expect ','
        let v ← parseDataLit
        ws; expect ')'
        pairs := pairs ++ [(k, v)]
    pure pairs

/-! ## Constant Value Parsing -/

/-- Parse a Cardano value literal: `[(#policy, [(#token, qty), ...]), ...]`
Represented as `Data.Map [(B policy, List [Map [(B token, I qty)]]), ...]` -/
private partial def parseValueLiteral : Parser (List (Data × Data)) := do
  ws; expect '['
  let mut pairs : List (Data × Data) := []
  let mut done := false
  while !done do
    ws
    let c? ← peek?
    match c? with
    | some ']' => discard next; done := true
    | _ =>
      if c? == some ',' then discard next; ws
      -- Each entry: (#policyId, [(#tokenName, qty), ...])
      expect '('
      let policyId ← parseByteString
      ws; expect ','
      ws
      -- Parse token map: [(#token, qty), ...]
      expect '['
      let mut tokenPairs : List (Data × Data) := []
      let mut tokenDone := false
      while !tokenDone do
        ws
        let tc? ← peek?
        match tc? with
        | some ']' => discard next; tokenDone := true
        | _ =>
          if tc? == some ',' then discard next; ws
          expect '('
          let tokenName ← parseByteString
          ws; expect ','
          ws
          let qty ← parseInt
          ws; expect ')'
          tokenPairs := tokenPairs ++ [(.B tokenName, .I qty)]
      ws; expect ')'
      pairs := pairs ++ [(.B policyId, .Map tokenPairs)]
  pure pairs

private partial def parseConstValue (ty : BuiltinType) : Parser Const := do
  match ty with
  | .AtomicType .TypeInteger => do
    let i ← parseInt
    pure (.Integer i)
  | .AtomicType .TypeBool => do
    let name ← parseIdent
    match name with
    | "True" => pure (.Bool true)
    | "False" => pure (.Bool false)
    | _ => throw s!"expected True or False, got {name}"
  | .AtomicType .TypeByteString => do
    let bs ← parseByteString
    pure (.ByteString bs)
  | .AtomicType .TypeString => do
    let s ← parseString
    pure (.String s)
  | .AtomicType .TypeUnit => do
    ws; expect '('; ws; expect ')'
    pure .Unit
  | .AtomicType .TypeData => do
    ws
    let c? ← peek?
    match c? with
    | some '0' =>
      -- BLS hex literals: 0x...
      let saved ← get
      discard next
      let c2? ← peek?
      if c2? == some 'x' || c2? == some 'X' then
        discard next
        let bs ← parseHexBytes
        pure (.ByteString bs)
      else
        set saved
        let d ← parseDataLit
        pure (.Data d)
    | some '[' =>
      -- Value literal: [{#policy: {#token: qty, ...}}, ...]
      -- Parse as Data (Map of Maps)
      let pairs ← parseValueLiteral
      pure (.Data (.Map pairs))
    | _ =>
      let d ← parseDataLit
      pure (.Data d)
  | .TypeOperator (.TypeList inner) => do
    ws; expect '['
    let mut items : List Const := []
    let mut done := false
    while !done do
      ws
      let c? ← peek?
      match c? with
      | some ']' => discard next; done := true
      | _ =>
        if c? == some ',' then discard next
        ws
        let item ← parseConstValue inner
        items := items ++ [item]
    -- Specialize for data lists
    match inner with
    | .AtomicType .TypeData =>
      let ds := items.filterMap fun
        | .Data d => some d
        | _ => none
      pure (.ConstDataList ds)
    | _ => pure (.ConstList items)
  | .TypeOperator (.TypePair t1 t2) => do
    ws; expect '('
    let v1 ← parseConstValue t1
    ws; expect ','
    let v2 ← parseConstValue t2
    ws; expect ')'
    -- Specialize for data pairs
    match t1, t2 with
    | .AtomicType .TypeData, .AtomicType .TypeData =>
      match v1, v2 with
      | .Data d1, .Data d2 => pure (.PairData (d1, d2))
      | _, _ => pure (.Pair (v1, v2))
    | _, _ => pure (.Pair (v1, v2))
  | .TypeOperator (.TypeArray inner) => do
    ws; expect '['
    let mut items : List Const := []
    let mut done := false
    while !done do
      ws
      let c? ← peek?
      match c? with
      | some ']' => discard next; done := true
      | _ =>
        if c? == some ',' then discard next
        ws
        let item ← parseConstValue inner
        items := items ++ [item]
    pure (.ConstArray items)
  | .AtomicType .TypeBls12_381_G1_element => do
    ws
    let c? ← peek?
    if c? == some '0' then
      let saved ← get
      discard next
      let c2? ← peek?
      if c2? == some 'x' || c2? == some 'X' then
        discard next
        let _bs ← parseHexBytes
        pure .Bls12_381_G1_element
      else
        set saved
        pure .Bls12_381_G1_element
    else pure .Bls12_381_G1_element
  | .AtomicType .TypeBls12_381_G2_element => do
    ws
    let c? ← peek?
    if c? == some '0' then
      let saved ← get
      discard next
      let c2? ← peek?
      if c2? == some 'x' || c2? == some 'X' then
        discard next
        let _bs ← parseHexBytes
        pure .Bls12_381_G2_element
      else
        set saved
        pure .Bls12_381_G2_element
    else pure .Bls12_381_G2_element
  | .AtomicType .TypeBls12_381_MlResult => do
    ws
    let c? ← peek?
    if c? == some '0' then
      let saved ← get
      discard next
      let c2? ← peek?
      if c2? == some 'x' || c2? == some 'X' then
        discard next
        let _bs ← parseHexBytes
        pure .Bls12_381_MlResult
      else
        set saved
        pure .Bls12_381_MlResult
    else pure .Bls12_381_MlResult

/-! ## Term Parsing -/

/-- Context for converting named variables to de Bruijn indices. -/
abbrev NameCtx := List String

private def lookupName (ctx : NameCtx) (name : String) : Option Nat :=
  go ctx 1
where
  go : List String → Nat → Option Nat
    | [], _ => none
    | x :: xs, n => if x == name then some n else go xs (n + 1)

partial def parseTerm (ctx : NameCtx) : Parser Term := do
  ws
  let c? ← peek?
  match c? with
  | none => throw "unexpected end of input"
  | some '(' => parseParen ctx
  | some '[' => parseApp ctx
  | _ => parseVarRef ctx
where
  parseParen (ctx : NameCtx) : Parser Term := do
    expect '('
    ws
    let kw ← parseIdent
    match kw with
    | "con" =>
      let ty ← parseType
      let val ← parseConstValue ty
      ws; expect ')'
      pure (.Constant (val, ty))
    | "lam" => do
      ws
      let name ← parseLamVar
      let body ← parseTerm (name :: ctx)
      ws; expect ')'
      pure (.Lam 0 body)
    | "builtin" => do
      let b ← parseBuiltinName
      ws; expect ')'
      pure (.Builtin b)
    | "force" => do
      let e ← parseTerm ctx
      ws; expect ')'
      pure (.Force e)
    | "delay" => do
      let e ← parseTerm ctx
      ws; expect ')'
      pure (.Delay e)
    | "constr" => do
      let tag ← parseNat
      let mut args : List Term := []
      let mut done := false
      while !done do
        ws
        let c? ← peek?
        match c? with
        | some ')' => discard next; done := true
        | _ =>
          let arg ← parseTerm ctx
          args := args ++ [arg]
      pure (.Constr tag args)
    | "case" => do
      let scrut ← parseTerm ctx
      let mut alts : List Term := []
      let mut done := false
      while !done do
        ws
        let c? ← peek?
        match c? with
        | some ')' => discard next; done := true
        | _ =>
          let alt ← parseTerm ctx
          alts := alts ++ [alt]
      pure (.Case scrut alts)
    | "error" => do
      ws; expect ')'
      pure .Error
    | "program" => throw "unexpected 'program' inside term"
    | other => throw s!"unknown keyword: {other}"

  parseApp (ctx : NameCtx) : Parser Term := do
    expect '['
    let fn ← parseTerm ctx
    let mut result := fn
    let mut done := false
    while !done do
      ws
      let c? ← peek?
      match c? with
      | some ']' => discard next; done := true
      | _ =>
        let arg ← parseTerm ctx
        result := .Apply result arg
    pure result

  parseVarRef (ctx : NameCtx) : Parser Term := do
    let name ← parseLamVar
    match lookupName ctx name with
    | some idx => pure (.Var idx)
    | none => pure (.Var 0)

  parseLamVar : Parser String := do
    ws
    let s ← get
    let start := s.pos
    let mut done := false
    while !done do
      let c? ← peek?
      match c? with
      | some c =>
        if isIdentChar c || c == '.' then discard next
        else done := true
      | none => done := true
    let s' ← get
    let ident := s.input.extract start s'.pos
    if ident.isEmpty then throw "expected variable name"
    pure ident

/-! ## Program Parsing -/

def parseVersion : Parser (Nat × Nat × Nat) := do
  let major ← parseNat
  ws; expect '.'
  let minor ← parseNat
  ws; expect '.'
  let patch ← parseNat
  pure (major, minor, patch)

def parseProgram : Parser (Nat × Nat × Nat × Term) := do
  ws; expect '('
  ws
  let kw ← parseIdent
  if kw != "program" then throw s!"expected 'program', got '{kw}'"
  let ver ← parseVersion
  let term ← parseTerm []
  ws; expect ')'
  ws
  pure (ver.1, ver.2.1, ver.2.2, term)

/-! ## Runner -/

def runParser (p : Parser α) (input : String) : Except String α :=
  match p { input := input, pos := ⟨0⟩ } with
  | .ok a _ => .ok a
  | .error e _ => .error e

/-! ## Expected Output Parsing -/

inductive ExpectedResult where
  | parseError : ExpectedResult
  | evalFailure : ExpectedResult
  | success : Term → ExpectedResult
deriving Repr

def parseExpected (input : String) : Except String ExpectedResult := do
  let trimmed := input.trim
  if trimmed == "parse error" then return .parseError
  if trimmed == "evaluation failure" then return .evalFailure
  match runParser parseProgram trimmed with
  | .ok (_, _, _, term) => return .success term
  | .error e => throw s!"failed to parse expected output: {e}"

def parseUplcProgram (input : String) : Except String Term :=
  match runParser parseProgram input with
  | .ok (_, _, _, term) => .ok term
  | .error e => .error e

end Moist.CEK.UplcParser
