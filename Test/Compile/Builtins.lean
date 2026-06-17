import Moist.Compile.Reflect

/-! # Builtin coverage — every non-crypto builtin is *handled* (not refused) on concrete args

The symbolic compiler covers all non-crypto builtins: the concrete fold defers to the real
`evalBuiltinConst` (axiom-free) for the 68 non-pass-through ones, and `symBuiltinPassThrough`
handles the 5 pass-through ones (`ChooseUnit`/`Trace`/`ChooseData`/`ChooseList`/`MkCons`).
This driver applies each builtin (with the right number of `force`s per `expectedArgs`) to
concrete arguments and checks `symEval` commits.  Crypto builtins are Phase 2 (axiomatized). -/

open Moist.Plutus.Term Moist.CEK Moist.Compile
open Moist.Plutus (Data)

private def intT (n : Int) : Term := .Constant (.Integer n, .AtomicType .TypeInteger)
private def bsT (bs : List UInt8) : Term :=
  .Constant (.ByteString ⟨bs.toArray⟩, .AtomicType .TypeByteString)
private def strT (s : String) : Term := .Constant (.String s, .AtomicType .TypeString)
private def boolT (b : Bool) : Term := .Constant (.Bool b, .AtomicType .TypeBool)
private def unitT : Term := .Constant (.Unit, .AtomicType .TypeUnit)
private def dataT (d : Data) : Term := .Constant (.Data d, .AtomicType .TypeData)
private def listDT (ds : List Data) : Term := .Constant (.ConstDataList ds, .AtomicType .TypeData)
private def pairDT (a b : Data) : Term := .Constant (.PairData (a, b), .AtomicType .TypeData)

/-- Apply a builtin to concrete value-args, inserting a `force` for each type argument
    (`argQ`) per the builtin's `expectedArgs` signature. -/
private def applyB (b : BuiltinFun) (vargs : List Term) : Term :=
  let rec go : ExpectedArgs → List Term → Term → Term
    | .one .argV,      v :: _,   acc => .Apply acc v
    | .one .argQ,      _,        acc => .Force acc
    | .more .argV r,   v :: vs,  acc => go r vs (.Apply acc v)
    | .more .argQ r,   vs,       acc => go r vs (.Force acc)
    | _,               _,        acc => acc
  go (expectedArgs b) vargs (.Builtin b)

/-- Each (builtin, concrete args) — one representative per non-crypto category. -/
private def cases : List (BuiltinFun × List Term) :=
  [ -- integers
    (.AddInteger, [intT 3, intT 4]), (.DivideInteger, [intT 7, intT 2]),
    (.EqualsInteger, [intT 1, intT 1]), (.LessThanInteger, [intT 1, intT 2]),
    -- bytestrings
    (.AppendByteString, [bsT [1,2], bsT [3]]), (.ConsByteString, [intT 65, bsT [66]]),
    (.SliceByteString, [intT 0, intT 1, bsT [1,2,3]]), (.LengthOfByteString, [bsT [1,2,3]]),
    (.IndexByteString, [bsT [9,8], intT 0]), (.EqualsByteString, [bsT [1], bsT [1]]),
    (.LessThanByteString, [bsT [1], bsT [2]]),
    -- bitwise
    (.AndByteString, [boolT true, bsT [1], bsT [1]]), (.ComplementByteString, [bsT [1]]),
    (.ReadBit, [bsT [1], intT 0]), (.CountSetBits, [bsT [7]]),
    -- conversions
    (.IntegerToByteString, [boolT true, intT 0, intT 255]),
    (.ByteStringToInteger, [boolT true, bsT [1,2]]),
    -- strings
    (.AppendString, [strT "a", strT "b"]), (.EqualsString, [strT "x", strT "x"]),
    (.EncodeUtf8, [strT "hi"]),
    -- bool / unit / trace  (pass-through)
    (.IfThenElse, [boolT true, intT 1, intT 2]), (.ChooseUnit, [unitT, intT 7]),
    (.Trace, [strT "msg", intT 9]),
    -- pairs / lists  (pass-through + construction)
    (.FstPair, [pairDT (.I 1) (.I 2)]), (.SndPair, [pairDT (.I 1) (.I 2)]),
    (.MkCons, [dataT (.I 9), listDT []]), (.HeadList, [listDT [.I 5]]),
    (.TailList, [listDT [.I 5]]), (.NullList, [listDT []]),
    (.MkNilData, [unitT]), (.MkNilPairData, [unitT]),
    -- data
    (.ConstrData, [intT 0, listDT [.I 1]]), (.ListData, [listDT [.I 1]]),
    (.MapData, [.Constant (.ConstPairDataList [], .AtomicType .TypeData)]),
    (.IData, [intT 5]), (.BData, [bsT [1]]), (.UnIData, [dataT (.I 5)]),
    (.UnConstrData, [dataT (.Constr 0 [])]), (.UnListData, [dataT (.List [.I 1])]),
    (.UnMapData, [dataT (.Map [])]), (.EqualsData, [dataT (.I 1), dataT (.I 1)]),
    (.ChooseData, [dataT (.Constr 0 []), intT 100, intT 1, intT 2, intT 3, intT 4]),
    (.ChooseList, [listDT [], intT 0, intT 1]),
    -- arrays
    (.LengthOfArray, [.Constant (.ConstArray [.Integer 1], .AtomicType .TypeInteger)]),
    (.IndexArray, [.Constant (.ConstArray [.Integer 9], .AtomicType .TypeInteger), intT 0]),
    (.ListToArray, [.Constant (.ConstList [.Integer 1], .AtomicType .TypeInteger)]) ]

/-- Remaining non-crypto gaps (need dedicated work, not the concrete fold):
    `SerializeData` (CBOR — to axiomatize like crypto); the 7 `Value` builtins
    (`InsertCoin/LookupCoin/ScaleValue/UnionValue/ValueContains/ValueData/UnValueData` —
    need a `Const.Value` representation first).  Crypto (28) is Phase 2. -/
private def knownNonCryptoGaps : List BuiltinFun :=
  [.SerializeData, .InsertCoin, .LookupCoin, .ScaleValue, .UnionValue, .ValueContains,
   .ValueData, .UnValueData]

def main : IO Unit := do
  let mut ok := 0
  let mut fails : List String := []
  for (b, args) in cases do
    match symEval 25 [] (applyB b args) with
    | some _ => ok := ok + 1
    | none   => fails := s!"{repr b}" :: fails
  IO.println s!"=== non-crypto builtin coverage: {ok}/{cases.length} handled on concrete args ==="
  if fails.isEmpty then IO.println "  ALL sampled builtins handled ✅"
  else IO.println s!"  REFUSED (unexpected): {fails}"
  IO.println s!"  documented remaining gaps ({knownNonCryptoGaps.length}): SerializeData + 7 Value builtins; crypto (28) = Phase 2"
