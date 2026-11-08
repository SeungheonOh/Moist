import Test.MIR.FuzzReal.Gen

/-! # Probes of the machine semantics the optimizer relies on

Closed programs exercising `case` on builtin values (integers, Booleans,
unit, lists, pairs, Data), constructor cases with mismatched arities, list
and pair builtins on values of the wrong element type, and partial and over-
saturated builtin applications. They run like generated programs: every
optimizer variant against the unoptimized lowering on the real machine, and
the Lean model against the real machine. -/

namespace Test.MIR.FuzzReal.Probes

open Moist.MIR
open Moist.Plutus (Data)
open Moist.Plutus.Term
open Test.MIR.FuzzReal

private def v (n : Nat) : VarId := { uid := 90000 + n, origin := .source, hint := "q" }

def intListT : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeInteger))
def boolListT : BuiltinType := .TypeOperator (.TypeList (.AtomicType .TypeBool))
def pairT : BuiltinType := .TypeOperator (.TypePair (.AtomicType .TypeData) (.AtomicType .TypeData))
def pairIntBoolT : BuiltinType :=
  .TypeOperator (.TypePair (.AtomicType .TypeInteger) (.AtomicType .TypeBool))

def intList (xs : List Int) : Expr := lit (.ConstList (.AtomicType .TypeInteger) (xs.map .Integer)) intListT
def results (n : Nat) : List Expr := (List.range n).map fun k => intE (Int.ofNat (10 + k))

/-- An alternative taking `arity` arguments and returning them in a constructor. -/
def taking (arity : Nat) (tag : Nat) : Expr :=
  let names := (List.range arity).map fun k => v (tag * 10 + k)
  names.foldr .Lam (.Constr tag (names.map .Var))

def scrutinees : List (String × Expr) :=
  [("int-1", intE (-1)), ("int0", intE 0), ("int1", intE 1), ("int2", intE 2), ("int3", intE 3),
   ("false", boolE false), ("true", boolE true), ("unit", unitE),
   ("nil", intList []), ("list1", intList [7]), ("list2", intList [7, 8]),
   ("datalist-nil", dataListE []), ("datalist1", dataListE [.I 5]),
   ("pairdata", pairDataE (.I 1, .B ⟨#[2]⟩)),
   ("pair-int-bool", lit (.Pair (.Integer 1, .Bool true)) pairIntBoolT),
   ("data", dataE (.Constr 0 [])), ("bytes", bytesE ⟨#[1]⟩),
   ("constr0-0", .Constr 0 []), ("constr1-0", .Constr 1 []), ("constr0-2", .Constr 0 [intE 1, intE 2]),
   ("constr2-1", .Constr 2 [intE 1])]

def alternativeSets : List (String × List Expr) :=
  [("none", []), ("plain1", results 1), ("plain2", results 2), ("plain3", results 3),
   ("lam1", [taking 1 0]), ("lam2", [taking 2 0]), ("lam2-plain", [taking 2 0, intE 99]),
   ("plain-lam2", [intE 99, taking 2 1]), ("lam1-lam1", [taking 1 0, taking 1 1]),
   ("lam0-lam2-lam1", [taking 0 0, taking 2 1, taking 1 2])]

def caseProbes : List (String × Expr) :=
  scrutinees.flatMap fun (sName, s) =>
    alternativeSets.map fun (aName, alts) => (s!"case/{sName}/{aName}", Expr.Case s alts)

def builtinProbes : List (String × Expr) :=
  [("mkcons/int-on-intlist", consE (intE 1) (intList [2])),
   ("mkcons/int-on-intnil", consE (intE 1) (intList [])),
   ("mkcons/bool-on-intlist", consE (boolE true) (intList [2])),
   ("mkcons/bool-on-intnil", consE (boolE true) (intList [])),
   ("mkcons/data-on-intnil", consE (dataE (.I 1)) (intList [])),
   ("mkcons/int-on-datanil", consE (intE 1) (dataListE [])),
   ("mkcons/data-on-datanil", consE (dataE (.I 1)) (dataListE [])),
   ("mkcons/pair-on-pairnil", consE (pairDataE (.I 1, .I 2)) (pairListE [])),
   ("mkcons/data-on-pairnil", consE (dataE (.I 1))
      (pairListE [])),
   ("mkcons/int-on-boolnil", consE (intE 1) (lit (.ConstList (.AtomicType .TypeBool) []) boolListT)),
   ("head/intnil", headE (intList [])), ("tail/intnil", tailE (intList [])),
   ("null/int", nullE (intE 0)), ("head/data", headE (dataE (.List [.I 1]))),
   ("fst/pair-int-bool", fstE (lit (.Pair (.Integer 1, .Bool true)) pairIntBoolT)),
   ("snd/pair-int-bool", sndE (lit (.Pair (.Integer 1, .Bool true)) pairIntBoolT)),
   ("equalsData/list", app2 .EqualsData (dataE (.I 1)) (dataListE [])),
   ("listData/intlist", app1 .ListData (intList [1])),
   ("mapData/datalist", app1 .MapData (dataListE [.I 1])),
   ("unconstr/I", app1 .UnConstrData (dataE (.I 1))),
   ("chooseList/int", .Force (apps (.Force (.Force (.Builtin .ChooseList))) [intE 1, .Delay (intE 1), .Delay (intE 2)])),
   ("ifThenElse/int", apps (.Force (.Builtin .IfThenElse)) [intE 1, intE 1, intE 2]),
   ("ifThenElse/unforced", apps (.Builtin .IfThenElse) [boolE true, intE 1, intE 2]),
   ("add/forced", .Force (.Builtin .AddInteger)),
   ("add/over", apps (.Builtin .AddInteger) [intE 1, intE 2, intE 3]),
   ("add/partial-forced", .Force (.App (.Builtin .AddInteger) (intE 1))),
   ("trace/over", apps (.Force (.Builtin .Trace)) [stringE "m", .Lam (v 1) (.Var (v 1)), intE 5]),
   ("headList/twice-forced", .App (.Force (.Force (.Builtin .HeadList))) (intList [1])),
   ("fstPair/once-forced", .App (.Force (.Builtin .FstPair)) (pairDataE (.I 1, .I 2))),
   ("apply/constant", .App (intE 1) (intE 2)), ("force/constant", .Force (intE 1)),
   ("force/lam", .Force (.Lam (v 2) (intE 1))), ("apply/delay", .App (.Delay (intE 1)) (intE 2)),
   ("apply/constr", .App (.Constr 0 []) (intE 1)), ("force/constr", .Force (.Constr 0 [])),
   ("divide/zero", app2 .DivideInteger (intE 1) (intE 0)),
   ("constr/error-field-unused", .Case (.Constr 1 [.Error]) [intE 1, intE 2]),
   ("let/unused-error", .Let [(v 3, .Error, false)] (intE 1)),
   ("let/unused-delay-error", .Let [(v 4, .Delay .Error, false)] (intE 1))]

def bs (bytes : List Nat) : Expr := bytesE ⟨(bytes.map (·.toUInt8)).toArray⟩
def rep (n : Nat) (b : Nat) : Expr := bs (List.replicate n b)
def g1Of (msg : Nat) : Expr := app2 .Bls12_381_G1_hashToGroup (bs [msg]) dstE
def g2Of (msg : Nat) : Expr := app2 .Bls12_381_G2_hashToGroup (bs [msg]) dstE
def valueE (entries : List (List Nat × List (List Nat × Int))) : Expr :=
  lit (.Value (entries.map fun (c, ts) => (⟨(c.map (·.toUInt8)).toArray⟩,
    ts.map fun (t, q) => (⟨(t.map (·.toUInt8)).toArray⟩, q)))) valueType
def insertCoin (c t : Expr) (q : Int) (v : Expr) : Expr := apps (.Builtin .InsertCoin) [c, t, intE q, v]

def cryptoProbes : List (String × Expr) :=
  [("sha2/empty", app1 .Sha2_256 (bs [])), ("sha3/abc", app1 .Sha3_256 (bs [97, 98, 99])),
   ("blake2b256/1", app1 .Blake2b_256 (bs [1])), ("blake2b224/1", app1 .Blake2b_224 (bs [1])),
   ("keccak/empty", app1 .Keccak_256 (bs [])), ("ripemd/abc", app1 .Ripemd_160 (bs [97, 98, 99])),
   ("ed25519/short-key", apps (.Builtin .VerifyEd25519Signature) [rep 31 1, bs [1], rep 64 2]),
   ("ed25519/short-sig", apps (.Builtin .VerifyEd25519Signature) [rep 32 1, bs [1], rep 63 2]),
   ("ed25519/random", apps (.Builtin .VerifyEd25519Signature) [rep 32 1, bs [1], rep 64 2]),
   ("ecdsa/short-key", apps (.Builtin .VerifyEcdsaSecp256k1Signature) [rep 32 2, rep 32 1, rep 64 1]),
   ("ecdsa/invalid-key", apps (.Builtin .VerifyEcdsaSecp256k1Signature) [rep 33 2, rep 32 1, rep 64 1]),
   ("ecdsa/short-msg", apps (.Builtin .VerifyEcdsaSecp256k1Signature) [rep 33 2, rep 31 1, rep 64 1]),
   ("schnorr/invalid-key", apps (.Builtin .VerifySchnorrSecp256k1Signature) [rep 32 0xff, bs [1], rep 64 1]),
   ("schnorr/short-sig", apps (.Builtin .VerifySchnorrSecp256k1Signature) [rep 32 1, bs [1], rep 63 1]),
   ("g1/compress-hash", app1 .Bls12_381_G1_compress (g1Of 1)),
   ("g1/roundtrip", app2 .Bls12_381_G1_equal (app1 .Bls12_381_G1_uncompress (app1 .Bls12_381_G1_compress (g1Of 1))) (g1Of 1)),
   ("g1/uncompress-zero", app1 .Bls12_381_G1_uncompress (rep 48 0)),
   ("g1/uncompress-infinity", app1 .Bls12_381_G1_compress (app1 .Bls12_381_G1_uncompress (bs (0xc0 :: List.replicate 47 0)))),
   ("g1/uncompress-short", app1 .Bls12_381_G1_uncompress (rep 47 0)),
   ("g1/add-neg", app1 .Bls12_381_G1_compress (app2 .Bls12_381_G1_add (g1Of 2) (app1 .Bls12_381_G1_neg (g1Of 2)))),
   ("g1/scalar0", app1 .Bls12_381_G1_compress (app2 .Bls12_381_G1_scalarMul (intE 0) (g1Of 3))),
   ("g1/scalar-neg", app2 .Bls12_381_G1_equal (app2 .Bls12_381_G1_scalarMul (intE (-1)) (g1Of 3)) (app1 .Bls12_381_G1_neg (g1Of 3))),
   ("g1/scalar-big", app1 .Bls12_381_G1_compress (app2 .Bls12_381_G1_scalarMul (intE (2 ^ 300)) (g1Of 3))),
   ("g1/equal-distinct", app2 .Bls12_381_G1_equal (g1Of 1) (g1Of 2)),
   ("g1/dst-too-long", app1 .Bls12_381_G1_compress (app2 .Bls12_381_G1_hashToGroup (bs [1]) (rep 256 1))),
   ("g1/dst-empty", app1 .Bls12_381_G1_compress (app2 .Bls12_381_G1_hashToGroup (bs [1]) (bs []))),
   ("g2/compress-hash", app1 .Bls12_381_G2_compress (g2Of 1)),
   ("g2/roundtrip", app2 .Bls12_381_G2_equal (app1 .Bls12_381_G2_uncompress (app1 .Bls12_381_G2_compress (g2Of 1))) (g2Of 1)),
   ("g2/uncompress-zero", app1 .Bls12_381_G2_uncompress (rep 96 0)),
   ("g2/add-neg", app1 .Bls12_381_G2_compress (app2 .Bls12_381_G2_add (g2Of 2) (app1 .Bls12_381_G2_neg (g2Of 2)))),
   ("g2/scalar7", app1 .Bls12_381_G2_compress (app2 .Bls12_381_G2_scalarMul (intE 7) (g2Of 3))),
   ("pairing/bilinear", app2 .Bls12_381_finalVerify
      (app2 .Bls12_381_millerLoop (app2 .Bls12_381_G1_scalarMul (intE 5) (g1Of 1)) (g2Of 1))
      (app2 .Bls12_381_millerLoop (g1Of 1) (app2 .Bls12_381_G2_scalarMul (intE 5) (g2Of 1)))),
   ("pairing/unequal", app2 .Bls12_381_finalVerify
      (app2 .Bls12_381_millerLoop (g1Of 1) (g2Of 1)) (app2 .Bls12_381_millerLoop (g1Of 2) (g2Of 1))),
   ("pairing/mul", app2 .Bls12_381_finalVerify
      (app2 .Bls12_381_mulMlResult (app2 .Bls12_381_millerLoop (g1Of 1) (g2Of 1)) (app2 .Bls12_381_millerLoop (g1Of 1) (g2Of 1)))
      (app2 .Bls12_381_millerLoop (app2 .Bls12_381_G1_scalarMul (intE 2) (g1Of 1)) (g2Of 1))),
   ("value/insert", insertCoin (bs [1]) (bs [0xaa]) 5 (valueE [])),
   ("value/insert-zero-removes", insertCoin (bs [1]) (bs []) 0 (valueE [([1], [([], 5)])])),
   ("value/insert-long-key", insertCoin (rep 33 1) (bs []) 5 (valueE [])),
   ("value/insert-long-token", insertCoin (bs [1]) (rep 33 1) 5 (valueE [])),
   ("value/insert-zero-long-key", insertCoin (rep 33 1) (bs []) 0 (valueE [])),
   ("value/insert-overflow", insertCoin (bs [1]) (bs []) (2 ^ 127) (valueE [])),
   ("value/insert-min", insertCoin (bs [1]) (bs []) (-(2 ^ 127)) (valueE [])),
   ("value/lookup", apps (.Builtin .LookupCoin) [bs [1], bs [0xaa], valueE [([1], [([0xaa], 9)])]]),
   ("value/lookup-missing", apps (.Builtin .LookupCoin) [bs [2], bs [], valueE [([1], [([0xaa], 9)])]]),
   ("value/union", app2 .UnionValue (valueE [([1], [([], 5)])]) (valueE [([1], [([], -5)]), ([2], [([], 1)])])),
   ("value/union-overflow", app2 .UnionValue (valueE [([1], [([], 2 ^ 126)])]) (valueE [([1], [([], 2 ^ 126)])])),
   ("value/contains", app2 .ValueContains (valueE [([1], [([], 5)]), ([2], [([], 1)])]) (valueE [([1], [([], 3)])])),
   ("value/contains-neg", app2 .ValueContains (valueE [([1], [([], 5)])]) (valueE [([1], [([], -3)])])),
   ("value/contains-neg-left", app2 .ValueContains (valueE [([1], [([], -5)])]) (valueE [])),
   ("value/scale0", app2 .ScaleValue (intE 0) (valueE [([1], [([], 5)])])),
   ("value/scale-neg", app2 .ScaleValue (intE (-2)) (valueE [([1], [([], 5)])])),
   ("value/scale-overflow", app2 .ScaleValue (intE (2 ^ 126)) (valueE [([1], [([], 5)])])),
   ("value/data", app1 .ValueData (valueE [([1], [([0xaa], 5), ([0xbb], -1)])])),
   ("value/roundtrip", app1 .UnValueData (app1 .ValueData (valueE [([1], [([0xaa], 5)])]))),
   ("value/undata-unsorted", app1 .UnValueData (dataE (.Map [(.B ⟨#[2]⟩, .Map [(.B ⟨#[]⟩, .I 1)]), (.B ⟨#[1]⟩, .Map [(.B ⟨#[]⟩, .I 1)])]))),
   ("value/undata-zero", app1 .UnValueData (dataE (.Map [(.B ⟨#[1]⟩, .Map [(.B ⟨#[]⟩, .I 0)])]))),
   ("value/undata-empty-inner", app1 .UnValueData (dataE (.Map [(.B ⟨#[1]⟩, .Map [])]))),
   ("value/undata-int", app1 .UnValueData (dataE (.I 1))),
   ("value/equalsData", app2 .EqualsData (app1 .ValueData (valueE [([1], [([], 1)])])) (dataE (.Map [(.B ⟨#[1]⟩, .Map [(.B ⟨#[]⟩, .I 1)])]))),
   ("i2b/width-small", apps (.Builtin .IntegerToByteString) [boolE true, intE 1, intE 256]),
   ("i2b/negative", apps (.Builtin .IntegerToByteString) [boolE true, intE 0, intE (-1)]),
   ("i2b/little", apps (.Builtin .IntegerToByteString) [boolE false, intE 4, intE 258]),
   ("b2i/little", app2 .ByteStringToInteger (boolE false) (bs [1, 2])),
   ("expmod/inverse", apps (.Builtin .ExpModInteger) [intE 3, intE (-1), intE 7]),
   ("expmod/no-inverse", apps (.Builtin .ExpModInteger) [intE 2, intE (-1), intE 4]),
   ("expmod/mod0", apps (.Builtin .ExpModInteger) [intE 2, intE 3, intE 0])]

/-- Programs over one argument whose results depend on the variant-E bounds,
    in the shapes the optimizer rewrites (identities, comparisons of a value
    with itself, round trips, constant folding), each applied to values inside
    and outside the bounds. -/
def boundPrograms : List (String × Expr) :=
  let x := v 50
  let fx (body : Expr) := Expr.Lam x body
  let X := Expr.Var x
  [("add0", fx (app2 .AddInteger X (intE 0))), ("add0-left", fx (app2 .AddInteger (intE 0) X)),
   ("sub0", fx (app2 .SubtractInteger X (intE 0))), ("mul1", fx (app2 .MultiplyInteger X (intE 1))),
   ("mul0", fx (app2 .MultiplyInteger X (intE 0))), ("div1", fx (app2 .DivideInteger X (intE 1))),
   ("quot1", fx (app2 .QuotientInteger X (intE 1))), ("mod1", fx (app2 .ModInteger X (intE 1))),
   ("eq-self", fx (app2 .EqualsInteger X X)), ("le-self", fx (app2 .LessThanEqualsInteger X X)),
   ("lt-self", fx (app2 .LessThanInteger X X)),
   ("idata-roundtrip", fx (app1 .UnIData (app1 .IData X))),
   ("idata-eq", fx (app2 .EqualsData (app1 .IData X) (app1 .IData X))),
   ("add-then-sub", fx (app2 .SubtractInteger (app2 .AddInteger X (intE 1)) (intE 1))),
   ("tag-chain", fx (iteCase (app2 .EqualsInteger X (intE 0)) (intE 10)
      (iteCase (app2 .EqualsInteger X (intE 1)) (intE 11) (iteCase (app2 .EqualsInteger X (intE 2)) (intE 12) .Error)))),
   ("range-chain", fx (iteCase (app2 .EqualsInteger X (intE 0)) .Error
      (iteCase (app2 .EqualsInteger X (intE 1)) .Error (iteCase (app2 .EqualsInteger X (intE 2)) .Error (intE 7))))),
   ("let-unused-add", fx (.Let [(v 51, app2 .AddInteger X (intE 1), false)] (intE 3))),
   ("let-unused-eq", fx (.Let [(v 52, app2 .EqualsInteger X (intE 1), false)] (intE 3))),
   ("i2b", fx (apps (.Builtin .IntegerToByteString) [boolE true, intE 0, X]))]

def boundBytesPrograms : List (String × Expr) :=
  let x := v 60
  let fx (body : Expr) := Expr.Lam x body
  let X := Expr.Var x
  [("eqbs-self", fx (app2 .EqualsByteString X X)), ("append-empty", fx (app2 .AppendByteString X (bs []))),
   ("append-empty-left", fx (app2 .AppendByteString (bs []) X)),
   ("length", fx (app1 .LengthOfByteString X)), ("length-append", fx (app1 .LengthOfByteString (app2 .AppendByteString X X))),
   ("bdata-roundtrip", fx (app1 .UnBData (app1 .BData X))),
   ("bdata-eq", fx (app2 .EqualsData (app1 .BData X) (app1 .BData X))),
   ("ltbs-self", fx (app2 .LessThanByteString X X)), ("lebs-self", fx (app2 .LessThanEqualsByteString X X)),
   ("let-unused-length", fx (.Let [(v 61, app1 .LengthOfByteString X, false)] (intE 3))),
   ("slice-all", fx (apps (.Builtin .SliceByteString) [intE 0, intE 100000, X])),
   ("sha2", fx (app1 .Sha2_256 X)), ("index0", fx (app2 .IndexByteString X (intE 0)))]

/-- A map lookup comparing keys with `equalsData` (the shape the guarded key
    comparison rewrites), on B keys of the lengths it distinguishes and on
    non-B keys, with the searched key as the second argument. -/
def keyLookup : Expr :=
  let m := v 70
  let k := v 71
  let go := v 72
  let ps := v 73
  let h := v 74
  let t := v 75
  let kb := v 76
  let body := Expr.Case (nullE (.Var ps))
    [lets [(h, headE (.Var ps)), (t, tailE (.Var ps))]
      (iteDelay (app2 .EqualsData (fstE (.Var h)) (.Var k)) (sndE (.Var h)) (.App (.Var go) (.Var t))),
     .Error]
  .Lam m (.Lam k (lets [(kb, app1 .UnBData (.Var k))]
    (.App (.Fix go (.Lam ps body)) (app1 .UnMapData (.Var m)))))

def keyLookupUnguarded : Expr :=
  let m := v 80
  let k := v 81
  let go := v 82
  let ps := v 83
  let h := v 84
  let t := v 85
  let body := Expr.Case (nullE (.Var ps))
    [lets [(h, headE (.Var ps)), (t, tailE (.Var ps))]
      (iteDelay (app2 .EqualsData (fstE (.Var h)) (.Var k)) (sndE (.Var h)) (.App (.Var go) (.Var t))),
     .Error]
  .Lam m (.Lam k (.App (.Fix go (.Lam ps body)) (app1 .UnMapData (.Var m))))

def keyLengths : List Nat := [0, 1, 63, 64, 65, 65536, 65537]

def keyOf (n : Nat) (last : Nat) : Data :=
  .B ⟨((List.replicate (n - 1) (0xaa : UInt8)) ++ (if n == 0 then [] else [last.toUInt8])).toArray⟩

def keyArguments : List (List Expr) :=
  let keys := keyLengths.map (keyOf · 1) ++ [Data.I 1, .Constr 0 [], .List []]
  let entries := (keyLengths.map fun n => (keyOf n 1, Data.I (Int.ofNat n))) ++ [(.I 1, .I 99)]
  let maps := [Data.Map entries, .Map (entries.reverse), .Map [(keyOf 64 2, .I 0)], .Map []]
  maps.flatMap fun mp => (keys ++ [keyOf 64 2, keyOf 65 2]).map fun key => [dataE mp, dataE key]

def boundIntArguments : List Int := [0, 1, 2] ++ hugeInts
def boundBytesArguments : List Nat := [0, 1, 65535, 65536, 65537]

def boundArguments : List (String × Expr × List Expr) :=
  (boundPrograms.map fun (name, p) => (s!"bound/int/{name}", p, boundIntArguments.map intE)) ++
  (boundBytesPrograms.map fun (name, p) => (s!"bound/bytes/{name}", p,
    boundBytesArguments.map fun n => rep n 7))

def keyPrograms : List (String × Expr × List (List Expr)) :=
  [("keys/guarded-bytes", keyLookup, keyArguments), ("keys/equalsData", keyLookupUnguarded, keyArguments)]

def all : List (String × Expr) := caseProbes ++ builtinProbes ++ cryptoProbes ++
  [("bound/literal/add-max", app2 .AddInteger (intE (hugeInts[0]!)) (intE 1)),
   ("bound/literal/add-max-plus1", app2 .AddInteger (intE (hugeInts[1]!)) (intE 0)),
   ("bound/literal/mul-square", app2 .MultiplyInteger (intE (hugeInts[4]!)) (intE (hugeInts[4]!))),
   ("bound/literal/mul-square-then-add", app2 .AddInteger (app2 .MultiplyInteger (intE (hugeInts[4]!)) (intE (hugeInts[4]!))) (intE 0)),
   ("bound/literal/eq-max-plus1-self", app2 .EqualsInteger (intE (hugeInts[1]!)) (intE (hugeInts[1]!))),
   ("bound/literal/append-long", app1 .LengthOfByteString (app2 .AppendByteString (rep 40000 1) (rep 40000 2))),
   ("bound/literal/append-long-eq", app2 .EqualsByteString (app2 .AppendByteString (rep 40000 1) (rep 40000 2)) (bs [])),
   ("bound/literal/eq-long", app2 .EqualsByteString (rep 65537 1) (rep 65537 1)),
   ("bound/literal/length-long", app1 .LengthOfByteString (rep 65537 1)),
   ("bound/literal/replicate", apps (.Builtin .ReplicateByte) [intE 8193, intE 0])]

end Test.MIR.FuzzReal.Probes
