import Moist.SMT.Soundness.SolverBoundary

namespace Test.SMT.SupportedQueries

open Moist.Plutus.Term
open Moist.SMT.UPLC
open Moist.SMT.UPLC.Soundness

/-! Constructor-complete coverage for the checked production-query boundary. -/

def allBuiltins : List BuiltinFun :=
  [ .AddInteger
  , .SubtractInteger
  , .MultiplyInteger
  , .DivideInteger
  , .QuotientInteger
  , .RemainderInteger
  , .ModInteger
  , .EqualsInteger
  , .LessThanInteger
  , .LessThanEqualsInteger
  , .AppendByteString
  , .ConsByteString
  , .SliceByteString
  , .LengthOfByteString
  , .IndexByteString
  , .EqualsByteString
  , .LessThanByteString
  , .LessThanEqualsByteString
  , .Sha2_256
  , .Sha3_256
  , .Blake2b_256
  , .VerifyEd25519Signature
  , .AppendString
  , .EqualsString
  , .EncodeUtf8
  , .DecodeUtf8
  , .IfThenElse
  , .ChooseUnit
  , .Trace
  , .FstPair
  , .SndPair
  , .ChooseList
  , .MkCons
  , .HeadList
  , .TailList
  , .NullList
  , .ChooseData
  , .ConstrData
  , .MapData
  , .ListData
  , .IData
  , .BData
  , .UnConstrData
  , .UnMapData
  , .UnListData
  , .UnIData
  , .UnBData
  , .EqualsData
  , .MkPairData
  , .MkNilData
  , .MkNilPairData
  , .SerializeData
  , .VerifyEcdsaSecp256k1Signature
  , .VerifySchnorrSecp256k1Signature
  , .Bls12_381_G1_add
  , .Bls12_381_G1_neg
  , .Bls12_381_G1_scalarMul
  , .Bls12_381_G1_equal
  , .Bls12_381_G1_hashToGroup
  , .Bls12_381_G1_compress
  , .Bls12_381_G1_uncompress
  , .Bls12_381_G2_add
  , .Bls12_381_G2_neg
  , .Bls12_381_G2_scalarMul
  , .Bls12_381_G2_equal
  , .Bls12_381_G2_hashToGroup
  , .Bls12_381_G2_compress
  , .Bls12_381_G2_uncompress
  , .Bls12_381_millerLoop
  , .Bls12_381_mulMlResult
  , .Bls12_381_finalVerify
  , .Keccak_256
  , .Blake2b_224
  , .IntegerToByteString
  , .ByteStringToInteger
  , .AndByteString
  , .OrByteString
  , .XorByteString
  , .ComplementByteString
  , .ReadBit
  , .WriteBits
  , .ReplicateByte
  , .ShiftByteString
  , .RotateByteString
  , .CountSetBits
  , .FindFirstSetBit
  , .Ripemd_160
  , .ExpModInteger
  , .DropList
  , .IndexArray
  , .LengthOfArray
  , .ListToArray
  , .InsertCoin
  , .LookupCoin
  , .ScaleValue
  , .UnionValue
  , .ValueContains
  , .ValueData
  , .UnValueData
  , .Bls12_381_G1_multiScalarMul
  , .Bls12_381_G2_multiScalarMul
  ]

theorem allBuiltins_complete (builtin : BuiltinFun) :
    builtin ∈ allBuiltins := by
  cases builtin <;> simp [allBuiltins]

/-- Exactly the builtin families intentionally outside the non-cryptographic
model.  The conversion and arithmetic builtins are deliberately absent. -/
def cryptoBuiltins : List BuiltinFun :=
  [ .Sha2_256
  , .Sha3_256
  , .Blake2b_256
  , .VerifyEd25519Signature
  , .VerifyEcdsaSecp256k1Signature
  , .VerifySchnorrSecp256k1Signature
  , .Bls12_381_G1_add
  , .Bls12_381_G1_neg
  , .Bls12_381_G1_scalarMul
  , .Bls12_381_G1_equal
  , .Bls12_381_G1_hashToGroup
  , .Bls12_381_G1_compress
  , .Bls12_381_G1_uncompress
  , .Bls12_381_G2_add
  , .Bls12_381_G2_neg
  , .Bls12_381_G2_scalarMul
  , .Bls12_381_G2_equal
  , .Bls12_381_G2_hashToGroup
  , .Bls12_381_G2_compress
  , .Bls12_381_G2_uncompress
  , .Bls12_381_millerLoop
  , .Bls12_381_mulMlResult
  , .Bls12_381_finalVerify
  , .Keccak_256
  , .Blake2b_224
  , .Ripemd_160
  , .Bls12_381_G1_multiScalarMul
  , .Bls12_381_G2_multiScalarMul
  ]

def isCryptoBuiltin (builtin : BuiltinFun) : Bool :=
  cryptoBuiltins.any fun candidate => candidate == builtin

/-- Non-cryptographic builtins that are deliberately outside the current
product model.  They remain rejected until their compiler semantics and CEK
simulation proofs are implemented together. -/
def unimplementedBuiltins : List BuiltinFun :=
  [ .SerializeData
  , .InsertCoin
  , .LookupCoin
  , .ScaleValue
  , .UnionValue
  , .ValueContains
  , .ValueData
  , .UnValueData
  ]

def unsupportedBuiltins : List BuiltinFun :=
  cryptoBuiltins ++ unimplementedBuiltins

def isUnsupportedBuiltin (builtin : BuiltinFun) : Bool :=
  unsupportedBuiltins.any fun candidate => candidate == builtin

/-- The checked soundness allowlist is exactly the complement of the one
explicit unsupported policy table, over the complete `BuiltinFun` enum. -/
def supportPolicyIsExact : Bool :=
  allBuiltins.all fun builtin =>
    builtinAllowedForSoundness builtin == !isUnsupportedBuiltin builtin

def certifiedBuiltins : List BuiltinFun :=
  allBuiltins.filter builtinAllowedForSoundness

def checkerMatchesSupportTable : Bool :=
  allBuiltins.all fun builtin =>
    (SupportedTerm.check (.Builtin builtin)).isSome ==
      builtinAllowedForSoundness builtin

def allSupportedQueriesAccepted : Bool :=
  certifiedBuiltins.all fun builtin =>
    (BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def allUnsupportedQueriesRejected : Bool :=
  unsupportedBuiltins.all fun builtin =>
    !(BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def allCryptoQueriesRejected : Bool :=
  cryptoBuiltins.all fun builtin =>
    !(BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def allUnimplementedQueriesRejected : Bool :=
  unimplementedBuiltins.all fun builtin =>
    !(BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def noUnsupportedBuiltinDeclaredSupported : Bool :=
  allBuiltins.all fun builtin =>
    !builtinAllowedForSoundness builtin || !isUnsupportedBuiltin builtin

def isUnconditionalTimeout : List Outcome → Bool
  | [.timeout (.bool true)] => true
  | _ => false

/-- Even callers below the checked production boundary cannot obtain a
symbolic success/error formula for an unsupported builtin. -/
def allUnsupportedRawBranchesTimeout : Bool :=
  unsupportedBuiltins.all fun builtin =>
    isUnconditionalTimeout (evalBuiltinSym builtin [])

/-- Unsupported behavior has no callable SMT declaration.  Exact ground
folding may still return a literal CEK result before this symbolic branch. -/
def unsupportedFunctionNames : List String :=
  [ "uplc_serializeData", "uplc_sha2_256", "uplc_sha3_256",
    "uplc_blake2b_256", "uplc_keccak_256", "uplc_blake2b_224",
    "uplc_ripemd_160", "uplc_verifyEd25519Signature",
    "uplc_verifyEcdsaSecp256k1Signature",
    "uplc_verifySchnorrSecp256k1Signature", "uplc_g1_add", "uplc_g1_neg",
    "uplc_g1_scalarMul", "uplc_g1_equal", "uplc_g1_hashToGroup",
    "uplc_g1_compress", "uplc_g1_uncompress", "uplc_g2_add",
    "uplc_g2_neg", "uplc_g2_scalarMul", "uplc_g2_equal",
    "uplc_g2_hashToGroup", "uplc_g2_compress", "uplc_g2_uncompress",
    "uplc_millerLoop", "uplc_mulMlResult", "uplc_finalVerify",
    "uplc_g1_multiScalarMul", "uplc_g2_multiScalarMul",
    "uplc_insertCoin", "uplc_lookupCoin", "uplc_scaleValue",
    "uplc_unionValue", "uplc_valueContains", "uplc_valueData",
    "uplc_unValueData" ]

def containsSubstring (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Inspect rendered text, including `.raw` commands.  Most of the prelude is
intentionally represented as raw, so checking only structured declarations
would leave this regression unable to detect reintroduced callable UFs. -/
def commandDefinesUnsupported (command : Moist.SMT.Command) : Bool :=
  unsupportedFunctionNames.any fun name =>
    containsSubstring command.render name

def noUnsupportedCallableFunctionInPrelude : Bool :=
  prelude.all fun command => !commandDefinesUnsupported command

example : allBuiltins.length = 101 := by native_decide
example : cryptoBuiltins.length = 28 := by native_decide
example : unimplementedBuiltins.length = 8 := by native_decide
example : unsupportedBuiltins.length = 36 := by native_decide
example : certifiedBuiltins.length = 65 := by native_decide
example : allBuiltins.eraseDups.length = allBuiltins.length := by native_decide
example : cryptoBuiltins.eraseDups.length = cryptoBuiltins.length := by native_decide
example : unimplementedBuiltins.eraseDups.length = unimplementedBuiltins.length := by
  native_decide
example : unsupportedBuiltins.eraseDups.length = unsupportedBuiltins.length := by
  native_decide
example : supportPolicyIsExact = true := by native_decide
example : checkerMatchesSupportTable = true := by native_decide
example : allSupportedQueriesAccepted = true := by native_decide
example : allUnsupportedQueriesRejected = true := by native_decide
example : allCryptoQueriesRejected = true := by native_decide
example : allUnimplementedQueriesRejected = true := by native_decide
example : noUnsupportedBuiltinDeclaredSupported = true := by native_decide
example : allUnsupportedRawBranchesTimeout = true := by native_decide
example : unsupportedFunctionNames.length = 36 := by native_decide
example : noUnsupportedCallableFunctionInPrelude = true := by native_decide

def nestedOpaqueTerm : Term :=
  .Case (.Constr 0 []) [.Lam 0 (.Builtin .Sha2_256)]

example : (BoolTrueQuery.compile? 20 [] nestedOpaqueTerm).isSome = false := by
  native_decide

/-- `SymDecl.wellFormed` controls SMT sort/validity assumptions, but constructor
fields may still contain higher-order opaque values.  This regression proves
that the independent production-fragment check is necessary and effective. -/
def wellFormedButOpaqueDeclaration : SymDecl :=
  symConstr "opaque" [.lam (.Builtin .Sha2_256) []]

example :
    (SupportedDeclarations.check [wellFormedButOpaqueDeclaration]).isSome = false := by
  native_decide

example :
    (BoolTrueQuery.compile? 20 [wellFormedButOpaqueDeclaration]
      (.Constant (.Bool true, .AtomicType .TypeBool))).isSome = false := by
  native_decide

def supportedDeclarations : List SymDecl :=
  [symInt "x", symConstr "tag" [.const .unit]]

example : (SupportedDeclarations.check supportedDeclarations).isSome = true := by
  native_decide

def delimiterInjectionDeclaration : SymDecl :=
  (symInt "x").withAssumptions
    [.sym "true) (assert false) ; renderer injection"]

example : expressionRendererSafe
    (.sym "true) (assert false) ; renderer injection") = false := by
  native_decide

example :
    (SupportedDeclarations.check [delimiterInjectionDeclaration]).isSome = false := by
  native_decide

def nestedRendererInjectionDeclaration : SymDecl :=
  symConstr "tag"
    [.const (.bool (.sym "x)\n(check-sat)\n(exit)\n;"))]

example :
    (SupportedDeclarations.check [nestedRendererInjectionDeclaration]).isSome = false := by
  native_decide

example :
    (BoolTrueQuery.compile? 20 [nestedRendererInjectionDeclaration]
      (.Case (.Var 1) [.Lam 0 (.Var 1)])).isSome = false := by
  native_decide

example : declarationNameRendererSafe (Moist.SMT.sanitize "x (y)") = true := by
  native_decide

example : declarationNameRendererSafe "x) (assert false)" = false := by
  native_decide

/-! SMT-LIB literals and nullary constructors must not be smuggled through
`Expr.sym`: the executable semantics treats a general symbol as a model
lookup, whereas Z3 assigns these tokens fixed meanings. -/

def literalAtomCollisionDeclaration (atom : String) : SymDecl :=
  (symInt "x").withAssumptions [.sym atom]

example : expressionRendererSafe (.sym "true") = false := by native_decide
example : expressionRendererSafe (.sym "false") = false := by native_decide
example : expressionRendererSafe (.sym "0") = false := by native_decide
example : expressionRendererSafe (.sym "VUnit") = false := by native_decide
example : expressionRendererSafe (.sym "DNil") = false := by native_decide
example : expressionRendererSafe (.app "true" []) = false := by native_decide
example : expressionRendererSafe (.app "0" []) = false := by native_decide
example : expressionRendererSafe (.app "VUnit" []) = true := by native_decide

example :
    (SupportedDeclarations.check
      [literalAtomCollisionDeclaration "true"]).isSome = false := by
  native_decide

example : expressionRendererSafe (.sym (Moist.SMT.sanitize "x")) = true := by
  native_decide

example : expressionRendererSafe (.sym "(as seq.empty Bytes)") = true := by
  native_decide

example : expressionRendererSafe (.sym "(as seq.empty (Seq Int))") = false := by
  native_decide

example : expressionSort? [] (.sym "(as seq.empty (Seq Int))") ==
    some .bytes := by
  native_decide

/-! Renderer-safe syntax is still rejected unless it is closed, uniquely
declared, and sorted according to the executable SMT semantics.  These cases
regress concrete Z3 `error`-then-`sat` and Bytes/UString aliasing failures. -/

def undeclaredAtomDeclaration : SymDecl :=
  symConstr "tag" [.const (.bool (.sym "$u$999"))]

example : declarationsRendererSafe [undeclaredAtomDeclaration] = true := by
  native_decide

example : declarationsSortSafe [undeclaredAtomDeclaration] = false := by
  native_decide

example :
    (SupportedDeclarations.check [undeclaredAtomDeclaration]).isSome = false := by
  native_decide

def crossSortEqualityDeclaration : SymDecl :=
  symConstr "tag"
    [.const (.bool (.app "=" [.bytes (ByteArray.mk #[65]), .str "A"]))]

example : expressionSort? []
    (.app "=" [.bytes (ByteArray.mk #[65]), .str "A"]) == none := by
  native_decide

example : expressionSort? [] (.app "(_ is VInt)" []) == none := by
  native_decide

example : expressionSort? []
    (.app "(_ is VInt)" [.app "VInt" [.int 0], .app "VInt" [.int 1]]) ==
      none := by
  native_decide

example : declarationsSortSafe [crossSortEqualityDeclaration] = false := by
  native_decide

example :
    (BoolTrueQuery.compile? 20 [crossSortEqualityDeclaration]
      (.Case (.Var 1) [.Lam 0 (.Var 1)])).isSome = false := by
  native_decide

def nullaryLiteralApplicationDeclaration : SymDecl :=
  symConstr "tag" [.const (.bool (.app "true" []))]

example :
    (SupportedDeclarations.check
      [nullaryLiteralApplicationDeclaration]).isSome = false := by
  native_decide

example : declarationNamesDistinct [symInt "x", symInt "x"] = false := by
  native_decide

example :
    (SupportedDeclarations.check [symInt "x", symInt "x"]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check [symInt "x", symBytes "x"]).isSome = false := by
  native_decide

/-! Z3 assigns values to partial selectors and sequence operations outside
their CEK/executable domains.  Public declaration expressions reject those
operations instead of accepting a raw `sat` model that cannot be decoded. -/

def constructorWithBoolField (expression : SExpr) : SymDecl :=
  symConstr "partial_bool" [.const (.bool expression)]

def constructorWithIntField (expression : SExpr) : SymDecl :=
  symConstr "partial_int" [.const (.integer expression)]

def constructorWithBytesField (expression : SExpr) : SymDecl :=
  symConstr "partial_bytes" [.const (.bytes expression)]

def constructorWithStringField (expression : SExpr) : SymDecl :=
  symConstr "partial_string" [.const (.string expression)]

def wrongSelector : SExpr :=
  .app "unVBool" [.app "VInt" [.int 0]]

def outOfRangeNth : SExpr :=
  .app "seq.nth" [.bytes (ByteArray.mk #[1]), .int 1]

def invalidSingleton : SExpr := .app "seq.unit" [.int 300]
def zeroDivision : SExpr := .app "uplc_tdiv" [.int 1, .int 0]
def invalidDecode : SExpr :=
  .app "uplc_decodeUtf8" [.bytes (ByteArray.mk #[255])]

def negativeExtract : SExpr :=
  .app "seq.extract" [.bytes (ByteArray.mk #[1, 2]), .int (-1), .int 1]

example : expressionTotalitySafe wrongSelector = false := by native_decide
example : expressionTotalitySafe outOfRangeNth = false := by native_decide
example : expressionTotalitySafe invalidSingleton = false := by native_decide
example : expressionTotalitySafe zeroDivision = false := by native_decide
example : expressionTotalitySafe invalidDecode = false := by native_decide
example : expressionTotalitySafe negativeExtract = false := by native_decide

example : declarationsSortSafe [constructorWithBoolField wrongSelector] = true := by
  native_decide

example :
    (SupportedDeclarations.check
      [constructorWithBoolField wrongSelector]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check
      [constructorWithIntField outOfRangeNth]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check
      [constructorWithBytesField invalidSingleton]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check
      [constructorWithIntField zeroDivision]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check
      [constructorWithStringField invalidDecode]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check
      [constructorWithBytesField negativeExtract]).isSome = false := by
  native_decide

def nondecodableNestedConstructor : SymDecl :=
  symConstr "nested"
    [.dyn (.app "VConstr" [.int (-1), .app "VNil" []])]

def nondecodableConstList : SymDecl :=
  symConstr "const_list"
    [.const (.constList
      (.app "VCons"
        [.app "VConstr" [.int 0, .app "VNil" []], .app "VNil" []])
      .unknown)]

example : declarationsSortSafe [nondecodableNestedConstructor] = true := by
  native_decide

example :
    (SupportedDeclarations.check [nondecodableNestedConstructor]).isSome = false := by
  native_decide

example :
    (SupportedDeclarations.check [nondecodableConstList]).isSome = false := by
  native_decide

def pairContainingRuntimeConstructor : SymDecl :=
  symConstr "pair_constr"
    [.pair (.constr (.int 0) []) (.const .unit)]

def pairContainingSymbolicVal : List SymDecl :=
  let value := symVal "pair_value"
  [value,
   symConstr "pair_tag"
     [.pair (.dyn (.sym value.name)) (.const .unit)]]

example : declarationsSortSafe [pairContainingRuntimeConstructor] = true := by
  native_decide

example :
    (SupportedDeclarations.check [pairContainingRuntimeConstructor]).isSome = false := by
  native_decide

example : declarationsSortSafe pairContainingSymbolicVal = true := by
  native_decide

example :
    (SupportedDeclarations.check pairContainingSymbolicVal).isSome = false := by
  native_decide

example :
    (IntEqQuery.compile? 20 supportedDeclarations
      (.Constant (.Integer 1, .AtomicType .TypeInteger)) 1).isSome = true := by
  native_decide

end Test.SMT.SupportedQueries
