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

def checkerMatchesSupportTable : Bool :=
  allBuiltins.all fun builtin =>
    (SupportedTerm.check (.Builtin builtin)).isSome ==
      builtinAllowedForSoundness builtin

def allSupportedQueriesAccepted : Bool :=
  allBuiltins.all fun builtin =>
    !builtinAllowedForSoundness builtin ||
      (BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def allCryptoQueriesRejected : Bool :=
  cryptoBuiltins.all fun builtin =>
    !(BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def allUnimplementedQueriesRejected : Bool :=
  unimplementedBuiltins.all fun builtin =>
    !(BoolTrueQuery.compile? 1 [] (.Builtin builtin)).isSome

def noUnsupportedBuiltinDeclaredSupported : Bool :=
  allBuiltins.all fun builtin =>
    !builtinAllowedForSoundness builtin || !isUnsupportedBuiltin builtin

example : allBuiltins.length = 101 := by native_decide
example : cryptoBuiltins.length = 28 := by native_decide
example : unimplementedBuiltins.length = 8 := by native_decide
example : checkerMatchesSupportTable = true := by native_decide
example : allSupportedQueriesAccepted = true := by native_decide
example : allCryptoQueriesRejected = true := by native_decide
example : allUnimplementedQueriesRejected = true := by native_decide
example : noUnsupportedBuiltinDeclaredSupported = true := by native_decide

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

example :
    (SupportedDeclarations.check
      [literalAtomCollisionDeclaration "true"]).isSome = false := by
  native_decide

example : expressionRendererSafe (.sym (Moist.SMT.sanitize "x")) = true := by
  native_decide

example : expressionRendererSafe (.sym "(as seq.empty Bytes)") = true := by
  native_decide

example :
    (IntEqQuery.compile? 20 supportedDeclarations
      (.Constant (.Integer 1, .AtomicType .TypeInteger)) 1).isSome = true := by
  native_decide

#print axioms BoolTrueQuery.sound
#print axioms IntEqQuery.sound
#print axioms ErrorQuery.sound

end Test.SMT.SupportedQueries
