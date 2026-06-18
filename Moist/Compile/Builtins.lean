import Moist.Compile.SymValue
import Moist.CEK.Builtins

/-! # Symbolic builtin denotations (`smtBuiltin` + the saturation dispatch)

The symbolic counterpart of `Moist.CEK.evalBuiltin`, with the **same two-stage shape**:

1. `symBuiltinPassThrough` — builtins that return one of their `SymVal` arguments unchanged
   (here: `IfThenElse`).  Mirrors `evalBuiltinPassThrough`.
2. `smtBuiltin` — pure first-order computation on the argument *expressions*, producing a
   value `SmtExpr` **and a definedness guard** `SmtExpr` (e.g. `divideInteger` contributes
   `y ≠ 0`).  Mirrors `evalBuiltinConst`.

`symEvalBuiltin` composes them exactly as `evalBuiltin` does.  Arguments are in **reversed**
order (most recent first), matching the `VBuiltin`/`evalBuiltinConst` convention — so the
clauses line up one-for-one with the trusted `evalBuiltin_*` denotation axioms in
`Moist.Verified.BigStep`, which is what makes the agreement lemmas (§6.2) definitional.

**v0 fragment.**  The fully-supported, fully-*proved* builtins are the ten integer
arithmetic/comparison operations — enough for the straight-line arithmetic validator class.
`IfThenElse` is implemented (concrete-condition control flow runs concretely; a symbolic
boolean condition with first-order branches becomes an SMT `ite`); its adequacy is part of
the symbolic-dispatch story.  Every other builtin returns `none` ⇒ `symEval` **refuses**
(returns `none`) rather than mis-compiling — the sound failure mode (§2.5, R1).
-/

namespace Moist.Compile

open Moist.Plutus.Term (Const BuiltinFun)
open Moist.CEK (evalBuiltinConst)
open Moist.Smt (SmtExpr SmtSort)
open Moist.Smt.BinOp

/-- The six builtins handled by `evalBuiltinPassThrough` (they may return a non-`VCon`
    argument unchanged): they must NOT be routed through the concrete `evalBuiltinConst`
    fold.  Mirrors `evalBuiltinPassThrough_none_of_not_passthrough`. -/
def isPassthroughBuiltin : BuiltinFun → Bool
  | .IfThenElse | .ChooseUnit | .Trace | .ChooseData | .ChooseList | .MkCons => true
  | _ => false

/-- Extract a fully concrete `Const` list from symbolic arguments: `sConst c ↦ c`, and the
    concrete `sCon` literals `litI`/`litB ↦ Integer`/`Bool`.  `none` if any argument is
    genuinely symbolic.  Used by the concrete-fold path of `symEvalBuiltin`. -/
def symConcrete : List SymVal → Option (List Const)
  | []                  => some []
  | .sConst c :: rest    => (symConcrete rest).map (c :: ·)
  | .sCon (.litI n) :: rest => (symConcrete rest).map (.Integer n :: ·)
  | .sCon (.litB b) :: rest => (symConcrete rest).map (.Bool b :: ·)
  | _ :: _              => none

/-- Build a sort-guarded binary operator on `need`-sorted operands.  An ill-sorted operand
    ⇒ `none` ⇒ refuse — a light, sound type check that makes the agreement lemmas (§6.2)
    dischargeable (the guarded operands evaluate to the right `SVal` kind, `evalSmt_sort`).
    `grd` is the definedness guard (e.g. `y ≠ 0` for division). -/
def sortBin (op : Moist.Smt.BinOp) (grd : SmtExpr) (need : SmtSort) (ex ey : SmtExpr) :
    Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf ex = some need ∧ SmtExpr.sortOf ey = some need
  then some (.bin op ex ey, grd) else none

/-- Build a sort-guarded unary operator: commits only when the operand is `need`-sorted.
    `grd` is the definedness guard (e.g. `isI e` for `unIData`). -/
def uOp (op : Moist.Smt.UnOp) (grd : SmtExpr) (need : SmtSort) (e : SmtExpr) :
    Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf e = some need then some (.uop op e, grd) else none

/-- `unConstrData`: a `Data` commits to the `(tag, fields)` builtin pair, guarded by `isConstr`. -/
def unConstrOp (e : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf e = some .data then
    some (.mkpair (.uop .constrTag e) (.uop .dArgs e), .uop .isConstr e) else none

/-- A BLS binary/mixed op committing on its two declared operand sorts (axiomatized). -/
def blsBinOp (op : Moist.Smt.BlsBinOp) (a b : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf a = some (Moist.Smt.BlsBinOp.operandSorts op).1 ∧
     SmtExpr.sortOf b = some (Moist.Smt.BlsBinOp.operandSorts op).2
  then some (.blsBin op a b, .trueE) else none

/-- A signature-verification op committing on three `bytes`-sorted operands (axiomatized). -/
def verifySigOp (k : Moist.Smt.VerifyKind) (pk msg sig : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf pk = some .bytes ∧ SmtExpr.sortOf msg = some .bytes ∧
     SmtExpr.sortOf sig = some .bytes
  then some (.verifySig k pk msg sig, .trueE) else none

/-- A unary projection committing on `pair`-sorted operands (`fstPair`/`sndPair`; total). -/
def pairProj (mk : SmtExpr → SmtExpr) (e : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  match SmtExpr.sortOf e with | some (.pair _ _) => some (mk e, .trueE) | _ => none

/-- A `list data` operation guarded **non-empty** (`headList`/`tailList`). -/
def listOpNE (mk : SmtExpr → SmtExpr) (e : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf e = some (.list .data) then some (mk e, .not (.nullL e)) else none
/-- A **total** `list data` operation (`nullList`). -/
def listOpT (mk : SmtExpr → SmtExpr) (e : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf e = some (.list .data) then some (mk e, .trueE) else none

/-- `constrData`: `tag : int`, `fields : list data` ↦ the `Data` term `mkConstr tag fields`. -/
def constrDataOp (tag fields : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  match SmtExpr.sortOf tag, SmtExpr.sortOf fields with
  | some .int, some (.list .data) => some (.mkConstrD tag fields, .trueE)
  | _, _ => none

/-- `mkCons h tl`: prepend a `data` head to a `list data` tail (the only element sort the CEK's
    `ConstDataList` supports) ↦ `consL h tl`. -/
def consDataOp (h tl : SmtExpr) : Option (SmtExpr × SmtExpr) :=
  if SmtExpr.sortOf h = some .data ∧ SmtExpr.sortOf tl = some (.list .data)
  then some (.consL h tl, .trueE) else none

/-- First-order builtin denotation: argument expressions ↦ `(value, definedness-guard)`.
    Reversed-argument convention (`[ey, ex]` = second then first UPLC argument), matching
    `evalBuiltinConst`.  Arity is matched first, then the operator dispatched, so the
    agreement proof gets a single shape per arity.  `none` = unsupported/ill-sorted ⇒ refuse. -/
def smtBuiltin (b : BuiltinFun) (args : List SmtExpr) : Option (SmtExpr × SmtExpr) :=
  match args with
  | [e] =>
    match b with
    -- Data injection/projection (projections guarded by the constructor tester)
    | .IData    => uOp .iData .trueE .int e
    | .BData    => uOp .bData .trueE .bytes e
    | .UnIData  => uOp .unIData (.uop .isI e) .data e
    | .UnBData  => uOp .unBData (.uop .isB e) .data e
    -- Structured Data destructors ⇒ builtin Pair / List (guarded by the constructor tester):
    | .UnConstrData => unConstrOp e                              -- Data → pair int (list data)
    | .UnListData => uOp .dItems (.uop .isList e) .data e        -- Data → list data
    | .ListData => uOp .mkDList .trueE (.list .data) e           -- list data → Data  (construct)
    -- (UnMapData → list (pair data data) deferred: the empty `Map`/`List` reconstruction is
    --  ambiguous under sort-erased `svalToConst`; the data-list destructors below are exact.)
    -- Pair / List operations (the CEK supports `ConstDataList`, so list ops are on `list data`)
    | .FstPair  => pairProj .fstP e
    | .SndPair  => pairProj .sndP e
    | .HeadList => listOpNE (.headL .data) e   -- partial ⇒ guard non-empty
    | .TailList => listOpNE .tailL e
    | .NullList => listOpT .nullL e
    -- ByteString length (total)
    | .LengthOfByteString => uOp .lenBytes .trueE .bytes e
    -- Cryptographic hashes (bytes → bytes, axiomatized as uninterpreted functions)
    | .Sha2_256    => uOp .sha2_256 .trueE .bytes e
    | .Sha3_256    => uOp .sha3_256 .trueE .bytes e
    | .Blake2b_256 => uOp .blake2b_256 .trueE .bytes e
    | .Blake2b_224 => uOp .blake2b_224 .trueE .bytes e
    | .Keccak_256  => uOp .keccak_256 .trueE .bytes e
    | .Ripemd_160  => uOp .ripemd_160 .trueE .bytes e
    | .SerializeData => uOp .serialiseData .trueE .data e   -- data → bytes (CBOR, uninterpreted)
    -- BLS12-381 unary (bytes → bytes; elements as compressed bytes)
    | .Bls12_381_G1_neg => uOp .blsG1Neg .trueE .bytes e
    | .Bls12_381_G2_neg => uOp .blsG2Neg .trueE .bytes e
    | .Bls12_381_G1_compress => uOp .blsG1Compress .trueE .bytes e
    | .Bls12_381_G2_compress => uOp .blsG2Compress .trueE .bytes e
    | .Bls12_381_G1_uncompress => uOp .blsG1Uncompress .trueE .bytes e
    | .Bls12_381_G2_uncompress => uOp .blsG2Uncompress .trueE .bytes e
    | _ => none
  | [ey, ex] =>
    match b with
    -- Integer arithmetic (total ⇒ guard `true`)
    | .AddInteger      => sortBin .add .trueE .int ex ey
    | .SubtractInteger => sortBin .sub .trueE .int ex ey
    | .MultiplyInteger => sortBin .mul .trueE .int ex ey
    -- Integer division family (partial ⇒ guard `y ≠ 0`).  Floored vs truncated per Plutus.
    | .DivideInteger    => sortBin .fdiv (.neZeroE ey) .int ex ey
    | .ModInteger       => sortBin .fmod (.neZeroE ey) .int ex ey
    | .QuotientInteger  => sortBin .tdiv (.neZeroE ey) .int ex ey
    | .RemainderInteger => sortBin .tmod (.neZeroE ey) .int ex ey
    -- Integer comparison (total ⇒ guard `true`)
    | .EqualsInteger         => sortBin .eq .trueE .int ex ey
    | .LessThanInteger       => sortBin .lt .trueE .int ex ey
    | .LessThanEqualsInteger => sortBin .le .trueE .int ex ey
    -- Data / ByteString equality
    | .EqualsData       => sortBin .eq .trueE .data ex ey
    | .EqualsByteString => sortBin .eq .trueE .bytes ex ey
    -- Data construction: `constrData tag fields` (symbolic on BOTH; reversed args ⇒ ex=tag, ey=fields)
    | .ConstrData => constrDataOp ex ey
    -- `mkCons h tl` on a `list data` (reversed ⇒ ex=head, ey=tail)
    | .MkCons => consDataOp ex ey
    -- BLS12-381 binary (operand1 = ex, operand2 = ey, matching the reversed CEK args)
    | .Bls12_381_G1_add => blsBinOp .g1Add ex ey
    | .Bls12_381_G2_add => blsBinOp .g2Add ex ey
    | .Bls12_381_mulMlResult => blsBinOp .mulMlResult ex ey
    | .Bls12_381_G1_hashToGroup => blsBinOp .g1HashToGroup ex ey
    | .Bls12_381_G2_hashToGroup => blsBinOp .g2HashToGroup ex ey
    | .Bls12_381_millerLoop => blsBinOp .millerLoop ex ey
    | .Bls12_381_G1_equal => blsBinOp .g1Equal ex ey
    | .Bls12_381_G2_equal => blsBinOp .g2Equal ex ey
    | .Bls12_381_finalVerify => blsBinOp .finalVerify ex ey
    -- scalarMul: scalar (ex, the 1st UPLC arg, int) × point (ey, bytes) — operand1=int, operand2=bytes
    | .Bls12_381_G1_scalarMul => blsBinOp .g1ScalarMul ex ey
    | .Bls12_381_G2_scalarMul => blsBinOp .g2ScalarMul ex ey
    | _ => none
  | [eSig, eMsg, ePk] =>   -- reversed args: signature, message, pubkey
    match b with
    | .VerifyEd25519Signature          => verifySigOp .ed25519 ePk eMsg eSig
    | .VerifyEcdsaSecp256k1Signature   => verifySigOp .ecdsaSecp256k1 ePk eMsg eSig
    | .VerifySchnorrSecp256k1Signature => verifySigOp .schnorrSecp256k1 ePk eMsg eSig
    | _ => none
  | _ => none

/-- Recognise a *concrete* boolean literal expression (resolves control flow concretely). -/
def asLitBool : SmtExpr → Option Bool
  | .litB b => some b
  | _       => none

/-- Pass-through builtins (return a `SymVal` argument).  Mirrors `evalBuiltinPassThrough`.

    `IfThenElse [elseV, thenV, condV]`:
    * a **concrete** condition (`litB true/false`) picks the branch directly — branches may
      be *any* value, including closures, so concrete control flow is fully supported;
    * a **symbolic** boolean condition with **first-order** branches (`sCon`) becomes an SMT
      `ite`;
    * any other shape (symbolic choice of a *function*) ⇒ `none` (refuse, R1). -/
def symBuiltinPassThrough : BuiltinFun → List SymVal → Option SymOut
  | .IfThenElse, [elseV, thenV, .sCon condE] =>
    match asLitBool condE with
    | some true  => some ⟨thenV, .trueE⟩   -- concrete condition: pick the branch
    | some false => some ⟨elseV, .trueE⟩
    | none =>                               -- symbolic boolean condition
      if SmtExpr.sortOf condE = some .bool then
        match thenV, elseV with
        | .sCon thenE, .sCon elseE => some ⟨.sCon (.ite condE thenE elseE), .trueE⟩  -- first-order
        | _, _ => some ⟨.sIte condE thenV elseV, .trueE⟩                              -- lazy ⇒ defer
      else none
  -- `chooseUnit u r = r`, `trace _ r = r` (the discriminant is fully concrete) ⇒ pass `r` through
  | .ChooseUnit, [result, .sConst .Unit]        => some ⟨result, .trueE⟩
  | .Trace,      [result, .sConst (.String _)]  => some ⟨result, .trueE⟩
  -- `chooseData d c m l i b`: dispatch on a *concrete* `Data`'s variant
  | .ChooseData, [bC, iC, lC, mC, cC, .sConst (.Data d)] =>
    some ⟨(match d with | .Constr _ _ => cC | .Map _ => mC | .List _ => lC | .I _ => iC | .B _ => bC),
          .trueE⟩
  -- `chooseList l nilC consC`: dispatch on whether a *concrete* list is empty
  | .ChooseList, [consC, nilC, .sConst (.ConstDataList l)] =>
    some ⟨if l.isEmpty then nilC else consC, .trueE⟩
  | .ChooseList, [consC, nilC, .sConst (.ConstList l)] =>
    some ⟨if l.isEmpty then nilC else consC, .trueE⟩
  -- `mkCons x xs` on concrete operands (the element may be any constant)
  | .MkCons, [.sConst (.ConstDataList tl), .sConst (.Data h)] =>
    some ⟨.sConst (.ConstDataList (h :: tl)), .trueE⟩
  | .MkCons, [.sConst (.ConstList tl), .sConst c] =>
    some ⟨.sConst (.ConstList (c :: tl)), .trueE⟩
  | _, _ => none

/-- `mkNilData ()` ↦ a *symbolic* empty `list data` (so it composes with the symbolic `mkCons`).
    Handled as its own stage (not in `symBuiltinPassThrough`/`smtBuiltin`) because the argument is
    the concrete `sConst .Unit`, not an `sCon`.  (`mkNilPairData` → `ConstPairDataList []` is the
    map path: deferred — `svalToConst (.L [])` can't distinguish it from `ConstDataList []`.) -/
def symNil : BuiltinFun → List SymVal → Option SymOut
  | .MkNilData, [.sConst .Unit] => some ⟨.sCon (.nilL .data), .trueE⟩
  | _, _ => none

/-- Extract argument expressions from `sCon`-wrapped symbolic values.  `none` if any
    argument is not a first-order `sCon` (mirrors `extractConsts`). -/
def symExtractCons : List SymVal → Option (List SmtExpr)
  | []           => some []
  | .sCon e :: rest => (symExtractCons rest).map (e :: ·)
  | _ :: _       => none

/-- The symbolic path: extract first-order argument expressions and run `smtBuiltin`. -/
def symBuiltinSymbolic (b : BuiltinFun) (args : List SymVal) : Option SymOut :=
  match symExtractCons args with
  | some exprs =>
    match smtBuiltin b exprs with
    | some (v, g) => some ⟨.sCon v, g⟩
    | none        => none
  | none => none

/-- Evaluate a fully saturated builtin symbolically.  Three stages:
    1. pass-through (`IfThenElse` & friends, may return a `SymVal` argument);
    2. **symbolic** — `symBuiltinSymbolic` (the `smtBuiltin` table); tried *before* the fold so
       that symbolic-capable builtins (arithmetic, `Data` inject/project, equality) keep a
       first-order `sCon` representation that composes with other symbolic values;
    3. **concrete fold** — for a builtin `smtBuiltin` does not cover, if all arguments are
       concrete and `b` is not a pass-through builtin, defer to the real `evalBuiltinConst`
       (axiom-free, full CEK coverage on concrete data). -/
def symEvalBuiltin (b : BuiltinFun) (args : List SymVal) : Option SymOut :=
  match symNil b args with
  | some o => some o
  | none =>
  match symBuiltinPassThrough b args with
  | some o => some o
  | none =>
    match symBuiltinSymbolic b args with
    | some o => some o
    | none =>
      match (if isPassthroughBuiltin b then none else symConcrete args) with
      | some consts => (evalBuiltinConst b consts).map (fun c => ⟨.sConst c, .trueE⟩)
      | none => none

end Moist.Compile
