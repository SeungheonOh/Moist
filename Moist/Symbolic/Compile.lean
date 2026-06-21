import Moist.Symbolic.Value
import Moist.CEK.Builtins

/-! # The UPLC → SMT-LIB denotational compiler

`symEval : Nat → SymEnv → Term → SymR` is a fuel-bounded normalisation-by-
evaluation interpreter that is, by construction, a structural clone of
`Moist.Verified.BigStep.bigEval` (same fuel discipline, same mutual shape:
`symApply`/`symForce`/`symEvalList`/`symApplyList` mirror
`applyVal`/`forceVal`/`bigEvalList`/`applyValList`). The difference is the value
domain: instead of concrete `CekValue`s it computes over `SymV`, emitting SMT
`SExpr`s, so that *branching on symbolic data becomes SMT `ite`* rather than a
Lean-level fork.

The three-outcome result `SymR = ⟨inc, err, val⟩` (incomplete / error / value),
all carried as *symbolic* conditions, is what makes bounded symbolic recursion
work: a recursive validator built with `force`/`delay` thunks unrolls lazily
through `choice` distribution, so the fuel-out condition `inc` is a *path
condition in the symbolic inputs* (e.g. `x ≥ depth`), not a blanket failure.

## Builtin coverage (formally verified fragment)

* **Precise SMT**: integer arithmetic/comparison/division, simple byte/string
  operations, structural list/pair builtins, data constructors/destructors, and
  the CEK pass-through builtins (`ifThenElse`, `chooseUnit`, `trace`,
  `chooseData`, `chooseList`).
* **Definite error**: every builtin for which the reference CEK has no denotation,
  including hashes, signature checks, `SerializeData`, BLS, and unsupported batch-7
  operations. Saturating one of these enters `State.error`, just as the CEK does.
* **Indeterminate (`inc = true`, no CEK-value claim)**: remaining CEK-supported
  operations whose symbolic denotations are not yet connected to the formal
  adequacy proof.

> Note: legacy opaque `uf_*` declarations and BLS element sorts remain in the SMT
> preamble (`Smt.lean`), but compiler output does not call those functions.
-/

namespace Moist.Symbolic

open Moist.Plutus.Term (Term Const BuiltinType BuiltinFun)
open Moist.CEK (ExpectedArgs expectedArgs)
open SExpr (sNot sAnd sOr sImplies sIte sEq)

/-! ## Type-guard helpers (error when a `V` value has the wrong variant) -/

def gInt  (e : SExpr) : SExpr := sNot (V.sIsCon "VInt" e)
def gBool (e : SExpr) : SExpr := sNot (V.sIsCon "VBool" e)
def gBS   (e : SExpr) : SExpr := sNot (V.sIsCon "VBS" e)
def gStr  (e : SExpr) : SExpr := sNot (V.sIsCon "VStr" e)
def gData (e : SExpr) : SExpr := sNot (V.sIsCon "VData" e)
def gUnit (e : SExpr) : SExpr := sNot (V.sIsCon "VUnit" e)
def gCon (con : String) (e : SExpr) : SExpr := sNot (V.sIsCon con e)

/-- Data-kind discriminator `(is-DCon dd)`. -/
def dIs (con : String) (dd : SExpr) : SExpr := .app s!"is-{con}" [dd]
/-- Negated Data-kind discriminator. -/
def dNot (con : String) (dd : SExpr) : SExpr := sNot (dIs con dd)

/-- A definite-error result (declared early; reused by the list dispatcher). -/
def errR' : SymR := ⟨.bool false, .bool true, junk⟩
/-- An indeterminate result (out of fuel / unsupported / undetermined flavour). -/
def incR' : SymR := ⟨.bool true, .bool false, junk⟩

/-- Dispatch a list builtin across the two valid `Const` list flavours.  The
discriminators remain symbolic when `l` is a bare `V` input, so this agrees with
the CEK for every runtime variant instead of becoming indeterminate. -/
def onList (l : SExpr) (onD : SExpr → SymR) (onV : SExpr → SymR) : SymR :=
  symMerge (V.sIsCon "VDList" l) (onD (V.sAsDL l))
    (symMerge (V.sIsCon "VList" l) (onV (V.sAsList l)) errR')

/-- A definite-error result. -/
def errR : SymR := ⟨.bool false, .bool true, junk⟩
/-- An indeterminate result (out of fuel / unsupported). -/
def incR : SymR := ⟨.bool true, .bool false, junk⟩
/-- A pure (non-erroring, complete) first-order result. -/
def okFO (e : SExpr) : SymR := ⟨.bool false, .bool false, .fo e⟩
/-- A pure (non-erroring, complete) result that can be higher-order. -/
def okV (v : SymV) : SymR := ⟨.bool false, .bool false, v⟩
/-- A first-order result that errors under `g`. -/
def foGuard (g e : SExpr) : SymR := ⟨.bool false, g, .fo e⟩

/-! ## Saturated builtin evaluation on first-order arguments

`symBuiltin b argEs` takes the builtin's value arguments **in application order**
as `V`-sorted `SExpr`s and returns the saturated result. `inc = true` marks a
CEK-supported builtin whose symbolic denotation is not implemented yet;
otherwise `err` is the precise UPLC failure condition (type mismatch, division
by zero, head-of-nil, or a builtin absent from the CEK denotation). -/

open V (sAsInt sAsBool sAsBS sAsStr sAsData sAsList sAsDL sAsDM sFst sSnd)

def intDivZero (b : SExpr) : SExpr := sEq b (.int 0)
def intBinGuard (a b : SExpr) : SExpr := sOr (gInt a) (gInt b)
def dataKindGuard (con : String) (e : SExpr) : SExpr :=
  sOr (gData e) (dNot con (sAsData e))
def seqLen (e : SExpr) : SExpr := Seq.len e
def seqNth (s i : SExpr) : SExpr := Seq.nth s i
def seqExtractCEK (s start len : SExpr) : SExpr :=
  let start' := sIte (Op.lt start (.int 0)) (.int 0) start
  let len' := sIte (Op.lt len (.int 0)) (.int 0) len
  Seq.extract s start' len'
def byteInRange (n : SExpr) : SExpr :=
  sAnd (Op.le (.int 0) n) (Op.le n (.int 255))
def dropVL (n xs : SExpr) : SExpr := .app "moist_vdrop" [n, xs]
def dropDL (n xs : SExpr) : SExpr := .app "moist_ddrop" [n, xs]

def symBuiltin : BuiltinFun → List SExpr → SymR
  -- Integer arithmetic
  | .AddInteger,      [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.int (Op.add (sAsInt a) (sAsInt b)))
  | .SubtractInteger, [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.int (Op.sub (sAsInt a) (sAsInt b)))
  | .MultiplyInteger, [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.int (Op.mul (sAsInt a) (sAsInt b)))
  | .DivideInteger,   [a, b] => foGuard (sOr (intBinGuard a b) (intDivZero (sAsInt b)))
      (V.int (.app "moist_fdiv" [sAsInt a, sAsInt b]))
  | .QuotientInteger, [a, b] => foGuard (sOr (intBinGuard a b) (intDivZero (sAsInt b)))
      (V.int (.app "moist_qdiv" [sAsInt a, sAsInt b]))
  | .RemainderInteger, [a, b] => foGuard (sOr (intBinGuard a b) (intDivZero (sAsInt b)))
      (V.int (.app "moist_qrem" [sAsInt a, sAsInt b]))
  | .ModInteger, [a, b] => foGuard (sOr (intBinGuard a b) (intDivZero (sAsInt b)))
      (V.int (.app "moist_fmod" [sAsInt a, sAsInt b]))
  -- Integer comparison
  | .EqualsInteger,         [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.bool (sEq (sAsInt a) (sAsInt b)))
  | .LessThanInteger,       [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.bool (Op.lt (sAsInt a) (sAsInt b)))
  | .LessThanEqualsInteger, [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.bool (Op.le (sAsInt a) (sAsInt b)))
  -- ByteString operations expressible exactly with SMT sequences.
  | .AppendByteString, [a, b] =>
      foGuard (sOr (gBS a) (gBS b)) (V.bs (Seq.append (sAsBS a) (sAsBS b)))
  | .EqualsByteString, [a, b] =>
      foGuard (sOr (gBS a) (gBS b)) (V.bool (sEq (sAsBS a) (sAsBS b)))
  | .SliceByteString, [start, len, bs] =>
      foGuard (sOr (sOr (gInt start) (gInt len)) (gBS bs))
        (V.bs (seqExtractCEK (sAsBS bs) (sAsInt start) (sAsInt len)))
  | .LengthOfByteString, [bs] =>
      foGuard (gBS bs) (V.int (seqLen (sAsBS bs)))
  | .IndexByteString, [bs, idx] =>
      foGuard (sOr (sOr (gBS bs) (gInt idx))
        (sOr (Op.lt (sAsInt idx) (.int 0)) (Op.ge (sAsInt idx) (seqLen (sAsBS bs)))))
        (V.int (seqNth (sAsBS bs) (sAsInt idx)))
  | .ConsByteString, [n, bs] =>
      foGuard (sOr (sOr (gInt n) (gBS bs)) (sNot (byteInRange (sAsInt n))))
        (V.bs (Seq.append (Seq.unit (sAsInt n)) (sAsBS bs)))
  -- String operations expressible exactly in SMT.
  | .AppendString, [a, b] =>
      foGuard (sOr (gStr a) (gStr b)) (V.str (.app "str.++" [sAsStr a, sAsStr b]))
  | .EqualsString, [a, b] =>
      foGuard (sOr (gStr a) (gStr b)) (V.bool (sEq (sAsStr a) (sAsStr b)))
  -- Pair destructors
  | .FstPair, [p] =>
      symMerge (V.sIsCon "VPairD" p) (okFO (V.data (V.sFstD p)))
        (symMerge (V.sIsCon "VPair" p) (okFO (V.sFst p)) errR)
  | .SndPair, [p] =>
      symMerge (V.sIsCon "VPairD" p) (okFO (V.data (V.sSndD p)))
        (symMerge (V.sIsCon "VPair" p) (okFO (V.sSnd p)) errR)
  -- List operations over both `ConstDataList` and general `ConstList`.
  | .HeadList, [l] =>
      onList l
        (fun dl => foGuard (DL.sIsNil dl) (V.data (DL.sHd dl)))
        (fun vl => foGuard (VL.sIsNil vl) (VL.sHd vl))
  | .TailList, [l] =>
      onList l
        (fun dl => foGuard (DL.sIsNil dl) (V.dlist (DL.sTl dl)))
        (fun vl => foGuard (VL.sIsNil vl) (V.list (VL.sTl vl)))
  | .NullList, [l] =>
      onList l
        (fun dl => okFO (V.bool (DL.sIsNil dl)))
        (fun vl => okFO (V.bool (VL.sIsNil vl)))
  | .MkCons, [h, t] =>
      symMerge (V.sIsCon "VDList" t)
        (foGuard (gData h) (V.dlist (DL.cons (sAsData h) (sAsDL t))))
        (symMerge (V.sIsCon "VList" t)
          -- Any well-formed first-order value except an SOP `VConstr` denotes a `Const`.
          (foGuard (V.sIsCon "VConstr" h) (V.list (VL.cons h (sAsList t))))
          errR)
  | .DropList, [n, l] =>
      onList l
        (fun dl => foGuard (gInt n) (V.dlist (dropDL (sAsInt n) dl)))
        (fun vl => foGuard (gInt n) (V.list (dropVL (sAsInt n) vl)))
  -- Data constructors/destructors.
  | .ConstrData, [tag, fields] =>
      foGuard (sOr (gInt tag) (gCon "VDList" fields))
        (V.data (D.constr (sAsInt tag) (sAsDL fields)))
  | .MapData, [m] =>
      foGuard (gCon "VPDList" m) (V.data (D.map (sAsDM m)))
  | .ListData, [l] =>
      foGuard (gCon "VDList" l) (V.data (D.list (sAsDL l)))
  | .IData, [i] =>
      foGuard (gInt i) (V.data (D.i (sAsInt i)))
  | .BData, [bs] =>
      foGuard (gBS bs) (V.data (D.b (sAsBS bs)))
  | .UnConstrData, [d] =>
      foGuard (dataKindGuard "DConstr" d)
        (V.pairD (D.i (D.dcTag (sAsData d))) (D.list (D.dcArgs (sAsData d))))
  | .UnMapData, [d] =>
      foGuard (dataKindGuard "DMap" d) (V.pdlist (D.dmEntries (sAsData d)))
  | .UnListData, [d] =>
      foGuard (dataKindGuard "DList" d) (V.dlist (D.dlElems (sAsData d)))
  | .UnIData, [d] =>
      foGuard (dataKindGuard "DI" d) (V.int (D.diVal (sAsData d)))
  | .UnBData, [d] =>
      foGuard (dataKindGuard "DB" d) (V.bs (D.dbVal (sAsData d)))
  | .EqualsData, [a, b] =>
      foGuard (sOr (gData a) (gData b)) (V.bool (sEq (sAsData a) (sAsData b)))
  | .MkPairData, [a, b] =>
      foGuard (sOr (gData a) (gData b)) (V.pairD (sAsData a) (sAsData b))
  -- Empty data-list constructors.
  | .MkNilData, [u] =>
      foGuard (gUnit u) (V.dlist DL.nil)
  | .MkNilPairData, [u] =>
      foGuard (gUnit u) (V.pdlist DM.nil)
  -- The reference CEK has no denotation for these builtins.  Saturation therefore
  -- deterministically enters `State.error`; reporting `inc` here was observably
  -- different and made a stable CEK error look like a fuel/coverage limitation.
  | .Sha2_256, _ | .Sha3_256, _ | .Blake2b_256, _
  | .VerifyEd25519Signature, _ | .SerializeData, _
  | .VerifyEcdsaSecp256k1Signature, _ | .VerifySchnorrSecp256k1Signature, _
  | .Bls12_381_G1_add, _ | .Bls12_381_G1_neg, _ | .Bls12_381_G1_scalarMul, _
  | .Bls12_381_G1_equal, _ | .Bls12_381_G1_hashToGroup, _
  | .Bls12_381_G1_compress, _ | .Bls12_381_G1_uncompress, _
  | .Bls12_381_G2_add, _ | .Bls12_381_G2_neg, _ | .Bls12_381_G2_scalarMul, _
  | .Bls12_381_G2_equal, _ | .Bls12_381_G2_hashToGroup, _
  | .Bls12_381_G2_compress, _ | .Bls12_381_G2_uncompress, _
  | .Bls12_381_millerLoop, _ | .Bls12_381_mulMlResult, _ | .Bls12_381_finalVerify, _
  | .Keccak_256, _ | .Blake2b_224, _ | .Ripemd_160, _
  | .IndexArray, _ | .LengthOfArray, _ | .ListToArray, _
  | .InsertCoin, _ | .LookupCoin, _ | .ScaleValue, _ | .UnionValue, _
  | .ValueContains, _ | .ValueData, _ | .UnValueData, _
  | .Bls12_381_G1_multiScalarMul, _ | .Bls12_381_G2_multiScalarMul, _ => errR
  -- CEK-supported operations whose symbolic denotations are not implemented yet,
  -- including the remaining Data constructors/destructors and higher-order
  -- pass-through builtins.
  | _, _ => incR

def addErr (extra : SExpr) (r : SymR) : SymR :=
  ⟨r.inc, sOr extra r.err, r.val⟩

def passGuard (guard : SExpr) (v : SymV) : SymR :=
  ⟨.bool false, guard, v⟩

def symPassThrough (b : BuiltinFun) (args : List SymV) : Option SymR :=
  match b with
  | .IfThenElse =>
      match args with
      -- Application order: condition thenCase elseCase.
      | [c, t, e] =>
          let (nf, ce) := reifyFO c
          some ⟨.bool false, sOr nf (gBool ce), mergeVal (sAsBool ce) t e⟩
      | _ => none
  | .ChooseUnit =>
      match args with
      | [u, r] =>
          let (nf, ue) := reifyFO u
          some (passGuard (sOr nf (gUnit ue)) r)
      | _ => none
  | .Trace =>
      match args with
      | [msg, r] =>
          let (nf, me) := reifyFO msg
          some (passGuard (sOr nf (gStr me)) r)
      | _ => none
  | .ChooseList =>
      match args with
      | [l, nilCase, consCase] =>
          let (nf, le) := reifyFO l
          let r :=
            onList le
              (fun dl => symMerge (DL.sIsNil dl) (okV nilCase) (okV consCase))
              (fun vl => symMerge (VL.sIsNil vl) (okV nilCase) (okV consCase))
          some (addErr nf r)
      | _ => none
  | .ChooseData =>
      match args with
      | [d, constrCase, mapCase, listCase, iCase, bCase] =>
          let (nf, de) := reifyFO d
          let dd := sAsData de
          let r :=
            symMerge (dIs "DConstr" dd) (okV constrCase)
              (symMerge (dIs "DMap" dd) (okV mapCase)
                (symMerge (dIs "DList" dd) (okV listCase)
                  (symMerge (dIs "DI" dd) (okV iCase)
                    (symMerge (dIs "DB" dd) (okV bCase) errR))))
          some (addErr (sOr nf (gData de)) r)
      | _ => none
  | _ => none

/-! ## Saturating a builtin from its accumulated (reversed) value arguments

All saturated arguments are reified to first order and dispatched to `symBuiltin`.
Higher-order CEK pass-through builtins are currently reported as indeterminate until
their symbolic denotations are connected to the adequacy proof. -/

def symSaturate (b : BuiltinFun) (args : List SymV) : SymR :=
  let appArgs := args.reverse
  match symPassThrough b appArgs with
  | some r => r
  | none =>
      let reified := appArgs.map reifyFO
      let nfErr := sOrs (reified.map Prod.fst)
      let r := symBuiltin b (reified.map Prod.snd)
      ⟨r.inc, sOr nfErr r.err, r.val⟩

/-! ## Pure `Case`-dispatch helpers (no fuel / recursion into the evaluator) -/

/-- Integer-tag dispatch: branch `i` taken when `tagE = i`; out of range → error.
This realises `constToTagAndFields` for `Integer` scrutinees (no fields). -/
def dispatchIntFrom (tagE : SExpr) : Nat → List SymR → SymR
  | _, []      => errR
  | i, r :: rs => symMerge (sEq tagE (.int (Int.ofNat i))) r (dispatchIntFrom tagE (i + 1) rs)

/-- Safe indexing into the evaluated alternatives. -/
def altOr (altRs : List SymR) (i : Nat) : SymR :=
  match altRs[i]? with | some r => r | none => errR

/-! ## The evaluator (mutual, fuel-structural — a clone of `bigEval`) -/

mutual
/-- Symbolic evaluation of `t` in environment `ρ`. Total; the three components of
the result are symbolic conditions (incomplete / error) and the value. -/
def symEval : Nat → SymEnv → Term → SymR
  | 0, _, _ => incR
  | _+1, ρ, .Var k =>
      match symLookup ρ k with
      | some v => ⟨.bool false, .bool false, v⟩
      | none   => errR
  | _+1, _, .Constant (c, _) => ⟨.bool false, .bool false, .fo (constToSExpr c)⟩
  | _+1, _, .Builtin b => ⟨.bool false, .bool false, .builtin b [] (expectedArgs b)⟩
  | _+1, ρ, .Lam _ body => ⟨.bool false, .bool false, .lam body ρ⟩
  | _+1, ρ, .Delay body => ⟨.bool false, .bool false, .delay body ρ⟩
  | n+1, ρ, .Apply f a =>
      let rf := symEval n ρ f
      let ra := symEval n ρ a
      let rap := symApply n rf.val ra.val
      symThen rf (symThen ra rap)
  | n+1, ρ, .Force t =>
      let rt := symEval n ρ t
      let rfo := symForce n rt.val
      symThen rt rfo
  | n+1, ρ, .Constr tag ms =>
      let rs := symEvalList n ρ ms
      symThenList rs (.constr tag (rs.map SymR.val))
  | n+1, ρ, .Case scrut alts =>
      let rsc := symEval n ρ scrut
      let rc := symCase n ρ alts rsc.val
      symThen rsc rc
  | _+1, _, .Error => errR
termination_by n _ t => (n, sizeOf t)

/-- Apply a value to an argument (β / builtin saturation / choice distribution). -/
def symApply : Nat → SymV → SymV → SymR
  | 0, _, _ => incR
  | n+1, .lam body ρ, va => symEval n (va :: ρ) body
  | _+1, .builtin b args ea, va =>
      match ea.head with
      | .argV => match ea.tail with
                 | some rest => ⟨.bool false, .bool false, .builtin b (va :: args) rest⟩
                 | none      => symSaturate b (va :: args)
      | .argQ => errR
  | n+1, .choice c x y, va => symMerge c (symApply n x va) (symApply n y va)
  | _+1, _, _ => errR
termination_by n _ _ => (n, 0)

/-- Force a value (delay / builtin force / choice distribution). -/
def symForce : Nat → SymV → SymR
  | 0, _ => incR
  | n+1, .delay body ρ => symEval n ρ body
  | _+1, .builtin b args ea =>
      match ea.head with
      | .argQ => match ea.tail with
                 | some rest => ⟨.bool false, .bool false, .builtin b args rest⟩
                 | none      => symSaturate b args
      | .argV => errR
  | n+1, .choice c x y => symMerge c (symForce n x) (symForce n y)
  | _+1, _ => errR
termination_by n _ => (n, 0)

/-- Evaluate a `Case` once the scrutinee value is known. -/
def symCase : Nat → SymEnv → List Term → SymV → SymR
  | 0, _, _, _ => incR
  | m+1, ρ, alts, .constr tag fields =>
      match alts[tag]? with
      | some alt =>
          let r := symEval m ρ alt
          let ra := symApplyList m r.val fields
          symThen r ra
      | none => errR
  | m+1, ρ, alts, .choice c x y => symMerge c (symCase m ρ alts x) (symCase m ρ alts y)
  | m+1, ρ, alts, .fo e =>
      let altRs := symEvalList m ρ alts
      -- Dispatch on every CEK-caseable constant flavour symbolically. Smart
      -- `sIsCon` folds this to a single arm when `e` has a known constructor.
      -- A symbolic SOP constructor remains indeterminate because its `VL` field
      -- count is unbounded; `compile`'s `.anyV` input excludes that case.
      let boolR :=
        if altRs.length > 2 then errR
        else symMerge (sAsBool e) (altOr altRs 1) (altOr altRs 0)
      let unitR :=
        if altRs.length > 1 then errR else altOr altRs 0
      let intR := dispatchIntFrom (sAsInt e) 0 altRs
      let listR :=
        if altRs.length > 2 then errR
        else
          let lE := sAsList e
          let r := altOr altRs 0
          let ra := symApplyList m r.val [.fo (VL.sHd lE), .fo (V.list (VL.sTl lE))]
          symMerge (VL.sIsNil lE) (altOr altRs 1) (symThen r ra)
      let dlistR :=
        if altRs.length > 2 then errR
        else
          let dl := V.sAsDL e
          let r := altOr altRs 0
          let ra := symApplyList m r.val
            [.fo (V.data (DL.sHd dl)), .fo (V.dlist (DL.sTl dl))]
          symMerge (DL.sIsNil dl) (altOr altRs 1) (symThen r ra)
      let pairR :=
        if altRs.length > 1 then errR
        else
          let r := altOr altRs 0
          symThen r (symApplyList m r.val [.fo (sFst e), .fo (sSnd e)])
      let pairDR :=
        if altRs.length > 1 then errR
        else
          let r := altOr altRs 0
          symThen r (symApplyList m r.val
            [.fo (V.data (V.sFstD e)), .fo (V.data (V.sSndD e))])
      symMerge (V.sIsCon "VBool" e) boolR
        (symMerge (V.sIsCon "VUnit" e) unitR
          (symMerge (V.sIsCon "VInt" e) intR
            (symMerge (V.sIsCon "VList" e) listR
              (symMerge (V.sIsCon "VDList" e) dlistR
                (symMerge (V.sIsCon "VPair" e) pairR
                  (symMerge (V.sIsCon "VPairD" e) pairDR
                    (symMerge (V.sIsCon "VConstr" e) incR errR)))))))
  | _+1, _, _, _ => errR
termination_by n _ _ _ => (n, 0)

/-- Evaluate constructor fields / case alternatives left-to-right. -/
def symEvalList : Nat → SymEnv → List Term → List SymR
  | _, _, []      => []
  | n, ρ, t :: ts => symEval n ρ t :: symEvalList n ρ ts
termination_by n _ ts => (n, sizeOf ts)

/-- Apply `vf` to a list of already-evaluated arguments (a `Case` branch to fields). -/
def symApplyList : Nat → SymV → List SymV → SymR
  | _, vf, []      => ⟨.bool false, .bool false, vf⟩
  | n, vf, a :: as =>
      let r := symApply n vf a
      let r2 := symApplyList n r.val as
      symThen r r2
termination_by n _ vs => (n, sizeOf vs)
end

/-! ## Symbolic inputs and the top-level driver -/

/-- The UPLC type of a symbolic input — determines its SMT sort and `V`-wrapper. -/
inductive InputKind where
  | integer | bool | bytestring | str | data | unit
  /-- `list(data)` — a `ConstDataList`. -/
  | dataList
  /-- `list(pair(data,data))` — a `ConstPairDataList` (Plutus maps). -/
  | pairDataList
  /-- A general `list(a)` — a `ConstList`. -/
  | list
  /-- An input of unknown/polymorphic `Const` type: a bare, well-formed `V`.
  SOP constructors are runtime values rather than `Const`s and are excluded. -/
  | anyV
deriving Repr, DecidableEq

/-- A declared symbolic input: a value to seed into the environment, the SMT
constant(s) to declare, and any well-formedness side-conditions. -/
structure SymInput where
  value : SymV
  consts : List SymConst
  sides  : List SExpr

/-- The byte-range side-condition for a symbolic `(Seq Int)` bytestring: every
element is in `0..255`. (A bounded quantifier over the sequence indices.) -/
private def byteRange (name : String) : SExpr :=
  .app "forall" [.atom "((i Int))",
    sImplies (sAnd (Op.le (.int 0) (.atom "i")) (Op.lt (.atom "i") (Seq.len (.atom name))))
             (sAnd (Op.le (.int 0) (Seq.nth (.atom name) (.atom "i")))
                   (Op.le (Seq.nth (.atom name) (.atom "i")) (.int 255)))]

/-- Recursive well-formedness predicates from the SMT preamble. They ensure raw
symbolic datatype inputs decode losslessly to the corresponding CEK constants. -/
private def wfData (e : SExpr) : SExpr := .app "moist_wf_d" [e]
private def wfDataList (e : SExpr) : SExpr := .app "moist_wf_dl" [e]
private def wfDataMap (e : SExpr) : SExpr := .app "moist_wf_dm" [e]
private def wfConstList (e : SExpr) : SExpr := .app "moist_const_vl" [e]
private def wfConstV (e : SExpr) : SExpr := .app "moist_const_v" [e]

/-- Build a symbolic input of the given kind. The raw SMT constant is declared at
its natural sort and wrapped in the matching `V` constructor. -/
def mkInput (name : String) : InputKind → SymInput
  | .integer    => ⟨.fo (V.int (.atom name)),  [⟨name, .int⟩],    []⟩
  | .bool       => ⟨.fo (V.bool (.atom name)), [⟨name, .bool⟩],   []⟩
  | .bytestring => ⟨.fo (V.bs (.atom name)),   [⟨name, .seqInt⟩], [byteRange name]⟩
  | .str        => ⟨.fo (V.str (.atom name)),  [⟨name, .string⟩], []⟩
  | .data       => ⟨.fo (V.data (.atom name)), [⟨name, .data⟩],   [wfData (.atom name)]⟩
  | .unit       => ⟨.fo V.unit, [], []⟩
  | .dataList     => ⟨.fo (V.dlist (.atom name)),  [⟨name, .dataList⟩], [wfDataList (.atom name)]⟩
  | .pairDataList => ⟨.fo (V.pdlist (.atom name)), [⟨name, .dataMap⟩], [wfDataMap (.atom name)]⟩
  | .list         => ⟨.fo (V.list (.atom name)),   [⟨name, .valList⟩], [wfConstList (.atom name)]⟩
  | .anyV       => ⟨.fo (.atom name), [⟨name, .val⟩], [wfConstV (.atom name)]⟩

/-- The result of compiling a UPLC term against a list of symbolic inputs. -/
structure Compiled where
  /-- The symbolic outcome of evaluating the term. -/
  result : SymR
  /-- The symbolic constants to solve for. -/
  consts : List SymConst
  /-- Well-formedness side-conditions on the inputs. -/
  sides  : List SExpr

/-- Compile a closed UPLC term `t` whose free variables are the given symbolic
`inputs` — `inputs[i]` is referenced by `Term.Var (i+1)` (de Bruijn, head = first
input). Evaluation uses `fuel` levels of unrolling. -/
def compile (fuel : Nat) (inputs : List (String × InputKind)) (t : Term) : Compiled :=
  let seeded := inputs.map (fun p => mkInput p.1 p.2)
  let env : SymEnv := seeded.map (·.value)
  { result := symEval fuel env t
    consts := seeded.flatMap (·.consts)
    sides  := seeded.flatMap (·.sides) }

/-! ## Goal builders — labelled assertions handed to the solver

Each goal is a list of `(label, assertion)`. The `¬inc` guard is always labelled
`"determinate"` so that, on a failed (`unsat`) query, `(get-unsat-core)` reveals
whether the fuel bound was the culprit: if `determinate` is in the core, the
result is bound-limited (raise the fuel); otherwise it is genuine. -/

/-- A goal: a function from the compiled result to labelled assertions. -/
abbrev Goal := SymR → List (String × SExpr)

/-- Assert the term completes (`¬inc`), does not error (`¬err`), and its
first-order value equals `target` (a `V`-sorted `SExpr`). -/
def goalEqualsV (r : SymR) (target : SExpr) : List (String × SExpr) :=
  let (nf, e) := reifyFO r.val
  [("determinate", sNot r.inc), ("no_error", sNot r.err),
   ("first_order", sNot nf), ("goal", sEq e target)]

/-- Assert the term returns the boolean `b`. -/
def goalReturnsBool (r : SymR) (b : Bool) : List (String × SExpr) := goalEqualsV r (V.bool (.bool b))

/-- Assert the term returns the integer `i`. -/
def goalReturnsInt (r : SymR) (i : Int) : List (String × SExpr) := goalEqualsV r (V.int (.int i))

/-- Assert the term **errors** (definitely, not merely indeterminate). -/
def goalErrors (r : SymR) : List (String × SExpr) := [("determinate", sNot r.inc), ("is_error", r.err)]

/-- Assert the term completes successfully (no error). -/
def goalSucceeds (r : SymR) : List (String × SExpr) := [("determinate", sNot r.inc), ("no_error", sNot r.err)]

/-- Diagnostic query: is **any** input indeterminate (its evaluation exceeds the
fuel)? `unsat` ⇒ the fuel covers every (well-formed) input, so all other results
are final; `sat` ⇒ some inputs are beyond the horizon, so a negative result there
is inconclusive — raise the fuel. -/
def goalIndeterminate (r : SymR) : List (String × SExpr) := [("indeterminate", r.inc)]

/-- Assemble the full SMT-LIB script for a compiled term and a goal. -/
def Compiled.script (c : Compiled) (goal : SymR → List (String × SExpr)) : SmtScript :=
  { consts := c.consts, side := c.sides, asserts := goal c.result }

/-- Emit runnable SMT-LIB v2 text for a compiled term and a goal. -/
def Compiled.toSMTLib (c : Compiled) (goal : SymR → List (String × SExpr)) : String :=
  (c.script goal).toSMTLib

end Moist.Symbolic
