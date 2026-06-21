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

## Builtin coverage (v1)

* **Precise SMT**: all `Integer` ops (incl. floor/trunc div & mod), `EqualsByteString`/
  `AppendByteString`/`ConsByteString`/`LengthOfByteString`/`IndexByteString`,
  `EqualsString`/`AppendString`, `IfThenElse`/`ChooseUnit`/`Trace`, `FstPair`/`SndPair`/
  `MkPairData`, `ChooseList`/`MkCons`/`HeadList`/`TailList`/`NullList`/`MkNil*`,
  `ChooseData` + all `Data` con/destructors + `EqualsData`.
* **Indeterminate (`inc = true`, no claim)**: every builtin the reference CEK
  (`Moist.CEK.evalBuiltin`) does **not** compute. This includes the cryptographic
  hashes (`Sha2_256`/…/`Ripemd_160`), signature checks, `SerializeData`, **all BLS**
  ops — which the CEK *errors* on (no `evalBuiltinConst` case), so modelling them as
  succeeding opaque UFs would be **unsound** (Stage-2 soundness: SMT-pass must imply
  CEK-pass). It also covers builtins the CEK *does* implement but we have not modelled
  precisely yet: `SliceByteString`, bytestring `<`/`≤`, utf8 encode/decode, bitwise
  batch-5, int↔bytestring conversions, `ExpModInteger`, batch-7. All of these make
  **no claim** (`inc = true`): sound but incomplete; widen coverage by giving them a
  precise arm (and, for the crypto/BLS family, a matching CEK denotation) as needed.

> Note: the opaque `uf_*` declarations and BLS element sorts remain in the SMT
> preamble (`Smt.lean`) — harmless, and they let a future "precise opaque" mode
> (CEK extended with trusted hash/BLS denotations) be switched back on.
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

/-- Data-kind discriminator `(is-DCon dd)`. -/
def dIs (con : String) (dd : SExpr) : SExpr := .app s!"is-{con}" [dd]
/-- Negated Data-kind discriminator. -/
def dNot (con : String) (dd : SExpr) : SExpr := sNot (dIs con dd)

/-- A definite-error result (declared early; reused by the list dispatcher). -/
def errR' : SymR := ⟨.bool false, .bool true, junk⟩
/-- An indeterminate result (out of fuel / unsupported / undetermined flavour). -/
def incR' : SymR := ⟨.bool true, .bool false, junk⟩

/-- Dispatch a list builtin across the two valid `Const` list flavours, exactly as
the CEK does: `VDList` (`ConstDataList`, elements projected as a `DL`) or `VList`
(`ConstList`, elements a `VL`); a *known* non-list variant errors; an *unknown*
flavour is indeterminate (no claim). -/
def onList (l : SExpr) (onD : SExpr → SymR) (onV : SExpr → SymR) : SymR :=
  match V.vConName l with
  | some "VDList" => onD (V.sAsDL l)
  | some "VList"  => onV (V.sAsList l)
  | none          => incR'
  | some _        => errR'

/-- A definite-error result. -/
def errR : SymR := ⟨.bool false, .bool true, junk⟩
/-- An indeterminate result (out of fuel / unsupported). -/
def incR : SymR := ⟨.bool true, .bool false, junk⟩
/-- A pure (non-erroring, complete) first-order result. -/
def okFO (e : SExpr) : SymR := ⟨.bool false, .bool false, .fo e⟩
/-- A first-order result that errors under `g`. -/
def foGuard (g e : SExpr) : SymR := ⟨.bool false, g, .fo e⟩

/-! ## Saturated builtin evaluation on first-order arguments

`symBuiltin b argEs` takes the builtin's value arguments **in application order**
as `V`-sorted `SExpr`s and returns the saturated result. `inc = true` marks an
unsupported builtin (no claim); otherwise `err` is the precise UPLC failure
condition (type mismatch, division by zero, head-of-nil, …). -/

open V (sAsInt sAsBool sAsBS sAsStr sAsData sAsList sFst sSnd)

def symBuiltin : BuiltinFun → List SExpr → SymR
  -- Integer arithmetic
  | .AddInteger,      [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.int (Op.add (sAsInt a) (sAsInt b)))
  | .SubtractInteger, [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.int (Op.sub (sAsInt a) (sAsInt b)))
  | .MultiplyInteger, [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.int (Op.mul (sAsInt a) (sAsInt b)))
  | .DivideInteger,   [a, b] =>
      foGuard (sOrs [gInt a, gInt b, sEq (sAsInt b) (.int 0)]) (V.int (.app "moist_fdiv" [sAsInt a, sAsInt b]))
  | .ModInteger,      [a, b] =>
      foGuard (sOrs [gInt a, gInt b, sEq (sAsInt b) (.int 0)]) (V.int (.app "moist_fmod" [sAsInt a, sAsInt b]))
  | .QuotientInteger, [a, b] =>
      foGuard (sOrs [gInt a, gInt b, sEq (sAsInt b) (.int 0)]) (V.int (.app "moist_qdiv" [sAsInt a, sAsInt b]))
  | .RemainderInteger,[a, b] =>
      foGuard (sOrs [gInt a, gInt b, sEq (sAsInt b) (.int 0)]) (V.int (.app "moist_qrem" [sAsInt a, sAsInt b]))
  -- Integer comparison
  | .EqualsInteger,         [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.bool (sEq (sAsInt a) (sAsInt b)))
  | .LessThanInteger,       [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.bool (Op.lt (sAsInt a) (sAsInt b)))
  | .LessThanEqualsInteger, [a, b] => foGuard (sOr (gInt a) (gInt b)) (V.bool (Op.le (sAsInt a) (sAsInt b)))
  -- ByteString
  | .EqualsByteString, [a, b] => foGuard (sOr (gBS a) (gBS b)) (V.bool (sEq (sAsBS a) (sAsBS b)))
  | .AppendByteString, [a, b] => foGuard (sOr (gBS a) (gBS b)) (V.bs (Seq.append (sAsBS a) (sAsBS b)))
  | .ConsByteString,   [n, bs] =>
      foGuard (sOrs [gInt n, gBS bs, Op.lt (sAsInt n) (.int 0), Op.lt (.int 255) (sAsInt n)])
              (V.bs (Seq.append (Seq.unit (sAsInt n)) (sAsBS bs)))
  | .LengthOfByteString, [bs] => foGuard (gBS bs) (V.int (Seq.len (sAsBS bs)))
  | .IndexByteString,    [bs, idx] =>
      foGuard (sOrs [gBS bs, gInt idx, Op.lt (sAsInt idx) (.int 0), Op.le (Seq.len (sAsBS bs)) (sAsInt idx)])
              (V.int (Seq.nth (sAsBS bs) (sAsInt idx)))
  -- String
  | .EqualsString, [a, b] => foGuard (sOr (gStr a) (gStr b)) (V.bool (sEq (sAsStr a) (sAsStr b)))
  | .AppendString, [a, b] => foGuard (sOr (gStr a) (gStr b)) (V.str (.app "str.++" [sAsStr a, sAsStr b]))
  -- Pairs (flavour-faithful: VPairD returns the projected Data; VPair the raw const)
  | .FstPair, [p] =>
      match V.vConName p with
      | some "VPairD" => okFO (V.data (V.sFstD p))
      | some "VPair"  => okFO (sFst p)
      | none => incR | some _ => errR
  | .SndPair, [p] =>
      match V.vConName p with
      | some "VPairD" => okFO (V.data (V.sSndD p))
      | some "VPair"  => okFO (sSnd p)
      | none => incR | some _ => errR
  | .MkPairData, [a, b] => foGuard (sOr (gData a) (gData b)) (V.pairD (sAsData a) (sAsData b))
  -- Lists (both ConstDataList = VDList and ConstList = VList)
  | .HeadList, [l] => onList l (fun dl => foGuard (DL.sIsNil dl) (V.data (DL.sHd dl)))
                               (fun vl => foGuard (VL.sIsNil vl) (VL.sHd vl))
  | .TailList, [l] => onList l (fun dl => foGuard (DL.sIsNil dl) (V.dlist (DL.sTl dl)))
                               (fun vl => foGuard (VL.sIsNil vl) (V.list (VL.sTl vl)))
  | .NullList, [l] => onList l (fun dl => okFO (V.bool (DL.sIsNil dl)))
                               (fun vl => okFO (V.bool (VL.sIsNil vl)))
  -- MkCons: onto a data-list the head MUST be Data (else CEK errors); onto a
  -- general list any value conses; onto any other flavour it errors.
  | .MkCons, [h, l] =>
      match V.vConName l with
      | some "VDList" => foGuard (gData h) (V.dlist (DL.cons (sAsData h) (V.sAsDL l)))
      | some "VList"  => okFO (V.list (VL.cons h (V.sAsList l)))
      | none => incR | some _ => errR
  | .MkNilData,     [u] => foGuard (gUnit u) (V.dlist DL.nil)
  | .MkNilPairData, [u] => foGuard (gUnit u) (V.pdlist DM.nil)
  -- Data constructors (require the exact source flavour, like evalBuiltinConst)
  | .ConstrData, [tag, fields] =>
      match V.vConName fields with
      | some "VDList" => foGuard (gInt tag) (V.data (D.constr (sAsInt tag) (V.sAsDL fields)))
      | none => incR | some _ => errR
  | .IData,    [i] => foGuard (gInt i)  (V.data (D.i (sAsInt i)))
  | .BData,    [b] => foGuard (gBS b)   (V.data (D.b (sAsBS b)))
  | .ListData, [l] =>
      match V.vConName l with
      | some "VDList" => okFO (V.data (D.list (V.sAsDL l)))
      | none => incR | some _ => errR
  | .MapData,  [l] =>
      match V.vConName l with
      | some "VPDList" => okFO (V.data (D.map (V.sAsDM l)))
      | none => incR | some _ => errR
  -- Data destructors
  | .UnConstrData, [d] =>
      foGuard (sOr (gData d) (dNot "DConstr" (sAsData d)))
              (V.pairD (D.i (D.dcTag (sAsData d))) (D.list (D.dcArgs (sAsData d))))
  | .UnIData,    [d] => foGuard (sOr (gData d) (dNot "DI" (sAsData d)))    (V.int (D.diVal (sAsData d)))
  | .UnBData,    [d] => foGuard (sOr (gData d) (dNot "DB" (sAsData d)))    (V.bs (D.dbVal (sAsData d)))
  | .UnListData, [d] => foGuard (sOr (gData d) (dNot "DList" (sAsData d))) (V.dlist (D.dlElems (sAsData d)))
  | .UnMapData,  [d] => foGuard (sOr (gData d) (dNot "DMap" (sAsData d)))  (V.pdlist (D.dmEntries (sAsData d)))
  | .EqualsData, [a, b] => foGuard (sOr (gData a) (gData b)) (V.bool (sEq (sAsData a) (sAsData b)))
  -- Indeterminate / unsupported (sound: no claim). This includes every builtin the
  -- reference CEK (`evalBuiltin`) does not compute — the cryptographic hashes,
  -- signature checks, `SerializeData`, and all BLS operations (the CEK *errors* on
  -- them), as well as the not-yet-modelled `SliceByteString`, bytestring `<`/`≤`,
  -- utf8, bitwise, int↔bytestring, `ExpModInteger`, and batch-7 builtins.
  | _, _ => incR

/-! ## Saturating a builtin from its accumulated (reversed) value arguments

Pass-through builtins keep their non-condition arguments *as values* (they may be
higher-order: a `Case`/`if` branch can be a closure). Everything else reifies its
arguments to first order and dispatches to `symBuiltin`. -/

def symSaturate (b : BuiltinFun) (args : List SymV) : SymR :=
  match b, args with
  -- IfThenElse [elseV, thenV, condV] (args reversed): branch on the condition's V-Bool.
  | .IfThenElse, [elseV, thenV, condV] =>
      let (cNf, cE) := reifyFO condV
      ⟨.bool false, sOrs [cNf, gBool cE], mergeVal (sAsBool cE) thenV elseV⟩
  -- ChooseUnit [result, unitV]
  | .ChooseUnit, [result, unitV] =>
      let (uNf, uE) := reifyFO unitV
      ⟨.bool false, sOrs [uNf, gUnit uE], result⟩
  -- Trace [result, strV]
  | .Trace, [result, strV] =>
      let (sNf, sE) := reifyFO strV
      ⟨.bool false, sOrs [sNf, gStr sE], result⟩
  -- ChooseData [bCase, iCase, listCase, mapCase, constrCase, dataV]
  | .ChooseData, [bCase, iCase, listCase, mapCase, constrCase, dataV] =>
      let (dNf, dE) := reifyFO dataV
      let dd := sAsData dE
      let chosen :=
        mergeVal (dIs "DConstr" dd) constrCase
          (mergeVal (dIs "DMap" dd) mapCase
            (mergeVal (dIs "DList" dd) listCase
              (mergeVal (dIs "DI" dd) iCase bCase)))
      ⟨.bool false, sOrs [dNf, gData dE], chosen⟩
  -- ChooseList [consCase, nilCase, listV] — works on VDList and VList only
  | .ChooseList, [consCase, nilCase, listV] =>
      let (lNf, lE) := reifyFO listV
      match V.vConName lE with
      | some "VDList" => ⟨.bool false, lNf, mergeVal (DL.sIsNil (V.sAsDL lE)) nilCase consCase⟩
      | some "VList"  => ⟨.bool false, lNf, mergeVal (VL.sIsNil (V.sAsList lE)) nilCase consCase⟩
      | none          => incR
      | some _        => errR
  -- everything else: reify args to first order, dispatch to symBuiltin
  | _, _ =>
      let reified := (args.reverse).map reifyFO
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
      ⟨sOrs [rf.inc, ra.inc, rap.inc], sOrs [rf.err, ra.err, rap.err], rap.val⟩
  | n+1, ρ, .Force t =>
      let rt := symEval n ρ t
      let rfo := symForce n rt.val
      ⟨sOr rt.inc rfo.inc, sOr rt.err rfo.err, rfo.val⟩
  | n+1, ρ, .Constr tag ms =>
      let rs := symEvalList n ρ ms
      ⟨sOrs (rs.map SymR.inc), sOrs (rs.map SymR.err), .constr tag (rs.map SymR.val)⟩
  | n+1, ρ, .Case scrut alts =>
      let rsc := symEval n ρ scrut
      let rc := symCase n ρ alts rsc.val
      ⟨sOr rsc.inc rc.inc, sOr rsc.err rc.err, rc.val⟩
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
          ⟨sOr r.inc ra.inc, sOr r.err ra.err, ra.val⟩
      | none => errR
  | m+1, ρ, alts, .choice c x y => symMerge c (symCase m ρ alts x) (symCase m ρ alts y)
  | m+1, ρ, alts, .fo e =>
      let altRs := symEvalList m ρ alts
      -- apply branch `i` (0 fields) — for Bool/Unit/Integer scrutinees
      match V.vConName e with
      | some "VBool" =>   -- false→0, true→1 (2 constructors)
          if altRs.length > 2 then errR
          else symMerge (sAsBool e) (altOr altRs 1) (altOr altRs 0)
      | some "VUnit" =>   -- 1 constructor, tag 0
          if altRs.length > 1 then errR else altOr altRs 0
      | some "VInt" => dispatchIntFrom (sAsInt e) 0 altRs
      | some "VList" =>   -- ConstList: nil→1, cons→0 [head (raw), VList tail]
          if altRs.length > 2 then errR
          else
            let lE := sAsList e
            let consR :=
              let r := altOr altRs 0
              let ra := symApplyList m r.val [.fo (VL.sHd lE), .fo (V.list (VL.sTl lE))]
              ⟨sOr r.inc ra.inc, sOr r.err ra.err, ra.val⟩
            symMerge (VL.sIsNil lE) (altOr altRs 1) consR
      | some "VDList" =>  -- ConstDataList: nil→1, cons→0 [VData head, VDList tail]
          if altRs.length > 2 then errR
          else
            let dl := V.sAsDL e
            let consR :=
              let r := altOr altRs 0
              let ra := symApplyList m r.val [.fo (V.data (DL.sHd dl)), .fo (V.dlist (DL.sTl dl))]
              ⟨sOr r.inc ra.inc, sOr r.err ra.err, ra.val⟩
            symMerge (DL.sIsNil dl) (altOr altRs 1) consR
      | some "VPair" =>   -- Pair: 1 constructor, tag 0, fields [fst, snd]
          if altRs.length > 1 then errR
          else
            let r := altOr altRs 0
            let ra := symApplyList m r.val [.fo (sFst e), .fo (sSnd e)]
            ⟨sOr r.inc ra.inc, sOr r.err ra.err, ra.val⟩
      | some "VPairD" =>  -- PairData: 1 constructor, fields [VData a, VData b]
          if altRs.length > 1 then errR
          else
            let r := altOr altRs 0
            let ra := symApplyList m r.val [.fo (V.data (V.sFstD e)), .fo (V.data (V.sSndD e))]
            ⟨sOr r.inc ra.inc, sOr r.err ra.err, ra.val⟩
      | none   => incR   -- unknown variant: no claim
      | some _ => errR   -- known non-`case`-able variant (ByteString/String/Data/…): CEK errors
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
      ⟨sOr r.inc r2.inc, sOr r.err r2.err, r2.val⟩
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
  /-- An input of unknown/polymorphic type: a bare `V` constant. -/
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

/-- Build a symbolic input of the given kind. The raw SMT constant is declared at
its natural sort and wrapped in the matching `V` constructor. -/
def mkInput (name : String) : InputKind → SymInput
  | .integer    => ⟨.fo (V.int (.atom name)),  [⟨name, .int⟩],    []⟩
  | .bool       => ⟨.fo (V.bool (.atom name)), [⟨name, .bool⟩],   []⟩
  | .bytestring => ⟨.fo (V.bs (.atom name)),   [⟨name, .seqInt⟩], [byteRange name]⟩
  | .str        => ⟨.fo (V.str (.atom name)),  [⟨name, .string⟩], []⟩
  | .data       => ⟨.fo (V.data (.atom name)), [⟨name, .data⟩],   []⟩
  | .unit       => ⟨.fo V.unit, [], []⟩
  | .dataList     => ⟨.fo (V.dlist (.atom name)),  [⟨name, .dataList⟩], []⟩
  | .pairDataList => ⟨.fo (V.pdlist (.atom name)), [⟨name, .dataMap⟩], []⟩
  | .list         => ⟨.fo (V.list (.atom name)),   [⟨name, .valList⟩], []⟩
  | .anyV       => ⟨.fo (.atom name), [⟨name, .val⟩], []⟩

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
