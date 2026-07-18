import Moist.SMT.Compiler.UPLC.Projection
import Moist.SMT.Compiler.UPLC.Compaction
import Moist.SMT.Compiler.GroundBuiltin

/-!
# UPLC compiler symbolic evaluation

Fueled symbolic evaluation, the CEK-backed ground builtin path, and symbolic
builtin lowering.  This is executable compiler code; its simulation proofs
remain in the soundness modules.
-/

namespace Moist.SMT.UPLC

open Moist.Plutus.Term
open Moist.Plutus (Data ByteString)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs)

/-! ## CEK-backed ground evaluation

`SymConst` records an SMT expression, so being in the `.const` constructor does
not by itself mean an expression is ground.  This recognizer is deliberately
strict: it succeeds only for literal syntax emitted from a UPLC constant.
When every saturated argument is literal, use the isolated executable ground
builtin adapter as the single source of truth and re-embed its result.  The
adapter delegates to CEK without duplicating builtin semantics.  This both
avoids unnecessary SMT and prevents the ground case from drifting away from
CEK while a symbolic encoding is optimized.
-/

def symValLiteral? : SymVal → Option Const
  | .const (.integer (.int i)) => some (.Integer i)
  | .const (.bytes (.bytes bs)) => some (.ByteString bs)
  | .const (.string (.str s)) => some (.String s)
  | .const (.bool (.bool b)) => some (.Bool b)
  | .const .unit => some .Unit
  | .const (.data (.dataLit d)) => some (.Data d)
  | .const (.constList (.constListLit xs) _) => some (.ConstList xs)
  | .const (.dataList (.dataListLit xs)) => some (.ConstDataList xs)
  | .const (.pairDataList (.dataPairListLit xs)) => some (.ConstPairDataList xs)
  | .const (.pairData (.dataLit a) (.dataLit b)) => some (.PairData (a, b))
  | .const (.array (.constListLit xs)) => some (.ConstArray xs)
  | .pair a b => do
      let ca ← symValLiteral? a
      let cb ← symValLiteral? b
      some (.Pair (ca, cb))
  | _ => none

def evalBuiltinStatic? (b : BuiltinFun) (args : List SymVal) : Option (List Outcome) := do
  let constArgs ← args.mapM symValLiteral?
  match Moist.SMT.Compiler.GroundBuiltin.evaluateStackArguments b constArgs with
  | .value c => some (ok (constLiteral c))
  | .error => some err
  | .deferred => none

def staticOrSymbolic (b : BuiltinFun) (args : List SymVal)
    (symbolic : Unit → List Outcome) : List Outcome :=
  match evalBuiltinStatic? b args with
  | some outs => outs
  | none => symbolic ()

def lookupEnv : List SymVal → Nat → Option SymVal
  | [], _ => none
  | _, 0 => none
  | v :: _, 1 => some v
  | _ :: ρ, n + 1 => lookupEnv ρ n

def extendEnv (ρ : List SymVal) (v : SymVal) : List SymVal := v :: ρ

def branchOutcomes (alts : List (SExpr × List Outcome)) (extraErrors : List SExpr := []) : List Outcome :=
  alts.flatMap (fun (g, os) => mapPc g os) ++ extraErrors.map Outcome.error

def enumerate (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 xs

def fieldFromValList (xs : SExpr) : SymVal := .dyn (.app "vhead" [xs])
def tailFromValList (xs : SExpr) : SymVal :=
  .const (.constList (.app "vtail" [xs]) .unknown)
def fieldFromDataList (xs : SExpr) : SymVal := .const (.data (.app "dhead" [xs]))
def tailFromDataList (xs : SExpr) : SymVal := .const (.dataList (.app "dtail" [xs]))

def divisionGuard (b : SExpr) : SExpr := SExpr.ne b (.int 0)

def nonnegGuard (x : SExpr) : SExpr := SExpr.ge x (.int 0)

mutual
  def evalSym : Nat → List SymVal → Term → List Outcome
    | 0, _, _ => timeout
    | _ + 1, ρ, .Var k =>
        match lookupEnv ρ k with
        | some v => ok v
        | none => err
    | _ + 1, _, .Constant (c, _) => ok (constLiteral c)
    | _ + 1, _, .Builtin b => ok (.builtin b [] (expectedArgs b))
    | _ + 1, ρ, .Lam _ body => ok (.lam body ρ)
    | _ + 1, ρ, .Delay body => ok (.delay body ρ)
    | n + 1, ρ, .Apply f a =>
        -- An application is a first-order join after a symbolic function
        -- choice.  Compact its result before an enclosing application can
        -- multiply every function branch by every argument branch.
        compactOutcomes <| bindOut (evalSym n ρ f) fun vf =>
          bindOut (evalSym n ρ a) fun va =>
          applySym n vf va
    | n + 1, ρ, .Force t =>
        compactOutcomes <| bindOut (evalSym n ρ t) fun vt =>
          forceSym n vt
    | n + 1, ρ, .Constr tag fields =>
        bindOut (evalListSym n ρ fields) fun vals =>
          match vals with
          | .constr (.int (-1)) vs => ok (.constr (.int (Int.ofNat tag)) vs)
          | _ => err
    | n + 1, ρ, .Case scrut alts =>
        -- `Case` is a semantic join point just like forcing a lazy branch.
        -- Compact first-order alternatives before a surrounding continuation
        -- can duplicate once for every constructor/tag alternative.
        compactOutcomes <| bindOut (evalSym n ρ scrut) fun v =>
          caseSym n ρ v alts
    | _ + 1, _, .Error => err
  termination_by n _ t => (n, (1, sizeOf t))

  def evalListSym : Nat → List SymVal → List Term → List Outcome
    | _, _, [] => ok (.constr (.int (-1)) [])
    | n, ρ, t :: ts =>
        bindOut (evalSym n ρ t) fun v =>
        bindOut (evalListSym n ρ ts) fun rest =>
          match rest with
          | .constr (.int (-1)) vs => ok (.constr (.int (-1)) (v :: vs))
          | _ => err
  termination_by n _ ts => (n, (2, sizeOf ts))

  def applySym : Nat → SymVal → SymVal → List Outcome
    | 0, _, _ => timeout
    | n + 1, .lam body ρ, va => evalSym n (extendEnv ρ va) body
    | _ + 1, .builtin b args ea, va =>
        match ea.head with
        | .argV =>
            match ea.tail with
            | some rest => ok (.builtin b (va :: args) rest)
            | none => evalBuiltinSaturated b (va :: args)
        | .argQ => err
    | _ + 1, _, _ => err
  termination_by n _ _ => (n, (0, 0))

  def forceSym : Nat → SymVal → List Outcome
    | 0, _ => timeout
    | n + 1, .delay body ρ => evalSym n ρ body
    | _ + 1, .builtin b args ea =>
        match ea.head with
        | .argQ =>
            match ea.tail with
            | some rest => ok (.builtin b args rest)
            | none => evalBuiltinSaturated b args
        | .argV => err
    | _ + 1, _ => err
  termination_by n _ => (n, (0, 0))

  def applyListSym : Nat → SymVal → List SymVal → List Outcome
    | _, vf, [] => ok vf
    | n, vf, a :: as =>
        bindOut (applySym n vf a) fun vf' =>
        applyListSym n vf' as
  termination_by n _ vs => (n, (2, sizeOf vs))

  def applyValListSym : Nat → SymVal → SExpr → List Outcome
    | 0, _, _ => timeout
    | n + 1, vf, xs =>
        let nilBranch := (SExpr.isCtor "VNil" xs, ok vf)
        let consBranch :=
          (SExpr.not (SExpr.isCtor "VNil" xs),
            bindOut (applySym n vf (.dyn (.app "vhead" [xs]))) fun vf' =>
              applyValListSym n vf' (.app "vtail" [xs]))
        branchOutcomes [nilBranch, consBranch]
  termination_by n _ _ => (n, (2, 0))

  def caseSym : Nat → List SymVal → SymVal → List Term → List Outcome
    | n, ρ, .constr tag fields, alts =>
        let branches := (enumerate alts).map fun (i, alt) =>
          (SExpr.eq tag (.int (Int.ofNat i)),
            bindOut (evalSym n ρ alt) fun vAlt => applyListSym n vAlt fields)
        let covered := SExpr.any ((enumerate alts).map fun (i, _) => SExpr.eq tag (.int (Int.ofNat i)))
        branchOutcomes branches [SExpr.not covered]
    | n, ρ, .const (.bool b), alts =>
        let tag := SExpr.ite b (.int 1) (.int 0)
        if alts.length > 2 then err
        else
          let branches := (enumerate alts).map fun (i, alt) =>
            (SExpr.eq tag (.int (Int.ofNat i)), evalSym n ρ alt)
          branchOutcomes branches [SExpr.not (SExpr.any ((enumerate alts).map fun (i, _) => SExpr.eq tag (.int (Int.ofNat i))))]
    | n, ρ, .const .unit, alts =>
        if alts.length > 1 then err
        else match alts[0]? with
          | some alt => evalSym n ρ alt
          | none => err
    | n, ρ, .const (.integer x), alts =>
        let branches := (enumerate alts).map fun (i, alt) =>
          (SExpr.and (nonnegGuard x) (SExpr.eq x (.int (Int.ofNat i))), evalSym n ρ alt)
        let covered := SExpr.and (nonnegGuard x)
          (SExpr.any ((enumerate alts).map fun (i, _) => SExpr.eq x (.int (Int.ofNat i))))
        branchOutcomes branches [SExpr.not covered]
    | n, ρ, .const (.constList xs _), alts =>
        if alts.length > 2 then err
        else
          let nilBranch := match alts[1]? with
            | some alt => [(SExpr.isCtor "VNil" xs, evalSym n ρ alt)]
            | none => []
          let consBranch := match alts[0]? with
            | some alt =>
                [(SExpr.not (SExpr.isCtor "VNil" xs),
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [fieldFromValList xs, tailFromValList xs])]
            | none => []
          let branches := consBranch ++ nilBranch
          branchOutcomes branches [SExpr.not (SExpr.any (branches.map Prod.fst))]
    | n, ρ, .const (.dataList xs), alts =>
        if alts.length > 2 then err
        else
          let nilBranch := match alts[1]? with
            | some alt => [(SExpr.isCtor "DNil" xs, evalSym n ρ alt)]
            | none => []
          let consBranch := match alts[0]? with
            | some alt =>
                [(SExpr.not (SExpr.isCtor "DNil" xs),
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [fieldFromDataList xs, tailFromDataList xs])]
            | none => []
          let branches := consBranch ++ nilBranch
          branchOutcomes branches [SExpr.not (SExpr.any (branches.map Prod.fst))]
    | n, ρ, .pair a b, alts =>
        if alts.length > 1 then err
        else match alts[0]? with
          | some alt => bindOut (evalSym n ρ alt) fun vAlt => applyListSym n vAlt [a, b]
          | none => err
    | n, ρ, .const (.pairData a b), alts =>
        if alts.length > 1 then err
        else match alts[0]? with
          | some alt =>
              bindOut (evalSym n ρ alt) fun vAlt =>
                applyListSym n vAlt [.const (.data a), .const (.data b)]
          | none => err
    | n, ρ, .dyn v, alts =>
        let enum := enumerate alts
        let tagCovered (tag : SExpr) : SExpr :=
          SExpr.any (enum.map fun (i, _) => SExpr.eq tag (.int (Int.ofNat i)))
        let boolTag := SExpr.ite (.app "unVBool" [v]) (.int 1) (.int 0)
        let boolBranches :=
          if alts.length > 2 then []
          else enum.map fun (i, alt) =>
            (SExpr.all [SExpr.isCtor "VBool" v, SExpr.eq boolTag (.int (Int.ofNat i))], evalSym n ρ alt)
        let boolError :=
          if alts.length > 2 then SExpr.isCtor "VBool" v
          else SExpr.and (SExpr.isCtor "VBool" v) (SExpr.not (tagCovered boolTag))
        let unitBranches :=
          if alts.length > 1 then []
          else match alts[0]? with
            | some alt => [(SExpr.isCtor "VUnit" v, evalSym n ρ alt)]
            | none => []
        let unitError :=
          if alts.length > 1 then SExpr.isCtor "VUnit" v
          else SExpr.and (SExpr.isCtor "VUnit" v) (SExpr.not (SExpr.any (unitBranches.map Prod.fst)))
        let intVal := .app "unVInt" [v]
        let intBranches := enum.map fun (i, alt) =>
          (SExpr.all [SExpr.isCtor "VInt" v, nonnegGuard intVal, SExpr.eq intVal (.int (Int.ofNat i))], evalSym n ρ alt)
        let intError := SExpr.and (SExpr.isCtor "VInt" v)
          (SExpr.not (SExpr.and (nonnegGuard intVal) (tagCovered intVal)))
        let listVal := .app "unVList" [v]
        let listBranches :=
          if alts.length > 2 then []
          else
            let nilBranch := match alts[1]? with
              | some alt => [(SExpr.all [SExpr.isCtor "VList" v, SExpr.isCtor "VNil" listVal], evalSym n ρ alt)]
              | none => []
            let consBranch := match alts[0]? with
              | some alt =>
                  [(SExpr.all [SExpr.isCtor "VList" v, SExpr.not (SExpr.isCtor "VNil" listVal)],
                    bindOut (evalSym n ρ alt) fun vAlt =>
                      applyListSym n vAlt [fieldFromValList listVal, tailFromValList listVal])]
              | none => []
            consBranch ++ nilBranch
        let listError :=
          if alts.length > 2 then SExpr.isCtor "VList" v
          else SExpr.and (SExpr.isCtor "VList" v) (SExpr.not (SExpr.any (listBranches.map Prod.fst)))
        let dataListVal := .app "unVDataList" [v]
        let dataListBranches :=
          if alts.length > 2 then []
          else
            let nilBranch := match alts[1]? with
              | some alt => [(SExpr.all [SExpr.isCtor "VDataList" v, SExpr.isCtor "DNil" dataListVal], evalSym n ρ alt)]
              | none => []
            let consBranch := match alts[0]? with
              | some alt =>
                  [(SExpr.all [SExpr.isCtor "VDataList" v, SExpr.not (SExpr.isCtor "DNil" dataListVal)],
                    bindOut (evalSym n ρ alt) fun vAlt =>
                      applyListSym n vAlt [fieldFromDataList dataListVal, tailFromDataList dataListVal])]
              | none => []
            consBranch ++ nilBranch
        let dataListError :=
          if alts.length > 2 then SExpr.isCtor "VDataList" v
          else SExpr.and (SExpr.isCtor "VDataList" v) (SExpr.not (SExpr.any (dataListBranches.map Prod.fst)))
        let pairBranches :=
          if alts.length > 1 then []
          else match alts[0]? with
            | some alt =>
                [(SExpr.isCtor "VPair" v,
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [.dyn (.app "vfst" [v]), .dyn (.app "vsnd" [v])])]
            | none => []
        let pairError :=
          if alts.length > 1 then SExpr.isCtor "VPair" v
          else SExpr.and (SExpr.isCtor "VPair" v) (SExpr.not (SExpr.any (pairBranches.map Prod.fst)))
        let pairDataBranches :=
          if alts.length > 1 then []
          else match alts[0]? with
            | some alt =>
                [(SExpr.isCtor "VPairData" v,
                  bindOut (evalSym n ρ alt) fun vAlt =>
                    applyListSym n vAlt [.const (.data (.app "pdfst" [v])), .const (.data (.app "pdsnd" [v]))])]
            | none => []
        let pairDataError :=
          if alts.length > 1 then SExpr.isCtor "VPairData" v
          else SExpr.and (SExpr.isCtor "VPairData" v) (SExpr.not (SExpr.any (pairDataBranches.map Prod.fst)))
        let constrTag := .app "vConstrTag" [v]
        let constrBranches := enum.map fun (i, alt) =>
          (SExpr.all [SExpr.isCtor "VConstr" v, SExpr.eq constrTag (.int (Int.ofNat i))],
            bindOut (evalSym n ρ alt) fun vAlt =>
              applyValListSym n vAlt (.app "vConstrFields" [v]))
        let constrError := SExpr.and (SExpr.isCtor "VConstr" v) (SExpr.not (tagCovered constrTag))
        let unsupportedError := SExpr.any [
          SExpr.isCtor "VBytes" v, SExpr.isCtor "VString" v, SExpr.isCtor "VData" v,
          SExpr.isCtor "VPairDataList" v, SExpr.isCtor "VArray" v, SExpr.isCtor "VG1" v,
          SExpr.isCtor "VG2" v, SExpr.isCtor "VMlResult" v]
        let branches := boolBranches ++ unitBranches ++ intBranches ++ listBranches ++
          dataListBranches ++ pairBranches ++ pairDataBranches ++ constrBranches
        branchOutcomes branches [
          boolError, unitError, intError, listError, dataListError,
          pairError, pairDataError, constrError, unsupportedError]
    | _, _, _, _ => err
  termination_by n _ _ _ => (n, (3, 0))

  def evalBuiltinSym : BuiltinFun → List SymVal → List Outcome
    | .AddInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.intAdd (asInt a) (asInt b)) .integer
    | .SubtractInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.intSub (asInt a) (asInt b)) .integer
    | .MultiplyInteger, [b, a] =>
        checkedConst (Proj.map2 SExpr.intMul (asInt a) (asInt b)) .integer
    | .DivideInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_div" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .QuotientInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_tdiv" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .RemainderInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_tmod" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .ModInteger, [b, a] =>
        let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
        checked2 p fun (a, b) =>
          [.ok (divisionGuard b) (.const (.integer (.app "uplc_mod" [a, b]))),
           .error (SExpr.not (divisionGuard b))]
    | .EqualsInteger, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asInt a) (asInt b))
    | .LessThanInteger, [b, a] => checkedBool (Proj.map2 SExpr.lt (asInt a) (asInt b))
    | .LessThanEqualsInteger, [b, a] => checkedBool (Proj.map2 SExpr.le (asInt a) (asInt b))

    | .AppendByteString, [b, a] => checkedConst (Proj.map2 SExpr.seqAppend (asBytes a) (asBytes b)) .bytes
    | .ConsByteString, [bs, n] =>
        let p := Proj.map2 (fun n bs => (n, bs)) (asInt n) (asBytes bs)
        checked2 p fun (n, bs) =>
          let inByte := SExpr.and (SExpr.ge n (.int 0)) (SExpr.le n (.int 255))
          [.ok inByte (.const (.bytes (SExpr.seqAppend (SExpr.seqUnit n) bs))),
           .error (SExpr.not inByte)]
    | .SliceByteString, [bs, len, start] =>
        let p := Proj.map3 (fun start len bs => (start, len, bs)) (asInt start) (asInt len) (asBytes bs)
        checkedConst (p.map fun (start, len, bs) =>
          let s := SExpr.ite (SExpr.lt start (.int 0)) (.int 0) start
          let l := SExpr.ite (SExpr.lt len (.int 0)) (.int 0) len
          SExpr.seqExtract bs s l) .bytes
    | .LengthOfByteString, [bs] => checkedConst ((asBytes bs).map SExpr.seqLen) .integer
    | .IndexByteString, [idx, bs] =>
        let p := Proj.map2 (fun bs idx => (bs, idx)) (asBytes bs) (asInt idx)
        checked2 p fun (bs, idx) =>
          let inRange := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (SExpr.seqLen bs))
          [.ok inRange (.const (.integer (SExpr.seqNth bs idx))), .error (SExpr.not inRange)]
    | .EqualsByteString, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asBytes a) (asBytes b))
    | .LessThanByteString, [b, a] => checkedBool (Proj.map2 (fun a b => .app "bytes_lt" [a, b]) (asBytes a) (asBytes b))
    | .LessThanEqualsByteString, [b, a] => checkedBool (Proj.map2 (fun a b => .app "bytes_le" [a, b]) (asBytes a) (asBytes b))

    | .Sha2_256, _ => timeout
    | .Sha3_256, _ => timeout
    | .Blake2b_256, _ => timeout
    | .VerifyEd25519Signature, _ => timeout

    | .AppendString, [b, a] => checkedConst (Proj.map2 SExpr.strAppend (asString a) (asString b)) .string
    | .EqualsString, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asString a) (asString b))
    | .EncodeUtf8, [s] => checkedConst ((asString s).map fun x => .app "uplc_encodeUtf8" [x]) .bytes
    | .DecodeUtf8, [bs] =>
        checked2 (asBytes bs) fun b =>
          [.ok (.app "valid_utf8" [b]) (.const (.string (.app "uplc_decodeUtf8" [b]))),
           .error (SExpr.not (.app "valid_utf8" [b]))]

    | .IfThenElse, [elseV, thenV, cond] =>
        let c := asBool cond
        [.ok (SExpr.and c.guard c.val) thenV,
         .ok (SExpr.and c.guard (SExpr.not c.val)) elseV,
         .error (SExpr.not c.guard)]
    | .ChooseUnit, [result, unitV] =>
        match unitV with
        | .const .unit => ok result
        | .dyn v => [.ok (SExpr.isCtor "VUnit" v) result, .error (SExpr.not (SExpr.isCtor "VUnit" v))]
        | _ => err
    | .Trace, [result, msg] =>
        checked2 (asString msg) fun _ => ok result
    | .FstPair, [p] =>
        let pp := asPair p
        let pd := asPairData p
        [.ok pp.guard pp.val.1,
         .ok pd.guard (.const (.data pd.val.1)),
         .error (SExpr.not (SExpr.or pp.guard pd.guard))]
    | .SndPair, [p] =>
        let pp := asPair p
        let pd := asPairData p
        [.ok pp.guard pp.val.2,
         .ok pd.guard (.const (.data pd.val.2)),
         .error (SExpr.not (SExpr.or pp.guard pd.guard))]

    | .ChooseList, [consCase, nilCase, xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        let dBranches :=
          [.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val)) nilCase,
           .ok (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val))) consCase]
        let nilOutcome := .ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val)) nilCase
        let consOutcome :=
          .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val))) consCase
        let vBranches := constListBranches (knownConstListLength xs) nilOutcome consOutcome
        dBranches ++ vBranches ++ [.error (SExpr.not (SExpr.or dl.guard vl.guard))]
    | .MkCons, [tail, head] =>
        let dl := asDataList tail
        let hd := asData head
        let vl := asConstList tail
        let hv := asConstVal head
        let dataOk := SExpr.and dl.guard hd.guard
        let constOk := SExpr.and vl.guard hv.guard
        [.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
         .ok constOk (consConstListValue hv.val tail),
         .error (SExpr.not (SExpr.or dataOk constOk))]
    | .HeadList, [xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        [.ok (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val))) (.const (.data (.app "dhead" [dl.val]))),
         .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val))) (.dyn (.app "vhead" [vl.val])),
         .error (SExpr.not (SExpr.or (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                                     (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]
    | .TailList, [xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        [.ok (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val))) (.const (.dataList (.app "dtail" [dl.val]))),
         .ok (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
           (tailConstListValue xs),
         .error (SExpr.not (SExpr.or (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                                     (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]
    | .NullList, [xs] =>
        let dl := asDataList xs
        let vl := asConstList xs
        [.ok dl.guard (.const (.bool (SExpr.isCtor "DNil" dl.val))),
         .ok vl.guard (.const (.bool (SExpr.isCtor "VNil" vl.val))),
         .error (SExpr.not (SExpr.or dl.guard vl.guard))]

    | .ChooseData, [bCase, iCase, listCase, mapCase, constrCase, dVal] =>
        let d := asData dVal
        [.ok (SExpr.and d.guard (SExpr.isCtor "DConstr" d.val)) constrCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DMap" d.val)) mapCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DList" d.val)) listCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DI" d.val)) iCase,
         .ok (SExpr.and d.guard (SExpr.isCtor "DB" d.val)) bCase,
         .error (SExpr.not d.guard)]
    | .ConstrData, [fields, tag] =>
        checkedConst (Proj.map2 (fun tag fields => .app "DConstr" [tag, fields]) (asInt tag) (asDataList fields)) .data
    | .MapData, [ps] => checkedConst ((asPairDataList ps).map fun ps => .app "DMap" [ps]) .data
    | .ListData, [xs] => checkedConst ((asDataList xs).map fun xs => .app "DList" [xs]) .data
    | .IData, [i] => checkedConst ((asInt i).map fun i => .app "DI" [i]) .data
    | .BData, [bs] => checkedConst ((asBytes bs).map fun bs => .app "DB" [bs]) .data
    | .UnConstrData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DConstr" d
          [.ok is (.const (.pairData (.app "DI" [.app "dataConstrTag" [d]]) (.app "DList" [.app "dataConstrFields" [d]]))),
           .error (SExpr.not is)]
    | .UnMapData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DMap" d
          [.ok is (.const (.pairDataList (.app "dataMapEntries" [d]))), .error (SExpr.not is)]
    | .UnListData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DList" d
          [.ok is (.const (.dataList (.app "dataListItems" [d]))), .error (SExpr.not is)]
    | .UnIData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DI" d
          [.ok is (.const (.integer (.app "dataInt" [d]))), .error (SExpr.not is)]
    | .UnBData, [dVal] =>
        let d := asData dVal
        checked2 d fun d =>
          let is := SExpr.isCtor "DB" d
          [.ok is (.const (.bytes (.app "dataBytes" [d]))), .error (SExpr.not is)]
    | .EqualsData, [b, a] =>
        checkedBool (Proj.map2 SExpr.reflexiveEq (asData a) (asData b))
    | .MkPairData, [b, a] => checked1 (Proj.map2 (fun a b => (a, b)) (asData a) (asData b)) (fun (a, b) => .const (.pairData a b))
    | .MkNilData, [u] =>
        let g := unitGuard u
        [.ok g (.const (.dataList (.app "DNil" []))), .error (SExpr.not g)]
    | .MkNilPairData, [u] =>
        let g := unitGuard u
        [.ok g (.const (.pairDataList (.app "DPNil" []))), .error (SExpr.not g)]

    | .SerializeData, _ => timeout
    | .VerifyEcdsaSecp256k1Signature, _ => timeout
    | .VerifySchnorrSecp256k1Signature, _ => timeout

    | .Keccak_256, _ => timeout
    | .Blake2b_224, _ => timeout
    | .IntegerToByteString, [n, width, endian] =>
        let p := Proj.map3 (fun endian width n => (endian, width, n)) (asBool endian) (asInt width) (asInt n)
        checked2 p fun (endian, width, n) =>
          let defined := .app "uplc_integerToByteString_defined" [endian, width, n]
          [.ok defined (.const (.bytes (.app "uplc_integerToByteString" [endian, width, n]))),
           .error (SExpr.not defined)]
    | .ByteStringToInteger, [bs, endian] =>
        checkedConst (Proj.map2 (fun endian bs => .app "uplc_byteStringToInteger" [endian, bs])
          (asBool endian) (asBytes bs)) .integer

    | .AndByteString, [b, a, pad] =>
        checkedConst (Proj.map3 (fun pad a b => .app "uplc_andByteString" [pad, a, b]) (asBool pad) (asBytes a) (asBytes b)) .bytes
    | .OrByteString, [b, a, pad] =>
        checkedConst (Proj.map3 (fun pad a b => .app "uplc_orByteString" [pad, a, b]) (asBool pad) (asBytes a) (asBytes b)) .bytes
    | .XorByteString, [b, a, pad] =>
        checkedConst (Proj.map3 (fun pad a b => .app "uplc_xorByteString" [pad, a, b]) (asBool pad) (asBytes a) (asBytes b)) .bytes
    | .ComplementByteString, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_complementByteString" [b]) .bytes
    | .ReadBit, [idx, bs] =>
        let p := Proj.map2 (fun bs idx => (bs, idx)) (asBytes bs) (asInt idx)
        checked2 p fun (bs, idx) =>
          let defined := .app "uplc_readBit_defined" [bs, idx]
          [.ok defined (.const (.bool (.app "uplc_readBit" [bs, idx]))),
           .error (SExpr.not defined)]
    | .WriteBits, [val, idxs, bs] =>
        let p := Proj.map3 (fun bs idxs val => (bs, idxs, val)) (asBytes bs) (asConstList idxs) (asBool val)
        checked2 p fun (bs, idxs, val) =>
          let defined := .app "uplc_writeBits_defined" [bs, idxs, val]
          [.ok defined (.const (.bytes (.app "uplc_writeBits" [bs, idxs, val]))), .error (SExpr.not defined)]
    | .ReplicateByte, [byte, count] =>
        let p := Proj.map2 (fun count byte => (count, byte)) (asInt count) (asInt byte)
        checked2 p fun (count, byte) =>
          let defined := .app "uplc_replicateByte_defined" [count, byte]
          [.ok defined (.const (.bytes (.app "uplc_replicateByte" [count, byte]))),
           .error (SExpr.not defined)]
    | .ShiftByteString, [n, bs] =>
        checkedConst
          (Proj.map2 (fun bs n => .app "uplc_shiftByteString" [bs, n])
            (asBytes bs) (asInt n)) .bytes
    | .RotateByteString, [n, bs] =>
        checkedConst
          (Proj.map2 (fun bs n => .app "uplc_rotateByteString" [bs, n])
            (asBytes bs) (asInt n)) .bytes
    | .CountSetBits, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_countSetBits" [b]) .integer
    | .FindFirstSetBit, [bs] => checkedConst ((asBytes bs).map fun b => .app "uplc_findFirstSetBit" [b]) .integer
    | .Ripemd_160, _ => timeout
    | .ExpModInteger, [m, e, b] =>
        let p := Proj.map3 (fun b e m => (b, e, m)) (asInt b) (asInt e) (asInt m)
        checked2 p fun (b, e, m) =>
          let defined := .app "uplc_expModInteger_defined" [b, e, m]
          [.ok defined (.const (.integer (.app "uplc_expModInteger" [b, e, m]))), .error (SExpr.not defined)]

    | .DropList, [xs, n] =>
        let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs]) (asInt n) (asConstList xs)
        let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs]) (asInt n) (asDataList xs)
        [.ok vl.guard (.const (.constList vl.val .unknown)),
         .ok dl.guard (.const (.dataList dl.val)),
         .error (SExpr.not (SExpr.or vl.guard dl.guard))]
    | .IndexArray, [idx, arr] =>
        let p := Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx)
        checked2 p fun (arr, idx) =>
          let g := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (.app "vlist_length" [arr]))
          [.ok g (.dyn (.app "vlist_index" [idx, arr])), .error (SExpr.not g)]
    | .LengthOfArray, [arr] => checkedConst ((asArray arr).map fun xs => .app "vlist_length" [xs]) .integer
    | .ListToArray, [xs] => checkedConst (asConstList xs) .array
    | .InsertCoin, _ => timeout
    | .LookupCoin, _ => timeout
    | .ScaleValue, _ => timeout
    | .UnionValue, _ => timeout
    | .ValueContains, _ => timeout
    | .ValueData, _ => timeout
    | .UnValueData, _ => timeout

    | .Bls12_381_G1_add, _ => timeout
    | .Bls12_381_G1_neg, _ => timeout
    | .Bls12_381_G1_scalarMul, _ => timeout
    | .Bls12_381_G1_equal, _ => timeout
    | .Bls12_381_G1_hashToGroup, _ => timeout
    | .Bls12_381_G1_compress, _ => timeout
    | .Bls12_381_G1_uncompress, _ => timeout
    | .Bls12_381_G2_add, _ => timeout
    | .Bls12_381_G2_neg, _ => timeout
    | .Bls12_381_G2_scalarMul, _ => timeout
    | .Bls12_381_G2_equal, _ => timeout
    | .Bls12_381_G2_hashToGroup, _ => timeout
    | .Bls12_381_G2_compress, _ => timeout
    | .Bls12_381_G2_uncompress, _ => timeout
    | .Bls12_381_millerLoop, _ => timeout
    | .Bls12_381_mulMlResult, _ => timeout
    | .Bls12_381_finalVerify, _ => timeout
    | .Bls12_381_G1_multiScalarMul, _ => timeout
    | .Bls12_381_G2_multiScalarMul, _ => timeout
    | _, _ => err

  /-- General saturated-builtin boundary.  Every fully applied builtin takes
  the same CEK-backed ground fast path; the handwritten encoding is used only
  when at least one argument is genuinely symbolic. -/
  def evalBuiltinSaturated (b : BuiltinFun) (args : List SymVal) : List Outcome :=
    staticOrSymbolic b args fun _ => evalBuiltinSym b args
end


end Moist.SMT.UPLC
