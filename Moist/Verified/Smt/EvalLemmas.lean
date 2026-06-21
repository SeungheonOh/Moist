import Moist.Verified.Smt.Model

/-! # Stage 2b — `evalDyn` algebra (Layer A)

Reduction/`@[simp]` lemmas for the SMT evaluator: the `Dyn` projections, the structural
unfolding of `evalDyn`, one rfl-lemma per `evalApp` head (so `simp` never has to unfold
the ~90-arm string match — which times out), and then the correctness of the compiler's
smart constructors (`sNot`/`sAnd`/`sOr`/`sImplies`/`sIte`/`sEq`/`sOrs`) and smart
projectors (`sAsInt`/…). The smart projectors are the crucial ones: both the folded and
the unfolded path land on the *same* canonical `Dyn` projection, so they agree with no
well-sortedness side condition. -/

namespace Moist.Verified.Smt

open Moist.Symbolic
open SExpr (sNot sAnd sOr sImplies sIte sEq)

/-! ## `Dyn` projections -/

@[simp] theorem toInt_i  (x : Int)      : (Dyn.i x).toInt = x := rfl
@[simp] theorem toBool_b (x : Bool)     : (Dyn.b x).toBool = x := rfl
@[simp] theorem toStr_s  (x : String)   : (Dyn.s x).toStr = x := rfl
@[simp] theorem toSeq_seq (x : List Int): (Dyn.seq x).toSeq = x := rfl
@[simp] theorem toD_d    (x : SemD)     : (Dyn.d x).toD = x := rfl
@[simp] theorem toDL_dl  (x : SemDL)    : (Dyn.dl x).toDL = x := rfl
@[simp] theorem toDM_dm  (x : SemDM)    : (Dyn.dm x).toDM = x := rfl
@[simp] theorem toV_v    (x : SemV)     : (Dyn.v x).toV = x := rfl
@[simp] theorem toVL_vl  (x : SemVL)    : (Dyn.vl x).toVL = x := rfl

/-! ## `evalDyn` structural unfolding -/

@[simp] theorem evalDyn_int (M : Model) (n : Int) : evalDyn M (.int n) = .i n := rfl
@[simp] theorem evalDyn_bool (M : Model) (b : Bool) : evalDyn M (.bool b) = .b b := rfl
@[simp] theorem evalDyn_str (M : Model) (s : String) : evalDyn M (.str s) = .s s := rfl
@[simp] theorem evalDyn_app (M : Model) (h : String) (as : List SExpr) :
    evalDyn M (.app h as) = evalApp h (evalDynList M as) := rfl
@[simp] theorem evalDynList_nil (M : Model) : evalDynList M [] = [] := rfl
@[simp] theorem evalDynList_cons (M : Model) (e : SExpr) (es : List SExpr) :
    evalDynList M (e :: es) = evalDyn M e :: evalDynList M es := rfl

/-! ## `evalApp` per-head reductions (each is its own match arm: `rfl`). -/

-- V constructors
@[simp] theorem ea_VInt   (d : Dyn)    : evalApp "VInt"   [d] = .v (.int d.toInt) := rfl
@[simp] theorem ea_VBS    (d : Dyn)    : evalApp "VBS"    [d] = .v (.bs d.toSeq) := rfl
@[simp] theorem ea_VBool  (d : Dyn)    : evalApp "VBool"  [d] = .v (.bool d.toBool) := rfl
@[simp] theorem ea_VStr   (d : Dyn)    : evalApp "VStr"   [d] = .v (.str d.toStr) := rfl
@[simp] theorem ea_VData  (d : Dyn)    : evalApp "VData"  [d] = .v (.data d.toD) := rfl
@[simp] theorem ea_VList  (d : Dyn)    : evalApp "VList"  [d] = .v (.list d.toVL) := rfl
@[simp] theorem ea_VDList (d : Dyn)    : evalApp "VDList" [d] = .v (.dlist d.toDL) := rfl
@[simp] theorem ea_VPDList(d : Dyn)    : evalApp "VPDList" [d] = .v (.pdlist d.toDM) := rfl
@[simp] theorem ea_VPair  (a b : Dyn)  : evalApp "VPair"  [a,b] = .v (.pair a.toV b.toV) := rfl
@[simp] theorem ea_VPairD (a b : Dyn)  : evalApp "VPairD" [a,b] = .v (.pairD a.toD b.toD) := rfl
@[simp] theorem ea_VArr   (d : Dyn)    : evalApp "VArr"   [d] = .v (.arr d.toVL) := rfl
@[simp] theorem ea_VConstr(t a : Dyn)  : evalApp "VConstr" [t,a] = .v (.constr t.toInt a.toVL) := rfl
@[simp] theorem ea_VG1    (d : Dyn)    : evalApp "VG1"    [d] = .v .g1 := rfl
@[simp] theorem ea_VG2    (d : Dyn)    : evalApp "VG2"    [d] = .v .g2 := rfl
@[simp] theorem ea_VMl    (d : Dyn)    : evalApp "VMl"    [d] = .v .ml := rfl
-- V selectors
@[simp] theorem ea_viVal  (d : Dyn) : evalApp "viVal"  [d] = .i d.toV.getInt := rfl
@[simp] theorem ea_vbsVal (d : Dyn) : evalApp "vbsVal" [d] = .seq d.toV.getSeq := rfl
@[simp] theorem ea_vbVal  (d : Dyn) : evalApp "vbVal"  [d] = .b d.toV.getBool := rfl
@[simp] theorem ea_vsVal  (d : Dyn) : evalApp "vsVal"  [d] = .s d.toV.getStr := rfl
@[simp] theorem ea_vdVal  (d : Dyn) : evalApp "vdVal"  [d] = .d d.toV.getData := rfl
@[simp] theorem ea_vlElems(d : Dyn) : evalApp "vlElems" [d] = .vl d.toV.getList := rfl
@[simp] theorem ea_vdlElems(d : Dyn): evalApp "vdlElems" [d] = .dl d.toV.getDList := rfl
@[simp] theorem ea_vpdlElems(d : Dyn): evalApp "vpdlElems" [d] = .dm d.toV.getDM := rfl
@[simp] theorem ea_varrElems(d : Dyn): evalApp "varrElems" [d] = .vl d.toV.getArr := rfl
@[simp] theorem ea_vpFst  (d : Dyn) : evalApp "vpFst"  [d] = .v d.toV.pFst := rfl
@[simp] theorem ea_vpSnd  (d : Dyn) : evalApp "vpSnd"  [d] = .v d.toV.pSnd := rfl
@[simp] theorem ea_vpdFst (d : Dyn) : evalApp "vpdFst" [d] = .d d.toV.pdFst := rfl
@[simp] theorem ea_vpdSnd (d : Dyn) : evalApp "vpdSnd" [d] = .d d.toV.pdSnd := rfl
@[simp] theorem ea_vcTag  (d : Dyn) : evalApp "vcTag"  [d] = .i d.toV.cTag := rfl
@[simp] theorem ea_vcArgs (d : Dyn) : evalApp "vcArgs" [d] = .vl d.toV.cArgs := rfl
-- D constructors
@[simp] theorem ea_DConstr(t a : Dyn) : evalApp "DConstr" [t,a] = .d (.constr t.toInt a.toDL) := rfl
@[simp] theorem ea_DMap   (d : Dyn)   : evalApp "DMap"   [d] = .d (.map d.toDM) := rfl
@[simp] theorem ea_DList  (d : Dyn)   : evalApp "DList"  [d] = .d (.list d.toDL) := rfl
@[simp] theorem ea_DI     (d : Dyn)   : evalApp "DI"     [d] = .d (.i d.toInt) := rfl
@[simp] theorem ea_DB     (d : Dyn)   : evalApp "DB"     [d] = .d (.b d.toSeq) := rfl
-- D selectors
@[simp] theorem ea_dcTag  (d : Dyn) : evalApp "dcTag"  [d] = .i d.toD.kTag := rfl
@[simp] theorem ea_dcArgs (d : Dyn) : evalApp "dcArgs" [d] = .dl d.toD.kArgs := rfl
@[simp] theorem ea_dmEntries(d : Dyn): evalApp "dmEntries" [d] = .dm d.toD.kMap := rfl
@[simp] theorem ea_dlElems(d : Dyn) : evalApp "dlElems" [d] = .dl d.toD.kList := rfl
@[simp] theorem ea_diVal  (d : Dyn) : evalApp "diVal"  [d] = .i d.toD.kInt := rfl
@[simp] theorem ea_dbVal  (d : Dyn) : evalApp "dbVal"  [d] = .seq d.toD.kBs := rfl
-- list constructors / selectors
@[simp] theorem ea_dcons  (h t : Dyn) : evalApp "dcons" [h,t] = .dl (.cons h.toD t.toDL) := rfl
@[simp] theorem ea_dhd    (d : Dyn)   : evalApp "dhd"   [d] = .d d.toDL.hd := rfl
@[simp] theorem ea_dtl    (d : Dyn)   : evalApp "dtl"   [d] = .dl d.toDL.tl := rfl
@[simp] theorem ea_mcons  (k v t : Dyn): evalApp "mcons" [k,v,t] = .dm (.cons k.toD v.toD t.toDM) := rfl
@[simp] theorem ea_vcons  (h t : Dyn) : evalApp "vcons" [h,t] = .vl (.cons h.toV t.toVL) := rfl
@[simp] theorem ea_vhd    (d : Dyn)   : evalApp "vhd"   [d] = .v d.toVL.hd := rfl
@[simp] theorem ea_vtl    (d : Dyn)   : evalApp "vtl"   [d] = .vl d.toVL.tl := rfl
-- testers
@[simp] theorem ea_isVInt   (d : Dyn) : evalApp "is-VInt"   [d] = .b (d.toV.conName == "VInt") := rfl
@[simp] theorem ea_isVBS    (d : Dyn) : evalApp "is-VBS"    [d] = .b (d.toV.conName == "VBS") := rfl
@[simp] theorem ea_isVBool  (d : Dyn) : evalApp "is-VBool"  [d] = .b (d.toV.conName == "VBool") := rfl
@[simp] theorem ea_isVUnit  (d : Dyn) : evalApp "is-VUnit"  [d] = .b (d.toV.conName == "VUnit") := rfl
@[simp] theorem ea_isVStr   (d : Dyn) : evalApp "is-VStr"   [d] = .b (d.toV.conName == "VStr") := rfl
@[simp] theorem ea_isVData  (d : Dyn) : evalApp "is-VData"  [d] = .b (d.toV.conName == "VData") := rfl
@[simp] theorem ea_isVList  (d : Dyn) : evalApp "is-VList"  [d] = .b (d.toV.conName == "VList") := rfl
@[simp] theorem ea_isVDList (d : Dyn) : evalApp "is-VDList" [d] = .b (d.toV.conName == "VDList") := rfl
@[simp] theorem ea_isVPDList(d : Dyn) : evalApp "is-VPDList" [d] = .b (d.toV.conName == "VPDList") := rfl
@[simp] theorem ea_isVPair  (d : Dyn) : evalApp "is-VPair"  [d] = .b (d.toV.conName == "VPair") := rfl
@[simp] theorem ea_isVPairD (d : Dyn) : evalApp "is-VPairD" [d] = .b (d.toV.conName == "VPairD") := rfl
@[simp] theorem ea_isVArr   (d : Dyn) : evalApp "is-VArr"   [d] = .b (d.toV.conName == "VArr") := rfl
@[simp] theorem ea_isVConstr(d : Dyn) : evalApp "is-VConstr" [d] = .b (d.toV.conName == "VConstr") := rfl
@[simp] theorem ea_isVG1    (d : Dyn) : evalApp "is-VG1"    [d] = .b (d.toV.conName == "VG1") := rfl
@[simp] theorem ea_isVG2    (d : Dyn) : evalApp "is-VG2"    [d] = .b (d.toV.conName == "VG2") := rfl
@[simp] theorem ea_isVMl    (d : Dyn) : evalApp "is-VMl"    [d] = .b (d.toV.conName == "VMl") := rfl
@[simp] theorem ea_isDConstr(d : Dyn) : evalApp "is-DConstr" [d] = .b (d.toD.conName == "DConstr") := rfl
@[simp] theorem ea_isDMap   (d : Dyn) : evalApp "is-DMap"   [d] = .b (d.toD.conName == "DMap") := rfl
@[simp] theorem ea_isDList  (d : Dyn) : evalApp "is-DList"  [d] = .b (d.toD.conName == "DList") := rfl
@[simp] theorem ea_isDI     (d : Dyn) : evalApp "is-DI"     [d] = .b (d.toD.conName == "DI") := rfl
@[simp] theorem ea_isDB     (d : Dyn) : evalApp "is-DB"     [d] = .b (d.toD.conName == "DB") := rfl
@[simp] theorem ea_isdnil   (d : Dyn) : evalApp "is-dnil"   [d] = .b d.toDL.isNil := rfl
@[simp] theorem ea_isvnil   (d : Dyn) : evalApp "is-vnil"   [d] = .b d.toVL.isNil := rfl
@[simp] theorem ea_ismnil   (d : Dyn) : evalApp "is-mnil"   [d] = .b d.toDM.isNil := rfl
-- integer / boolean operators
@[simp] theorem ea_add (a b : Dyn) : evalApp "+" [a,b] = .i (a.toInt + b.toInt) := rfl
@[simp] theorem ea_sub (a b : Dyn) : evalApp "-" [a,b] = .i (a.toInt - b.toInt) := rfl
@[simp] theorem ea_mul (a b : Dyn) : evalApp "*" [a,b] = .i (a.toInt * b.toInt) := rfl
@[simp] theorem ea_lt  (a b : Dyn) : evalApp "<" [a,b] = .b (decide (a.toInt < b.toInt)) := rfl
@[simp] theorem ea_le  (a b : Dyn) : evalApp "<=" [a,b] = .b (decide (a.toInt ≤ b.toInt)) := rfl
@[simp] theorem ea_ge  (a b : Dyn) : evalApp ">=" [a,b] = .b (decide (a.toInt ≥ b.toInt)) := rfl
@[simp] theorem ea_fdiv (a b : Dyn) : evalApp "moist_fdiv" [a,b] = .i (smtFdiv a.toInt b.toInt) := rfl
@[simp] theorem ea_fmod (a b : Dyn) : evalApp "moist_fmod" [a,b] = .i (smtFmod a.toInt b.toInt) := rfl
@[simp] theorem ea_qdiv (a b : Dyn) : evalApp "moist_qdiv" [a,b] = .i (smtQdiv a.toInt b.toInt) := rfl
@[simp] theorem ea_qrem (a b : Dyn) : evalApp "moist_qrem" [a,b] = .i (smtQrem a.toInt b.toInt) := rfl
@[simp] theorem ea_sunit (a : Dyn) : evalApp "seq.unit" [a] = .seq [a.toInt] := rfl
@[simp] theorem ea_slen (a : Dyn) : evalApp "seq.len" [a] = .i (Int.ofNat a.toSeq.length) := rfl
@[simp] theorem ea_snth (s i : Dyn) : evalApp "seq.nth" [s,i] = .i (seqNth s.toSeq i.toInt) := rfl
@[simp] theorem ea_sapp (a b : Dyn) : evalApp "seq.++" [a,b] = .seq (a.toSeq ++ b.toSeq) := rfl
@[simp] theorem ea_strapp (a b : Dyn) : evalApp "str.++" [a,b] = .s (a.toStr ++ b.toStr) := rfl
@[simp] theorem ea_not (a : Dyn) : evalApp "not" [a] = .b (!a.toBool) := rfl
@[simp] theorem ea_and (a b : Dyn) : evalApp "and" [a,b] = .b (a.toBool && b.toBool) := rfl
@[simp] theorem ea_or  (a b : Dyn) : evalApp "or"  [a,b] = .b (a.toBool || b.toBool) := rfl
@[simp] theorem ea_imp (a b : Dyn) : evalApp "=>" [a,b] = .b (!a.toBool || b.toBool) := rfl
@[simp] theorem ea_eq  (a b : Dyn) : evalApp "=" [a,b] = .b (decide (a = b)) := rfl
@[simp] theorem ea_ite (c t e : Dyn) : evalApp "ite" [c,t,e] = (if c.toBool then t else e) := rfl

/-! ## Structural `beq` soundness (`beq a b = true → a = b`) -/

mutual
theorem beq_sound : ∀ {a b : SExpr}, SExpr.beq a b = true → a = b
  | .int _,  .int _,  h => by simp only [SExpr.beq, beq_iff_eq] at h; subst h; rfl
  | .bool _, .bool _, h => by simp only [SExpr.beq, beq_iff_eq] at h; subst h; rfl
  | .str _,  .str _,  h => by simp only [SExpr.beq, beq_iff_eq] at h; subst h; rfl
  | .atom _, .atom _, h => by simp only [SExpr.beq, beq_iff_eq] at h; subst h; rfl
  | .app f as, .app g bs, h => by
      simp only [SExpr.beq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hf, hl⟩ := h; subst hf; rw [beqList_sound hl]
  | .int _,  .bool _, h | .int _,  .str _,  h | .int _,  .atom _, h | .int _,  .app _ _, h
  | .bool _, .int _,  h | .bool _, .str _,  h | .bool _, .atom _, h | .bool _, .app _ _, h
  | .str _,  .int _,  h | .str _,  .bool _, h | .str _,  .atom _, h | .str _,  .app _ _, h
  | .atom _, .int _,  h | .atom _, .bool _, h | .atom _, .str _,  h | .atom _, .app _ _, h
  | .app _ _, .int _, h | .app _ _, .bool _, h | .app _ _, .str _, h | .app _ _, .atom _, h =>
      by simp [SExpr.beq] at h
termination_by a => sizeOf a
theorem beqList_sound : ∀ {as bs : List SExpr}, SExpr.beqList as bs = true → as = bs
  | [],      [],      _ => rfl
  | _ :: _,  [],      h => by simp [SExpr.beqList] at h
  | [],      _ :: _,  h => by simp [SExpr.beqList] at h
  | x :: xs, y :: ys, h => by
      simp only [SExpr.beqList, Bool.and_eq_true] at h
      rw [beq_sound h.1, beqList_sound h.2]
termination_by as => sizeOf as
end

/-! ## Smart boolean constructors -/

@[simp] theorem evalDyn_sNot (M : Model) (e : SExpr) :
    (evalDyn M (sNot e)).toBool = !(evalDyn M e).toBool := by
  cases e <;> simp [sNot]

@[simp] theorem evalDyn_sAnd (M : Model) (a b : SExpr) :
    (evalDyn M (sAnd a b)).toBool = ((evalDyn M a).toBool && (evalDyn M b).toBool) := by
  unfold sAnd; split <;> simp_all

@[simp] theorem evalDyn_sOr (M : Model) (a b : SExpr) :
    (evalDyn M (sOr a b)).toBool = ((evalDyn M a).toBool || (evalDyn M b).toBool) := by
  unfold sOr; split <;> simp_all

@[simp] theorem evalDyn_sImplies (M : Model) (a b : SExpr) :
    (evalDyn M (sImplies a b)).toBool = (!(evalDyn M a).toBool || (evalDyn M b).toBool) := by
  unfold sImplies; split <;> simp_all

@[simp] theorem evalDyn_sEq (M : Model) (a b : SExpr) :
    (evalDyn M (sEq a b)).toBool = decide (evalDyn M a = evalDyn M b) := by
  cases a <;> cases b <;> simp [sEq] <;> rfl

theorem evalDyn_sOrs (M : Model) (es : List SExpr) :
    (evalDyn M (sOrs es)).toBool = es.foldr (fun e acc => (evalDyn M e).toBool || acc) false := by
  induction es with
  | nil => rfl
  | cons e es ih => show (evalDyn M (sOr e (sOrs es))).toBool = _; rw [evalDyn_sOr, ih]; rfl

theorem evalDyn_sIte (M : Model) (c t e : SExpr) :
    evalDyn M (sIte c t e) = if (evalDyn M c).toBool then evalDyn M t else evalDyn M e := by
  unfold sIte
  split
  · simp
  · simp
  · split
    · next hbeq => rw [beq_sound hbeq]; simp
    · simp

/-! ## Smart projectors (now non-folding — each denotes to the canonical `Dyn` projection
of `⟦e⟧`, unconditionally and as a *full* `Dyn` value, not just `.toX`). -/

@[simp] theorem evalDyn_sAsInt (M : Model) (e : SExpr) :
    evalDyn M (V.sAsInt e) = .i ((evalDyn M e).toV.getInt) := by simp [V.sAsInt, V.asInt]
@[simp] theorem evalDyn_sAsBool (M : Model) (e : SExpr) :
    evalDyn M (V.sAsBool e) = .b ((evalDyn M e).toV.getBool) := by simp [V.sAsBool, V.asBool]
@[simp] theorem evalDyn_sAsBS (M : Model) (e : SExpr) :
    evalDyn M (V.sAsBS e) = .seq ((evalDyn M e).toV.getSeq) := by simp [V.sAsBS, V.asBS]
@[simp] theorem evalDyn_sAsStr (M : Model) (e : SExpr) :
    evalDyn M (V.sAsStr e) = .s ((evalDyn M e).toV.getStr) := by simp [V.sAsStr, V.asStr]
@[simp] theorem evalDyn_sAsData (M : Model) (e : SExpr) :
    evalDyn M (V.sAsData e) = .d ((evalDyn M e).toV.getData) := by simp [V.sAsData, V.asData]
@[simp] theorem evalDyn_sAsList (M : Model) (e : SExpr) :
    evalDyn M (V.sAsList e) = .vl ((evalDyn M e).toV.getList) := by simp [V.sAsList, V.asList]
@[simp] theorem evalDyn_sAsDL (M : Model) (e : SExpr) :
    evalDyn M (V.sAsDL e) = .dl ((evalDyn M e).toV.getDList) := by simp [V.sAsDL, V.asDL]
@[simp] theorem evalDyn_sAsDM (M : Model) (e : SExpr) :
    evalDyn M (V.sAsDM e) = .dm ((evalDyn M e).toV.getDM) := by simp [V.sAsDM, V.asDM]
@[simp] theorem evalDyn_sFst (M : Model) (e : SExpr) :
    evalDyn M (V.sFst e) = .v ((evalDyn M e).toV.pFst) := by simp [V.sFst, V.fst]
@[simp] theorem evalDyn_sSnd (M : Model) (e : SExpr) :
    evalDyn M (V.sSnd e) = .v ((evalDyn M e).toV.pSnd) := by simp [V.sSnd, V.snd]
@[simp] theorem evalDyn_sFstD (M : Model) (e : SExpr) :
    evalDyn M (V.sFstD e) = .d ((evalDyn M e).toV.pdFst) := by simp [V.sFstD, V.fstD]
@[simp] theorem evalDyn_sSndD (M : Model) (e : SExpr) :
    evalDyn M (V.sSndD e) = .d ((evalDyn M e).toV.pdSnd) := by simp [V.sSndD, V.sndD]
@[simp] theorem evalDyn_sCTag (M : Model) (e : SExpr) :
    evalDyn M (V.sCTag e) = .i ((evalDyn M e).toV.cTag) := by simp [V.sCTag, V.cTag]
@[simp] theorem evalDyn_sCArgs (M : Model) (e : SExpr) :
    evalDyn M (V.sCArgs e) = .vl ((evalDyn M e).toV.cArgs) := by simp [V.sCArgs, V.cArgs]

/-! ## `VL`/`DL` head/tail (now non-folding) -/

@[simp] theorem evalDyn_vlHd (M : Model) (e : SExpr) :
    evalDyn M (VL.sHd e) = .v ((evalDyn M e).toVL.hd) := by simp [VL.sHd, VL.hd]
@[simp] theorem evalDyn_vlTl (M : Model) (e : SExpr) :
    evalDyn M (VL.sTl e) = .vl ((evalDyn M e).toVL.tl) := by simp [VL.sTl, VL.tl]

@[simp] theorem evalDyn_dlHd (M : Model) (e : SExpr) :
    evalDyn M (DL.sHd e) = .d ((evalDyn M e).toDL.hd) := by simp [DL.sHd, DL.hd]
@[simp] theorem evalDyn_dlTl (M : Model) (e : SExpr) :
    evalDyn M (DL.sTl e) = .dl ((evalDyn M e).toDL.tl) := by simp [DL.sTl, DL.tl]

end Moist.Verified.Smt
