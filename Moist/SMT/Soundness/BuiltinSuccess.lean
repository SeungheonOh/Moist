import Moist.SMT.Soundness.Foundations

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.Verified.BigStep
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekEnv CekValue)

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_AddInteger_eq (b a : SymVal) :
    evalBuiltinSym .AddInteger [b, a] =
      checkedConst (Proj.map2 SExpr.add (asInt a) (asInt b)) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_SubtractInteger_eq (b a : SymVal) :
    evalBuiltinSym .SubtractInteger [b, a] =
      checkedConst (Proj.map2 SExpr.sub (asInt a) (asInt b)) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MultiplyInteger_eq (b a : SymVal) :
    evalBuiltinSym .MultiplyInteger [b, a] =
      checkedConst (Proj.map2 SExpr.mul (asInt a) (asInt b)) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_DivideInteger_eq (b a : SymVal) :
    evalBuiltinSym .DivideInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_div" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_QuotientInteger_eq (b a : SymVal) :
    evalBuiltinSym .QuotientInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_tdiv" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_RemainderInteger_eq (b a : SymVal) :
    evalBuiltinSym .RemainderInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_tmod" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ModInteger_eq (b a : SymVal) :
    evalBuiltinSym .ModInteger [b, a] =
      (let p := Proj.map2 (fun a b => (a, b)) (asInt a) (asInt b)
       checked2 p fun (a, b) =>
        [.ok (divisionGuard b) (.const (.integer (.app "uplc_mod" [a, b]))),
         .error (SExpr.not (divisionGuard b))]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsInteger_eq (b a : SymVal) :
    evalBuiltinSym .EqualsInteger [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asInt a) (asInt b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanInteger_eq (b a : SymVal) :
    evalBuiltinSym .LessThanInteger [b, a] =
      checkedBool (Proj.map2 SExpr.lt (asInt a) (asInt b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanEqualsInteger_eq (b a : SymVal) :
    evalBuiltinSym .LessThanEqualsInteger [b, a] =
      checkedBool (Proj.map2 SExpr.le (asInt a) (asInt b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_AppendByteString_eq (b a : SymVal) :
    evalBuiltinSym .AppendByteString [b, a] =
      checkedConst (Proj.map2 SExpr.seqAppend (asBytes a) (asBytes b)) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ConsByteString_eq (bs n : SymVal) :
    evalBuiltinSym .ConsByteString [bs, n] =
      (let p := Proj.map2 (fun n bs => (n, bs)) (asInt n) (asBytes bs)
       checked2 p fun (n, bs) =>
        let inByte := SExpr.and (SExpr.ge n (.int 0)) (SExpr.le n (.int 255))
        [.ok inByte (.const (.bytes (SExpr.seqAppend (SExpr.seqUnit n) bs))),
         .error (SExpr.not inByte)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_SliceByteString_eq (bs len start : SymVal) :
    evalBuiltinSym .SliceByteString [bs, len, start] =
      (let p := Proj.map3 (fun start len bs => (start, len, bs))
        (asInt start) (asInt len) (asBytes bs)
       checkedConst (p.map fun (start, len, bs) =>
        let s := SExpr.ite (SExpr.lt start (.int 0)) (.int 0) start
        let l := SExpr.ite (SExpr.lt len (.int 0)) (.int 0) len
        SExpr.seqExtract bs s l) .bytes) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LengthOfByteString_eq (bs : SymVal) :
    evalBuiltinSym .LengthOfByteString [bs] =
      checkedConst ((asBytes bs).map SExpr.seqLen) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_IndexByteString_eq (idx bs : SymVal) :
    evalBuiltinSym .IndexByteString [idx, bs] =
      (let p := Proj.map2 (fun bs idx => (bs, idx)) (asBytes bs) (asInt idx)
       checked2 p fun (bs, idx) =>
        let inRange := SExpr.and (SExpr.ge idx (.int 0)) (SExpr.lt idx (SExpr.seqLen bs))
        [.ok inRange (.const (.integer (SExpr.seqNth bs idx))),
         .error (SExpr.not inRange)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsByteString_eq (b a : SymVal) :
    evalBuiltinSym .EqualsByteString [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asBytes a) (asBytes b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanByteString_eq (b a : SymVal) :
    evalBuiltinSym .LessThanByteString [b, a] =
      checkedBool (Proj.map2 (fun a b => .app "bytes_lt" [a, b])
        (asBytes a) (asBytes b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_LessThanEqualsByteString_eq (b a : SymVal) :
    evalBuiltinSym .LessThanEqualsByteString [b, a] =
      checkedBool (Proj.map2 (fun a b => .app "bytes_le" [a, b])
        (asBytes a) (asBytes b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_AppendString_eq (b a : SymVal) :
    evalBuiltinSym .AppendString [b, a] =
      checkedConst (Proj.map2 SExpr.strAppend (asString a) (asString b)) .string := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsString_eq (b a : SymVal) :
    evalBuiltinSym .EqualsString [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asString a) (asString b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EncodeUtf8_eq (s : SymVal) :
    evalBuiltinSym .EncodeUtf8 [s] =
      checkedConst ((asString s).map fun x => .app "uplc_encodeUtf8" [x]) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_DecodeUtf8_eq (bs : SymVal) :
    evalBuiltinSym .DecodeUtf8 [bs] =
      checked2 (asBytes bs) fun b =>
        [.ok (.app "valid_utf8" [b]) (.const (.string (.app "uplc_decodeUtf8" [b]))),
         .error (SExpr.not (.app "valid_utf8" [b]))] := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_IfThenElse_eq (elseV thenV cond : SymVal) :
    evalBuiltinSym .IfThenElse [elseV, thenV, cond] =
      (let c := asBool cond
       [.ok (SExpr.and c.guard c.val) thenV,
        .ok (SExpr.and c.guard (SExpr.not c.val)) elseV,
        .error (SExpr.not c.guard)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_Trace_eq (result msg : SymVal) :
    evalBuiltinSym .Trace [result, msg] =
      checked2 (asString msg) fun _ => ok result := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MkNilData_eq (u : SymVal) :
    evalBuiltinSym .MkNilData [u] =
      (let g := unitGuard u
       [.ok g (.const (.dataList (.app "DNil" []))), .error (SExpr.not g)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MkNilPairData_eq (u : SymVal) :
    evalBuiltinSym .MkNilPairData [u] =
      (let g := unitGuard u
       [.ok g (.const (.pairDataList (.app "DPNil" []))), .error (SExpr.not g)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ConstrData_eq (fields tag : SymVal) :
    evalBuiltinSym .ConstrData [fields, tag] =
      checkedConst
        (Proj.map2 (fun tag fields => .app "DConstr" [tag, fields])
          (asInt tag) (asDataList fields)) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MapData_eq (ps : SymVal) :
    evalBuiltinSym .MapData [ps] =
      checkedConst ((asPairDataList ps).map fun ps => .app "DMap" [ps]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ListData_eq (xs : SymVal) :
    evalBuiltinSym .ListData [xs] =
      checkedConst ((asDataList xs).map fun xs => .app "DList" [xs]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_IData_eq (i : SymVal) :
    evalBuiltinSym .IData [i] =
      checkedConst ((asInt i).map fun i => .app "DI" [i]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_BData_eq (bs : SymVal) :
    evalBuiltinSym .BData [bs] =
      checkedConst ((asBytes bs).map fun bs => .app "DB" [bs]) .data := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_SerializeData_eq (d : SymVal) :
    evalBuiltinSym .SerializeData [d] =
      checkedConst ((asData d).map fun d => .app "uplc_serializeData" [d]) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_ComplementByteString_eq (bs : SymVal) :
    evalBuiltinSym .ComplementByteString [bs] =
      checkedConst ((asBytes bs).map fun b => .app "uplc_complementByteString" [b]) .bytes := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_CountSetBits_eq (bs : SymVal) :
    evalBuiltinSym .CountSetBits [bs] =
      checkedConst ((asBytes bs).map fun b => .app "uplc_countSetBits" [b]) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_FindFirstSetBit_eq (bs : SymVal) :
    evalBuiltinSym .FindFirstSetBit [bs] =
      checkedConst ((asBytes bs).map fun b => .app "uplc_findFirstSetBit" [b]) .integer := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_EqualsData_eq (b a : SymVal) :
    evalBuiltinSym .EqualsData [b, a] =
      checkedBool (Proj.map2 SExpr.eq (asData a) (asData b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_MkPairData_eq (b a : SymVal) :
    evalBuiltinSym .MkPairData [b, a] =
      checked1 (Proj.map2 (fun a b => (a, b)) (asData a) (asData b))
        (fun (a, b) => SymVal.const (SymConst.pairData a b)) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnConstrData_eq (dVal : SymVal) :
    evalBuiltinSym .UnConstrData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DConstr" d
        [.ok is (.const (.pairData
          (.app "DI" [.app "dataConstrTag" [d]])
          (.app "DList" [.app "dataConstrFields" [d]]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnMapData_eq (dVal : SymVal) :
    evalBuiltinSym .UnMapData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DMap" d
        [.ok is (.const (.pairDataList (.app "dataMapEntries" [d]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnListData_eq (dVal : SymVal) :
    evalBuiltinSym .UnListData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DList" d
        [.ok is (.const (.dataList (.app "dataListItems" [d]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnIData_eq (dVal : SymVal) :
    evalBuiltinSym .UnIData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DI" d
        [.ok is (.const (.integer (.app "dataInt" [d]))),
         .error (SExpr.not is)]) := by
  rfl

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_UnBData_eq (dVal : SymVal) :
    evalBuiltinSym .UnBData [dVal] =
      (let d := asData dVal
       checked2 d fun d =>
        let is := SExpr.isCtor "DB" d
        [.ok is (.const (.bytes (.app "dataBytes" [d]))),
         .error (SExpr.not is)]) := by
  rfl

def BuiltinOkSound (b : BuiltinFun) : Prop :=
  ∀ {m : SmtSem.Model} {args : List SymVal} {cargs : List CekValue}
    {pc : SExpr} {v : SymVal},
    symValListToCekList? m args = some cargs →
    symValsNoOpaqueForSoundness args = true →
    Outcome.ok pc v ∈ evalBuiltinSym b args →
    pcHolds m pc = true →
    ∃ cv, symValToCek? m v = some cv ∧
      symValNoOpaqueForSoundness v = true ∧
      Moist.CEK.evalBuiltin b cargs = some cv

def BuiltinErrorSound (b : BuiltinFun) : Prop :=
  ∀ {m : SmtSem.Model} {args : List SymVal} {cargs : List CekValue} {out : Outcome},
    symValListToCekList? m args = some cargs →
    out ∈ evalBuiltinSym b args →
    outcomeErrorActive m out = true →
    Moist.CEK.evalBuiltin b cargs = none

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_AddInteger : BuiltinOkSound .AddInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AddInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.add (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Integer (ia + ib)), ?_, ?_, ?_⟩
                ·
                  have hadd := Moist.SMT.Semantics.eval_add_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.add (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.int (ia + ib)) at hadd
                  simp [symValToCek?, symConstToCek?, hadd]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_SubtractInteger : BuiltinOkSound .SubtractInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_SubtractInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.sub (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Integer (ia - ib)), ?_, ?_, ?_⟩
                ·
                  have hsub := Moist.SMT.Semantics.eval_sub_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.sub (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.int (ia - ib)) at hsub
                  simp [symValToCek?, symConstToCek?, hsub]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MultiplyInteger : BuiltinOkSound .MultiplyInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MultiplyInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.integer
                    (SExpr.mul (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Integer (ia * ib)), ?_, ?_, ?_⟩
                ·
                  have hmul := Moist.SMT.Semantics.eval_mul_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.mul (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.int (ia * ib)) at hmul
                  simp [symValToCek?, symConstToCek?, hmul]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_DivideInteger : BuiltinOkSound .DivideInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_DivideInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerDiv ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hdiv := Moist.SMT.Semantics.eval_uplc_div_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hdiv]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_DivideInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerDiv, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_QuotientInteger : BuiltinOkSound .QuotientInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_QuotientInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerTDiv ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hdiv := Moist.SMT.Semantics.eval_uplc_tdiv_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hdiv]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_QuotientInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerTDiv, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_RemainderInteger : BuiltinOkSound .RemainderInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_RemainderInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerTMod ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hmod := Moist.SMT.Semantics.eval_uplc_tmod_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hmod]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_RemainderInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerTMod, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ModInteger : BuiltinOkSound .ModInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ModInteger_eq b a] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpDiv⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpArgs
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                have hne : (ib == 0) = false :=
                  pcHolds_ne_int_zero heb hpDiv
                refine ⟨.VCon (.Integer (Moist.Plutus.uplcIntegerMod ia ib)),
                  ?_, ?_, ?_⟩
                ·
                  have hmod := Moist.SMT.Semantics.eval_uplc_mod_of
                    (m := m) (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb hne
                  simpa [symValToCek?, symConstToCek?, Proj.map2, hmod]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hneq : ib ≠ 0 := by
                    intro hz
                    subst ib
                    simp at hne
                  have hconst := Moist.CEK.evalBuiltinConst_ModInteger_of
                    (a := ia) (b := ib) hne
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, hconst,
                    Moist.CEK.builtinIntegerMod, hneq]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsInteger : BuiltinOkSound .EqualsInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Bool (ia == ib)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_int_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.eq (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (ia == ib)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanInteger : BuiltinOkSound .LessThanInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.lt (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Bool (ia < ib)), ?_, ?_, ?_⟩
                ·
                  have hlt := Moist.SMT.Semantics.eval_lt_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.lt (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (ia < ib)) at hlt
                  simp [symValToCek?, symConstToCek?, hlt]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanEqualsInteger :
    BuiltinOkSound .LessThanEqualsInteger := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsInteger_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt a).guard (asInt b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.le (asInt a).val (asInt b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt a).guard (asInt b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt a).guard (asInt b).guard).mp hpc
                obtain ⟨ia, rfl, hea⟩ := asInt_sound ha hp.1
                obtain ⟨ib, rfl, heb⟩ := asInt_sound hb hp.2
                refine ⟨.VCon (.Bool (ia <= ib)), ?_, ?_, ?_⟩
                ·
                  have hle := Moist.SMT.Semantics.eval_le_of (m := m)
                    (a := (asInt a).val) (b := (asInt b).val)
                    (x := ia) (y := ib) hea heb
                  change SmtSem.eval m (SExpr.le (asInt a).val (asInt b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (ia <= ib)) at hle
                  simp [symValToCek?, symConstToCek?, hle]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_AppendByteString : BuiltinOkSound .AppendByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bytes
                    (SExpr.seqAppend (asBytes a).val (asBytes b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.ByteString (bsa ++ bsb)), ?_, ?_, ?_⟩
                ·
                  have happ := Moist.SMT.Semantics.eval_seqAppend_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m (SExpr.seqAppend (asBytes a).val (asBytes b).val) =
                    some (Moist.SMT.Semantics.SVal.bytes (bsa ++ bsb)) at happ
                  simp [symValToCek?, symConstToCek?, happ]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ConsByteString : BuiltinOkSound .ConsByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons nSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConsByteString_eq bsSym nSym] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpByte⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cbs, cn, hbsArg, hnArg, rfl⟩ :=
                  symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt nSym).guard (asBytes bsSym).guard).mp hpArgs
                obtain ⟨n, rfl, hnEval⟩ := asInt_sound hnArg hp.1
                obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.2
                have hpRange :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (SExpr.ge (asInt nSym).val (.int 0))
                    (SExpr.le (asInt nSym).val (.int 255))).mp hpByte
                have hge : 0 ≤ n :=
                  pcHolds_ge_int hnEval
                    (by simp [Moist.SMT.Semantics.eval]) hpRange.1
                have hle : n ≤ 255 :=
                  pcHolds_le_int hnEval
                    (by simp [Moist.SMT.Semantics.eval]) hpRange.2
                refine ⟨.VCon (.ByteString (Moist.Plutus.bytesSingletonValue n ++ bs)),
                  ?_, ?_, ?_⟩
                ·
                  have hunit := Moist.SMT.Semantics.eval_seqUnit_of
                    (m := m) (e := (asInt nSym).val) hnEval hge hle
                  have happ := Moist.SMT.Semantics.eval_seqAppend_of (m := m)
                    (a := SExpr.seqUnit (asInt nSym).val)
                    (b := (asBytes bsSym).val)
                    (x := Moist.SMT.Semantics.bytesSingletonValue n)
                    (y := bs) hunit hbsEval
                  change SmtSem.eval m
                    (SExpr.seqAppend (SExpr.seqUnit (asInt nSym).val)
                      (asBytes bsSym).val) =
                    some (Moist.SMT.Semantics.SVal.bytes
                      (Moist.SMT.Semantics.bytesSingletonValue n ++ bs)) at happ
                  simp [symValToCek?, symConstToCek?, Proj.map2, happ,
                    Moist.SMT.Semantics.bytesSingletonValue]
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hnlt : ¬ n < 0 := by
                    intro hn
                    exact (Int.not_le.mpr hn) hge
                  have hngt : ¬ n > 255 := by
                    intro hn
                    exact (Int.not_le.mpr hn) hle
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst,
                    hnlt, hngt]
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_SliceByteString : BuiltinOkSound .SliceByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons lenSym rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons startSym rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_SliceByteString_eq bsSym lenSym startSym] at hmem
                  change Outcome.ok pc v ∈
                    [Outcome.ok
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard])
                      (SymVal.const (SymConst.bytes
                        (SExpr.seqExtract (asBytes bsSym).val
                          (SExpr.ite (SExpr.lt (asInt startSym).val (.int 0))
                            (.int 0) (asInt startSym).val)
                          (SExpr.ite (SExpr.lt (asInt lenSym).val (.int 0))
                            (.int 0) (asInt lenSym).val)))),
                     Outcome.error (SExpr.not
                      (SExpr.all [(asInt startSym).guard, (asInt lenSym).guard,
                        (asBytes bsSym).guard]))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  rcases hmem with hmem | hmem
                  · injection hmem with hpcEq hvEq
                    subst pc
                    subst v
                    obtain ⟨cbs, clen, cstart, hbsArg, hlenArg, hstartArg, rfl⟩ :=
                      symValListToCekList_triple hargs
                    have hp := pcHolds_all3 (m := m) hpc
                    obtain ⟨start, rfl, hstartEval⟩ :=
                      asInt_sound hstartArg hp.1
                    obtain ⟨len, rfl, hlenEval⟩ :=
                      asInt_sound hlenArg hp.2.1
                    obtain ⟨bs, rfl, hbsEval⟩ :=
                      asBytes_sound hbsArg hp.2.2
                    refine ⟨.VCon (.ByteString
                      (Moist.Plutus.bytesExtractValue bs start len)), ?_, ?_, ?_⟩
                    ·
                      have hstartClamp :=
                        eval_nonneg_clamp_int_of (m := m)
                          (e := (asInt startSym).val) hstartEval
                      have hlenClamp :=
                        eval_nonneg_clamp_int_of (m := m)
                          (e := (asInt lenSym).val) hlenEval
                      have hextract := Moist.SMT.Semantics.eval_seqExtract_of (m := m)
                        (bs := (asBytes bsSym).val)
                        (start := SExpr.ite
                          (SExpr.lt (asInt startSym).val (.int 0))
                          (.int 0) (asInt startSym).val)
                        (len := SExpr.ite
                          (SExpr.lt (asInt lenSym).val (.int 0))
                          (.int 0) (asInt lenSym).val)
                        (x := bs)
                        (s := if start < 0 then 0 else start)
                        (l := if len < 0 then 0 else len)
                        hbsEval hstartClamp hlenClamp
                      unfold Moist.SMT.Semantics.bytesExtractValue at hextract
                      rw [Moist.Plutus.bytesExtractValue_clamp bs start len] at hextract
                      change SmtSem.eval m
                        (SExpr.seqExtract (asBytes bsSym).val
                          (SExpr.ite (SExpr.lt (asInt startSym).val (.int 0))
                            (.int 0) (asInt startSym).val)
                          (SExpr.ite (SExpr.lt (asInt lenSym).val (.int 0))
                            (.int 0) (asInt lenSym).val)) =
                        some (Moist.SMT.Semantics.SVal.bytes
                          (Moist.Plutus.bytesExtractValue bs start len)) at hextract
                      simp [symValToCek?, symConstToCek?, hextract]
                    · simp [symValNoOpaqueForSoundness]
                    · rfl
                  · rcases hmem with hbad | hfalse
                    · cases hbad
                    · cases hfalse
              | cons _ _ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LengthOfByteString : BuiltinOkSound .LengthOfByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_LengthOfByteString_eq bsSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.integer (SExpr.seqLen (asBytes bsSym).val))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbs hpc
            refine ⟨.VCon (.Integer (Int.ofNat bs.size)), ?_, ?_, ?_⟩
            ·
              have hlen := Moist.SMT.Semantics.eval_seqLen_of (m := m)
                (a := (asBytes bsSym).val) hbsEval
              change SmtSem.eval m (SExpr.seqLen (asBytes bsSym).val) =
                some (Moist.SMT.Semantics.SVal.int (Int.ofNat bs.size)) at hlen
              simp [symValToCek?, symConstToCek?, hlen]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IndexByteString : BuiltinOkSound .IndexByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons idxSym rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons bsSym rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_IndexByteString_eq idxSym bsSym] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpRange⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hinner | hinner
              · injection hinner with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cidx, cbs, hidxArg, hbsArg, rfl⟩ :=
                  symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes bsSym).guard (asInt idxSym).guard).mp hpArgs
                obtain ⟨idx, rfl, hidxEval⟩ := asInt_sound hidxArg hp.2
                obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbsArg hp.1
                have hpRangeSplit :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (SExpr.ge (asInt idxSym).val (.int 0))
                    (SExpr.lt (asInt idxSym).val
                      (SExpr.seqLen (asBytes bsSym).val))).mp hpRange
                have hge : 0 ≤ idx :=
                  pcHolds_ge_int hidxEval
                    (by simp [Moist.SMT.Semantics.eval]) hpRangeSplit.1
                have hlenEval := Moist.SMT.Semantics.eval_seqLen_of (m := m)
                  (a := (asBytes bsSym).val) hbsEval
                change SmtSem.eval m (SExpr.seqLen (asBytes bsSym).val) =
                  some (Moist.SMT.Semantics.SVal.int (Int.ofNat bs.size)) at hlenEval
                have hlt : idx < Int.ofNat bs.size :=
                  pcHolds_lt_int hidxEval hlenEval hpRangeSplit.2
                refine ⟨.VCon (.Integer (Moist.Plutus.bytesNthValue bs idx)),
                  ?_, ?_, ?_⟩
                ·
                  have hnth := Moist.SMT.Semantics.eval_seqNth_of (m := m)
                    (bs := (asBytes bsSym).val) (idx := (asInt idxSym).val)
                    (x := bs) (i := idx) hbsEval hidxEval hge hlt
                  have hnth' :
                      SmtSem.eval m
                        (SExpr.seqNth (asBytes bsSym).val (asInt idxSym).val) =
                      some (Moist.SMT.Semantics.SVal.int
                        (Moist.Plutus.bytesNthValue bs idx)) := by
                    simpa [SExpr.seqNth, Moist.SMT.Semantics.bytesNthValue] using hnth
                  change (match SmtSem.eval m
                      (SExpr.seqNth (asBytes bsSym).val (asInt idxSym).val) with
                    | some (Moist.SMT.Semantics.SVal.int i) =>
                        some (CekValue.VCon (.Integer i))
                    | _ => none) =
                    some (CekValue.VCon
                      (.Integer (Moist.Plutus.bytesNthValue bs idx)))
                  rw [hnth']
                · simp [symValNoOpaqueForSoundness]
                ·
                  have hnlt : ¬ idx < 0 := by
                    intro hn
                    exact (Int.not_le.mpr hn) hge
                  have hnge : ¬ idx ≥ Int.ofNat bs.size := by
                    intro hn
                    exact (Int.not_le.mpr hlt) hn
                  have hnotUpper : ¬ Int.ofNat bs.size ≤ idx := by
                    exact Int.not_le.mpr hlt
                  have hnotUpper' : ¬ (↑(ByteArray.size bs) : Int) ≤ idx := by
                    simpa using hnotUpper
                  simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough,
                    Moist.CEK.extractConsts, Moist.CEK.evalBuiltinConst, hnlt]
                  rw [if_neg hnotUpper']
              · rcases hinner with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsByteString : BuiltinOkSound .EqualsByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asBytes a).val (asBytes b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.Bool (bsa == bsb)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_bytes_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m (SExpr.eq (asBytes a).val (asBytes b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (bsa == bsb)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanByteString : BuiltinOkSound .LessThanByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_lt" [(asBytes a).val, (asBytes b).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.Bool (Moist.Plutus.bytesLt bsa bsb)), ?_, ?_, ?_⟩
                ·
                  have hlt := Moist.SMT.Semantics.eval_bytesLt_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m
                    (.app "bytes_lt" [(asBytes a).val, (asBytes b).val]) =
                    some (Moist.SMT.Semantics.SVal.bool
                      (Moist.Plutus.bytesLt bsa bsb)) at hlt
                  simp [symValToCek?, symConstToCek?, hlt]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LessThanEqualsByteString :
    BuiltinOkSound .LessThanEqualsByteString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_LessThanEqualsByteString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asBytes a).guard (asBytes b).guard)
                  (SymVal.const (SymConst.bool
                    (.app "bytes_le" [(asBytes a).val, (asBytes b).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asBytes a).guard (asBytes b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asBytes a).guard (asBytes b).guard).mp hpc
                obtain ⟨bsa, rfl, hea⟩ := asBytes_sound ha hp.1
                obtain ⟨bsb, rfl, heb⟩ := asBytes_sound hb hp.2
                refine ⟨.VCon (.Bool (Moist.Plutus.bytesLe bsa bsb)), ?_, ?_, ?_⟩
                ·
                  have hle := Moist.SMT.Semantics.eval_bytesLe_of (m := m)
                    (a := (asBytes a).val) (b := (asBytes b).val)
                    (x := bsa) (y := bsb) hea heb
                  change SmtSem.eval m
                    (.app "bytes_le" [(asBytes a).val, (asBytes b).val]) =
                    some (Moist.SMT.Semantics.SVal.bool
                      (Moist.Plutus.bytesLe bsa bsb)) at hle
                  simp [symValToCek?, symConstToCek?, hle]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
axiom evalBuiltinSym_active_ok_Sha2_256 : BuiltinOkSound .Sha2_256
axiom evalBuiltinSym_active_ok_Sha3_256 : BuiltinOkSound .Sha3_256
axiom evalBuiltinSym_active_ok_Blake2b_256 : BuiltinOkSound .Blake2b_256
axiom evalBuiltinSym_active_ok_VerifyEd25519Signature : BuiltinOkSound .VerifyEd25519Signature
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_AppendString : BuiltinOkSound .AppendString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_AppendString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asString a).guard (asString b).guard)
                  (SymVal.const (SymConst.string
                    (SExpr.strAppend (asString a).val (asString b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString a).guard (asString b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asString a).guard (asString b).guard).mp hpc
                obtain ⟨sa, rfl, hea⟩ := asString_sound ha hp.1
                obtain ⟨sb, rfl, heb⟩ := asString_sound hb hp.2
                refine ⟨.VCon (.String (sa ++ sb)), ?_, ?_, ?_⟩
                ·
                  have happ := Moist.SMT.Semantics.eval_strAppend_of (m := m)
                    (a := (asString a).val) (b := (asString b).val)
                    (x := sa) (y := sb) hea heb
                  change SmtSem.eval m (SExpr.strAppend (asString a).val (asString b).val) =
                    some (Moist.SMT.Semantics.SVal.string (sa ++ sb)) at happ
                  simp [symValToCek?, symConstToCek?, happ]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsString : BuiltinOkSound .EqualsString := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsString_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asString a).guard (asString b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asString a).val (asString b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asString a).guard (asString b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asString a).guard (asString b).guard).mp hpc
                obtain ⟨sa, rfl, hea⟩ := asString_sound ha hp.1
                obtain ⟨sb, rfl, heb⟩ := asString_sound hb hp.2
                refine ⟨.VCon (.Bool (sa == sb)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_string_of (m := m)
                    (a := (asString a).val) (b := (asString b).val)
                    (x := sa) (y := sb) hea heb
                  change SmtSem.eval m (SExpr.eq (asString a).val (asString b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (sa == sb)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltin_DecodeUtf8_of_valid {bs : ByteArray}
    (h : String.validateUTF8 bs) :
    Moist.CEK.evalBuiltin .DecodeUtf8 [.VCon (.ByteString bs)] =
      some (.VCon (.String (String.fromUTF8 bs h))) := by
  change (match (if h' : String.validateUTF8 bs then
      some (Const.String (String.fromUTF8 bs h')) else none) with
    | some c => some (CekValue.VCon c)
    | none => none) =
      some (.VCon (.String (String.fromUTF8 bs h)))
  simp [h]

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EncodeUtf8 : BuiltinOkSound .EncodeUtf8 := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons sSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_EncodeUtf8_eq sSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asString sSym).guard
              (SymVal.const (SymConst.bytes
                (.app "uplc_encodeUtf8" [(asString sSym).val]))),
             Outcome.error (SExpr.not (asString sSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cs, hs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨s, rfl, hsEval⟩ := asString_sound hs hpc
            refine ⟨.VCon (.ByteString s.toUTF8), ?_, ?_, ?_⟩
            ·
              have henc := Moist.SMT.Semantics.eval_uplcEncodeUtf8_of
                (m := m) (e := (asString sSym).val) (s := s) hsEval
              simp [symValToCek?, symConstToCek?, henc]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons extra rest2 =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_DecodeUtf8 : BuiltinOkSound .DecodeUtf8 := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_DecodeUtf8_eq bsSym] at hmem
          have hpath := checked2_path_ok hmem hpc
          rcases hpath with ⟨innerPc, hinner, hpcEq, hguard, hinnerPc⟩
          simp only [List.mem_cons, List.not_mem_nil] at hinner
          rcases hinner with hinner | hinner
          · injection hinner with hinnerPcEq hvEq
            subst innerPc
            subst v
            obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbs hguard
            have hvalid := Moist.SMT.Semantics.validUtf8_of_evalBoolIs_validUtf8_true
              (m := m) (e := (asBytes bsSym).val) (bs := bs) hbsEval
              (by simpa [pcHolds] using hinnerPc)
            refine ⟨.VCon (.String (String.fromUTF8 bs hvalid)), ?_, ?_, ?_⟩
            ·
              have hdec := Moist.SMT.Semantics.eval_uplcDecodeUtf8_of
                (m := m) (e := (asBytes bsSym).val) (bs := bs) hbsEval hvalid
              simp [symValToCek?, symConstToCek?, hdec]
            · simp [symValNoOpaqueForSoundness]
            · exact evalBuiltin_DecodeUtf8_of_valid hvalid
          · rcases hinner with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons extra rest2 =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IfThenElse : BuiltinOkSound .IfThenElse := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons elseV rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons thenV rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons cond rest3 =>
              cases rest3 with
              | nil =>
                  rw [evalBuiltinSym_IfThenElse_eq elseV thenV cond] at hmem
                  change Outcome.ok pc v ∈
                    [Outcome.ok (SExpr.and (asBool cond).guard (asBool cond).val) thenV,
                     Outcome.ok (SExpr.and (asBool cond).guard
                      (SExpr.not (asBool cond).val)) elseV,
                     Outcome.error (SExpr.not (asBool cond).guard)] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  obtain ⟨noElse, noThen, _noCond⟩ :=
                    symValsNoOpaque_triple hnoArgs
                  obtain ⟨celse, cthen, ccond, helse, hthen, hcond, rfl⟩ :=
                    symValListToCekList_triple hargs
                  rcases hmem with hthenBranch | hrest
                  · injection hthenBranch with hpcEq hvEq
                    subst pc
                    subst v
                    have hp :=
                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                        (asBool cond).guard (asBool cond).val).mp hpc
                    have hcondCek := asBool_true_to_cek (m := m) (v := cond)
                      hp.1 hp.2
                    rw [hcond] at hcondCek
                    injection hcondCek with hccond
                    subst ccond
                    refine ⟨cthen, hthen, noThen, ?_⟩
                    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
                  · rcases hrest with helseBranch | hbad
                    · injection helseBranch with hpcEq hvEq
                      subst pc
                      subst v
                      have hp :=
                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                          (asBool cond).guard
                          (SExpr.not (asBool cond).val)).mp hpc
                      have hfalse :=
                        (Moist.SMT.Semantics.evalBoolIs_not_true m
                          (asBool cond).val).mp hp.2
                      have hcondCek := asBool_false_to_cek (m := m) (v := cond)
                        hp.1 hfalse
                      rw [hcond] at hcondCek
                      injection hcondCek with hccond
                      subst ccond
                      refine ⟨celse, helse, noElse, ?_⟩
                      simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
                    · rcases hbad with hbad | hfalse
                      · cases hbad
                      · cases hfalse
              | cons _ _ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ChooseUnit : BuiltinOkSound .ChooseUnit := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons result rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons unitV rest2 =>
          cases rest2 with
          | nil =>
              obtain ⟨noResult, _noUnit⟩ := symValsNoOpaque_pair hnoArgs
              obtain ⟨cresult, cunit, hresult, hunit, rfl⟩ :=
                symValListToCekList_pair hargs
              cases unitV with
              | const c =>
                  cases c <;>
                    try
                      change Outcome.ok pc v ∈ err at hmem
                      simp [err] at hmem
                  case unit =>
                    change Outcome.ok pc v ∈ ok result at hmem
                    simp [ok] at hmem
                    rcases hmem with ⟨rfl, rfl⟩
                    have hunitCek := unitGuard_sound (m := m) (u := SymVal.const .unit)
                      hunit hpc
                    subst cunit
                    refine ⟨cresult, hresult, noResult, ?_⟩
                    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
              | dyn e =>
                  change Outcome.ok pc v ∈
                    [Outcome.ok (SExpr.isCtor "VUnit" e) result,
                     Outcome.error (SExpr.not (SExpr.isCtor "VUnit" e))] at hmem
                  simp only [List.mem_cons, List.not_mem_nil] at hmem
                  rcases hmem with hmem | hbad
                  · injection hmem with hpcEq hvEq
                    subst pc
                    subst v
                    have hunitCek := unitGuard_sound (m := m) (u := SymVal.dyn e)
                      hunit hpc
                    subst cunit
                    refine ⟨cresult, hresult, noResult, ?_⟩
                    simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
                  · rcases hbad with hbad | hfalse
                    · cases hbad
                    · cases hfalse
              | pair a b =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | constr tag fields =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | lam body ρ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | delay body ρ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | builtin b bargs ea =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_Trace : BuiltinOkSound .Trace := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons result rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons msg rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_Trace_eq result msg] at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hmsgGuard, _hinnerPc⟩
              change Outcome.ok innerPc v ∈ ok result at hinner
              simp [ok] at hinner
              rcases hinner with ⟨rfl, rfl⟩
              obtain ⟨noResult, _noMsg⟩ := symValsNoOpaque_pair hnoArgs
              obtain ⟨cresult, cmsg, hresult, hmsg, rfl⟩ :=
                symValListToCekList_pair hargs
              obtain ⟨s, rfl, _hmsgEval⟩ := asString_sound hmsg hmsgGuard
              refine ⟨cresult, hresult, noResult, ?_⟩
              simp [Moist.CEK.evalBuiltin, Moist.CEK.evalBuiltinPassThrough]
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0

theorem evalBuiltinSym_active_ok_FstPair : BuiltinOkSound .FstPair := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons p rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.1,
              Outcome.ok pd.guard (.const (.data pd.val.1)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          have hnoP := symValsNoOpaque_singleton hnoArgs
          rcases hmem with hpair | hpd | herr
          · injection hpair with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, hfst, _hsnd⟩ := asPair_sound hp hpc
            refine ⟨.VCon a, hfst, asPair_fst_noOpaque hnoP, ?_⟩
            exact Moist.CEK.evalBuiltin_FstPair_pair a b
          · injection hpd with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, hfst, _hsnd⟩ := asPairData_sound hp hpc
            refine ⟨.VCon (.Data a), ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hfst]
            · exact Moist.CEK.evalBuiltin_FstPair_pairData a b
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

theorem evalBuiltinSym_active_ok_SndPair : BuiltinOkSound .SndPair := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons p rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let pp := asPair p
             let pd := asPairData p
             [Outcome.ok pp.guard pp.val.2,
              Outcome.ok pd.guard (.const (.data pd.val.2)),
              Outcome.error (SExpr.not (SExpr.or pp.guard pd.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cp, hp, rfl⟩ := symValListToCekList_singleton hargs
          have hnoP := symValsNoOpaque_singleton hnoArgs
          rcases hmem with hpair | hpd | herr
          · injection hpair with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, _hfst, hsnd⟩ := asPair_sound hp hpc
            refine ⟨.VCon b, hsnd, asPair_snd_noOpaque hnoP, ?_⟩
            exact Moist.CEK.evalBuiltin_SndPair_pair a b
          · injection hpd with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨a, b, rfl, _hfst, hsnd⟩ := asPairData_sound hp hpc
            refine ⟨.VCon (.Data b), ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hsnd]
            · exact Moist.CEK.evalBuiltin_SndPair_pairData a b
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ChooseList : BuiltinOkSound .ChooseList := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons consCase rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons nilCase rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons xs rest3 =>
              cases rest3 with
              | nil =>
                  change Outcome.ok pc v ∈
                    (let dl := asDataList xs
                     let vl := asConstList xs
                     let dBranches :=
                       [Outcome.ok (SExpr.and dl.guard (SExpr.isCtor "DNil" dl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                          consCase]
                     let vBranches :=
                       [Outcome.ok (SExpr.and vl.guard (SExpr.isCtor "VNil" vl.val))
                          nilCase,
                        Outcome.ok
                          (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                          consCase]
                     dBranches ++ vBranches ++
                       [Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
                  simp only [List.mem_cons, List.not_mem_nil, List.mem_append] at hmem
                  obtain ⟨ccons, cnil, cxs, hcons, hnil, hxs, rfl⟩ :=
                    symValListToCekList_triple hargs
                  obtain ⟨hnoCons, hnoNil, _hnoXs⟩ :=
                    symValsNoOpaque_triple hnoArgs
                  rcases hmem with hdv | herr
                  · rcases hdv with hd | hv
                    · rcases hd with hdNil | hdRest
                      · injection hdNil with hpcEq hvEq
                        subst pc
                        subst v
                        have hp :=
                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                            (asDataList xs).guard
                            (SExpr.isCtor "DNil" (asDataList xs).val)).mp hpc
                        obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
                        cases ds with
                        | nil =>
                            exact ⟨cnil, hnil, hnoNil,
                              Moist.CEK.evalBuiltin_ChooseList_dataList_nil cnil ccons⟩
                        | cons d ds =>
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons
                                hEval
                            exact False.elim (evalBoolIs_true_false_contra hp.2 hfalse)
                      · rcases hdRest with hdCons | hdFalse
                        · injection hdCons with hpcEq hvEq
                          subst pc
                          subst v
                          have hp :=
                            (Moist.SMT.Semantics.evalBoolIs_and_true m
                              (asDataList xs).guard
                              (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val))).mp hpc
                          obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
                          cases ds with
                          | nil =>
                              have hnil :=
                                Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                                  hEval
                              have hnot :=
                                (Moist.SMT.Semantics.evalBoolIs_not_true m
                                  (SExpr.isCtor "DNil" (asDataList xs).val)).mp hp.2
                              exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          | cons d ds =>
                              exact ⟨ccons, hcons, hnoCons,
                                Moist.CEK.evalBuiltin_ChooseList_dataList_cons
                                  d ds cnil ccons⟩
                        · cases hdFalse
                    · rcases hv with hvNil | hvRest
                      · injection hvNil with hpcEq hvEq
                        subst pc
                        subst v
                        have hp :=
                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                            (asConstList xs).guard
                            (SExpr.isCtor "VNil" (asConstList xs).val)).mp hpc
                        obtain ⟨vals, cs, rfl, hEval, hconsts⟩ :=
                          asConstList_sound hxs hp.1
                        cases vals with
                        | nil =>
                            simp [semValListToConstList?] at hconsts
                            subst cs
                            exact ⟨cnil, hnil, hnoNil,
                              Moist.CEK.evalBuiltin_ChooseList_constList_nil cnil ccons⟩
                        | cons vh vt =>
                            have hfalse :=
                              Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons
                                hEval
                            exact False.elim (evalBoolIs_true_false_contra hp.2 hfalse)
                      · rcases hvRest with hvCons | hvFalse
                        · injection hvCons with hpcEq hvEq
                          subst pc
                          subst v
                          have hp :=
                            (Moist.SMT.Semantics.evalBoolIs_and_true m
                              (asConstList xs).guard
                              (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val))).mp hpc
                          obtain ⟨vals, cs, rfl, hEval, hconsts⟩ :=
                            asConstList_sound hxs hp.1
                          cases vals with
                          | nil =>
                              have hnil :=
                                Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                                  hEval
                              have hnot :=
                                (Moist.SMT.Semantics.evalBoolIs_not_true m
                                  (SExpr.isCtor "VNil" (asConstList xs).val)).mp hp.2
                              exact False.elim (evalBoolIs_true_false_contra hnil hnot)
                          | cons vh vt =>
                              cases hheadConst : semValToConst? vh <;>
                                simp [semValListToConstList?, hheadConst] at hconsts
                              rename_i ch
                              cases htailConst : semValListToConstList? vt <;>
                                simp [htailConst] at hconsts
                              rename_i ct
                              subst cs
                              exact ⟨ccons, hcons, hnoCons,
                                Moist.CEK.evalBuiltin_ChooseList_constList_cons
                                  ch ct cnil ccons⟩
                        · cases hvFalse
                  · rcases herr with herr | hfalse
                    · cases herr
                    · cases hfalse
              | cons _ _ =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
theorem evalBuiltinSym_active_ok_MkCons : BuiltinOkSound .MkCons := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons tail rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons head rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈
                (let dl := asDataList tail
                 let hd := asData head
                 let vl := asConstList tail
                 let hv := asConstVal head
                 let dataOk := SExpr.and dl.guard hd.guard
                 let constOk := SExpr.and vl.guard hv.guard
                 [Outcome.ok dataOk (.const (.dataList (.app "DCons" [hd.val, dl.val]))),
                  Outcome.ok constOk (.const (.constList (.app "VCons" [hv.val, vl.val]))),
                  Outcome.error (SExpr.not (SExpr.or dataOk constOk))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨ctail, chead, htail, hhead, rfl⟩ :=
                symValListToCekList_pair hargs
              rcases hmem with hdata | hconst | herr
              · injection hdata with hpcEq hvEq
                subst pc
                subst v
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asDataList tail).guard (asData head).guard).mp hpc
                obtain ⟨ds, htailEq, htailEval⟩ := asDataList_sound htail hp.1
                subst ctail
                obtain ⟨d, hheadEq, hheadEval⟩ := asData_sound hhead hp.2
                subst chead
                have hconsEval :=
                  Moist.SMT.Semantics.eval_DCons_of
                    (m := m) (h := (asData head).val) (t := (asDataList tail).val)
                    hheadEval htailEval
                refine ⟨.VCon (.ConstDataList (d :: ds)), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hconsEval]
                · exact Moist.CEK.evalBuiltin_MkCons_dataList d ds
              · injection hconst with hpcEq hvEq
                subst pc
                subst v
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asConstList tail).guard (asConstVal head).guard).mp hpc
                obtain ⟨vals, cs, htailEq, htailEval, htailConsts⟩ :=
                  asConstList_sound htail hp.1
                subst ctail
                obtain ⟨c, semv, hheadEq, hheadEval, hheadConst⟩ :=
                  asConstVal_sound hhead hp.2
                subst chead
                have hconsEval :=
                  Moist.SMT.Semantics.eval_VCons_of
                    (m := m) (h := (asConstVal head).val) (t := (asConstList tail).val)
                    hheadEval htailEval
                refine ⟨.VCon (.ConstList (c :: cs)), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · have hconstsCons :
                    semValListToConstList? (semv :: vals) = some (c :: cs) := by
                    simp [semValListToConstList?, hheadConst, htailConsts]
                  simp [symValToCek?, symConstToCek?, hconsEval, hconstsCons]
                · exact Moist.CEK.evalBuiltin_MkCons_constList c cs
              · rcases herr with herr | hfalse
                · cases herr
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_HeadList : BuiltinOkSound .HeadList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.data (.app "dhead" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.dyn (.app "vhead" [vl.val])),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · injection hd with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asDataList xs).guard
                (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val))).mp hpc
            obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
            cases ds with
            | nil =>
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "DNil" (asDataList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons d ds =>
                have hhead :=
                  Moist.SMT.Semantics.eval_dhead_of (m := m)
                    (e := (asDataList xs).val) (h := d) (t := ds) hEval
                refine ⟨.VCon (.Data d), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hhead]
                · exact Moist.CEK.evalBuiltin_HeadList_dataList d ds
          · injection hv with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asConstList xs).guard
                (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val))).mp hpc
            obtain ⟨vals, cs, rfl, hEval, hconsts⟩ := asConstList_sound hxs hp.1
            cases vals with
            | nil =>
                simp [semValListToConstList?] at hconsts
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "VNil" (asConstList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons vh vt =>
                cases hheadConst : semValToConst? vh <;>
                  simp [semValListToConstList?, hheadConst] at hconsts
                rename_i ch
                cases htailConst : semValListToConstList? vt <;>
                  simp [htailConst] at hconsts
                rename_i ct
                subst cs
                have hheadEval :=
                  Moist.SMT.Semantics.eval_vhead_of (m := m)
                    (e := (asConstList xs).val) (h := vh) (t := vt) hEval
                have hheadCek := semValToCek_of_const hheadConst
                refine ⟨.VCon ch, ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, hheadEval, hheadCek]
                · exact Moist.CEK.evalBuiltin_HeadList_constList ch ct
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_TailList : BuiltinOkSound .TailList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok
                (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                (.const (.dataList (.app "dtail" [dl.val]))),
              Outcome.ok
                (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))
                (.const (.constList (.app "vtail" [vl.val]))),
              Outcome.error (SExpr.not
                (SExpr.or
                  (SExpr.and dl.guard (SExpr.not (SExpr.isCtor "DNil" dl.val)))
                  (SExpr.and vl.guard (SExpr.not (SExpr.isCtor "VNil" vl.val)))))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · injection hd with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asDataList xs).guard
                (SExpr.not (SExpr.isCtor "DNil" (asDataList xs).val))).mp hpc
            obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hp.1
            cases ds with
            | nil =>
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "DNil" (asDataList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons d ds =>
                have htail :=
                  Moist.SMT.Semantics.eval_dtail_of (m := m)
                    (e := (asDataList xs).val) (h := d) (t := ds) hEval
                refine ⟨.VCon (.ConstDataList ds), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, htail]
                · exact Moist.CEK.evalBuiltin_TailList_dataList d ds
          · injection hv with hpcEq hvEq
            subst pc
            subst v
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asConstList xs).guard
                (SExpr.not (SExpr.isCtor "VNil" (asConstList xs).val))).mp hpc
            obtain ⟨vals, cs, rfl, hEval, hconsts⟩ := asConstList_sound hxs hp.1
            cases vals with
            | nil =>
                simp [semValListToConstList?] at hconsts
                have hnil :=
                  Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                    hEval
                have hnot :=
                  (Moist.SMT.Semantics.evalBoolIs_not_true m
                    (SExpr.isCtor "VNil" (asConstList xs).val)).mp hp.2
                exact False.elim (evalBoolIs_true_false_contra hnil hnot)
            | cons vh vt =>
                cases hheadConst : semValToConst? vh <;>
                  simp [semValListToConstList?, hheadConst] at hconsts
                rename_i ch
                cases htailConst : semValListToConstList? vt <;>
                  simp [htailConst] at hconsts
                rename_i ct
                subst cs
                have htailEval :=
                  Moist.SMT.Semantics.eval_vtail_of (m := m)
                    (e := (asConstList xs).val) (h := vh) (t := vt) hEval
                refine ⟨.VCon (.ConstList ct), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, htailEval, htailConst]
                · exact Moist.CEK.evalBuiltin_TailList_constList ch ct
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_NullList : BuiltinOkSound .NullList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            (let dl := asDataList xs
             let vl := asConstList xs
             [Outcome.ok dl.guard (.const (.bool (SExpr.isCtor "DNil" dl.val))),
              Outcome.ok vl.guard (.const (.bool (SExpr.isCtor "VNil" vl.val))),
              Outcome.error (SExpr.not (SExpr.or dl.guard vl.guard))]) at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hd | hv | herr
          · injection hd with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨ds, rfl, hEval⟩ := asDataList_sound hxs hpc
            cases ds with
            | nil =>
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "DNil" (asDataList xs).val) =
                      some (.bool true) :=
                  (Moist.SMT.Semantics.evalBoolIs_true_eq m
                    (SExpr.isCtor "DNil" (asDataList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isDNil_true_of_dataList_nil
                      hEval)
                refine ⟨.VCon (.Bool true), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_dataList []
            | cons d ds =>
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "DNil" (asDataList xs).val) =
                      some (.bool false) :=
                  (evalBoolIs_false_eq (m := m)
                    (e := SExpr.isCtor "DNil" (asDataList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isDNil_false_of_dataList_cons
                      hEval)
                refine ⟨.VCon (.Bool false), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_dataList (d :: ds)
          · injection hv with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨vals, cs, rfl, hEval, hconsts⟩ := asConstList_sound hxs hpc
            cases vals with
            | nil =>
                simp [semValListToConstList?] at hconsts
                subst cs
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "VNil" (asConstList xs).val) =
                      some (.bool true) :=
                  (Moist.SMT.Semantics.evalBoolIs_true_eq m
                    (SExpr.isCtor "VNil" (asConstList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isVNil_true_of_valList_nil
                      hEval)
                refine ⟨.VCon (.Bool true), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_constList []
            | cons vh vt =>
                cases hhead : semValToConst? vh <;>
                  simp [semValListToConstList?, hhead] at hconsts
                rename_i ch
                cases htail : semValListToConstList? vt <;>
                  simp [htail] at hconsts
                rename_i ct
                subst cs
                have hbool :
                    SmtSem.eval m (SExpr.isCtor "VNil" (asConstList xs).val) =
                      some (.bool false) :=
                  (evalBoolIs_false_eq (m := m)
                    (e := SExpr.isCtor "VNil" (asConstList xs).val)).mp
                    (Moist.SMT.Semantics.evalBoolIs_isVNil_false_of_valList_cons
                      hEval)
                refine ⟨.VCon (.Bool false), ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, symConstToCek?, hbool]
                · exact Moist.CEK.evalBuiltin_NullList_constList (ch :: ct)
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ChooseData : BuiltinOkSound .ChooseData := by
  intro m args cargs pc v hargs hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bCase rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons iCase rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons listCase rest3 =>
              cases rest3 with
              | nil =>
                  change Outcome.ok pc v ∈ err at hmem
                  simp [err] at hmem
              | cons mapCase rest4 =>
                  cases rest4 with
                  | nil =>
                      change Outcome.ok pc v ∈ err at hmem
                      simp [err] at hmem
                  | cons constrCase rest5 =>
                      cases rest5 with
                      | nil =>
                          change Outcome.ok pc v ∈ err at hmem
                          simp [err] at hmem
                      | cons dVal rest6 =>
                          cases rest6 with
                          | nil =>
                              change Outcome.ok pc v ∈
                                (let d := asData dVal
                                 [Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DConstr" d.val))
                                    constrCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DMap" d.val))
                                    mapCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DList" d.val))
                                    listCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DI" d.val))
                                    iCase,
                                  Outcome.ok (SExpr.and d.guard (SExpr.isCtor "DB" d.val))
                                    bCase,
                                  Outcome.error (SExpr.not d.guard)]) at hmem
                              simp only [List.mem_cons, List.not_mem_nil] at hmem
                              obtain ⟨cb, ci, cl, cm, cc, cd, hb, hi, hl, hm, hc, hd,
                                  rfl⟩ :=
                                symValListToCekList_six hargs
                              obtain ⟨hnoB, hnoI, hnoL, hnoM, hnoC, _hnoD⟩ :=
                                symValsNoOpaque_six hnoArgs
                              rcases hmem with hConstr | rest
                              · injection hConstr with hpcEq hvEq
                                subst pc
                                subst v
                                have hp :=
                                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                                    (asData dVal).guard
                                    (SExpr.isCtor "DConstr" (asData dVal).val)).mp hpc
                                obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                obtain ⟨tag, fields, hctorEval⟩ :=
                                  Moist.SMT.Semantics.evalBoolIs_isDConstr_true hp.2
                                have hdEq0 := hctorEval.symm.trans hdEval
                                injection hdEq0 with hdEq
                                cases hdEq
                                exact ⟨cc, hc, hnoC,
                                  Moist.CEK.evalBuiltin_ChooseData_constr
                                    tag fields cb ci cl cm cc⟩
                              · rcases rest with hMap | rest
                                · injection hMap with hpcEq hvEq
                                  subst pc
                                  subst v
                                  have hp :=
                                    (Moist.SMT.Semantics.evalBoolIs_and_true m
                                      (asData dVal).guard
                                      (SExpr.isCtor "DMap" (asData dVal).val)).mp hpc
                                  obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                  obtain ⟨ps, hctorEval⟩ :=
                                    Moist.SMT.Semantics.evalBoolIs_isDMap_true hp.2
                                  have hdEq0 := hctorEval.symm.trans hdEval
                                  injection hdEq0 with hdEq
                                  cases hdEq
                                  exact ⟨cm, hm, hnoM,
                                    Moist.CEK.evalBuiltin_ChooseData_map
                                      ps cb ci cl cm cc⟩
                                · rcases rest with hList | rest
                                  · injection hList with hpcEq hvEq
                                    subst pc
                                    subst v
                                    have hp :=
                                      (Moist.SMT.Semantics.evalBoolIs_and_true m
                                        (asData dVal).guard
                                        (SExpr.isCtor "DList" (asData dVal).val)).mp hpc
                                    obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                    obtain ⟨xs, hctorEval⟩ :=
                                      Moist.SMT.Semantics.evalBoolIs_isDList_true hp.2
                                    have hdEq0 := hctorEval.symm.trans hdEval
                                    injection hdEq0 with hdEq
                                    cases hdEq
                                    exact ⟨cl, hl, hnoL,
                                      Moist.CEK.evalBuiltin_ChooseData_list
                                        xs cb ci cl cm cc⟩
                                  · rcases rest with hI | rest
                                    · injection hI with hpcEq hvEq
                                      subst pc
                                      subst v
                                      have hp :=
                                        (Moist.SMT.Semantics.evalBoolIs_and_true m
                                          (asData dVal).guard
                                          (SExpr.isCtor "DI" (asData dVal).val)).mp hpc
                                      obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                      obtain ⟨i, hctorEval⟩ :=
                                        Moist.SMT.Semantics.evalBoolIs_isDI_true hp.2
                                      have hdEq0 := hctorEval.symm.trans hdEval
                                      injection hdEq0 with hdEq
                                      cases hdEq
                                      exact ⟨ci, hi, hnoI,
                                        Moist.CEK.evalBuiltin_ChooseData_i
                                          i cb ci cl cm cc⟩
                                    · rcases rest with hB | herr
                                      · injection hB with hpcEq hvEq
                                        subst pc
                                        subst v
                                        have hp :=
                                          (Moist.SMT.Semantics.evalBoolIs_and_true m
                                            (asData dVal).guard
                                            (SExpr.isCtor "DB" (asData dVal).val)).mp hpc
                                        obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
                                        obtain ⟨bs, hctorEval⟩ :=
                                          Moist.SMT.Semantics.evalBoolIs_isDB_true hp.2
                                        have hdEq0 := hctorEval.symm.trans hdEval
                                        injection hdEq0 with hdEq
                                        cases hdEq
                                        exact ⟨cb, hb, hnoB,
                                          Moist.CEK.evalBuiltin_ChooseData_b
                                            bs cb ci cl cm cc⟩
                                      · rcases herr with herr | hfalse
                                        · cases herr
                                        · cases hfalse
                          | cons _ _ =>
                              change Outcome.ok pc v ∈ err at hmem
                              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ConstrData : BuiltinOkSound .ConstrData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons fields rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons tag rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_ConstrData_eq fields tag] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asInt tag).guard (asDataList fields).guard)
                  (SymVal.const (SymConst.data
                    (.app "DConstr" [(asInt tag).val, (asDataList fields).val]))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asInt tag).guard (asDataList fields).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cfields, ctag, hfields, htag, rfl⟩ :=
                  symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt tag).guard (asDataList fields).guard).mp hpc
                obtain ⟨itag, rfl, htagEval⟩ := asInt_sound htag hp.1
                obtain ⟨xs, rfl, hfieldsEval⟩ := asDataList_sound hfields hp.2
                refine ⟨.VCon (.Data (.Constr itag xs)), ?_, ?_, ?_⟩
                ·
                  have hc := Moist.SMT.Semantics.eval_DConstr_of (m := m)
                    (tag := (asInt tag).val) (fields := (asDataList fields).val)
                    htagEval hfieldsEval
                  simp [symValToCek?, symConstToCek?, hc]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MapData : BuiltinOkSound .MapData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons ps rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MapData_eq ps] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asPairDataList ps).guard
              (SymVal.const (SymConst.data (.app "DMap" [(asPairDataList ps).val]))),
             Outcome.error (SExpr.not (asPairDataList ps).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cps, hps, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨xs, rfl, hpsEval⟩ := asPairDataList_sound hps hpc
            refine ⟨.VCon (.Data (.Map xs)), ?_, ?_, ?_⟩
            ·
              have hm := Moist.SMT.Semantics.eval_DMap_of (m := m)
                (ps := (asPairDataList ps).val) hpsEval
              simp [symValToCek?, symConstToCek?, hm]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ListData : BuiltinOkSound .ListData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_ListData_eq xsSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asDataList xsSym).guard
              (SymVal.const (SymConst.data (.app "DList" [(asDataList xsSym).val]))),
             Outcome.error (SExpr.not (asDataList xsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨xs, rfl, hxsEval⟩ := asDataList_sound hxs hpc
            refine ⟨.VCon (.Data (.List xs)), ?_, ?_, ?_⟩
            ·
              have hl := Moist.SMT.Semantics.eval_DList_of (m := m)
                (e := (asDataList xsSym).val) hxsEval
              simp [symValToCek?, symConstToCek?, hl]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IData : BuiltinOkSound .IData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons iSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_IData_eq iSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asInt iSym).guard
              (SymVal.const (SymConst.data (.app "DI" [(asInt iSym).val]))),
             Outcome.error (SExpr.not (asInt iSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨ci, hi, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨i, rfl, hiEval⟩ := asInt_sound hi hpc
            refine ⟨.VCon (.Data (.I i)), ?_, ?_, ?_⟩
            ·
              have hdi := Moist.SMT.Semantics.eval_DI_of (m := m)
                (e := (asInt iSym).val) hiEval
              simp [symValToCek?, symConstToCek?, hdi]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_BData : BuiltinOkSound .BData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons bsSym rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_BData_eq bsSym] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (asBytes bsSym).guard
              (SymVal.const (SymConst.data (.app "DB" [(asBytes bsSym).val]))),
             Outcome.error (SExpr.not (asBytes bsSym).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cbs, hbs, rfl⟩ := symValListToCekList_singleton hargs
            obtain ⟨bs, rfl, hbsEval⟩ := asBytes_sound hbs hpc
            refine ⟨.VCon (.Data (.B bs)), ?_, ?_, ?_⟩
            ·
              have hdb := Moist.SMT.Semantics.eval_DB_of (m := m)
                (e := (asBytes bsSym).val) hbsEval
              simp [symValToCek?, symConstToCek?, hdb]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnConstrData : BuiltinOkSound .UnConstrData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnConstrData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DConstr" (asData dVal).val))
              (SymVal.const (SymConst.pairData
                (.app "DI" [.app "dataConstrTag" [(asData dVal).val]])
                (.app "DList" [.app "dataConstrFields" [(asData dVal).val]]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DConstr" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DConstr" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨tag, fields, hctorEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDConstr_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hctorEval
            injection hctorEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.PairData (.I tag, .List fields)), ?_, ?_, ?_⟩
            ·
              have htagEval := Moist.SMT.Semantics.eval_dataConstrTag_of
                (m := m) (e := (asData dVal).val) hdEval
              have hfieldsEval := Moist.SMT.Semantics.eval_dataConstrFields_of
                (m := m) (e := (asData dVal).val) hdEval
              have hdi := Moist.SMT.Semantics.eval_DI_of (m := m)
                (e := .app "dataConstrTag" [(asData dVal).val]) htagEval
              have hdl := Moist.SMT.Semantics.eval_DList_of (m := m)
                (e := .app "dataConstrFields" [(asData dVal).val]) hfieldsEval
              simp [symValToCek?, symConstToCek?, hdi, hdl]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnMapData : BuiltinOkSound .UnMapData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnMapData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DMap" (asData dVal).val))
              (SymVal.const (SymConst.pairDataList
                (.app "dataMapEntries" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DMap" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DMap" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨ps, hmapEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDMap_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hmapEval
            injection hmapEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.ConstPairDataList ps), ?_, ?_, ?_⟩
            ·
              have hentries := Moist.SMT.Semantics.eval_dataMapEntries_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hentries]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnListData : BuiltinOkSound .UnListData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnListData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DList" (asData dVal).val))
              (SymVal.const (SymConst.dataList
                (.app "dataListItems" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DList" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DList" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨xs, hlistEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDList_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hlistEval
            injection hlistEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.ConstDataList xs), ?_, ?_, ?_⟩
            ·
              have hitems := Moist.SMT.Semantics.eval_dataListItems_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hitems]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnIData : BuiltinOkSound .UnIData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnIData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DI" (asData dVal).val))
              (SymVal.const (SymConst.integer
                (.app "dataInt" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DI" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DI" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨i, hiEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDI_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hiEval
            injection hiEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.Integer i), ?_, ?_, ?_⟩
            ·
              have hint := Moist.SMT.Semantics.eval_dataInt_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hint]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_UnBData : BuiltinOkSound .UnBData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons dVal rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_UnBData_eq dVal] at hmem
          change Outcome.ok pc v ∈
            [Outcome.ok (SExpr.and (asData dVal).guard
              (SExpr.isCtor "DB" (asData dVal).val))
              (SymVal.const (SymConst.bytes
                (.app "dataBytes" [(asData dVal).val]))),
             Outcome.error (SExpr.and (asData dVal).guard
              (SExpr.not (SExpr.isCtor "DB" (asData dVal).val))),
             Outcome.error (SExpr.not (asData dVal).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cd, hd, rfl⟩ := symValListToCekList_singleton hargs
            have hp :=
              (Moist.SMT.Semantics.evalBoolIs_and_true m
                (asData dVal).guard
                (SExpr.isCtor "DB" (asData dVal).val)).mp hpc
            obtain ⟨d, rfl, hdEval⟩ := asData_sound hd hp.1
            obtain ⟨bs, hbytesEval⟩ :=
              Moist.SMT.Semantics.evalBoolIs_isDB_true
                (m := m) (e := (asData dVal).val)
                (by simpa [pcHolds] using hp.2)
            change Moist.SMT.Semantics.eval m (asData dVal).val =
              some (Moist.SMT.Semantics.SVal.data d) at hdEval
            rw [hdEval] at hbytesEval
            injection hbytesEval with hdEq
            injection hdEq with hdDataEq
            subst d
            refine ⟨.VCon (.ByteString bs), ?_, ?_, ?_⟩
            ·
              have hbs := Moist.SMT.Semantics.eval_dataBytes_of
                (m := m) (e := (asData dVal).val) hdEval
              simp [symValToCek?, symConstToCek?, hbs]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hmem
            · cases hbad
            · rcases hmem with hbad | hfalse
              · cases hbad
              · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_EqualsData : BuiltinOkSound .EqualsData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_EqualsData_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asData a).guard (asData b).guard)
                  (SymVal.const (SymConst.bool
                    (SExpr.eq (asData a).val (asData b).val))),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData a).guard (asData b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asData a).guard (asData b).guard).mp hpc
                obtain ⟨da, rfl, hea⟩ := asData_sound ha hp.1
                obtain ⟨db, rfl, heb⟩ := asData_sound hb hp.2
                refine ⟨.VCon (.Bool (da == db)), ?_, ?_, ?_⟩
                ·
                  have heq := Moist.SMT.Semantics.eval_eq_data_of (m := m)
                    (a := (asData a).val) (b := (asData b).val)
                    (x := da) (y := db) hea heb
                  change SmtSem.eval m (SExpr.eq (asData a).val (asData b).val) =
                    some (Moist.SMT.Semantics.SVal.bool (da == db)) at heq
                  simp [symValToCek?, symConstToCek?, heq]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MkPairData : BuiltinOkSound .MkPairData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons b rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons a rest2 =>
          cases rest2 with
          | nil =>
              rw [evalBuiltinSym_MkPairData_eq b a] at hmem
              change Outcome.ok pc v ∈
                [Outcome.ok (SExpr.and (asData a).guard (asData b).guard)
                  (SymVal.const (SymConst.pairData (asData a).val (asData b).val)),
                 Outcome.error (SExpr.not
                  (SExpr.and (asData a).guard (asData b).guard))] at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              rcases hmem with hmem | hmem
              · injection hmem with hpcEq hvEq
                subst pc
                subst v
                obtain ⟨cb, ca, hb, ha, rfl⟩ := symValListToCekList_pair hargs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asData a).guard (asData b).guard).mp hpc
                obtain ⟨da, rfl, haEval⟩ := asData_sound ha hp.1
                obtain ⟨db, rfl, hbEval⟩ := asData_sound hb hp.2
                refine ⟨.VCon (.PairData (da, db)), ?_, ?_, ?_⟩
                · simp [symValToCek?, symConstToCek?, haEval, hbEval]
                · simp [symValNoOpaqueForSoundness]
                · rfl
              · rcases hmem with hbad | hfalse
                · cases hbad
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MkNilData : BuiltinOkSound .MkNilData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
            have hunit := unitGuard_sound hu hpc
            subst cu
            refine ⟨.VCon (.ConstDataList []), ?_, ?_, ?_⟩
            · simp [symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval_DNil]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_MkNilPairData : BuiltinOkSound .MkNilPairData := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons u rest =>
      cases rest with
      | nil =>
          rw [evalBuiltinSym_MkNilPairData_eq u] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · injection hmem with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨cu, hu, rfl⟩ := symValListToCekList_singleton hargs
            have hunit := unitGuard_sound hu hpc
            subst cu
            refine ⟨.VCon (.ConstPairDataList []), ?_, ?_, ?_⟩
            · simp [symValToCek?, symConstToCek?, Moist.SMT.Semantics.eval_DPNil]
            · simp [symValNoOpaqueForSoundness]
            · rfl
          · rcases hmem with hbad | hfalse
            · cases hbad
            · cases hfalse
      | cons _ rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem
axiom evalBuiltinSym_active_ok_SerializeData : BuiltinOkSound .SerializeData
axiom evalBuiltinSym_active_ok_VerifyEcdsaSecp256k1Signature : BuiltinOkSound .VerifyEcdsaSecp256k1Signature
axiom evalBuiltinSym_active_ok_VerifySchnorrSecp256k1Signature : BuiltinOkSound .VerifySchnorrSecp256k1Signature
axiom evalBuiltinSym_active_ok_Bls12_381_G1_add : BuiltinOkSound .Bls12_381_G1_add
axiom evalBuiltinSym_active_ok_Bls12_381_G1_neg : BuiltinOkSound .Bls12_381_G1_neg
axiom evalBuiltinSym_active_ok_Bls12_381_G1_scalarMul : BuiltinOkSound .Bls12_381_G1_scalarMul
axiom evalBuiltinSym_active_ok_Bls12_381_G1_equal : BuiltinOkSound .Bls12_381_G1_equal
axiom evalBuiltinSym_active_ok_Bls12_381_G1_hashToGroup : BuiltinOkSound .Bls12_381_G1_hashToGroup
axiom evalBuiltinSym_active_ok_Bls12_381_G1_compress : BuiltinOkSound .Bls12_381_G1_compress
axiom evalBuiltinSym_active_ok_Bls12_381_G1_uncompress : BuiltinOkSound .Bls12_381_G1_uncompress
axiom evalBuiltinSym_active_ok_Bls12_381_G2_add : BuiltinOkSound .Bls12_381_G2_add
axiom evalBuiltinSym_active_ok_Bls12_381_G2_neg : BuiltinOkSound .Bls12_381_G2_neg
axiom evalBuiltinSym_active_ok_Bls12_381_G2_scalarMul : BuiltinOkSound .Bls12_381_G2_scalarMul
axiom evalBuiltinSym_active_ok_Bls12_381_G2_equal : BuiltinOkSound .Bls12_381_G2_equal
axiom evalBuiltinSym_active_ok_Bls12_381_G2_hashToGroup : BuiltinOkSound .Bls12_381_G2_hashToGroup
axiom evalBuiltinSym_active_ok_Bls12_381_G2_compress : BuiltinOkSound .Bls12_381_G2_compress
axiom evalBuiltinSym_active_ok_Bls12_381_G2_uncompress : BuiltinOkSound .Bls12_381_G2_uncompress
axiom evalBuiltinSym_active_ok_Bls12_381_millerLoop : BuiltinOkSound .Bls12_381_millerLoop
axiom evalBuiltinSym_active_ok_Bls12_381_mulMlResult : BuiltinOkSound .Bls12_381_mulMlResult
axiom evalBuiltinSym_active_ok_Bls12_381_finalVerify : BuiltinOkSound .Bls12_381_finalVerify
axiom evalBuiltinSym_active_ok_Keccak_256 : BuiltinOkSound .Keccak_256
axiom evalBuiltinSym_active_ok_Blake2b_224 : BuiltinOkSound .Blake2b_224
axiom evalBuiltinSym_active_ok_IntegerToByteString : BuiltinOkSound .IntegerToByteString
axiom evalBuiltinSym_active_ok_ByteStringToInteger : BuiltinOkSound .ByteStringToInteger
axiom evalBuiltinSym_active_ok_AndByteString : BuiltinOkSound .AndByteString
axiom evalBuiltinSym_active_ok_OrByteString : BuiltinOkSound .OrByteString
axiom evalBuiltinSym_active_ok_XorByteString : BuiltinOkSound .XorByteString
axiom evalBuiltinSym_active_ok_ComplementByteString : BuiltinOkSound .ComplementByteString
axiom evalBuiltinSym_active_ok_ReadBit : BuiltinOkSound .ReadBit
axiom evalBuiltinSym_active_ok_WriteBits : BuiltinOkSound .WriteBits
axiom evalBuiltinSym_active_ok_ReplicateByte : BuiltinOkSound .ReplicateByte
axiom evalBuiltinSym_active_ok_ShiftByteString : BuiltinOkSound .ShiftByteString
axiom evalBuiltinSym_active_ok_RotateByteString : BuiltinOkSound .RotateByteString
axiom evalBuiltinSym_active_ok_CountSetBits : BuiltinOkSound .CountSetBits
axiom evalBuiltinSym_active_ok_FindFirstSetBit : BuiltinOkSound .FindFirstSetBit
axiom evalBuiltinSym_active_ok_Ripemd_160 : BuiltinOkSound .Ripemd_160
axiom evalBuiltinSym_active_ok_ExpModInteger : BuiltinOkSound .ExpModInteger
set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_DropList : BuiltinOkSound .DropList := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons n rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈
                (let vl := Proj.map2 (fun n xs => .app "vlist_drop" [n, xs])
                    (asInt n) (asConstList xs)
                 let dl := Proj.map2 (fun n xs => .app "dlist_drop" [n, xs])
                    (asInt n) (asDataList xs)
                 [Outcome.ok vl.guard (.const (.constList vl.val)),
                  Outcome.ok dl.guard (.const (.dataList dl.val)),
                  Outcome.error (SExpr.not (SExpr.or vl.guard dl.guard))]) at hmem
              simp only [List.mem_cons, List.not_mem_nil] at hmem
              obtain ⟨cxs, cn, hxs, hn, rfl⟩ := symValListToCekList_pair hargs
              rcases hmem with hv | hd | herr
              · injection hv with hpcEq hvEq
                subst pc
                subst v
                change pcHolds m
                  (SExpr.and (asInt n).guard (asConstList xs).guard) = true at hpc
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt n).guard (asConstList xs).guard).mp hpc
                obtain ⟨i, rfl, hiEval⟩ := asInt_sound hn hp.1
                obtain ⟨vals, cs, rfl, hxsEval, hconsts⟩ :=
                  asConstList_sound hxs hp.2
                have hdropEval :=
                  Moist.SMT.Semantics.eval_vlist_drop_of (m := m)
                    (n := (asInt n).val) (xs := (asConstList xs).val)
                    hiEval hxsEval
                have hdropBase :
                    semValListToConstList? (vals.drop i.toNat) =
                      some (cs.drop i.toNat) :=
                  semValListToConstList_drop (vals := vals) (cs := cs)
                    (n := i.toNat) hconsts
                have hdropConsts :
                    semValListToConstList?
                        (if i < 0 then vals else vals.drop i.toNat) =
                      some (if i < 0 then cs else cs.drop i.toNat) := by
                  by_cases hneg : i < 0
                  · simp [hneg, hconsts]
                  · simpa [hneg] using hdropBase
                refine ⟨.VCon (if i < 0 then .ConstList cs else .ConstList (cs.drop i.toNat)),
                  ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
                · by_cases hneg : i < 0
                  · simp [symValToCek?, symConstToCek?, Proj.map2,
                      hdropEval, hneg, hconsts]
                  · simp [symValToCek?, symConstToCek?, Proj.map2,
                      hdropEval, hneg, hdropBase]
                · exact Moist.CEK.evalBuiltin_DropList_constList cs i
              · injection hd with hpcEq hvEq
                subst pc
                subst v
                change pcHolds m
                  (SExpr.and (asInt n).guard (asDataList xs).guard) = true at hpc
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asInt n).guard (asDataList xs).guard).mp hpc
                obtain ⟨i, rfl, hiEval⟩ := asInt_sound hn hp.1
                obtain ⟨ds, rfl, hxsEval⟩ := asDataList_sound hxs hp.2
                have hdropEval :=
                  Moist.SMT.Semantics.eval_dlist_drop_of (m := m)
                    (n := (asInt n).val) (xs := (asDataList xs).val)
                    hiEval hxsEval
                refine ⟨.VCon (if i < 0 then .ConstDataList ds else .ConstDataList (ds.drop i.toNat)),
                  ?_, by simp [symValNoOpaqueForSoundness], ?_⟩
                · by_cases hneg : i < 0 <;>
                    simp [symValToCek?, symConstToCek?, Proj.map2, hdropEval, hneg]
                · exact Moist.CEK.evalBuiltin_DropList_dataList ds i
              · rcases herr with herr | hfalse
                · cases herr
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_IndexArray : BuiltinOkSound .IndexArray := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons idx rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem
      | cons arr rest2 =>
          cases rest2 with
          | nil =>
              change Outcome.ok pc v ∈
                checked2
                  (Proj.map2 (fun arr idx => (arr, idx)) (asArray arr) (asInt idx))
                  (fun (arr, idx) =>
                    let g := SExpr.and (SExpr.ge idx (.int 0))
                      (SExpr.lt idx (.app "vlist_length" [arr]))
                    [Outcome.ok g (.dyn (.app "vlist_index" [idx, arr])),
                     Outcome.error (SExpr.not g)]) at hmem
              have hpath := checked2_path_ok hmem hpc
              rcases hpath with ⟨innerPc, hinner, _hpcEq, hpArgs, hpRange⟩
              simp only [List.mem_cons, List.not_mem_nil] at hinner
              rcases hinner with hok | herr
              · injection hok with hinnerPcEq hvEq
                subst innerPc
                subst v
                obtain ⟨cidx, carr, hidxArg, harrArg, rfl⟩ :=
                  symValListToCekList_pair hargs
                change pcHolds m
                  (SExpr.and (asArray arr).guard (asInt idx).guard) = true at hpArgs
                have hp :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (asArray arr).guard (asInt idx).guard).mp hpArgs
                obtain ⟨i, rfl, hiEval⟩ := asInt_sound hidxArg hp.2
                obtain ⟨vals, cs, rfl, harrEval, hconsts⟩ :=
                  asArray_sound harrArg hp.1
                have hpRangeSplit :=
                  (Moist.SMT.Semantics.evalBoolIs_and_true m
                    (SExpr.ge (asInt idx).val (.int 0))
                    (SExpr.lt (asInt idx).val
                      (.app "vlist_length" [(asArray arr).val]))).mp hpRange
                have hge : 0 ≤ i :=
                  pcHolds_ge_int hiEval (by simp [Moist.SMT.Semantics.eval])
                    hpRangeSplit.1
                have hlenEval := Moist.SMT.Semantics.eval_vlist_length_of
                  (m := m) (e := (asArray arr).val) harrEval
                have hlt : i < Int.ofNat vals.length :=
                  pcHolds_lt_int hiEval hlenEval hpRangeSplit.2
                have hidxNatLt : i.toNat < vals.length :=
                  (Int.toNat_lt hge).mpr hlt
                have hgetVals :
                    vals[i.toNat]? = some vals[i.toNat] :=
                  List.getElem?_eq_getElem hidxNatLt
                obtain ⟨c, hgetCs, hconst⟩ :=
                  semValListToConstList_get? (vals := vals) (cs := cs)
                    (i := i.toNat) (v := vals[i.toNat])
                    hconsts hgetVals
                have hindexEval :=
                  Moist.SMT.Semantics.eval_vlist_index_of (m := m)
                    (idx := (asInt idx).val) (xs := (asArray arr).val)
                    hiEval harrEval hge hgetVals
                have hcek := semValToCek_of_const hconst
                refine ⟨.VCon c, ?_,
                  by simp [symValNoOpaqueForSoundness], ?_⟩
                · simp [symValToCek?, Proj.map2, hindexEval, hcek]
                · exact Moist.CEK.evalBuiltin_IndexArray cs i hge hgetCs
              · rcases herr with herr | hfalse
                · cases herr
                · cases hfalse
          | cons _ _ =>
              change Outcome.ok pc v ∈ err at hmem
              simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_LengthOfArray : BuiltinOkSound .LengthOfArray := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons arr rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            [Outcome.ok (asArray arr).guard
              (SymVal.const (SymConst.integer
                (.app "vlist_length" [(asArray arr).val]))),
             Outcome.error (SExpr.not (asArray arr).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨carr, harr, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · injection hok with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨vals, cs, rfl, harrEval, hconsts⟩ :=
              asArray_sound harr hpc
            have hlenEval := Moist.SMT.Semantics.eval_vlist_length_of
              (m := m) (e := (asArray arr).val) harrEval
            have hlenNat : vals.length = cs.length :=
              semValListToConstList_length hconsts
            have hlenEvalCs :
                SmtSem.eval m (.app "vlist_length" [(asArray arr).val]) =
                  some (.int (Int.ofNat cs.length)) := by
              simpa [hlenNat] using hlenEval
            refine ⟨.VCon (.Integer (Int.ofNat cs.length)), ?_,
              by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hlenEvalCs]
            · exact Moist.CEK.evalBuiltin_LengthOfArray cs
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

set_option maxHeartbeats 0 in
theorem evalBuiltinSym_active_ok_ListToArray : BuiltinOkSound .ListToArray := by
  intro m args cargs pc v hargs _hnoArgs hmem hpc
  cases args with
  | nil =>
      change Outcome.ok pc v ∈ err at hmem
      simp [err] at hmem
  | cons xs rest =>
      cases rest with
      | nil =>
          change Outcome.ok pc v ∈
            [Outcome.ok (asConstList xs).guard
              (SymVal.const (SymConst.array (asConstList xs).val)),
             Outcome.error (SExpr.not (asConstList xs).guard)] at hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          obtain ⟨cxs, hxs, rfl⟩ := symValListToCekList_singleton hargs
          rcases hmem with hok | herr
          · injection hok with hpcEq hvEq
            subst pc
            subst v
            obtain ⟨vals, cs, rfl, hxsEval, hconsts⟩ :=
              asConstList_sound hxs hpc
            refine ⟨.VCon (.ConstArray cs), ?_,
              by simp [symValNoOpaqueForSoundness], ?_⟩
            · simp [symValToCek?, symConstToCek?, hxsEval, hconsts]
            · exact Moist.CEK.evalBuiltin_ListToArray cs
          · rcases herr with herr | hfalse
            · cases herr
            · cases hfalse
      | cons _ _ =>
          change Outcome.ok pc v ∈ err at hmem
          simp [err] at hmem

theorem extractConsts_length {args : List CekValue} {cs : List Const}
    (h : Moist.CEK.extractConsts args = some cs) :
    cs.length = args.length := by
  induction args generalizing cs with
  | nil =>
      simp [Moist.CEK.extractConsts] at h
      subst cs
      rfl
  | cons v vs ih =>
      cases v <;> simp [Moist.CEK.extractConsts] at h
      rename_i c
      cases hvs : Moist.CEK.extractConsts vs <;> simp [hvs] at h
      subst cs
      simp [ih hvs]

end Moist.SMT.UPLC.Soundness
