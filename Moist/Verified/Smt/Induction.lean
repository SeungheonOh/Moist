import Moist.Verified.Smt.BuiltinLemmas
import Moist.Verified.BigStep

/-! # Stage 2 — the matched-fuel structural simulation `symEval ≡ bigEval`

The spine: a 6-way mutual induction (mirroring `symEval`/`symApply`/`symForce`/`symCase`/
`symEvalList`/`symApplyList` and `bigEval`/`applyVal`/`forceVal`/…) showing the symbolic
result, denoted under a well-formed model, equals the big-step result — with `∀k` extra
fuel (so error fuel-stability is free) and `WF` preservation threaded.

The builtin saturation cases consume `symSaturate_agrees`/`symSaturate_wf` (the per-builtin
agreement = the separate "builtin grind"). -/

namespace Moist.Verified.Smt

open Moist.Symbolic Moist.CEK
open Moist.Plutus (Data ByteString)
open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.Verified.BigStep (bigEval applyVal forceVal bigEvalList applyValList)

/-- The compiled outcome as an `Option CekValue` (meaningful under `¬inc`). -/
def SymOut (M : Model) (r : SymR) : Option CekValue :=
  if denoteErr M r then none else some (denoteVal M r)

/-! ## Environment-lookup correspondence -/

theorem denoteEnv_lookup (M : Model) : ∀ (ρ : SymEnv) (j : Nat),
    (denoteEnv M ρ).lookup j = (symLookup ρ j).map (denoteSymV M)
  | [], j => by cases j <;> rfl
  | _ :: _, 0 => rfl
  | _ :: _, 1 => rfl
  | _ :: vs, (n+2) => by
      show (denoteEnv M vs).lookup (n+1) = _
      rw [denoteEnv_lookup M vs (n+1)]; rfl

theorem wf_symLookup (M : Model) : ∀ (ρ : SymEnv) (j : Nat) (v : SymV),
    WFSymEnv M ρ → symLookup ρ j = some v → WFSymVal M v
  | _ :: _, 1, _, hwf, h => by
      simp only [symLookup, Option.some.injEq] at h; subst h
      rw [WFSymEnv] at hwf; exact hwf.1
  | _ :: vs, (n+2), w, hwf, h => by
      rw [WFSymEnv] at hwf
      exact wf_symLookup M vs (n+1) w hwf.2 h
  | [], j, _, _, h => by cases j <;> simp [symLookup] at h
  | _ :: _, 0, _, _, h => by simp [symLookup] at h

/-! ## Constant round-trips (`decode ∘ evalDyn ∘ constToSExpr = id`) -/


theorem eval_ofBytes (M : Model) : ∀ (xs : List UInt8),
    (evalDyn M (Seq.ofBytes xs)).toSeq = xs.map (fun b => (Int.ofNat b.toNat))
  | [] => rfl
  | [_] => rfl
  | x :: y :: xs => by
      show (evalDyn M (Seq.append (Seq.unit _) (Seq.ofBytes (y :: xs)))).toSeq = _
      simp only [Seq.append, Seq.unit, evalDyn_app, evalDynList, ea_sapp, ea_sunit, toSeq_seq,
        toInt_i, List.map_cons]
      rw [eval_ofBytes M (y :: xs)]; rfl

theorem byte_roundtrip (bs : ByteArray) :
    bytesToBA (bs.data.toList.map (fun b => (Int.ofNat b.toNat))) = bs := by
  show ByteArray.mk _ = bs
  simp only [List.map_map, Function.comp_def]
  rw [show (fun b : UInt8 => UInt8.ofNat (Int.ofNat b.toNat).toNat) = id from by funext b; exact UInt8.ofNat_toNat]
  simp

theorem bs_roundtrip (M : Model) (bs : ByteArray) :
    bytesToBA ((evalDyn M (Seq.ofBytes bs.data.toList)).toSeq) = bs := by
  rw [eval_ofBytes]; exact byte_roundtrip bs

mutual
theorem decodeD_eval (M : Model) : ∀ (d : Data), decodeD (evalDyn M (dataToSExpr d)).toD = d
  | .Constr i ds => by
      simp only [dataToSExpr, D.constr, evalDyn_app, evalDynList, evalDyn_int, ea_DConstr, toD_d, toInt_i]
      show Data.Constr i (decodeDL (evalDyn M (dataToDL ds)).toDL) = _
      rw [decodeDL_eval M ds]
  | .Map ps => by
      simp only [dataToSExpr, D.map, evalDyn_app, evalDynList, ea_DMap, toD_d]
      show Data.Map (decodeDM (evalDyn M (dataPairsToDM ps)).toDM) = _
      rw [decodeDM_eval M ps]
  | .List ds => by
      simp only [dataToSExpr, D.list, evalDyn_app, evalDynList, ea_DList, toD_d]
      show Data.List (decodeDL (evalDyn M (dataToDL ds)).toDL) = _
      rw [decodeDL_eval M ds]
  | .I _ => rfl
  | .B bs => by
      simp only [dataToSExpr, D.b, evalDyn_app, evalDynList, ea_DB, toD_d]
      show Data.B (bytesToBA (evalDyn M (Seq.ofBytes bs.data.toList)).toSeq) = _
      exact congrArg Data.B (bs_roundtrip M bs)
theorem decodeDL_eval (M : Model) : ∀ (ds : List Data), decodeDL (evalDyn M (dataToDL ds)).toDL = ds
  | [] => rfl
  | d :: ds => by
      simp only [dataToDL, DL.cons, evalDyn_app, evalDynList, ea_dcons, toDL_dl, toD_d]
      show decodeD (evalDyn M (dataToSExpr d)).toD :: decodeDL (evalDyn M (dataToDL ds)).toDL = _
      rw [decodeD_eval M d, decodeDL_eval M ds]
theorem decodeDM_eval (M : Model) : ∀ (ps : List (Data × Data)), decodeDM (evalDyn M (dataPairsToDM ps)).toDM = ps
  | [] => rfl
  | (k, v) :: ps => by
      simp only [dataPairsToDM, DM.cons, evalDyn_app, evalDynList, ea_mcons, toDM_dm, toD_d]
      show (decodeD (evalDyn M (dataToSExpr k)).toD, decodeD (evalDyn M (dataToSExpr v)).toD) :: decodeDM (evalDyn M (dataPairsToDM ps)).toDM = _
      rw [decodeD_eval M k, decodeD_eval M v, decodeDM_eval M ps]
end

mutual
theorem decode_const (M : Model) : ∀ (c : Const), decodeV (evalDyn M (constToSExpr c)).toV = .VCon c
  | .Integer _ => rfl
  | .Bool _ => rfl
  | .Unit => rfl
  | .String _ => rfl
  | .Bls12_381_G1_element => rfl
  | .Bls12_381_G2_element => rfl
  | .Bls12_381_MlResult => rfl
  | .ByteString bs => by
      simp only [constToSExpr, V.bs, evalDyn_app, evalDynList, ea_VBS, toV_v]
      show CekValue.VCon (.ByteString (bytesToBA (evalDyn M (Seq.ofBytes bs.data.toList)).toSeq)) = _
      rw [bs_roundtrip M bs]
  | .Data d => by
      simp only [constToSExpr, V.data, evalDyn_app, evalDynList, ea_VData, toV_v]
      show CekValue.VCon (.Data (decodeD (evalDyn M (dataToSExpr d)).toD)) = _
      rw [decodeD_eval M d]
  | .ConstDataList ds => by
      simp only [constToSExpr, V.dlist, evalDyn_app, evalDynList, ea_VDList, toV_v]
      show CekValue.VCon (.ConstDataList (decodeDL (evalDyn M (dataToDL ds)).toDL)) = _
      rw [decodeDL_eval M ds]
  | .ConstPairDataList ps => by
      simp only [constToSExpr, V.pdlist, evalDyn_app, evalDynList, ea_VPDList, toV_v]
      show CekValue.VCon (.ConstPairDataList (decodeDM (evalDyn M (dataPairsToDM ps)).toDM)) = _
      rw [decodeDM_eval M ps]
  | .ConstList cs => by
      simp only [constToSExpr, V.list, evalDyn_app, evalDynList, ea_VList, toV_v]
      show CekValue.VCon (.ConstList ((decodeVL (evalDyn M (constListToVL cs)).toVL).map cekToConst)) = _
      rw [decodeVL_const M cs]
  | .ConstArray cs => by
      simp only [constToSExpr, V.arr, evalDyn_app, evalDynList, ea_VArr, toV_v]
      show CekValue.VCon (.ConstArray ((decodeVL (evalDyn M (constListToVL cs)).toVL).map cekToConst)) = _
      rw [decodeVL_const M cs]
  | .Pair (a, b) => by
      simp only [constToSExpr, V.pair, evalDyn_app, evalDynList, ea_VPair, toV_v]
      show CekValue.VCon (.Pair (cekToConst (decodeV (evalDyn M (constToSExpr a)).toV), cekToConst (decodeV (evalDyn M (constToSExpr b)).toV))) = _
      rw [decode_const M a, decode_const M b]; rfl
  | .PairData (a, b) => by
      simp only [constToSExpr, V.pairD, evalDyn_app, evalDynList, ea_VPairD, toV_v]
      show CekValue.VCon (.PairData (decodeD (evalDyn M (dataToSExpr a)).toD, decodeD (evalDyn M (dataToSExpr b)).toD)) = _
      rw [decodeD_eval M a, decodeD_eval M b]
theorem decodeVL_const (M : Model) : ∀ (cs : List Const),
    (decodeVL (evalDyn M (constListToVL cs)).toVL).map cekToConst = cs
  | [] => rfl
  | c :: cs => by
      simp only [constListToVL, VL.cons, evalDyn_app, evalDynList, ea_vcons, toVL_vl, toV_v]
      show (cekToConst (decodeV (evalDyn M (constToSExpr c)).toV) :: (decodeVL (evalDyn M (constListToVL cs)).toVL).map cekToConst) = _
      rw [decode_const M c, decodeVL_const M cs]; rfl
end

/-! ## Well-formedness of constants + an `sOrs` extraction helper -/

theorem wf_ofBytes (M : Model) (xs : List UInt8) : WFSeq (evalDyn M (Seq.ofBytes xs)).toSeq := by
  rw [eval_ofBytes]; intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  have hb : b.toNat < 256 := b.toNat_lt
  show (0:Int) ≤ (b.toNat : Int) ∧ (b.toNat : Int) ≤ 255
  omega

mutual
theorem wf_dataToSExpr (M : Model) : ∀ (d : Data), WFD (evalDyn M (dataToSExpr d)).toD
  | .Constr _ ds => by simp only [dataToSExpr, D.constr, evalDyn_app, evalDynList, evalDyn_int, ea_DConstr, toD_d, WFD]; exact wf_dataToDL M ds
  | .Map ps => by simp only [dataToSExpr, D.map, evalDyn_app, evalDynList, ea_DMap, toD_d, WFD]; exact wf_dataPairsToDM M ps
  | .List ds => by simp only [dataToSExpr, D.list, evalDyn_app, evalDynList, ea_DList, toD_d, WFD]; exact wf_dataToDL M ds
  | .I _ => by simp only [dataToSExpr, D.i, evalDyn_app, evalDynList, evalDyn_int, ea_DI, toD_d, WFD]
  | .B bs => by simp only [dataToSExpr, D.b, evalDyn_app, evalDynList, ea_DB, toD_d, WFD]; exact wf_ofBytes M _
theorem wf_dataToDL (M : Model) : ∀ (ds : List Data), WFDL (evalDyn M (dataToDL ds)).toDL
  | [] => by simp [dataToDL, DL.nil, WFDL]
  | d :: ds => by
      simp only [dataToDL, DL.cons, evalDyn_app, evalDynList, ea_dcons, toDL_dl, WFDL]
      exact ⟨wf_dataToSExpr M d, wf_dataToDL M ds⟩
theorem wf_dataPairsToDM (M : Model) : ∀ (ps : List (Data × Data)), WFDM (evalDyn M (dataPairsToDM ps)).toDM
  | [] => by simp [dataPairsToDM, DM.nil, WFDM]
  | (k, v) :: ps => by
      simp only [dataPairsToDM, DM.cons, evalDyn_app, evalDynList, ea_mcons, toDM_dm, WFDM]
      exact ⟨wf_dataToSExpr M k, wf_dataToSExpr M v, wf_dataPairsToDM M ps⟩
end

theorem eval_const_v (M : Model) (c : Const) :
    evalDyn M (constToSExpr c) = .v ((evalDyn M (constToSExpr c)).toV) := by cases c <;> rfl

mutual
theorem wf_const_v (M : Model) : ∀ (c : Const), WFV (evalDyn M (constToSExpr c)).toV
  | .Integer _ => by simp [constToSExpr, V.int, WFV]
  | .Bool _ => by simp [constToSExpr, V.bool, WFV]
  | .Unit => by simp [constToSExpr, V.unit, WFV]
  | .String _ => by simp [constToSExpr, V.str, WFV]
  | .Bls12_381_G1_element => by simp [constToSExpr, V.g1, WFV]
  | .Bls12_381_G2_element => by simp [constToSExpr, V.g2, WFV]
  | .Bls12_381_MlResult => by simp [constToSExpr, V.ml, WFV]
  | .ByteString bs => by simp only [constToSExpr, V.bs, evalDyn_app, evalDynList, ea_VBS, toV_v, WFV]; exact wf_ofBytes M _
  | .Data d => by simp only [constToSExpr, V.data, evalDyn_app, evalDynList, ea_VData, toV_v, WFV]; exact wf_dataToSExpr M d
  | .ConstDataList ds => by simp only [constToSExpr, V.dlist, evalDyn_app, evalDynList, ea_VDList, toV_v, WFV]; exact wf_dataToDL M ds
  | .ConstPairDataList ps => by simp only [constToSExpr, V.pdlist, evalDyn_app, evalDynList, ea_VPDList, toV_v, WFV]; exact wf_dataPairsToDM M ps
  | .ConstList cs => by
      simp only [constToSExpr, V.list, evalDyn_app, evalDynList, ea_VList, toV_v, WFV]
      exact ⟨wf_constListToVL M cs, const_constListToVL M cs⟩
  | .ConstArray cs => by
      simp only [constToSExpr, V.arr, evalDyn_app, evalDynList, ea_VArr, toV_v, WFV]
      exact ⟨wf_constListToVL M cs, const_constListToVL M cs⟩
  | .Pair (a, b) => by
      simp only [constToSExpr, V.pair, evalDyn_app, evalDynList, ea_VPair, toV_v, WFV]
      exact ⟨wf_const_v M a, wf_const_v M b, const_const_v M a, const_const_v M b⟩
  | .PairData (a, b) => by simp only [constToSExpr, V.pairD, evalDyn_app, evalDynList, ea_VPairD, toV_v, WFV]; exact ⟨wf_dataToSExpr M a, wf_dataToSExpr M b⟩
theorem wf_constListToVL (M : Model) : ∀ (cs : List Const), WFVL (evalDyn M (constListToVL cs)).toVL
  | [] => by simp [constListToVL, VL.nil, WFVL]
  | c :: cs => by
      simp only [constListToVL, VL.cons, evalDyn_app, evalDynList, ea_vcons, toVL_vl, WFVL]
      exact ⟨wf_const_v M c, wf_constListToVL M cs⟩
theorem const_const_v (M : Model) : ∀ (c : Const), ConstSemV (evalDyn M (constToSExpr c)).toV
  | .Integer _ => by simp [constToSExpr, V.int, ConstSemV]
  | .Bool _ => by simp [constToSExpr, V.bool, ConstSemV]
  | .Unit => by simp [constToSExpr, V.unit, ConstSemV]
  | .String _ => by simp [constToSExpr, V.str, ConstSemV]
  | .Bls12_381_G1_element => by simp [constToSExpr, V.g1, ConstSemV]
  | .Bls12_381_G2_element => by simp [constToSExpr, V.g2, ConstSemV]
  | .Bls12_381_MlResult => by simp [constToSExpr, V.ml, ConstSemV]
  | .ByteString _ => by simp [constToSExpr, V.bs, ConstSemV]
  | .Data _ => by simp [constToSExpr, V.data, ConstSemV]
  | .ConstDataList _ => by simp [constToSExpr, V.dlist, ConstSemV]
  | .ConstPairDataList _ => by simp [constToSExpr, V.pdlist, ConstSemV]
  | .ConstList cs => by
      simp only [constToSExpr, V.list, evalDyn_app, evalDynList, ea_VList, toV_v, ConstSemV]
      exact const_constListToVL M cs
  | .ConstArray cs => by
      simp only [constToSExpr, V.arr, evalDyn_app, evalDynList, ea_VArr, toV_v, ConstSemV]
      exact const_constListToVL M cs
  | .Pair (a, b) => by
      simp only [constToSExpr, V.pair, evalDyn_app, evalDynList, ea_VPair, toV_v, ConstSemV]
      exact ⟨const_const_v M a, const_const_v M b⟩
  | .PairData _ => by simp [constToSExpr, V.pairD, ConstSemV]
theorem const_constListToVL (M : Model) : ∀ (cs : List Const), ConstSemVL (evalDyn M (constListToVL cs)).toVL
  | [] => by simp [constListToVL, VL.nil, ConstSemVL]
  | c :: cs => by
      simp only [constListToVL, VL.cons, evalDyn_app, evalDynList, ea_vcons, toVL_vl, ConstSemVL]
      exact ⟨const_const_v M c, const_constListToVL M cs⟩
end

theorem wf_const (M : Model) (c : Const) : WFDyn (evalDyn M (constToSExpr c)) := by
  rw [eval_const_v]; exact wf_const_v M c

/-- From `⟦sOrs L⟧ = false`, every element is `false`. -/
theorem sOrs_false (M : Model) : ∀ {L : List SExpr}, (evalDyn M (sOrs L)).toBool = false →
    ∀ e ∈ L, (evalDyn M e).toBool = false
  | [], _, e, he => by cases he
  | a :: L, h, e, he => by
      rw [show sOrs (a :: L) = SExpr.sOr a (sOrs L) from rfl, evalDyn_sOr, Bool.or_eq_false_iff] at h
      cases he with
      | head => exact h.1
      | tail _ he' => exact sOrs_false M h.2 e he'

/-- `SymOut` distributes over a symbolic merge. -/
theorem SymOut_symMerge (M : Model) (c : SExpr) (A B : SymR) :
    SymOut M (symMerge c A B) = if (evalDyn M c).toBool then SymOut M A else SymOut M B := by
  simp only [SymOut, denoteErr_symMerge, denoteVal_symMerge]
  by_cases hc : (evalDyn M c).toBool <;> simp [hc]

@[simp] theorem evalInc_symMerge (M : Model) (c : SExpr) (A B : SymR) :
    (evalDyn M (symMerge c A B).inc).toBool =
      if (evalDyn M c).toBool then (evalDyn M A.inc).toBool else (evalDyn M B.inc).toBool := by
  simpa [denoteInc] using denoteInc_symMerge M c A B

@[simp] theorem evalErr_symMerge (M : Model) (c : SExpr) (A B : SymR) :
    (evalDyn M (symMerge c A B).err).toBool =
      if (evalDyn M c).toBool then (evalDyn M A.err).toBool else (evalDyn M B.err).toBool := by
  simpa [denoteErr] using denoteErr_symMerge M c A B

mutual
/-- The merge value is well-formed once the *selected* branch is (the other is unobserved). -/
theorem WFSymVal_mergeVal (M : Model) (c : SExpr) : ∀ (x y : SymV),
    (if (evalDyn M c).toBool then WFSymVal M x else WFSymVal M y) → WFSymVal M (mergeVal c x y)
  | .fo a, .fo b, hsel => by
      simp only [mergeVal, WFSymVal, evalDyn_sIte]
      by_cases hc : (evalDyn M c).toBool <;> simp_all [WFSymVal]
  | .constr t1 fs1, .constr t2 fs2, hsel => by
      simp only [mergeVal]
      by_cases hcond : (t1 == t2 && fs1.length == fs2.length) = true
      · rw [if_pos hcond]
        simp only [WFSymVal] at hsel ⊢
        exact WFSymList_mergeValList M c fs1 fs2 hsel
      · rw [if_neg hcond]; simpa only [WFSymVal] using hsel
  | .fo _, .lam _ _, hsel | .fo _, .delay _ _, hsel | .fo _, .constr _ _, hsel
  | .fo _, .builtin _ _ _, hsel | .fo _, .choice _ _ _, hsel
  | .lam _ _, _, hsel | .delay _ _, _, hsel | .builtin _ _ _, _, hsel | .choice _ _ _, _, hsel
  | .constr _ _, .fo _, hsel | .constr _ _, .lam _ _, hsel | .constr _ _, .delay _ _, hsel
  | .constr _ _, .builtin _ _ _, hsel | .constr _ _, .choice _ _ _, hsel =>
      by simpa only [mergeVal, WFSymVal] using hsel
termination_by x _ => sizeOf x
theorem WFSymList_mergeValList (M : Model) (c : SExpr) : ∀ (xs ys : List SymV),
    (if (evalDyn M c).toBool then WFSymList M xs else WFSymList M ys) →
    WFSymList M (mergeValList c xs ys)
  | [], [], _ => trivial
  | x :: xs, y :: ys, hsel => by
      simp only [mergeValList, WFSymList]
      by_cases hc : (evalDyn M c).toBool <;>
        simp only [hc, if_true, if_false, Bool.false_eq_true, WFSymList] at hsel <;>
        exact ⟨WFSymVal_mergeVal M c x y (by simp [hc, hsel.1]),
               WFSymList_mergeValList M c xs ys (by simp [hc, hsel.2])⟩
  | [], _ :: _, _ => trivial
  | _ :: _, [], _ => trivial
termination_by xs _ => sizeOf xs
end

theorem WFSymVal_symMerge (M : Model) (c : SExpr) (A B : SymR)
    (hsel : if (evalDyn M c).toBool then WFSymVal M A.val else WFSymVal M B.val) :
    WFSymVal M (symMerge c A B).val :=
  WFSymVal_mergeVal M c A.val B.val hsel

/-- `forceVal`/`applyVal` of a *decoded* value (`VCon`/`VConstr`, never a closure) is `none`. -/
theorem forceVal_decodeV (m : Nat) (sv : SemV) : forceVal (m+1) (decodeV sv) = none := by
  cases sv <;> simp [decodeV, forceVal]
theorem applyVal_decodeV (m : Nat) (sv : SemV) (va : CekValue) : applyVal (m+1) (decodeV sv) va = none := by
  cases sv <;> simp [decodeV, applyVal]

/-! ## `SymOut` distributes over the inc/err combinators -/

/-- A determinate sequential result has a determinate left computation; its
right computation is required to be determinate only when the left succeeds. -/
theorem symThen_inc_false (M : Model) (x y : SymR)
    (h : denoteInc M (symThen x y) = false) :
    denoteInc M x = false ∧ (denoteErr M x = false → denoteInc M y = false) := by
  simp only [denoteInc, denoteErr, symThen, evalDyn_sIte] at h ⊢
  cases hx : (evalDyn M x.inc).toBool <;>
    cases he : (evalDyn M x.err).toBool <;>
    cases hy : (evalDyn M y.inc).toBool <;> simp_all

/-- If a determinate sequential result succeeds, both reached computations
succeed. -/
theorem symThen_err_false (M : Model) (x y : SymR)
    (hi : denoteInc M (symThen x y) = false)
    (he : denoteErr M (symThen x y) = false) :
    denoteErr M x = false ∧ denoteErr M y = false := by
  simp only [denoteInc, denoteErr, symThen, evalDyn_sIte] at hi he ⊢
  cases hxi : (evalDyn M x.inc).toBool <;>
    cases hxe : (evalDyn M x.err).toBool <;>
    cases hye : (evalDyn M y.err).toBool <;> simp_all

/-- Under its determinacy guard, `symThen` is exactly `Option.bind` on the
denoted CEK outcomes. -/
theorem SymOut_symThen (M : Model) (x y : SymR)
    (h : denoteInc M (symThen x y) = false) :
    SymOut M (symThen x y) = (SymOut M x).bind (fun _ => SymOut M y) := by
  simp only [denoteInc, symThen, evalDyn_sIte] at h
  simp only [SymOut, denoteErr, denoteVal, symThen, evalDyn_sIte]
  cases hxi : (evalDyn M x.inc).toBool <;>
    cases hxe : (evalDyn M x.err).toBool <;>
    cases hyi : (evalDyn M y.inc).toBool <;>
    cases hye : (evalDyn M y.err).toBool <;> simp_all [Option.bind]

/-- A two-component (`sOr`) result: error propagates left-then-right. -/
theorem symOut_seq2 (M : Model) (r1 r2 : SymR) :
    SymOut M ⟨SExpr.sOr r1.inc r2.inc, SExpr.sOr r1.err r2.err, r2.val⟩
      = (SymOut M r1).bind (fun _ => SymOut M r2) := by
  simp only [SymOut, denoteErr, denoteVal, evalDyn_sOr]
  by_cases h1 : (evalDyn M r1.err).toBool <;> by_cases h2 : (evalDyn M r2.err).toBool <;>
    simp_all [Option.bind]

/-- A three-component (`sOrs`) result (the `Apply` shape). -/
theorem symOut_seq3 (M : Model) (r1 r2 r3 : SymR) :
    SymOut M ⟨sOrs [r1.inc, r2.inc, r3.inc], sOrs [r1.err, r2.err, r3.err], r3.val⟩
      = (SymOut M r1).bind (fun _ => (SymOut M r2).bind (fun _ => SymOut M r3)) := by
  simp only [SymOut, denoteErr, denoteVal, evalDyn_sOrs, List.foldr, Bool.or_false]
  by_cases h1 : (evalDyn M r1.err).toBool <;> by_cases h2 : (evalDyn M r2.err).toBool <;>
    by_cases h3 : (evalDyn M r3.err).toBool <;> simp_all [Option.bind]

/-- The denoted error of an `sOrs`-of-errors is the disjunction of the component errors. -/
theorem denoteErr_sOrs_map (M : Model) (rs : List SymR) :
    (evalDyn M (sOrs (rs.map SymR.err))).toBool = rs.any (fun r => (evalDyn M r.err).toBool) := by
  rw [evalDyn_sOrs]
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, List.foldr, List.any_cons, ih]

/-- `denoteSymList` is the pointwise `denoteSymV`. -/
theorem denoteSymList_eq_map (M : Model) (L : List SymV) :
    denoteSymList M L = L.map (denoteSymV M) := by
  induction L with
  | nil => rfl
  | cons v vs ih => simp only [denoteSymList, List.map_cons, ih]

/-- `WFSymList` unfolds to membership-wise `WFSymVal`. -/
theorem wfSymList_mem (M : Model) : ∀ {L : List SymV}, WFSymList M L → ∀ v ∈ L, WFSymVal M v
  | [], _, _, hv => by cases hv
  | w :: ws, hwf, v, hv => by
      rw [WFSymList] at hwf
      rcases List.mem_cons.1 hv with h | h
      · subst h; exact hwf.1
      · exact wfSymList_mem M hwf.2 v h

/-- The converse: membership-wise `WFSymVal` rebuilds `WFSymList`. -/
theorem wfSymList_of_mem (M : Model) : ∀ {L : List SymV}, (∀ v ∈ L, WFSymVal M v) → WFSymList M L
  | [], _ => trivial
  | w :: ws, h => ⟨h w (by simp), wfSymList_of_mem M (fun v hv => h v (List.mem_cons_of_mem w hv))⟩

/-! ## Shape lemmas: a `conName` pins the `SemV` constructor -/

theorem semV_VUnit  {sv : SemV} (h : sv.conName = "VUnit")  : sv = .unit := by
  cases sv <;> simp_all [SemV.conName]
theorem semV_VBool  {sv : SemV} (h : sv.conName = "VBool")  : sv = .bool sv.getBool := by
  cases sv <;> simp_all [SemV.conName, SemV.getBool]
theorem semV_VInt   {sv : SemV} (h : sv.conName = "VInt")   : sv = .int sv.getInt := by
  cases sv <;> simp_all [SemV.conName, SemV.getInt]
theorem semV_VList  {sv : SemV} (h : sv.conName = "VList")  : sv = .list sv.getList := by
  cases sv <;> simp_all [SemV.conName, SemV.getList]
theorem semV_VDList {sv : SemV} (h : sv.conName = "VDList") : sv = .dlist sv.getDList := by
  cases sv <;> simp_all [SemV.conName, SemV.getDList]
theorem semV_VPair  {sv : SemV} (h : sv.conName = "VPair")  : sv = .pair sv.pFst sv.pSnd := by
  cases sv <;> simp_all [SemV.conName, SemV.pFst, SemV.pSnd]
theorem semV_VPairD {sv : SemV} (h : sv.conName = "VPairD") : sv = .pairD sv.pdFst sv.pdSnd := by
  cases sv <;> simp_all [SemV.conName, SemV.pdFst, SemV.pdSnd]
theorem semV_VConstr {sv : SemV} (h : sv.conName = "VConstr") : sv = .constr sv.cTag sv.cArgs := by
  cases sv <;> simp_all [SemV.conName, SemV.cTag, SemV.cArgs]

/-- `symEvalList` is the pointwise `symEval`. -/
theorem symEvalList_eq_map (m : Nat) (ρ : SymEnv) (alts : List Term) :
    symEvalList m ρ alts = alts.map (symEval m ρ) := by
  induction alts with
  | nil => simp [symEvalList]
  | cons t ts ih => simp only [symEvalList, List.map_cons, ih]

/-- The list outcome of a `symEvalList` (some iff no component errs). -/
def SymOutList (M : Model) (rs : List SymR) : Option (List CekValue) :=
  if rs.any (fun r => denoteErr M r) then none else some (rs.map (denoteVal M))

/-- `SymOutList` of a cons: head-then-tail (error short-circuits). -/
theorem SymOutList_cons (M : Model) (r : SymR) (rs : List SymR) :
    SymOutList M (r :: rs)
      = (SymOut M r).bind (fun v => (SymOutList M rs).map (fun vs => v :: vs)) := by
  unfold SymOutList SymOut
  rw [List.any_cons]
  cases hr : denoteErr M r with
  | true => simp [hr]
  | false =>
      cases hrs : rs.any (fun r => denoteErr M r) with
      | true => simp [hr, hrs]
      | false => simp [hr, hrs, denoteVal]

/-- If `SymOutList` succeeds, its payload is the pointwise `denoteVal`. -/
theorem symOutList_some (M : Model) {rs : List SymR} {vs : List CekValue}
    (h : SymOutList M rs = some vs) : vs = rs.map (denoteVal M) := by
  simp only [SymOutList] at h; split at h <;> simp_all

/-- `SymOut` of a `symThenList` (under its determinacy guard): all components
must succeed, then the constructed value is returned. -/
theorem SymOut_symThenList (M : Model) : ∀ (rs : List SymR) (v0 : SymV),
    denoteInc M (symThenList rs v0) = false →
    SymOut M (symThenList rs v0) = (SymOutList M rs).bind (fun _ => some (denoteSymV M v0))
  | [], v0, _ => by simp [symThenList, SymOut, SymOutList, denoteErr, denoteVal]
  | r :: rs, v0, h => by
      rw [symThenList, SymOut_symThen M r (symThenList rs v0) h, SymOutList_cons]
      obtain ⟨_, hthen⟩ := symThen_inc_false M r (symThenList rs v0) h
      cases hsr : SymOut M r with
      | none => simp
      | some v =>
          have hre : denoteErr M r = false := by
            by_cases hh : denoteErr M r = false
            · exact hh
            · simp only [Bool.not_eq_false] at hh; simp [SymOut, hh] at hsr
          rw [SymOut_symThenList M rs v0 (hthen hre)]
          cases SymOutList M rs <;> simp

theorem symThenList_inc_irrel (rs : List SymR) (a b : SymV) :
    (symThenList rs a).inc = (symThenList rs b).inc := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [symThenList, symThen, ih]

theorem symThenList_err_irrel (rs : List SymR) (a b : SymV) :
    (symThenList rs a).err = (symThenList rs b).err := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [symThenList, symThen, ih]

theorem symThenList_val (rs : List SymR) (v : SymV) :
    (symThenList rs v).val = v := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [symThenList, symThen, ih]

/-- The `Constr` shape: `SymOut` of the list-folded result is the mapped `SymOutList`. -/
theorem symOut_constr (M : Model) (tag : Nat) (rs : List SymR) :
    SymOut M ⟨sOrs (rs.map SymR.inc), sOrs (rs.map SymR.err), .constr tag (rs.map SymR.val)⟩
      = (SymOutList M rs).map (fun vs => CekValue.VConstr tag vs) := by
  simp only [SymOut, SymOutList, denoteErr, denoteVal, denoteSymV, denoteErr_sOrs_map]
  by_cases h : rs.any (fun r => (evalDyn M r.err).toBool) = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h, denoteSymList_eq_map, List.map_map, Function.comp_def, denoteVal]

theorem dispatchIntFrom_neg_none (M : Model) (tagE : SExpr) (n : Int)
    (hEval : evalDyn M tagE = .i n) (hneg : n < 0) :
    ∀ (start : Nat) (rs : List SymR),
      (none : Option CekValue) = SymOut M (dispatchIntFrom tagE start rs)
  | _, [] => by simp [dispatchIntFrom, SymOut, denoteErr, errR]
  | start, _ :: rs => by
      have hneq : evalDyn M tagE ≠ .i (Int.ofNat start) := by
        rw [hEval]
        intro h
        injection h with hn
        have hstart : (0 : Int) ≤ Int.ofNat start := Int.ofNat_nonneg start
        omega
      have htest : (evalDyn M (SExpr.sEq tagE (.int (Int.ofNat start)))).toBool = false := by
        simpa [evalDyn_sEq] using hneq
      rw [dispatchIntFrom, SymOut_symMerge, htest]
      exact dispatchIntFrom_neg_none M tagE n hEval hneg (start+1) rs

theorem dispatchIntFrom_nat_sim (M : Model) (tagE : SExpr)
    (m k : Nat) (ρs : SymEnv) (ρc : CekEnv) :
    ∀ (start idx : Nat) (ts : List Term),
      evalDyn M tagE = .i (Int.ofNat (start + idx)) →
      (∀ i,
        denoteInc M (altOr (symEvalList m ρs ts) i) = false →
          (match ts[i]? with
           | some alt =>
               match bigEval (m + (k+1)) ρc alt with
               | some vAlt => applyValList (m + (k+1)) vAlt []
               | none => none
           | none => none) = SymOut M (altOr (symEvalList m ρs ts) i)) →
      denoteInc M (dispatchIntFrom tagE start (symEvalList m ρs ts)) = false →
      (match ts[idx]? with
       | some alt =>
           match bigEval (m + (k+1)) ρc alt with
           | some vAlt => applyValList (m + (k+1)) vAlt []
           | none => none
       | none => none) = SymOut M (dispatchIntFrom tagE start (symEvalList m ρs ts))
  | start, idx, [], hEval, H, hinc => by
      simp [symEvalList, dispatchIntFrom, SymOut, denoteErr, errR]
  | start, 0, t :: ts, hEval, H, hinc => by
      have heq : evalDyn M tagE = .i (Int.ofNat start) := by
        simpa using hEval
      have htest : (evalDyn M (SExpr.sEq tagE (.int (Int.ofNat start)))).toBool = true := by
        simpa [evalDyn_sEq] using heq
      have hi : denoteInc M (altOr (symEvalList m ρs (t :: ts)) 0) = false := by
        rw [symEvalList, dispatchIntFrom, denoteInc_symMerge, htest] at hinc
        simpa [altOr, symEvalList] using hinc
      have hs := H 0 hi
      rw [symEvalList, dispatchIntFrom, SymOut_symMerge, htest]
      simpa [altOr, symEvalList] using hs
  | start, idx+1, t :: ts, hEval, H, hinc => by
      have hneq : evalDyn M tagE ≠ .i (Int.ofNat start) := by
        rw [hEval]
        intro h
        injection h with hn
        have hn' : start + (idx + 1) = start := Int.ofNat.inj hn
        omega
      have htest : (evalDyn M (SExpr.sEq tagE (.int (Int.ofNat start)))).toBool = false := by
        simpa [evalDyn_sEq] using hneq
      have hrecinc : denoteInc M (dispatchIntFrom tagE (start+1) (symEvalList m ρs ts)) = false := by
        rw [symEvalList, dispatchIntFrom, denoteInc_symMerge, htest] at hinc
        exact hinc
      have Htail : ∀ i,
          denoteInc M (altOr (symEvalList m ρs ts) i) = false →
            (match ts[i]? with
             | some alt =>
                 match bigEval (m + (k+1)) ρc alt with
                 | some vAlt => applyValList (m + (k+1)) vAlt []
                 | none => none
             | none => none) = SymOut M (altOr (symEvalList m ρs ts) i) := by
        intro i hi
        have hs := H (i+1) (by simpa [symEvalList, altOr] using hi)
        simpa [symEvalList, altOr] using hs
      have hEval' : evalDyn M tagE = .i (Int.ofNat ((start+1) + idx)) := by
        have hnat : start + (idx + 1) = (start + 1) + idx := by omega
        simpa [hnat] using hEval
      have hrec := dispatchIntFrom_nat_sim M tagE m k ρs ρc (start+1) idx ts hEval' Htail hrecinc
      rw [symEvalList, dispatchIntFrom, SymOut_symMerge, htest]
      exact hrec

theorem dispatchIntFrom_wf (M : Model) (tagE : SExpr) :
    ∀ (start : Nat) (rs : List SymR),
      (∀ i,
        denoteInc M (altOr rs i) = false →
        denoteErr M (altOr rs i) = false →
        WFSymVal M (altOr rs i).val) →
      denoteInc M (dispatchIntFrom tagE start rs) = false →
      denoteErr M (dispatchIntFrom tagE start rs) = false →
      WFSymVal M (dispatchIntFrom tagE start rs).val
  | _, [], _, _, herr => by
      exfalso
      simpa [dispatchIntFrom, denoteErr, errR] using herr
  | start, r :: rs, H, hinc, herr => by
      refine WFSymVal_symMerge M (SExpr.sEq tagE (.int (Int.ofNat start))) r
        (dispatchIntFrom tagE (start + 1) rs) ?_
      cases htest : (evalDyn M (SExpr.sEq tagE (.int (Int.ofNat start)))).toBool with
      | true =>
        have hi : denoteInc M (altOr (r :: rs) 0) = false := by
          rw [dispatchIntFrom, denoteInc_symMerge, htest] at hinc
          simpa [altOr] using hinc
        have he : denoteErr M (altOr (r :: rs) 0) = false := by
          rw [dispatchIntFrom, denoteErr_symMerge, htest] at herr
          simpa [altOr] using herr
        simpa [altOr] using H 0 hi he
      | false =>
        have hincTail : denoteInc M (dispatchIntFrom tagE (start + 1) rs) = false := by
          rw [dispatchIntFrom, denoteInc_symMerge, htest] at hinc
          exact hinc
        have herrTail : denoteErr M (dispatchIntFrom tagE (start + 1) rs) = false := by
          rw [dispatchIntFrom, denoteErr_symMerge, htest] at herr
          exact herr
        have Htail : ∀ i,
            denoteInc M (altOr rs i) = false →
            denoteErr M (altOr rs i) = false →
            WFSymVal M (altOr rs i).val := by
          intro i hi he
          have hs := H (i+1) (by simpa [altOr] using hi) (by simpa [altOr] using he)
          simpa [altOr] using hs
        exact dispatchIntFrom_wf M tagE (start + 1) rs Htail hincTail herrTail

/-! ## The builtin agreement interface (the "grind", proven per builtin elsewhere) -/

/-- Saturated-builtin agreement: `evalBuiltin` on the denoted args equals the symbolic
outcome. (Proven per builtin; `binIntGuard_agrees` + the six integer builtins are done.) -/
def SatAgrees (M : Model) : Prop := ∀ (b : BuiltinFun) (args : List SymV),
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    evalBuiltin b (denoteSymList M args) = SymOut M (symSaturate b args)

/-- Saturated-builtin WF preservation. -/
def SatWf (M : Model) : Prop := ∀ (b : BuiltinFun) (args : List SymV),
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    denoteErr M (symSaturate b args) = false → WFSymVal M (symSaturate b args).val

/-! ## The matched-fuel simulation (mutual) -/

section
variable (M : Model) (hSat : SatAgrees M) (hWf : SatWf M)

/-- `bigEval`'s `Case` dispatch, factored out so `CaseSim` can mirror `symCase`. -/
def caseDispatch (n : Nat) (ρ : CekEnv) (alts : List Term) (vsc : CekValue) : Option CekValue :=
  match vsc with
  | .VConstr tag fields =>
      match alts[tag]? with
      | some alt => match bigEval n ρ alt with
                    | some vAlt => applyValList n vAlt fields
                    | none => none
      | none => none
  | .VCon c =>
      match constToTagAndFields c with
      | some (tag, numCtors, fields) =>
          if numCtors > 0 && alts.length > numCtors then none
          else match alts[tag]? with
            | some alt => match bigEval n ρ alt with
                          | some vAlt => applyValList n vAlt fields
                          | none => none
            | none => none
      | none => none
  | _ => none

/-- `bigEval` of a `Case` factors as scrutinee-then-`caseDispatch`. -/
theorem bigEval_case (n : Nat) (ρ : CekEnv) (scrut : Term) (alts : List Term) :
    bigEval (n+1) ρ (.Case scrut alts)
      = (bigEval n ρ scrut).bind (fun vsc => caseDispatch n ρ alts vsc) := by
  cases hv : bigEval n ρ scrut with
  | none => simp only [bigEval, hv, Option.none_bind]
  | some v =>
      cases v with
      | VCon c =>
          cases hcf : constToTagAndFields c with
          | none => simp only [bigEval, hv, hcf, Option.some_bind, caseDispatch]
          | some x =>
              obtain ⟨tag, nc, fields⟩ := x
              cases ha : alts[tag]? with
              | none => simp only [bigEval, hv, hcf, ha, Option.some_bind, caseDispatch]
              | some alt =>
                  cases hb : bigEval n ρ alt with
                  | none => simp only [bigEval, hv, hcf, ha, hb, Option.some_bind, caseDispatch]
                  | some vAlt => simp only [bigEval, hv, hcf, ha, hb, Option.some_bind, caseDispatch]
      | VConstr tag fields =>
          cases ha : alts[tag]? with
          | none => simp only [bigEval, hv, ha, Option.some_bind, caseDispatch]
          | some alt =>
              cases hb : bigEval n ρ alt with
              | none => simp only [bigEval, hv, ha, hb, Option.some_bind, caseDispatch]
              | some vAlt => simp only [bigEval, hv, ha, hb, Option.some_bind, caseDispatch]
      | VLam body env => simp only [bigEval, hv, Option.some_bind, caseDispatch]
      | VDelay body env => simp only [bigEval, hv, Option.some_bind, caseDispatch]
      | VBuiltin b args ea => simp only [bigEval, hv, Option.some_bind, caseDispatch]

include hSat hWf

mutual
theorem EvalSim : ∀ (f : Nat) (ρ : SymEnv) (t : Term), WFSymEnv M ρ →
    denoteInc M (symEval f ρ t) = false →
    (∀ k, bigEval (f + k) (denoteEnv M ρ) t = SymOut M (symEval f ρ t)) ∧
    (denoteErr M (symEval f ρ t) = false → WFSymVal M (symEval f ρ t).val)
  | 0, _, _, _, hinc => by simp [symEval, denoteInc, incR] at hinc
  | n+1, ρ, .Var j, hwf, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval]
        rw [denoteEnv_lookup]
        cases hl : symLookup ρ j with
        | some v => simp [symEval, hl, SymOut, denoteErr, denoteVal, errR]
        | none => simp [symEval, hl, SymOut, denoteErr, errR]
      · cases hl : symLookup ρ j with
        | some v => simp only [symEval, hl]; exact wf_symLookup M ρ j v hwf hl
        | none => exfalso; revert herr; simp [symEval, hl, denoteErr, errR]
  | n+1, ρ, .Constant cb, _, _ => by
      obtain ⟨c, bt⟩ := cb
      refine ⟨fun k => ?_, fun _ => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval]
        simp only [symEval, SymOut, denoteErr, denoteVal, denoteSymV]
        rw [decode_const M c]; simp
      · simp only [symEval, WFSymVal]; exact wf_const M c
  | n+1, ρ, .Builtin b, _, _ => by
      refine ⟨fun k => ?_, fun _ => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval]
        simp [symEval, SymOut, denoteErr, denoteVal, denoteSymV, denoteSymList]
      · simp [symEval, WFSymVal, WFSymList]
  | n+1, ρ, .Lam nm body, hwf, _ => by
      refine ⟨fun k => ?_, fun _ => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval]
        simp [symEval, SymOut, denoteErr, denoteVal, denoteSymV]
      · simpa [symEval, WFSymVal] using hwf
  | n+1, ρ, .Delay body, hwf, _ => by
      refine ⟨fun k => ?_, fun _ => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval]
        simp [symEval, SymOut, denoteErr, denoteVal, denoteSymV]
      · simpa [symEval, WFSymVal] using hwf
  | n+1, ρ, .Error, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval]
        simp [symEval, SymOut, denoteErr, errR]
      · exfalso; revert herr; simp [symEval, denoteErr, errR]
  | n+1, ρ, .Apply f' a, hwf, hinc => by
      let rf := symEval n ρ f'
      let ra := symEval n ρ a
      let rap := symApply n rf.val ra.val
      have hout : denoteInc M (symThen rf (symThen ra rap)) = false := by
        simpa only [symEval] using hinc
      have hf_inc := (symThen_inc_false M rf (symThen ra rap) hout).1
      obtain ⟨IHf1, IHf2⟩ := EvalSim n ρ f' hwf hf_inc
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval, symEval]
        rw [SymOut_symThen M rf (symThen ra rap) hout, IHf1 k]
        cases hfe : denoteErr M rf with
        | true => simp [SymOut, rf, hfe]
        | false =>
            have hin := (symThen_inc_false M rf (symThen ra rap) hout).2 hfe
            have ha_inc := (symThen_inc_false M ra rap hin).1
            obtain ⟨IHa1, IHa2⟩ := EvalSim n ρ a hwf ha_inc
            rw [SymOut_symThen M ra rap hin, IHa1 k]
            cases hae : denoteErr M ra with
            | true => simp [SymOut, rf, ra, hfe, hae]
            | false =>
                have hap_inc := (symThen_inc_false M ra rap hin).2 hae
                obtain ⟨IHap1, _⟩ := ApplySim n rf.val ra.val
                  (IHf2 hfe) (IHa2 hae) hap_inc
                simpa [SymOut, rf, ra, hfe, hae, Option.bind] using IHap1 k
      · have herr' : denoteErr M (symThen rf (symThen ra rap)) = false := by
          simpa only [symEval] using herr
        have ⟨hrf, hrin⟩ := symThen_err_false M rf (symThen ra rap) hout herr'
        have hin := (symThen_inc_false M rf (symThen ra rap) hout).2 hrf
        have ⟨hra, hrap⟩ := symThen_err_false M ra rap hin hrin
        have ha_inc := (symThen_inc_false M ra rap hin).1
        have hap_inc := (symThen_inc_false M ra rap hin).2 hra
        obtain ⟨_, IHa2⟩ := EvalSim n ρ a hwf ha_inc
        obtain ⟨_, IHap2⟩ := ApplySim n rf.val ra.val
          (IHf2 hrf) (IHa2 hra) hap_inc
        simpa only [symEval, symThen] using IHap2 hrap
  | n+1, ρ, .Force e, hwf, hinc => by
      let rt := symEval n ρ e
      let rfo := symForce n rt.val
      have hinc' : denoteInc M (symThen rt rfo) = false := by simpa only [symEval] using hinc
      have htinc := (symThen_inc_false M rt rfo hinc').1
      obtain ⟨IHt1, IHt2⟩ := EvalSim n ρ e hwf htinc
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval, symEval]
        rw [SymOut_symThen M rt rfo hinc', IHt1 k]
        cases hte : denoteErr M rt with
        | true => simp [SymOut, rt, hte]
        | false =>
            have hfoinc := (symThen_inc_false M rt rfo hinc').2 hte
            obtain ⟨IHfo1, _⟩ := ForceSim n rt.val (IHt2 hte) hfoinc
            simpa [SymOut, rt, hte, Option.bind] using IHfo1 k
      · have herr' : denoteErr M (symThen rt rfo) = false := by simpa only [symEval] using herr
        have ⟨hrte, hrfo⟩ := symThen_err_false M rt rfo hinc' herr'
        have hfoinc := (symThen_inc_false M rt rfo hinc').2 hrte
        obtain ⟨_, IHfo2⟩ := ForceSim n rt.val (IHt2 hrte) hfoinc
        simpa only [symEval, symThen] using IHfo2 hrfo
  | n+1, ρ, .Constr tag ms, hwf, hinc => by
      let rs := symEvalList n ρ ms
      let vc := SymV.constr tag (rs.map SymR.val)
      have hincv : denoteInc M (symThenList rs vc) = false := by simpa only [symEval] using hinc
      have hincs : denoteInc M (symThenList rs junk) = false := by
        simpa only [denoteInc, symThenList_inc_irrel rs vc junk] using hincv
      obtain ⟨IHL1, IHL2⟩ := EvalListSim n ρ ms hwf hincs
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval, symEval]
        rw [SymOut_symThenList M rs vc hincv, IHL1 k]
        cases hL : SymOutList M rs with
        | none => simp [hL]
        | some vs =>
            have hvs := symOutList_some M hL
            simp [hL, vc, denoteSymV, denoteSymList_eq_map, denoteVal, hvs]
      · have herrv : denoteErr M (symThenList rs vc) = false := by
          simpa only [symEval] using herr
        have herr' : denoteErr M (symThenList rs junk) = false := by
          simpa only [denoteErr, symThenList_err_irrel rs vc junk] using herrv
        have hmem := IHL2 herr'
        rw [show (symEval (n + 1) ρ (.Constr tag ms)).val = vc by simp [symEval, vc, rs, symThenList_val]]
        simp only [vc, WFSymVal]
        apply wfSymList_of_mem M
        intro v hv
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
        exact hmem r hr
  | n+1, ρ, .Case scrut alts, hwf, hinc => by
      let rsc := symEval n ρ scrut
      let rc := symCase n ρ alts rsc.val
      have hinc' : denoteInc M (symThen rsc rc) = false := by simpa only [symEval] using hinc
      have hscinc := (symThen_inc_false M rsc rc hinc').1
      obtain ⟨IHs1, IHs2⟩ := EvalSim n ρ scrut hwf hscinc
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add, bigEval_case, IHs1 k]
        simp only [symEval]
        rw [SymOut_symThen M rsc rc hinc']
        cases hse : denoteErr M rsc with
        | true => simp [SymOut, rsc, hse]
        | false =>
            have hrcinc := (symThen_inc_false M rsc rc hinc').2 hse
            obtain ⟨IHc1, _⟩ := CaseSim n ρ alts rsc.val hwf (IHs2 hse) hrcinc
            simpa [SymOut, rsc, hse, Option.bind] using IHc1 k
      · have herr' : denoteErr M (symThen rsc rc) = false := by simpa only [symEval] using herr
        have ⟨hrsc, hrc⟩ := symThen_err_false M rsc rc hinc' herr'
        have hrcinc := (symThen_inc_false M rsc rc hinc').2 hrsc
        obtain ⟨_, IHc2⟩ := CaseSim n ρ alts rsc.val hwf (IHs2 hrsc) hrcinc
        simpa only [symEval, symThen] using IHc2 hrc
termination_by f _ t => (f, sizeOf t)
theorem ApplySim : ∀ (f : Nat) (vf va : SymV), WFSymVal M vf → WFSymVal M va →
    denoteInc M (symApply f vf va) = false →
    (∀ k, applyVal (f + k) (denoteSymV M vf) (denoteSymV M va) = SymOut M (symApply f vf va)) ∧
    (denoteErr M (symApply f vf va) = false → WFSymVal M (symApply f vf va).val)
  | 0, _, _, _, _, hinc => by simp [symApply, denoteInc, incR] at hinc
  | n+1, .lam body ρ, va, hwf, hva, hinc => by
      simp only [symApply] at hinc ⊢
      have hwfe : WFSymEnv M (va :: ρ) := ⟨hva, hwf⟩
      obtain ⟨IH1, IH2⟩ := EvalSim n (va :: ρ) body hwfe hinc
      refine ⟨fun k => ?_, IH2⟩
      rw [Nat.succ_add]; simp only [denoteSymV, applyVal]; exact IH1 k
  | n+1, .fo e, _, _, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]; simp only [denoteSymV]; rw [applyVal_decodeV]
        simp [symApply, SymOut, denoteErr, errR]
      · exfalso; revert herr; simp [symApply, denoteErr, errR]
  | n+1, .delay body ρ, _, _, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]; simp [symApply, SymOut, denoteErr, errR, denoteSymV, applyVal]
      · exfalso; revert herr; simp [symApply, denoteErr, errR]
  | n+1, .constr tag fs, _, _, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]; simp [symApply, SymOut, denoteErr, errR, denoteSymV, applyVal]
      · exfalso; revert herr; simp [symApply, denoteErr, errR]
  | n+1, .builtin b args ea, va, hwf, hva, hinc => by
      have hwa : WFSymList M (va :: args) := ⟨hva, hwf⟩
      cases hh : ea.head with
      | argQ =>
          refine ⟨fun k => ?_, fun herr => ?_⟩
          · rw [Nat.succ_add]; simp [symApply, hh, denoteSymV, applyVal, SymOut, denoteErr, errR]
          · exfalso; revert herr; simp [symApply, hh, denoteErr, errR]
      | argV =>
          cases ht : ea.tail with
          | some rest =>
              refine ⟨fun k => ?_, fun _ => ?_⟩
              · rw [Nat.succ_add]
                simp [symApply, hh, ht, denoteSymV, applyVal, SymOut, denoteErr, denoteVal, denoteSymList]
              · simpa [symApply, hh, ht, WFSymVal] using hwa
          | none =>
              have hinc' : denoteInc M (symSaturate b (va :: args)) = false := by
                simpa only [symApply, hh, ht] using hinc
              refine ⟨fun k => ?_, fun herr => ?_⟩
              · rw [Nat.succ_add]
                simp only [denoteSymV, applyVal, hh, ht]
                show evalBuiltin b (denoteSymList M (va :: args)) = _
                rw [hSat b (va :: args) hwa hinc']; simp only [symApply, hh, ht]
              · simp only [symApply, hh, ht]
                exact hWf b (va :: args) hwa hinc' (by simpa only [symApply, hh, ht] using herr)
  | n+1, .choice c x y, va, hwf, hva, hinc => by
      simp only [symApply, denoteInc_symMerge] at hinc
      simp only [WFSymVal] at hwf
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at hinc hwf
        obtain ⟨IH1, IH2⟩ := ApplySim n x va hwf hva hinc
        refine ⟨fun k => ?_, fun herr => ?_⟩
        · simp only [symApply, denoteSymV, hc, if_true, SymOut_symMerge]
          have hfk : (n+1)+k = n+(k+1) := by omega
          rw [hfk]; exact IH1 (k+1)
        · simp only [symApply]
          refine WFSymVal_symMerge M c _ _ ?_
          simp only [hc, if_true]
          exact IH2 (by simp only [symApply, denoteErr_symMerge, hc, if_true] at herr; exact herr)
      · simp only [hc, if_false, Bool.false_eq_true] at hinc hwf
        obtain ⟨IH1, IH2⟩ := ApplySim n y va hwf hva hinc
        refine ⟨fun k => ?_, fun herr => ?_⟩
        · simp only [symApply, denoteSymV, hc, if_false, Bool.false_eq_true, SymOut_symMerge]
          have hfk : (n+1)+k = n+(k+1) := by omega
          rw [hfk]; exact IH1 (k+1)
        · simp only [symApply]
          refine WFSymVal_symMerge M c _ _ ?_
          simp only [hc, if_false, Bool.false_eq_true]
          exact IH2 (by simp only [symApply, denoteErr_symMerge, hc, if_false, Bool.false_eq_true] at herr; exact herr)
termination_by f _ _ => (f, 0)
theorem ForceSim : ∀ (f : Nat) (vt : SymV), WFSymVal M vt →
    denoteInc M (symForce f vt) = false →
    (∀ k, forceVal (f + k) (denoteSymV M vt) = SymOut M (symForce f vt)) ∧
    (denoteErr M (symForce f vt) = false → WFSymVal M (symForce f vt).val)
  | 0, _, _, hinc => by simp [symForce, denoteInc, incR] at hinc
  | n+1, .delay body ρ, hwf, hinc => by
      simp only [symForce] at hinc ⊢
      obtain ⟨IH1, IH2⟩ := EvalSim n ρ body hwf hinc
      exact ⟨fun k => by rw [Nat.succ_add]; simpa only [denoteSymV, forceVal] using IH1 k, IH2⟩
  | n+1, .fo e, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]; simp only [denoteSymV]; rw [forceVal_decodeV]; simp [symForce, SymOut, denoteErr, errR]
      · exfalso; revert herr; simp [symForce, denoteErr, errR]
  | n+1, .lam body ρ, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]; simp [symForce, SymOut, denoteErr, errR, denoteSymV, forceVal]
      · exfalso; revert herr; simp [symForce, denoteErr, errR]
  | n+1, .constr tag fs, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]; simp [symForce, SymOut, denoteErr, errR, denoteSymV, forceVal]
      · exfalso; revert herr; simp [symForce, denoteErr, errR]
  | n+1, .builtin b args ea, hwf, hinc => by
      have hwa : WFSymList M args := hwf
      cases hh : ea.head with
      | argV =>
          refine ⟨fun k => ?_, fun herr => ?_⟩
          · rw [Nat.succ_add]; simp [symForce, hh, denoteSymV, forceVal, SymOut, denoteErr, errR]
          · exfalso; revert herr; simp [symForce, hh, denoteErr, errR]
      | argQ =>
          cases ht : ea.tail with
          | some rest =>
              refine ⟨fun k => ?_, fun _ => ?_⟩
              · rw [Nat.succ_add]
                simp [symForce, hh, ht, denoteSymV, forceVal, SymOut, denoteErr, denoteVal, denoteSymList]
              · simpa [symForce, hh, ht, WFSymVal] using hwa
          | none =>
              have hinc' : denoteInc M (symSaturate b args) = false := by
                simpa only [symForce, hh, ht] using hinc
              refine ⟨fun k => ?_, fun herr => ?_⟩
              · rw [Nat.succ_add]
                simp only [denoteSymV, forceVal, hh, ht]
                rw [hSat b args hwa hinc']; simp only [symForce, hh, ht]
              · simp only [symForce, hh, ht]
                exact hWf b args hwa hinc' (by simpa only [symForce, hh, ht] using herr)
  | n+1, .choice c x y, hwf, hinc => by
      simp only [symForce, denoteInc_symMerge] at hinc
      simp only [WFSymVal] at hwf
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at hinc hwf
        obtain ⟨IH1, IH2⟩ := ForceSim n x hwf hinc
        refine ⟨fun k => ?_, fun herr => ?_⟩
        · simp only [symForce, denoteSymV, hc, if_true, SymOut_symMerge]
          have hfk : (n+1)+k = n+(k+1) := by omega
          rw [hfk]; exact IH1 (k+1)
        · simp only [symForce]
          refine WFSymVal_symMerge M c _ _ ?_
          simp only [hc, if_true]
          exact IH2 (by simp only [symForce, denoteErr_symMerge, hc, if_true] at herr; exact herr)
      · simp only [hc, if_false, Bool.false_eq_true] at hinc hwf
        obtain ⟨IH1, IH2⟩ := ForceSim n y hwf hinc
        refine ⟨fun k => ?_, fun herr => ?_⟩
        · simp only [symForce, denoteSymV, hc, if_false, Bool.false_eq_true, SymOut_symMerge]
          have hfk : (n+1)+k = n+(k+1) := by omega
          rw [hfk]; exact IH1 (k+1)
        · simp only [symForce]
          refine WFSymVal_symMerge M c _ _ ?_
          simp only [hc, if_false, Bool.false_eq_true]
          exact IH2 (by simp only [symForce, denoteErr_symMerge, hc, if_false, Bool.false_eq_true] at herr; exact herr)
termination_by f _ => (f, 0)
theorem CaseSim : ∀ (f : Nat) (ρ : SymEnv) (alts : List Term) (sv : SymV),
    WFSymEnv M ρ → WFSymVal M sv → denoteInc M (symCase f ρ alts sv) = false →
    (∀ k, caseDispatch (f + k) (denoteEnv M ρ) alts (denoteSymV M sv) = SymOut M (symCase f ρ alts sv)) ∧
    (denoteErr M (symCase f ρ alts sv) = false → WFSymVal M (symCase f ρ alts sv).val)
  | 0, _, _, _, _, _, hinc => by simp [symCase, denoteInc, incR] at hinc
  | m+1, ρ, alts, .constr tag fields, hwfenv, hwfsv, hinc => by
      cases hat : alts[tag]? with
      | none =>
          refine ⟨fun k => ?_, fun herr => ?_⟩
          · simp [symCase, hat, denoteSymV, caseDispatch, SymOut, denoteErr, errR]
          · exfalso; revert herr; simp [symCase, hat, denoteErr, errR]
      | some alt =>
          let re := symEval m ρ alt
          let ra := symApplyList m re.val fields
          have hinc' : denoteInc M (symThen re ra) = false := by
            simpa only [symCase, hat] using hinc
          have heinc := (symThen_inc_false M re ra hinc').1
          obtain ⟨IHe1, IHe2⟩ := EvalSim m ρ alt hwfenv heinc
          have hfields : ∀ v ∈ fields, WFSymVal M v := wfSymList_mem M hwfsv
          refine ⟨fun k => ?_, fun herr => ?_⟩
          · simp only [symCase, hat, denoteSymV, caseDispatch]
            have hfk : (m+1)+k = m+(k+1) := by omega
            rw [hfk, IHe1 (k+1), SymOut_symThen M re ra hinc']
            cases hre : denoteErr M re with
            | true => simp [SymOut, re, hre]
            | false =>
                have hrainc := (symThen_inc_false M re ra hinc').2 hre
                obtain ⟨IHr1, _⟩ := ApplyListSim m re.val fields (IHe2 hre) hfields hrainc
                rw [denoteSymList_eq_map]
                simpa [SymOut, re, hre, Option.bind] using IHr1 (k+1)
          · have herr' : denoteErr M (symThen re ra) = false := by
              simpa only [symCase, hat] using herr
            have ⟨hre, hra⟩ := symThen_err_false M re ra hinc' herr'
            have hrainc := (symThen_inc_false M re ra hinc').2 hre
            obtain ⟨_, IHr2⟩ := ApplyListSim m re.val fields (IHe2 hre) hfields hrainc
            simpa only [symCase, hat, symThen] using IHr2 hra
  | m+1, ρ, alts, .choice c x y, hwfenv, hwfsv, hinc => by
      simp only [symCase, denoteInc_symMerge] at hinc
      simp only [WFSymVal] at hwfsv
      by_cases hc : (evalDyn M c).toBool
      · simp only [hc, if_true] at hinc hwfsv
        obtain ⟨IHx1, IHx2⟩ := CaseSim m ρ alts x hwfenv hwfsv hinc
        refine ⟨fun k => ?_, fun herr => ?_⟩
        · simp only [symCase, denoteSymV, hc, if_true, SymOut_symMerge]
          have hfk : (m+1)+k = m+(k+1) := by omega
          rw [hfk]; exact IHx1 (k+1)
        · simp only [symCase]
          refine WFSymVal_symMerge M c _ _ ?_
          simp only [hc, if_true]
          exact IHx2 (by simp only [symCase, denoteErr_symMerge, hc, if_true] at herr; exact herr)
      · simp only [hc, if_false, Bool.false_eq_true] at hinc hwfsv
        obtain ⟨IHy1, IHy2⟩ := CaseSim m ρ alts y hwfenv hwfsv hinc
        refine ⟨fun k => ?_, fun herr => ?_⟩
        · simp only [symCase, denoteSymV, hc, if_false, Bool.false_eq_true, SymOut_symMerge]
          have hfk : (m+1)+k = m+(k+1) := by omega
          rw [hfk]; exact IHy1 (k+1)
        · simp only [symCase]
          refine WFSymVal_symMerge M c _ _ ?_
          simp only [hc, if_false, Bool.false_eq_true]
          exact IHy2 (by simp only [symCase, denoteErr_symMerge, hc, if_false, Bool.false_eq_true] at herr; exact herr)
  | m+1, ρ, alts, .lam body env, _, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · simp [symCase, denoteSymV, caseDispatch, SymOut, denoteErr, errR]
      · exfalso; revert herr; simp [symCase, denoteErr, errR]
  | m+1, ρ, alts, .delay body env, _, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · simp [symCase, denoteSymV, caseDispatch, SymOut, denoteErr, errR]
      · exfalso; revert herr; simp [symCase, denoteErr, errR]
  | m+1, ρ, alts, .builtin b args ea, _, _, _ => by
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · simp [symCase, denoteSymV, caseDispatch, SymOut, denoteErr, errR]
      · exfalso; revert herr; simp [symCase, denoteErr, errR]
  | m+1, ρ, alts, .fo e, hwfenv, hwfsv, hinc => by
      let altRs := symEvalList m ρ alts
      have hAlt : ∀ (i : Nat),
          denoteInc M (altOr altRs i) = false →
          (∀ k,
            (match alts[i]? with
             | some alt => bigEval (m + (k+1)) (denoteEnv M ρ) alt
             | none => none) = SymOut M (altOr altRs i)) ∧
          (denoteErr M (altOr altRs i) = false → WFSymVal M (altOr altRs i).val) := by
        intro i hi
        cases ha : alts[i]? with
        | none =>
            have hnone : altOr altRs i = errR := by
              simp [altRs, altOr, symEvalList_eq_map, ha]
            refine ⟨fun k => ?_, fun herr => ?_⟩
            · simp [ha, hnone, SymOut, denoteErr, errR]
            · exfalso; revert herr; simp [hnone, denoteErr, errR]
        | some alt =>
            have hsome : altOr altRs i = symEval m ρ alt := by
              simp [altRs, altOr, symEvalList_eq_map, ha]
            have hi' : denoteInc M (symEval m ρ alt) = false := by simpa [hsome] using hi
            obtain ⟨IHa1, IHa2⟩ := EvalSim m ρ alt hwfenv hi'
            refine ⟨fun k => ?_, fun herr => ?_⟩
            · simp [ha, hsome, IHa1 (k+1)]
            · simpa [hsome] using IHa2 (by simpa [hsome] using herr)
      have hAltApply : ∀ (i : Nat) (fields : List SymV),
          (∀ v ∈ fields, WFSymVal M v) →
          denoteInc M (symThen (altOr altRs i) (symApplyList m (altOr altRs i).val fields)) = false →
          (∀ k,
            (match alts[i]? with
             | some alt =>
                 match bigEval (m + (k+1)) (denoteEnv M ρ) alt with
                 | some vAlt => applyValList (m + (k+1)) vAlt (fields.map (denoteSymV M))
                 | none => none
             | none => none)
              = SymOut M (symThen (altOr altRs i) (symApplyList m (altOr altRs i).val fields))) ∧
          (denoteErr M (symThen (altOr altRs i) (symApplyList m (altOr altRs i).val fields)) = false →
            WFSymVal M (symThen (altOr altRs i) (symApplyList m (altOr altRs i).val fields)).val) := by
        intro i fields hfields hi
        cases ha : alts[i]? with
        | none =>
            have hnone : altOr altRs i = errR := by
              simp [altRs, altOr, symEvalList_eq_map, ha]
            refine ⟨fun k => ?_, fun herr => ?_⟩
            · simp [ha, hnone, SymOut, symThen, denoteErr, errR, evalDyn_sIte]
            · exfalso; revert herr; simp [hnone, symThen, denoteErr, errR, evalDyn_sIte]
        | some alt =>
            have hsome : altOr altRs i = symEval m ρ alt := by
              simp [altRs, altOr, symEvalList_eq_map, ha]
            let re := symEval m ρ alt
            let ra := symApplyList m re.val fields
            have hi' : denoteInc M (symThen re ra) = false := by
              simpa [hsome, re, ra] using hi
            have heinc := (symThen_inc_false M re ra hi').1
            obtain ⟨IHe1, IHe2⟩ := EvalSim m ρ alt hwfenv heinc
            refine ⟨fun k => ?_, fun herr => ?_⟩
            · simp only [ha]
              rw [IHe1 (k+1)]
              simp only [hsome, re, ra]
              change (match SymOut M re with
                | some vAlt => applyValList (m + (k + 1)) vAlt (fields.map (denoteSymV M))
                | none => none) = SymOut M (symThen re ra)
              rw [SymOut_symThen M re ra hi']
              cases hre : denoteErr M re with
              | true => simp [SymOut, re, hre, hsome]
              | false =>
                  have hrainc := (symThen_inc_false M re ra hi').2 hre
                  obtain ⟨IHr1, _⟩ := ApplyListSim m re.val fields (IHe2 hre) hfields hrainc
                  simpa [SymOut, re, ra, hre, Option.bind, hsome] using IHr1 (k+1)
            · have herr' : denoteErr M (symThen re ra) = false := by
                simpa [hsome, re, ra] using herr
              have ⟨hre, hra⟩ := symThen_err_false M re ra hi' herr'
              have hrainc := (symThen_inc_false M re ra hi').2 hre
              obtain ⟨_, IHr2⟩ := ApplyListSim m re.val fields (IHe2 hre) hfields hrainc
              simpa [hsome, re, ra, symThen] using IHr2 hra
      have hAltNoFields : ∀ (i kk : Nat),
          denoteInc M (altOr altRs i) = false →
            (match alts[i]? with
             | some alt =>
                 match bigEval (m + (kk+1)) (denoteEnv M ρ) alt with
                 | some vAlt => applyValList (m + (kk+1)) vAlt []
                 | none => none
             | none => none) = SymOut M (altOr altRs i) := by
        intro i kk hi
        have hs := (hAlt i hi).1 kk
        cases ha : alts[i]? with
        | none =>
            simp [ha] at hs ⊢
            exact hs
        | some alt =>
            cases hb : bigEval (m + (kk+1)) (denoteEnv M ρ) alt <;>
              simp [ha, hb, applyValList] at hs ⊢
            all_goals exact hs
      have hlen_altRs : altRs.length = alts.length := by
        simp [altRs, symEvalList_eq_map]
      have hAltWf : ∀ (i : Nat),
          denoteInc M (altOr altRs i) = false →
          denoteErr M (altOr altRs i) = false →
          WFSymVal M (altOr altRs i).val := by
        intro i hi he
        exact (hAlt i hi).2 he
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · have hfk : (m+1)+k = m+(k+1) := by omega
        rw [hfk]
        cases hv : (evalDyn M e).toV with
        | int n =>
            have hEvalTag : evalDyn M (V.sAsInt e) = .i n := by
              simpa [evalDyn_sAsInt, hv, SemV.getInt]
            have hincInt : denoteInc M (dispatchIntFrom (V.sAsInt e) 0 (symEvalList m ρ alts)) = false := by
              simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                SemV.conName, SemV.getInt, errR, incR, hv] using hinc
            by_cases hn0 : 0 ≤ n
            · let idx : Nat := n.toNat
              have hEvalNat : evalDyn M (V.sAsInt e) = .i (Int.ofNat (0 + idx)) := by
                have hcast : (Int.ofNat (0 + idx)) = n := by
                  simpa [idx] using (Int.toNat_of_nonneg hn0)
                have hrhs : (.i n : Dyn) = .i (Int.ofNat (0 + idx)) := by
                  rw [hcast]
                exact hEvalTag.trans hrhs
              have Hdispatch : ∀ i,
                  denoteInc M (altOr (symEvalList m ρ alts) i) = false →
                    (match alts[i]? with
                     | some alt =>
                         match bigEval (m + (k+1)) (denoteEnv M ρ) alt with
                         | some vAlt => applyValList (m + (k+1)) vAlt []
                         | none => none
                     | none => none) = SymOut M (altOr (symEvalList m ρ alts) i) := by
                intro i hi
                simpa [altRs] using hAltNoFields i k (by simpa [altRs] using hi)
              have hs := dispatchIntFrom_nat_sim M (V.sAsInt e) m k ρ (denoteEnv M ρ)
                0 idx alts hEvalNat Hdispatch hincInt
              simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch,
                denoteSymV, decodeV, constToTagAndFields, SemV.conName, SemV.getInt,
                dispatchIntFrom, errR, incR, hv, hn0, idx] using hs
            · have hneg : n < 0 := by omega
              have hs := dispatchIntFrom_neg_none M (V.sAsInt e) n hEvalTag hneg
                0 (symEvalList m ρ alts)
              simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch,
                denoteSymV, decodeV, constToTagAndFields, SemV.conName, SemV.getInt,
                dispatchIntFrom, errR, incR, hv, hn0] using hs
        | bool b =>
            by_cases hlen : 2 < altRs.length
            · have hlenA : 2 < alts.length := by simpa [hlen_altRs] using hlen
              cases b <;>
                simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
                  decodeV, constToTagAndFields, SemV.conName, SemV.getBool, SymOut, denoteErr,
                  errR, hlen, hlenA, hv] at hinc ⊢
            · have hlenA : ¬ 2 < alts.length := by simpa [hlen_altRs] using hlen
              cases b
              · have hi : denoteInc M (altOr altRs 0) = false := by
                  simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, SemV.conName,
                    SemV.getBool, hlen, hv] using hinc
                have hs := hAltNoFields 0 k hi
                simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV,
                  constToTagAndFields, SemV.conName, SemV.getBool, applyValList,
                  hlen, hlenA, hv] using hs
              · have hi : denoteInc M (altOr altRs 1) = false := by
                  simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, SemV.conName,
                    SemV.getBool, hlen, hv] using hinc
                have hs := hAltNoFields 1 k hi
                simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV,
                  constToTagAndFields, SemV.conName, SemV.getBool, applyValList,
                  hlen, hlenA, hv] using hs
        | unit =>
            by_cases hlen : 1 < altRs.length
            · have hlenA : 1 < alts.length := by simpa [hlen_altRs] using hlen
              simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
                decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr,
                errR, hlen, hlenA, hv] at hinc ⊢
            · have hlenA : ¬ 1 < alts.length := by simpa [hlen_altRs] using hlen
              have hi : denoteInc M (altOr altRs 0) = false := by
                simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, SemV.conName,
                  hlen, hv] using hinc
              have hs := hAltNoFields 0 k hi
              simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV,
                constToTagAndFields, SemV.conName, applyValList, hlen, hlenA, hv] using hs
        | bs s =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | str s =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | data d =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | pdlist dm =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | arr vl =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | g1 =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | g2 =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | ml =>
            simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
              decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr, errR, hv] at hinc ⊢
        | list vl =>
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfl : WFVL vl ∧ ConstSemVL vl := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 2 < altRs.length
            · have hlenA : 2 < alts.length := by simpa [hlen_altRs] using hlen
              cases vl <;>
                simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
                  decodeV, decodeVL, constToTagAndFields, SemV.conName, SymOut, denoteErr,
                  errR, hlen, hlenA, hv] at hinc ⊢
            · have hlenA : ¬ 2 < alts.length := by simpa [hlen_altRs] using hlen
              cases vl with
              | nil =>
                  have hi : denoteInc M (altOr altRs 1) = false := by
                    simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                      SemV.conName, SemV.getList, hlen, hv] using hinc
                  have hs := hAltNoFields 1 k hi
                  simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV, decodeVL,
                    constToTagAndFields, SemV.conName, SemV.getList, applyValList,
                    SemVL.isNil, hlen, hlenA, hv] using hs
              | cons h t =>
                  have hwfcons : WFV h ∧ WFVL t := by
                    simpa [WFVL] using hwfl.1
                  have hcscons : ConstSemV h ∧ ConstSemVL t := by
                    simpa [ConstSemVL] using hwfl.2
                  let fs : List SymV :=
                    [SymV.fo (VL.sHd (V.sAsList e)), SymV.fo (V.list (VL.sTl (V.sAsList e)))]
                  have hfields : ∀ v ∈ fs, WFSymVal M v := by
                    intro v hvf
                    simp [fs] at hvf
                    rcases hvf with rfl | hvf
                    · simpa [WFSymVal, WFDyn, evalDyn_sAsList, hv, SemV.getList, SemVL.hd] using hwfcons.1
                    · rcases hvf with rfl
                      · simp [WFSymVal, WFDyn, V.list, evalDyn_sAsList, hv, SemV.getList,
                          SemVL.tl, WFV, hwfcons.2, hcscons.2]
                  have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                    simpa [fs, symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                      SemV.conName, SemV.getList, SemVL.isNil, hlen, hv] using hinc
                  have hs := (hAltApply 0 fs hfields hi).1 k
                  simp [fs, denoteSymV, evalDyn_sAsList, V.list, hv, SemV.getList,
                    SemVL.hd, SemVL.tl] at hs
                  have hdh := decodeV_constSem h hcscons.1
                  rw [hdh] at hs
                  simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV, decodeVL,
                    constToTagAndFields, SemV.conName, SemV.getList, SemVL.isNil,
                    hlen, hlenA, hv] using hs
        | dlist dl =>
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfl : WFDL dl := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 2 < altRs.length
            · have hlenA : 2 < alts.length := by simpa [hlen_altRs] using hlen
              cases dl <;>
                simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
                  decodeV, decodeDL, constToTagAndFields, SemV.conName, SymOut, denoteErr,
                  errR, hlen, hlenA, hv] at hinc ⊢
            · have hlenA : ¬ 2 < alts.length := by simpa [hlen_altRs] using hlen
              cases dl with
              | nil =>
                  have hi : denoteInc M (altOr altRs 1) = false := by
                    simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                      SemV.conName, SemV.getDList, hlen, hv] using hinc
                  have hs := hAltNoFields 1 k hi
                  simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV, decodeDL,
                    constToTagAndFields, SemV.conName, SemV.getDList, applyValList,
                    SemDL.isNil, hlen, hlenA, hv] using hs
              | cons h t =>
                  have hwfcons : WFD h ∧ WFDL t := by
                    simpa [WFDL] using hwfl
                  let fs : List SymV :=
                    [SymV.fo (V.data (DL.sHd (V.sAsDL e))), SymV.fo (V.dlist (DL.sTl (V.sAsDL e)))]
                  have hfields : ∀ v ∈ fs, WFSymVal M v := by
                    intro v hvf
                    simp [fs] at hvf
                    rcases hvf with rfl | hvf
                    · simpa [WFSymVal, WFDyn, V.data, evalDyn_sAsDL, hv, SemV.getDList,
                        SemDL.hd, WFV] using hwfcons.1
                    · rcases hvf with rfl
                      · simpa [WFSymVal, WFDyn, V.dlist, evalDyn_sAsDL, hv, SemV.getDList,
                          SemDL.tl, WFV] using hwfcons.2
                  have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                    simpa [fs, symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                      SemV.conName, SemV.getDList, SemDL.isNil, hlen, hv] using hinc
                  have hs := (hAltApply 0 fs hfields hi).1 k
                  simpa [fs, symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV, decodeDL,
                    V.data, V.dlist, evalDyn_sAsDL,
                    constToTagAndFields, SemV.conName, SemV.getDList, SemDL.hd, SemDL.tl, SemDL.isNil,
                    hlen, hlenA, hv] using hs
        | pair a b =>
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfp : WFV a ∧ WFV b ∧ ConstSemV a ∧ ConstSemV b := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 1 < altRs.length
            · have hlenA : 1 < alts.length := by simpa [hlen_altRs] using hlen
              simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
                decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr,
                errR, hlen, hlenA, hv] at hinc ⊢
            · have hlenA : ¬ 1 < alts.length := by simpa [hlen_altRs] using hlen
              let fs : List SymV := [SymV.fo (V.sFst e), SymV.fo (V.sSnd e)]
              have hfields : ∀ v ∈ fs, WFSymVal M v := by
                intro v hvf
                simp [fs] at hvf
                rcases hvf with rfl | hvf
                · simpa [WFSymVal, WFDyn, evalDyn_sFst, hv, SemV.pFst] using hwfp.1
                · rcases hvf with rfl
                  · simpa [WFSymVal, WFDyn, evalDyn_sSnd, hv, SemV.pSnd] using hwfp.2.1
              have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                simpa [fs, symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                  SemV.conName, SemV.pFst, SemV.pSnd, hlen, hv] using hinc
              have hs := (hAltApply 0 fs hfields hi).1 k
              have hda := decodeV_constSem a hwfp.2.2.1
              have hdb := decodeV_constSem b hwfp.2.2.2
              simp [fs, denoteSymV, evalDyn_sFst, evalDyn_sSnd, hv, SemV.pFst, SemV.pSnd] at hs
              rw [hda, hdb] at hs
              simpa [symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV,
                constToTagAndFields, SemV.conName, SemV.pFst, SemV.pSnd,
                hlen, hlenA, hv] using hs
        | pairD a b =>
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfp : WFD a ∧ WFD b := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 1 < altRs.length
            · have hlenA : 1 < alts.length := by simpa [hlen_altRs] using hlen
              simp [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, caseDispatch, denoteSymV,
                decodeV, constToTagAndFields, SemV.conName, SymOut, denoteErr,
                errR, hlen, hlenA, hv] at hinc ⊢
            · have hlenA : ¬ 1 < alts.length := by simpa [hlen_altRs] using hlen
              let fs : List SymV := [SymV.fo (V.data (V.sFstD e)), SymV.fo (V.data (V.sSndD e))]
              have hfields : ∀ v ∈ fs, WFSymVal M v := by
                intro v hvf
                simp [fs] at hvf
                rcases hvf with rfl | hvf
                · simpa [WFSymVal, WFDyn, evalDyn_sFstD, V.data, hv, SemV.pdFst, WFV] using hwfp.1
                · rcases hvf with rfl
                  · simpa [WFSymVal, WFDyn, evalDyn_sSndD, V.data, hv, SemV.pdSnd, WFV] using hwfp.2
              have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                simpa [fs, symCase, altRs, SymOut_symMerge, denoteInc_symMerge,
                  SemV.conName, SemV.pdFst, SemV.pdSnd, hlen, hv] using hinc
              have hs := (hAltApply 0 fs hfields hi).1 k
              simpa [fs, symCase, altRs, SymOut_symMerge, caseDispatch, denoteSymV, decodeV,
                evalDyn_sFstD, evalDyn_sSndD, V.data,
                constToTagAndFields, SemV.conName, SemV.pdFst, SemV.pdSnd,
                hlen, hlenA, hv] using hs
        | constr tag fields =>
            exfalso
            simpa [symCase, altRs, SymOut_symMerge, denoteInc_symMerge, denoteInc, SemV.conName,
              errR, incR, hv] using hinc
      · simp only [symCase]
        cases hv : (evalDyn M e).toV with
        | int n =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VUnit" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VInt" e) _ _ ?_
            simp [hv, SemV.conName]
            have hincInt : denoteInc M (dispatchIntFrom (V.sAsInt e) 0 (symEvalList m ρ alts)) = false := by
              simpa [symCase, altRs, denoteInc_symMerge, SemV.conName, SemV.getInt,
                errR, incR, hv] using hinc
            have herrInt : denoteErr M (dispatchIntFrom (V.sAsInt e) 0 (symEvalList m ρ alts)) = false := by
              simpa [symCase, altRs, denoteErr_symMerge, SemV.conName, SemV.getInt,
                errR, incR, hv] using herr
            exact dispatchIntFrom_wf M (V.sAsInt e) 0 (symEvalList m ρ alts)
              (by intro i hi he; simpa [altRs] using hAltWf i (by simpa [altRs] using hi) (by simpa [altRs] using he))
              hincInt herrInt
        | bool b =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            by_cases hlen : 2 < altRs.length
            · exfalso
              simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
                SemV.getBool, errR, hlen, hv] using herr
            · cases b
              · simp [altRs, hlen]
                refine WFSymVal_symMerge M (V.sAsBool e) (altOr altRs 1) (altOr altRs 0) ?_
                simp [evalDyn_sAsBool, hv, SemV.getBool]
                have hi : denoteInc M (altOr altRs 0) = false := by
                  simpa [symCase, altRs, denoteInc_symMerge, SemV.conName,
                    SemV.getBool, hlen, hv] using hinc
                have he : denoteErr M (altOr altRs 0) = false := by
                  simpa [symCase, altRs, denoteErr_symMerge, SemV.conName,
                    SemV.getBool, hlen, hv] using herr
                exact hAltWf 0 hi he
              · simp [altRs, hlen]
                refine WFSymVal_symMerge M (V.sAsBool e) (altOr altRs 1) (altOr altRs 0) ?_
                simp [evalDyn_sAsBool, hv, SemV.getBool]
                have hi : denoteInc M (altOr altRs 1) = false := by
                  simpa [symCase, altRs, denoteInc_symMerge, SemV.conName,
                    SemV.getBool, hlen, hv] using hinc
                have he : denoteErr M (altOr altRs 1) = false := by
                  simpa [symCase, altRs, denoteErr_symMerge, SemV.conName,
                    SemV.getBool, hlen, hv] using herr
                exact hAltWf 1 hi he
        | unit =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VUnit" e) _ _ ?_
            simp [hv, SemV.conName]
            by_cases hlen : 1 < altRs.length
            · exfalso
              simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
                errR, hlen, hv] using herr
            · have hi : denoteInc M (altOr altRs 0) = false := by
                simpa [symCase, altRs, denoteInc_symMerge, SemV.conName,
                  hlen, hv] using hinc
              have he : denoteErr M (altOr altRs 0) = false := by
                simpa [symCase, altRs, denoteErr_symMerge, SemV.conName,
                  hlen, hv] using herr
              simpa [altRs, hlen] using hAltWf 0 hi he
        | list vl =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VUnit" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VInt" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ ?_
            simp [hv, SemV.conName]
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfl : WFVL vl ∧ ConstSemVL vl := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 2 < altRs.length
            · exfalso
              cases vl <;>
                simpa [symCase, altRs, denoteErr_symMerge, denoteErr, evalDyn_sAsList,
                  SemV.conName, SemV.getList, SemVL.isNil, errR, hlen, hv] using herr
            · simp [altRs, hlen]
              cases vl with
              | nil =>
                  refine WFSymVal_symMerge M (VL.sIsNil (V.sAsList e)) (altOr altRs 1)
                    (symThen (altOr altRs 0)
                      (symApplyList m (altOr altRs 0).val
                        [SymV.fo (VL.sHd (V.sAsList e)), SymV.fo (V.list (VL.sTl (V.sAsList e)))])) ?_
                  simp [evalDyn_sAsList, hv, SemV.getList, SemVL.isNil]
                  have hi : denoteInc M (altOr altRs 1) = false := by
                    simpa [symCase, altRs, denoteInc_symMerge, SemV.conName,
                      SemV.getList, hlen, hv] using hinc
                  have he : denoteErr M (altOr altRs 1) = false := by
                    simpa [symCase, altRs, denoteErr_symMerge, SemV.conName,
                      SemV.getList, hlen, hv] using herr
                  exact hAltWf 1 hi he
              | cons h t =>
                  have hwfcons : WFV h ∧ WFVL t := by
                    simpa [WFVL] using hwfl.1
                  have hcscons : ConstSemV h ∧ ConstSemVL t := by
                    simpa [ConstSemVL] using hwfl.2
                  let fs : List SymV :=
                    [SymV.fo (VL.sHd (V.sAsList e)), SymV.fo (V.list (VL.sTl (V.sAsList e)))]
                  have hfields : ∀ v ∈ fs, WFSymVal M v := by
                    intro v hvf
                    simp [fs] at hvf
                    rcases hvf with rfl | hvf
                    · simpa [WFSymVal, WFDyn, evalDyn_sAsList, hv, SemV.getList, SemVL.hd] using hwfcons.1
                    · rcases hvf with rfl
                      · simp [WFSymVal, WFDyn, V.list, evalDyn_sAsList, hv, SemV.getList,
                          SemVL.tl, WFV, hwfcons.2, hcscons.2]
                  refine WFSymVal_symMerge M (VL.sIsNil (V.sAsList e)) (altOr altRs 1)
                    (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) ?_
                  simp [fs, evalDyn_sAsList, hv, SemV.getList, SemVL.isNil]
                  have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                    simpa [fs, symCase, altRs, denoteInc_symMerge, SemV.conName,
                      SemV.getList, SemVL.isNil, hlen, hv] using hinc
                  have he : denoteErr M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                    simpa [fs, symCase, altRs, denoteErr_symMerge, SemV.conName,
                      SemV.getList, SemVL.isNil, hlen, hv] using herr
                  exact (hAltApply 0 fs hfields hi).2 he
        | dlist dl =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VUnit" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VInt" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VDList" e) _ _ ?_
            simp [hv, SemV.conName]
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfl : WFDL dl := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 2 < altRs.length
            · exfalso
              cases dl <;>
                simpa [symCase, altRs, denoteErr_symMerge, denoteErr, evalDyn_sAsDL,
                  SemV.conName, SemV.getDList, SemDL.isNil, errR, hlen, hv] using herr
            · simp [altRs, hlen]
              cases dl with
              | nil =>
                  refine WFSymVal_symMerge M (DL.sIsNil (V.sAsDL e)) (altOr altRs 1)
                    (symThen (altOr altRs 0)
                      (symApplyList m (altOr altRs 0).val
                        [SymV.fo (V.data (DL.sHd (V.sAsDL e))), SymV.fo (V.dlist (DL.sTl (V.sAsDL e)))])) ?_
                  simp [evalDyn_sAsDL, hv, SemV.getDList, SemDL.isNil]
                  have hi : denoteInc M (altOr altRs 1) = false := by
                    simpa [symCase, altRs, denoteInc_symMerge, SemV.conName,
                      SemV.getDList, hlen, hv] using hinc
                  have he : denoteErr M (altOr altRs 1) = false := by
                    simpa [symCase, altRs, denoteErr_symMerge, SemV.conName,
                      SemV.getDList, hlen, hv] using herr
                  exact hAltWf 1 hi he
              | cons h t =>
                  have hwfcons : WFD h ∧ WFDL t := by
                    simpa [WFDL] using hwfl
                  let fs : List SymV :=
                    [SymV.fo (V.data (DL.sHd (V.sAsDL e))), SymV.fo (V.dlist (DL.sTl (V.sAsDL e)))]
                  have hfields : ∀ v ∈ fs, WFSymVal M v := by
                    intro v hvf
                    simp [fs] at hvf
                    rcases hvf with rfl | hvf
                    · simpa [WFSymVal, WFDyn, V.data, evalDyn_sAsDL, hv, SemV.getDList,
                        SemDL.hd, WFV] using hwfcons.1
                    · rcases hvf with rfl
                      · simpa [WFSymVal, WFDyn, V.dlist, evalDyn_sAsDL, hv, SemV.getDList,
                          SemDL.tl, WFV] using hwfcons.2
                  refine WFSymVal_symMerge M (DL.sIsNil (V.sAsDL e)) (altOr altRs 1)
                    (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) ?_
                  simp [fs, evalDyn_sAsDL, hv, SemV.getDList, SemDL.isNil]
                  have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                    simpa [fs, symCase, altRs, denoteInc_symMerge, SemV.conName,
                      SemV.getDList, SemDL.isNil, hlen, hv] using hinc
                  have he : denoteErr M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                    simpa [fs, symCase, altRs, denoteErr_symMerge, SemV.conName,
                      SemV.getDList, SemDL.isNil, hlen, hv] using herr
                  exact (hAltApply 0 fs hfields hi).2 he
        | pair a b =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VUnit" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VInt" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VDList" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VPair" e) _ _ ?_
            simp [hv, SemV.conName]
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfp : WFV a ∧ WFV b ∧ ConstSemV a ∧ ConstSemV b := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 1 < altRs.length
            · exfalso
              simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
                errR, hlen, hv] using herr
            · let fs : List SymV := [SymV.fo (V.sFst e), SymV.fo (V.sSnd e)]
              have hfields : ∀ v ∈ fs, WFSymVal M v := by
                intro v hvf
                simp [fs] at hvf
                rcases hvf with rfl | hvf
                · simpa [WFSymVal, WFDyn, evalDyn_sFst, hv, SemV.pFst] using hwfp.1
                · rcases hvf with rfl
                  · simpa [WFSymVal, WFDyn, evalDyn_sSnd, hv, SemV.pSnd] using hwfp.2.1
              have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                simpa [fs, symCase, altRs, denoteInc_symMerge, SemV.conName,
                  SemV.pFst, SemV.pSnd, hlen, hv] using hinc
              have he : denoteErr M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                simpa [fs, symCase, altRs, denoteErr_symMerge, SemV.conName,
                  SemV.pFst, SemV.pSnd, hlen, hv] using herr
              simpa [fs, altRs, hlen] using (hAltApply 0 fs hfields hi).2 he
        | pairD a b =>
            refine WFSymVal_symMerge M (V.sIsCon "VBool" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VUnit" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VInt" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VDList" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VPair" e) _ _ ?_
            simp [hv, SemV.conName]
            refine WFSymVal_symMerge M (V.sIsCon "VPairD" e) _ _ ?_
            simp [hv, SemV.conName]
            have hwfd : WFDyn (evalDyn M e) := by simpa [WFSymVal] using hwfsv
            have hwfv : WFV (evalDyn M e).toV := WFV_toV_of_WFDyn hwfd
            have hwfp : WFD a ∧ WFD b := by
              simpa [hv, WFV] using hwfv
            by_cases hlen : 1 < altRs.length
            · exfalso
              simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
                errR, hlen, hv] using herr
            · let fs : List SymV := [SymV.fo (V.data (V.sFstD e)), SymV.fo (V.data (V.sSndD e))]
              have hfields : ∀ v ∈ fs, WFSymVal M v := by
                intro v hvf
                simp [fs] at hvf
                rcases hvf with rfl | hvf
                · simpa [WFSymVal, WFDyn, evalDyn_sFstD, V.data, hv, SemV.pdFst, WFV] using hwfp.1
                · rcases hvf with rfl
                  · simpa [WFSymVal, WFDyn, evalDyn_sSndD, V.data, hv, SemV.pdSnd, WFV] using hwfp.2
              have hi : denoteInc M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                simpa [fs, symCase, altRs, denoteInc_symMerge, SemV.conName,
                  SemV.pdFst, SemV.pdSnd, hlen, hv] using hinc
              have he : denoteErr M (symThen (altOr altRs 0) (symApplyList m (altOr altRs 0).val fs)) = false := by
                simpa [fs, symCase, altRs, denoteErr_symMerge, SemV.conName,
                  SemV.pdFst, SemV.pdSnd, hlen, hv] using herr
              simpa [fs, altRs, hlen] using (hAltApply 0 fs hfields hi).2 he
        | constr tag fields =>
            exfalso
            simpa [symCase, altRs, denoteInc_symMerge, denoteInc, SemV.conName,
              errR, incR, hv] using hinc
        | bs s =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | str s =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | data d =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | pdlist dm =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | arr vl =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | g1 =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | g2 =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
        | ml =>
            exfalso
            simpa [symCase, altRs, denoteErr_symMerge, denoteErr, SemV.conName,
              errR, hv] using herr
termination_by f _ _ _ => (f, 0)
theorem EvalListSim : ∀ (f : Nat) (ρ : SymEnv) (ts : List Term), WFSymEnv M ρ →
    denoteInc M (symThenList (symEvalList f ρ ts) junk) = false →
    (∀ k, bigEvalList (f + k) (denoteEnv M ρ) ts = SymOutList M (symEvalList f ρ ts)) ∧
    (denoteErr M (symThenList (symEvalList f ρ ts) junk) = false →
      ∀ r ∈ symEvalList f ρ ts, WFSymVal M r.val)
  | _, _, [], _, _ => by
      refine ⟨fun k => ?_, fun _ r hr => ?_⟩
      · simp [symEvalList, bigEvalList, SymOutList]
      · simp [symEvalList] at hr
  | f, ρ, t :: ts, hwf, hinc => by
      let rt := symEval f ρ t
      let rts := symThenList (symEvalList f ρ ts) junk
      have hinc' : denoteInc M (symThen rt rts) = false := by
        simpa only [symEvalList, symThenList] using hinc
      have htinc := (symThen_inc_false M rt rts hinc').1
      obtain ⟨IHt1, IHt2⟩ := EvalSim f ρ t hwf htinc
      refine ⟨fun k => ?_, fun herr r hr => ?_⟩
      · simp only [symEvalList, bigEvalList]
        rw [IHt1 k, SymOutList_cons]
        cases hrt : SymOut M rt with
        | none => simpa [rt] using hrt
        | some v =>
            have hrte : denoteErr M rt = false := by
              cases he : denoteErr M rt <;> simp_all [SymOut]
            have htsinc := (symThen_inc_false M rt rts hinc').2 hrte
            obtain ⟨IHr1, _⟩ := EvalListSim f ρ ts hwf htsinc
            rw [IHr1 k]
            cases SymOutList M (symEvalList f ρ ts) <;> rfl
      · have herr' : denoteErr M (symThen rt rts) = false := by
          simpa only [symEvalList, symThenList] using herr
        have ⟨hrte, hrts⟩ := symThen_err_false M rt rts hinc' herr'
        have htsinc := (symThen_inc_false M rt rts hinc').2 hrte
        obtain ⟨_, IHr2⟩ := EvalListSim f ρ ts hwf htsinc
        simp only [symEvalList] at hr
        rcases List.mem_cons.1 hr with h | h
        · subst h; exact IHt2 hrte
        · exact IHr2 hrts r h
termination_by f _ ts => (f, sizeOf ts)
theorem ApplyListSim : ∀ (f : Nat) (vf : SymV) (vs : List SymV), WFSymVal M vf →
    (∀ v ∈ vs, WFSymVal M v) → denoteInc M (symApplyList f vf vs) = false →
    (∀ k, applyValList (f + k) (denoteSymV M vf) (vs.map (denoteSymV M)) = SymOut M (symApplyList f vf vs)) ∧
    (denoteErr M (symApplyList f vf vs) = false → WFSymVal M (symApplyList f vf vs).val)
  | _, vf, [], hvf, _, _ => by
      refine ⟨fun k => ?_, fun _ => ?_⟩
      · simp [symApplyList, applyValList, SymOut, denoteErr, denoteVal]
      · simpa [symApplyList] using hvf
  | f, vf, a :: as, hvf, hvs, hinc => by
      let ra := symApply f vf a
      let rr := symApplyList f ra.val as
      have hinc' : denoteInc M (symThen ra rr) = false := by simpa only [symApplyList] using hinc
      have hainc := (symThen_inc_false M ra rr hinc').1
      have hva : WFSymVal M a := hvs a (by simp)
      have hvas : ∀ v ∈ as, WFSymVal M v := fun v hv => hvs v (List.mem_cons_of_mem a hv)
      obtain ⟨IHa1, IHa2⟩ := ApplySim f vf a hvf hva hainc
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · simp only [List.map_cons, symApplyList, applyValList]
        rw [IHa1 k, SymOut_symThen M ra rr hinc']
        cases hae : denoteErr M ra with
        | true => simp [SymOut, ra, hae]
        | false =>
            have hrrinc := (symThen_inc_false M ra rr hinc').2 hae
            obtain ⟨IHr1, _⟩ := ApplyListSim f ra.val as (IHa2 hae) hvas hrrinc
            simpa [SymOut, ra, hae, Option.bind] using IHr1 k
      · have herr' : denoteErr M (symThen ra rr) = false := by simpa only [symApplyList] using herr
        have ⟨hra, hrr⟩ := symThen_err_false M ra rr hinc' herr'
        have hrrinc := (symThen_inc_false M ra rr hinc').2 hra
        obtain ⟨_, IHr2⟩ := ApplyListSim f ra.val as (IHa2 hra) hvas hrrinc
        simpa only [symApplyList, symThen] using IHr2 hrr
termination_by f _ vs => (f, sizeOf vs)
end

end

/-! ## The builtin agreement lemmas (the "grind")

The compiler currently emits precise SMT for the binary integer builtins, the
proved structural list/pair builtins, and the simple `Data` constructors below.
It emits a definite error for builtins that the reference CEK does not denote,
and marks the remaining CEK-supported builtins as indeterminate.  Consequently
the saturation interface is total: every non-indeterminate saturated result is
one of the proved precise cases or a CEK-undefined builtin that both sides
evaluate as error. -/

private def preciseBinIntBuiltin : BuiltinFun → Prop
  | .AddInteger | .SubtractInteger | .MultiplyInteger
  | .EqualsInteger | .LessThanInteger | .LessThanEqualsInteger => True
  | _ => False

private def preciseUnaryBuiltin : BuiltinFun → Prop
  | .FstPair | .SndPair
  | .HeadList | .TailList | .NullList
  | .IData | .BData | .MkNilData | .MkNilPairData => True
  | _ => False

private def preciseMkConsBuiltin : BuiltinFun → Prop
  | .MkCons => True
  | _ => False

private def smtUnsupportedBuiltin : BuiltinFun → Prop
  | .Sha2_256 | .Sha3_256 | .Blake2b_256
  | .VerifyEd25519Signature | .SerializeData
  | .VerifyEcdsaSecp256k1Signature | .VerifySchnorrSecp256k1Signature
  | .Bls12_381_G1_add | .Bls12_381_G1_neg | .Bls12_381_G1_scalarMul
  | .Bls12_381_G1_equal | .Bls12_381_G1_hashToGroup
  | .Bls12_381_G1_compress | .Bls12_381_G1_uncompress
  | .Bls12_381_G2_add | .Bls12_381_G2_neg | .Bls12_381_G2_scalarMul
  | .Bls12_381_G2_equal | .Bls12_381_G2_hashToGroup
  | .Bls12_381_G2_compress | .Bls12_381_G2_uncompress
  | .Bls12_381_millerLoop | .Bls12_381_mulMlResult | .Bls12_381_finalVerify
  | .Keccak_256 | .Blake2b_224 | .Ripemd_160
  | .IndexArray | .LengthOfArray | .ListToArray
  | .InsertCoin | .LookupCoin | .ScaleValue | .UnionValue
  | .ValueContains | .ValueData | .UnValueData
  | .Bls12_381_G1_multiScalarMul | .Bls12_381_G2_multiScalarMul => True
  | _ => False

private theorem symBuiltin_binInt_len_ne_two (b : BuiltinFun) (xs : List SExpr)
    (hb : preciseBinIntBuiltin b) (h : xs.length ≠ 2) : symBuiltin b xs = incR := by
  cases b <;> simp [preciseBinIntBuiltin] at hb
  all_goals
    cases xs with
    | nil => rfl
    | cons _ xs =>
        cases xs with
        | nil => rfl
        | cons _ xs =>
            cases xs with
            | nil => contradiction
            | cons _ _ => rfl

private theorem binInt_inc_true_len_ne_two (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : preciseBinIntBuiltin b) (h : args.length ≠ 2) :
    denoteInc M (symSaturate b args) = true := by
  unfold symSaturate
  dsimp only
  have hbuiltin : symBuiltin b ((args.reverse.map reifyFO).map Prod.snd) = incR := by
    apply symBuiltin_binInt_len_ne_two b
    · exact hb
    · simpa using h
  rw [hbuiltin]
  rfl

private theorem symBuiltin_unary_len_ne_one (b : BuiltinFun) (xs : List SExpr)
    (hb : preciseUnaryBuiltin b) (h : xs.length ≠ 1) : symBuiltin b xs = incR := by
  cases b <;> simp [preciseUnaryBuiltin] at hb
  all_goals
    cases xs with
    | nil => rfl
    | cons _ xs =>
        cases xs with
        | nil => contradiction
        | cons _ _ => rfl

private theorem unary_inc_true_len_ne_one (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : preciseUnaryBuiltin b) (h : args.length ≠ 1) :
    denoteInc M (symSaturate b args) = true := by
  unfold symSaturate
  dsimp only
  have hbuiltin : symBuiltin b ((args.reverse.map reifyFO).map Prod.snd) = incR := by
    apply symBuiltin_unary_len_ne_one b
    · exact hb
    · simpa using h
  rw [hbuiltin]
  rfl

private theorem symBuiltin_mkCons_len_ne_two (xs : List SExpr)
    (h : xs.length ≠ 2) : symBuiltin .MkCons xs = incR := by
  cases xs with
  | nil => rfl
  | cons _ xs =>
      cases xs with
      | nil => rfl
      | cons _ xs =>
          cases xs with
          | nil => contradiction
          | cons _ _ => rfl

private theorem symBuiltin_mkCons_two_eq (h t : SExpr) :
    symBuiltin .MkCons [h, t] =
      symMerge (V.sIsCon "VDList" t)
        (foGuard (gData h) (V.dlist (DL.cons (V.sAsData h) (V.sAsDL t))))
        (symMerge (V.sIsCon "VList" t)
          (foGuard (V.sIsCon "VConstr" h) (V.list (VL.cons h (V.sAsList t))))
          errR) := rfl

private theorem mkCons_inc_true_len_ne_two (M : Model) (args : List SymV)
    (h : args.length ≠ 2) :
    denoteInc M (symSaturate .MkCons args) = true := by
  unfold symSaturate
  dsimp only
  have hbuiltin : symBuiltin .MkCons ((args.reverse.map reifyFO).map Prod.snd) = incR := by
    apply symBuiltin_mkCons_len_ne_two
    simpa using h
  rw [hbuiltin]
  rfl

private theorem builtin_inc_true (M : Model) (b : BuiltinFun) (args : List SymV)
    (hbuiltin : ∀ xs, symBuiltin b xs = incR) :
    denoteInc M (symSaturate b args) = true := by
  unfold symSaturate
  dsimp only
  rw [hbuiltin ((args.reverse.map reifyFO).map Prod.snd)]
  rfl

private theorem symBuiltin_unsupported (b : BuiltinFun) (xs : List SExpr)
    (hb : smtUnsupportedBuiltin b) : symBuiltin b xs = errR := by
  cases b <;> simp [smtUnsupportedBuiltin] at hb
  all_goals rfl

private theorem symBuiltin_inc_of_not_precise_not_unsupported (b : BuiltinFun) (xs : List SExpr)
    (hp : ¬ preciseBinIntBuiltin b) (hpu : ¬ preciseUnaryBuiltin b)
    (hpm : ¬ preciseMkConsBuiltin b) (hu : ¬ smtUnsupportedBuiltin b) :
    symBuiltin b xs = incR := by
  cases b <;> simp [preciseBinIntBuiltin, preciseUnaryBuiltin,
    preciseMkConsBuiltin, smtUnsupportedBuiltin] at hp hpu hpm hu
  all_goals rfl

private theorem unsupported_err_true (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : smtUnsupportedBuiltin b) : denoteErr M (symSaturate b args) = true := by
  unfold symSaturate
  dsimp only
  have hbuiltin : symBuiltin b ((args.reverse.map reifyFO).map Prod.snd) = errR :=
    symBuiltin_unsupported b _ hb
  rw [hbuiltin]
  simp [denoteErr, errR, evalDyn_sOr]

private theorem evalBuiltin_none_of_none (b : BuiltinFun) (args : List CekValue)
    (hpt : evalBuiltinPassThrough b args = none)
    (hconst : ∀ cs, evalBuiltinConst b cs = none) : evalBuiltin b args = none := by
  rw [evalBuiltin, hpt]
  cases h : extractConsts args with
  | none => rfl
  | some cs => simpa [hconst cs]

private theorem evalBuiltin_unsupported_none (b : BuiltinFun) (args : List CekValue)
    (hb : smtUnsupportedBuiltin b) : evalBuiltin b args = none := by
  cases b <;> simp [smtUnsupportedBuiltin] at hb
  all_goals
    apply evalBuiltin_none_of_none
    · rfl
    · intro cs; rfl

private theorem satAgrees_binInt (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : preciseBinIntBuiltin b)
    (hagrees : ∀ vy vx, evalBuiltin b (denoteSymList M [vy, vx])
      = if denoteErr M (symSaturate b [vy, vx]) then none
        else some (denoteVal M (symSaturate b [vy, vx]))) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    evalBuiltin b (denoteSymList M args) = SymOut M (symSaturate b args) := by
  intro _ hinc
  cases args with
  | nil =>
      exfalso
      have ht := binInt_inc_true_len_ne_two M b [] hb (by simp)
      rw [ht] at hinc
      contradiction
  | cons vy rest =>
      cases rest with
      | nil =>
          exfalso
          have ht := binInt_inc_true_len_ne_two M b [vy] hb (by simp)
          rw [ht] at hinc
          contradiction
      | cons vx rest2 =>
          cases rest2 with
          | nil =>
              simpa [SymOut] using hagrees vy vx
          | cons z zs =>
              exfalso
              have ht := binInt_inc_true_len_ne_two M b (vy :: vx :: z :: zs) hb (by simp)
              rw [ht] at hinc
              contradiction

private theorem satAgrees_unary (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : preciseUnaryBuiltin b)
    (hagrees : ∀ v, WFSymVal M v →
      evalBuiltin b (denoteSymList M [v])
        = if denoteErr M (symSaturate b [v]) then none
          else some (denoteVal M (symSaturate b [v]))) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    evalBuiltin b (denoteSymList M args) = SymOut M (symSaturate b args) := by
  intro hwf hinc
  cases args with
  | nil =>
      exfalso
      have ht := unary_inc_true_len_ne_one M b [] hb (by simp)
      rw [ht] at hinc
      contradiction
  | cons v rest =>
      cases rest with
      | nil =>
          have hwfv : WFSymVal M v := by simpa [WFSymList] using hwf.1
          simpa [SymOut] using hagrees v hwfv
      | cons w ws =>
          exfalso
          have ht := unary_inc_true_len_ne_one M b (v :: w :: ws) hb (by simp)
          rw [ht] at hinc
          contradiction

private theorem satAgrees_mkCons (M : Model) (args : List SymV) :
    WFSymList M args → denoteInc M (symSaturate .MkCons args) = false →
    evalBuiltin .MkCons (denoteSymList M args) = SymOut M (symSaturate .MkCons args) := by
  intro hwf hinc
  cases args with
  | nil =>
      exfalso
      have ht := mkCons_inc_true_len_ne_two M [] (by simp)
      rw [ht] at hinc
      contradiction
  | cons tail rest =>
      cases rest with
      | nil =>
          exfalso
          have ht := mkCons_inc_true_len_ne_two M [tail] (by simp)
          rw [ht] at hinc
          contradiction
      | cons head rest2 =>
          cases rest2 with
          | nil =>
              have hwft : WFSymVal M tail := by simpa [WFSymList] using hwf.1
              have hwfh : WFSymVal M head := by simpa [WFSymList] using hwf.2.1
              simpa [SymOut] using mkCons_agrees M tail head hwft hwfh
          | cons z zs =>
              exfalso
              have ht := mkCons_inc_true_len_ne_two M (tail :: head :: z :: zs) (by simp)
              rw [ht] at hinc
              contradiction

private theorem satAgrees_unsupported (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : smtUnsupportedBuiltin b) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    evalBuiltin b (denoteSymList M args) = SymOut M (symSaturate b args) := by
  intro _ _
  rw [evalBuiltin_unsupported_none b (denoteSymList M args) hb]
  unfold SymOut
  rw [unsupported_err_true M b args hb]
  simp

private theorem satAgrees_inc (M : Model) (b : BuiltinFun) (args : List SymV)
    (hbuiltin : ∀ xs, symBuiltin b xs = incR) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    evalBuiltin b (denoteSymList M args) = SymOut M (symSaturate b args) := by
  intro _ hinc
  exfalso
  rw [builtin_inc_true M b args hbuiltin] at hinc
  contradiction

private theorem add_sat_wf (M : Model) (vy vx : SymV) :
    WFSymVal M (symSaturate .AddInteger [vy, vx]).val := by
  change WFSymVal M (.fo (V.int (Op.add (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))))
  simp [WFSymVal, WFDyn, WFV, V.int, Op.add]

private theorem sub_sat_wf (M : Model) (vy vx : SymV) :
    WFSymVal M (symSaturate .SubtractInteger [vy, vx]).val := by
  change WFSymVal M (.fo (V.int (Op.sub (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))))
  simp [WFSymVal, WFDyn, WFV, V.int, Op.sub]

private theorem mul_sat_wf (M : Model) (vy vx : SymV) :
    WFSymVal M (symSaturate .MultiplyInteger [vy, vx]).val := by
  change WFSymVal M (.fo (V.int (Op.mul (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))))
  simp [WFSymVal, WFDyn, WFV, V.int, Op.mul]

private theorem eq_sat_wf (M : Model) (vy vx : SymV) :
    WFSymVal M (symSaturate .EqualsInteger [vy, vx]).val := by
  change WFSymVal M (.fo (V.bool (SExpr.sEq (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))))
  simp [WFSymVal, WFDyn, WFV, V.bool]

private theorem lt_sat_wf (M : Model) (vy vx : SymV) :
    WFSymVal M (symSaturate .LessThanInteger [vy, vx]).val := by
  change WFSymVal M (.fo (V.bool (Op.lt (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))))
  simp [WFSymVal, WFDyn, WFV, V.bool, Op.lt]

private theorem le_sat_wf (M : Model) (vy vx : SymV) :
    WFSymVal M (symSaturate .LessThanEqualsInteger [vy, vx]).val := by
  change WFSymVal M (.fo (V.bool (Op.le (V.sAsInt (reifyFO vx).2) (V.sAsInt (reifyFO vy).2))))
  simp [WFSymVal, WFDyn, WFV, V.bool, Op.le]

private theorem iData_sat_wf (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .IData [v]).val := by
  change WFSymVal M (.fo (V.data (D.i (V.sAsInt (reifyFO v).2))))
  simp [WFSymVal, WFDyn, WFV, WFD, V.data, D.i]

private theorem bData_sat_wf (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .BData [v]).val := by
  change WFSymVal M (.fo (V.data (D.b (V.sAsBS (reifyFO v).2))))
  have hwfv := reifyFO_val_wf M v hwf
  cases hv : (evalDyn M (reifyFO v).2).toV <;>
    simp [WFSymVal, WFDyn, WFV, WFD, WFSeq, V.data, D.b, evalDyn_sAsBS,
      hv, SemV.getSeq] at hwfv ⊢ <;>
    first | exact hwfv | trivial

private theorem mkNilData_sat_wf (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .MkNilData [v]).val := by
  change WFSymVal M (.fo (V.dlist DL.nil))
  simp [WFSymVal, WFDyn, WFV, WFDL, V.dlist, DL.nil]

private theorem mkNilPairData_sat_wf (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .MkNilPairData [v]).val := by
  change WFSymVal M (.fo (V.pdlist DM.nil))
  simp [WFSymVal, WFDyn, WFV, WFDM, V.pdlist, DM.nil]

private theorem junk_sat_wf (M : Model) : WFSymVal M junk := by
  simp [junk, WFSymVal, WFDyn, WFV, V.unit]

private theorem errR_sat_wf (M : Model) : WFSymVal M errR.val := by
  simpa [errR] using junk_sat_wf M

private theorem errR'_sat_wf (M : Model) : WFSymVal M errR'.val := by
  simpa [errR'] using junk_sat_wf M

private theorem default_SemD : (default : SemD) = .i 0 := rfl

private theorem WFV_getData (sv : SemV) (h : WFV sv) : WFD sv.getData := by
  cases sv <;> simp [SemV.getData, WFV, WFD, WFDL, default_SemD] at h ⊢ <;>
    first | exact h | trivial

private theorem WFV_getDList (sv : SemV) (h : WFV sv) : WFDL sv.getDList := by
  cases sv <;> simp [SemV.getDList, WFV, WFDL] at h ⊢ <;>
    first | exact h | trivial

private theorem WFV_getList (sv : SemV) (h : WFV sv) :
    WFVL sv.getList ∧ ConstSemVL sv.getList := by
  cases sv <;> simp [SemV.getList, WFV, WFVL, ConstSemVL] at h ⊢ <;>
    first | exact h | constructor <;> trivial

private theorem WFDL_hd (dl : SemDL) (h : WFDL dl) : WFD dl.hd := by
  cases dl with
  | nil => simp [SemDL.hd, WFD, WFDL, default_SemD]
  | cons hd tl =>
      simpa [SemDL.hd, WFDL] using h.1

private theorem WFDL_tl (dl : SemDL) (h : WFDL dl) : WFDL dl.tl := by
  cases dl with
  | nil => simp [SemDL.tl, WFDL]
  | cons hd tl =>
      simpa [SemDL.tl, WFDL] using h.2

private theorem WFVL_hd (vl : SemVL) (h : WFVL vl) : WFV vl.hd := by
  cases vl with
  | nil => simp [SemVL.hd, WFV, default_SemV]
  | cons hd tl =>
      simpa [SemVL.hd, WFVL] using h.1

private theorem WFVL_tl (vl : SemVL) (h : WFVL vl) : WFVL vl.tl := by
  cases vl with
  | nil => simp [SemVL.tl, WFVL]
  | cons hd tl =>
      simpa [SemVL.tl, WFVL] using h.2

private theorem ConstSemVL_tl (vl : SemVL) (h : ConstSemVL vl) : ConstSemVL vl.tl := by
  cases vl with
  | nil => simp [SemVL.tl, ConstSemVL]
  | cons hd tl =>
      simpa [SemVL.tl, ConstSemVL] using h.2

private theorem WFV_pFst (sv : SemV) (h : WFV sv) : WFV sv.pFst := by
  cases sv <;> simp [SemV.pFst, WFV, default_SemV] at h ⊢ <;>
    first | exact h.1 | trivial

private theorem WFV_pSnd (sv : SemV) (h : WFV sv) : WFV sv.pSnd := by
  cases sv <;> simp [SemV.pSnd, WFV, default_SemV] at h ⊢ <;>
    first | exact h.2.1 | trivial

private theorem WFV_pdFst (sv : SemV) (h : WFV sv) : WFD sv.pdFst := by
  cases sv <;> simp [SemV.pdFst, WFV, WFD, WFDL, default_SemD] at h ⊢ <;>
    first | exact h.1 | trivial

private theorem WFV_pdSnd (sv : SemV) (h : WFV sv) : WFD sv.pdSnd := by
  cases sv <;> simp [SemV.pdSnd, WFV, WFD, WFDL, default_SemD] at h ⊢ <;>
    first | exact h.2 | trivial

private theorem wf_data_sAsData (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.data (V.sAsData e))) := by
  simpa [WFSymVal, WFDyn, WFV, V.data, evalDyn_sAsData]
    using WFV_getData (evalDyn M e).toV hwfv

private theorem wf_dlist_sAsDL (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.dlist (V.sAsDL e))) := by
  simpa [WFSymVal, WFDyn, WFV, V.dlist, evalDyn_sAsDL]
    using WFV_getDList (evalDyn M e).toV hwfv

private theorem wf_list_sAsList (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.list (V.sAsList e))) := by
  simpa [WFSymVal, WFDyn, WFV, V.list, evalDyn_sAsList]
    using WFV_getList (evalDyn M e).toV hwfv

private theorem wf_data_dlist_hd (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.data (DL.sHd (V.sAsDL e)))) := by
  have hdl := WFV_getDList (evalDyn M e).toV hwfv
  exact by
    simpa [WFSymVal, WFDyn, WFV, V.data, evalDyn_sAsDL]
      using WFDL_hd (evalDyn M e).toV.getDList hdl

private theorem wf_dlist_dlist_tl (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.dlist (DL.sTl (V.sAsDL e)))) := by
  have hdl := WFV_getDList (evalDyn M e).toV hwfv
  exact by
    simpa [WFSymVal, WFDyn, WFV, V.dlist, evalDyn_sAsDL]
      using WFDL_tl (evalDyn M e).toV.getDList hdl

private theorem wf_list_hd (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (VL.sHd (V.sAsList e))) := by
  have hvl := WFV_getList (evalDyn M e).toV hwfv
  exact by
    simpa [WFSymVal, WFDyn, evalDyn_sAsList]
      using WFVL_hd (evalDyn M e).toV.getList hvl.1

private theorem wf_list_tl (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.list (VL.sTl (V.sAsList e)))) := by
  have hvl := WFV_getList (evalDyn M e).toV hwfv
  have hwft := WFVL_tl (evalDyn M e).toV.getList hvl.1
  have hcst := ConstSemVL_tl (evalDyn M e).toV.getList hvl.2
  simp [WFSymVal, WFDyn, WFV, V.list, evalDyn_sAsList, hwft, hcst]

private theorem wf_pair_fst (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.sFst e)) := by
  simpa [WFSymVal, WFDyn, evalDyn_sFst]
    using WFV_pFst (evalDyn M e).toV hwfv

private theorem wf_pair_snd (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.sSnd e)) := by
  simpa [WFSymVal, WFDyn, evalDyn_sSnd]
    using WFV_pSnd (evalDyn M e).toV hwfv

private theorem wf_pairD_fst (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.data (V.sFstD e))) := by
  simpa [WFSymVal, WFDyn, WFV, V.data, evalDyn_sFstD]
    using WFV_pdFst (evalDyn M e).toV hwfv

private theorem wf_pairD_snd (M : Model) (e : SExpr)
    (hwfv : WFV (evalDyn M e).toV) :
    WFSymVal M (.fo (V.data (V.sSndD e))) := by
  simpa [WFSymVal, WFDyn, WFV, V.data, evalDyn_sSndD]
    using WFV_pdSnd (evalDyn M e).toV hwfv

private theorem fstPair_sat_wf (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .FstPair [v]).val := by
  let e := (reifyFO v).2
  change WFSymVal M
    (symMerge (V.sIsCon "VPairD" e) (okFO (V.data (V.sFstD e)))
      (symMerge (V.sIsCon "VPair" e) (okFO (V.sFst e)) errR)).val
  have hwfv : WFV (evalDyn M e).toV := by simpa [e] using reifyFO_val_wf M v hwf
  have hpd : WFSymVal M (okFO (V.data (V.sFstD e))).val := by
    simpa [okFO] using wf_pairD_fst M e hwfv
  have hp : WFSymVal M (okFO (V.sFst e)).val := by
    simpa [okFO] using wf_pair_fst M e hwfv
  have hi : WFSymVal M (symMerge (V.sIsCon "VPair" e) (okFO (V.sFst e)) errR).val :=
    WFSymVal_symMerge M (V.sIsCon "VPair" e) _ _ (by
      by_cases hc : (evalDyn M (V.sIsCon "VPair" e)).toBool <;>
        simp [hc, hp, errR_sat_wf M])
  exact WFSymVal_symMerge M (V.sIsCon "VPairD" e) _ _ (by
    by_cases hc : (evalDyn M (V.sIsCon "VPairD" e)).toBool <;>
      simp [hc, hpd, hi])

private theorem sndPair_sat_wf (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .SndPair [v]).val := by
  let e := (reifyFO v).2
  change WFSymVal M
    (symMerge (V.sIsCon "VPairD" e) (okFO (V.data (V.sSndD e)))
      (symMerge (V.sIsCon "VPair" e) (okFO (V.sSnd e)) errR)).val
  have hwfv : WFV (evalDyn M e).toV := by simpa [e] using reifyFO_val_wf M v hwf
  have hpd : WFSymVal M (okFO (V.data (V.sSndD e))).val := by
    simpa [okFO] using wf_pairD_snd M e hwfv
  have hp : WFSymVal M (okFO (V.sSnd e)).val := by
    simpa [okFO] using wf_pair_snd M e hwfv
  have hi : WFSymVal M (symMerge (V.sIsCon "VPair" e) (okFO (V.sSnd e)) errR).val :=
    WFSymVal_symMerge M (V.sIsCon "VPair" e) _ _ (by
      by_cases hc : (evalDyn M (V.sIsCon "VPair" e)).toBool <;>
        simp [hc, hp, errR_sat_wf M])
  exact WFSymVal_symMerge M (V.sIsCon "VPairD" e) _ _ (by
    by_cases hc : (evalDyn M (V.sIsCon "VPairD" e)).toBool <;>
      simp [hc, hpd, hi])

private theorem headList_sat_wf (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .HeadList [v]).val := by
  let e := (reifyFO v).2
  change WFSymVal M
    (onList e
      (fun dl => foGuard (DL.sIsNil dl) (V.data (DL.sHd dl)))
      (fun vl => foGuard (VL.sIsNil vl) (VL.sHd vl))).val
  unfold onList
  have hwfv : WFV (evalDyn M e).toV := by simpa [e] using reifyFO_val_wf M v hwf
  have hd : WFSymVal M (foGuard (DL.sIsNil (V.sAsDL e)) (V.data (DL.sHd (V.sAsDL e)))).val := by
    simpa [foGuard] using wf_data_dlist_hd M e hwfv
  have hv : WFSymVal M (foGuard (VL.sIsNil (V.sAsList e)) (VL.sHd (V.sAsList e))).val := by
    simpa [foGuard] using wf_list_hd M e hwfv
  have hi : WFSymVal M
      (symMerge (V.sIsCon "VList" e)
        (foGuard (VL.sIsNil (V.sAsList e)) (VL.sHd (V.sAsList e))) errR').val :=
    WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ (by
      by_cases hc : (evalDyn M (V.sIsCon "VList" e)).toBool <;>
        simp [hc, hv, errR'_sat_wf M])
  exact WFSymVal_symMerge M (V.sIsCon "VDList" e) _ _ (by
    by_cases hc : (evalDyn M (V.sIsCon "VDList" e)).toBool <;>
      simp [hc, hd, hi])

private theorem tailList_sat_wf (M : Model) (v : SymV) (hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .TailList [v]).val := by
  let e := (reifyFO v).2
  change WFSymVal M
    (onList e
      (fun dl => foGuard (DL.sIsNil dl) (V.dlist (DL.sTl dl)))
      (fun vl => foGuard (VL.sIsNil vl) (V.list (VL.sTl vl)))).val
  unfold onList
  have hwfv : WFV (evalDyn M e).toV := by simpa [e] using reifyFO_val_wf M v hwf
  have hd : WFSymVal M (foGuard (DL.sIsNil (V.sAsDL e)) (V.dlist (DL.sTl (V.sAsDL e)))).val := by
    simpa [foGuard] using wf_dlist_dlist_tl M e hwfv
  have hv : WFSymVal M (foGuard (VL.sIsNil (V.sAsList e)) (V.list (VL.sTl (V.sAsList e)))).val := by
    simpa [foGuard] using wf_list_tl M e hwfv
  have hi : WFSymVal M
      (symMerge (V.sIsCon "VList" e)
        (foGuard (VL.sIsNil (V.sAsList e)) (V.list (VL.sTl (V.sAsList e)))) errR').val :=
    WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ (by
      by_cases hc : (evalDyn M (V.sIsCon "VList" e)).toBool <;>
        simp [hc, hv, errR'_sat_wf M])
  exact WFSymVal_symMerge M (V.sIsCon "VDList" e) _ _ (by
    by_cases hc : (evalDyn M (V.sIsCon "VDList" e)).toBool <;>
      simp [hc, hd, hi])

private theorem nullList_sat_wf (M : Model) (v : SymV) (_hwf : WFSymVal M v) :
    WFSymVal M (symSaturate .NullList [v]).val := by
  let e := (reifyFO v).2
  change WFSymVal M
    (onList e
      (fun dl => okFO (V.bool (DL.sIsNil dl)))
      (fun vl => okFO (V.bool (VL.sIsNil vl)))).val
  unfold onList
  have hd : WFSymVal M (okFO (V.bool (DL.sIsNil (V.sAsDL e)))).val := by
    simp [okFO, WFSymVal, WFDyn, WFV, V.bool]
  have hv : WFSymVal M (okFO (V.bool (VL.sIsNil (V.sAsList e)))).val := by
    simp [okFO, WFSymVal, WFDyn, WFV, V.bool]
  have hi : WFSymVal M
      (symMerge (V.sIsCon "VList" e)
        (okFO (V.bool (VL.sIsNil (V.sAsList e)))) errR').val :=
    WFSymVal_symMerge M (V.sIsCon "VList" e) _ _ (by
      by_cases hc : (evalDyn M (V.sIsCon "VList" e)).toBool <;>
        simp [hc, hv, errR'_sat_wf M])
  exact WFSymVal_symMerge M (V.sIsCon "VDList" e) _ _ (by
    by_cases hc : (evalDyn M (V.sIsCon "VDList" e)).toBool <;>
      simp [hc, hd, hi])

private theorem wf_dlist_cons (M : Model) (hE tE : SExpr)
    (hwfh : WFV (evalDyn M hE).toV) (hwft : WFV (evalDyn M tE).toV) :
    WFSymVal M (.fo (V.dlist (DL.cons (V.sAsData hE) (V.sAsDL tE)))) := by
  have hhd := WFV_getData (evalDyn M hE).toV hwfh
  have htd := WFV_getDList (evalDyn M tE).toV hwft
  simp [WFSymVal, WFDyn, WFV, WFDL, V.dlist, evalDyn_sAsData, evalDyn_sAsDL,
    DL.cons, hhd, htd]

private theorem wf_list_cons (M : Model) (hE tE : SExpr)
    (hwfh : WFV (evalDyn M hE).toV) (hwft : WFV (evalDyn M tE).toV)
    (hcsh : ConstSemV (evalDyn M hE).toV) :
    WFSymVal M (.fo (V.list (VL.cons hE (V.sAsList tE)))) := by
  have htl := WFV_getList (evalDyn M tE).toV hwft
  simp [WFSymVal, WFDyn, WFV, WFVL, ConstSemVL, V.list, evalDyn_sAsList,
    VL.cons, hwfh, hcsh, htl.1, htl.2]

private theorem mkCons_two_sat_wf (M : Model) (tail head : SymV)
    (hwft : WFSymVal M tail) (hwfh : WFSymVal M head)
    (_hinc : denoteInc M (symSaturate .MkCons [tail, head]) = false)
    (herr : denoteErr M (symSaturate .MkCons [tail, head]) = false) :
    WFSymVal M (symSaturate .MkCons [tail, head]).val := by
  let hE := (reifyFO head).2
  let tE := (reifyFO tail).2
  change WFSymVal M
    (symMerge (V.sIsCon "VDList" tE)
      (foGuard (gData hE) (V.dlist (DL.cons (V.sAsData hE) (V.sAsDL tE))))
      (symMerge (V.sIsCon "VList" tE)
        (foGuard (V.sIsCon "VConstr" hE) (V.list (VL.cons hE (V.sAsList tE)))) errR)).val
  have hwfH : WFV (evalDyn M hE).toV := by simpa [hE] using reifyFO_val_wf M head hwfh
  have hwfT : WFV (evalDyn M tE).toV := by simpa [tE] using reifyFO_val_wf M tail hwft
  have hd : WFSymVal M
      (foGuard (gData hE) (V.dlist (DL.cons (V.sAsData hE) (V.sAsDL tE)))).val := by
    simpa [foGuard] using wf_dlist_cons M hE tE hwfH hwfT
  have hi : WFSymVal M
      (symMerge (V.sIsCon "VList" tE)
        (foGuard (V.sIsCon "VConstr" hE) (V.list (VL.cons hE (V.sAsList tE)))) errR).val := by
    refine WFSymVal_symMerge M (V.sIsCon "VList" tE) _ _ ?_
    by_cases hlist : (evalDyn M (V.sIsCon "VList" tE)).toBool
    · have htailName : (evalDyn M tE).toV.conName = "VList" := by
        simpa [sIsCon_VList, beq_iff_eq] using hlist
      have hnotConName : (evalDyn M hE).toV.conName ≠ "VConstr" := by
        have herr' := herr
        unfold denoteErr symSaturate at herr'
        dsimp only at herr'
        rw [evalDyn_sOr, Bool.or_eq_false_iff] at herr'
        have hm := herr'.2
        simpa [symBuiltin_mkCons_two_eq, evalErr_symMerge, hE, tE, htailName, foGuard] using hm
      have hcs := constSem_of_wfv_not_constr _ hwfH hnotConName
      have hv : WFSymVal M
          (foGuard (V.sIsCon "VConstr" hE) (V.list (VL.cons hE (V.sAsList tE)))).val := by
        simpa [foGuard] using wf_list_cons M hE tE hwfH hwfT hcs
      simp [hlist, hv]
    · simp [hlist, errR_sat_wf M]
  exact WFSymVal_symMerge M (V.sIsCon "VDList" tE) _ _ (by
    by_cases hc : (evalDyn M (V.sIsCon "VDList" tE)).toBool <;>
      simp [hc, hd, hi])

private theorem satWf_binInt (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : preciseBinIntBuiltin b)
    (hwfval : ∀ vy vx, WFSymVal M (symSaturate b [vy, vx]).val) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    denoteErr M (symSaturate b args) = false → WFSymVal M (symSaturate b args).val := by
  intro _ hinc _
  cases args with
  | nil =>
      exfalso
      have ht := binInt_inc_true_len_ne_two M b [] hb (by simp)
      rw [ht] at hinc
      contradiction
  | cons vy rest =>
      cases rest with
      | nil =>
          exfalso
          have ht := binInt_inc_true_len_ne_two M b [vy] hb (by simp)
          rw [ht] at hinc
          contradiction
      | cons vx rest2 =>
          cases rest2 with
          | nil => exact hwfval vy vx
          | cons z zs =>
              exfalso
              have ht := binInt_inc_true_len_ne_two M b (vy :: vx :: z :: zs) hb (by simp)
              rw [ht] at hinc
              contradiction

private theorem satWf_unary (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : preciseUnaryBuiltin b)
    (hwfval : ∀ v, WFSymVal M v → WFSymVal M (symSaturate b [v]).val) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    denoteErr M (symSaturate b args) = false → WFSymVal M (symSaturate b args).val := by
  intro hwf hinc _
  cases args with
  | nil =>
      exfalso
      have ht := unary_inc_true_len_ne_one M b [] hb (by simp)
      rw [ht] at hinc
      contradiction
  | cons v rest =>
      cases rest with
      | nil =>
          have hwfv : WFSymVal M v := by simpa [WFSymList] using hwf.1
          exact hwfval v hwfv
      | cons w ws =>
          exfalso
          have ht := unary_inc_true_len_ne_one M b (v :: w :: ws) hb (by simp)
          rw [ht] at hinc
          contradiction

private theorem satWf_mkCons (M : Model) (args : List SymV) :
    WFSymList M args → denoteInc M (symSaturate .MkCons args) = false →
    denoteErr M (symSaturate .MkCons args) = false → WFSymVal M (symSaturate .MkCons args).val := by
  intro hwf hinc herr
  cases args with
  | nil =>
      exfalso
      have ht := mkCons_inc_true_len_ne_two M [] (by simp)
      rw [ht] at hinc
      contradiction
  | cons tail rest =>
      cases rest with
      | nil =>
          exfalso
          have ht := mkCons_inc_true_len_ne_two M [tail] (by simp)
          rw [ht] at hinc
          contradiction
      | cons head rest2 =>
          cases rest2 with
          | nil =>
              have hwft : WFSymVal M tail := by simpa [WFSymList] using hwf.1
              have hwfh : WFSymVal M head := by simpa [WFSymList] using hwf.2.1
              exact mkCons_two_sat_wf M tail head hwft hwfh hinc herr
          | cons z zs =>
              exfalso
              have ht := mkCons_inc_true_len_ne_two M (tail :: head :: z :: zs) (by simp)
              rw [ht] at hinc
              contradiction

private theorem satWf_unsupported (M : Model) (b : BuiltinFun) (args : List SymV)
    (hb : smtUnsupportedBuiltin b) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    denoteErr M (symSaturate b args) = false → WFSymVal M (symSaturate b args).val := by
  intro _ _ herr
  rw [unsupported_err_true M b args hb] at herr
  contradiction

private theorem satWf_inc (M : Model) (b : BuiltinFun) (args : List SymV)
    (hbuiltin : ∀ xs, symBuiltin b xs = incR) :
    WFSymList M args → denoteInc M (symSaturate b args) = false →
    denoteErr M (symSaturate b args) = false → WFSymVal M (symSaturate b args).val := by
  intro _ hinc _
  exfalso
  rw [builtin_inc_true M b args hbuiltin] at hinc
  contradiction

theorem satAgrees (M : Model) : SatAgrees M := by
  intro b args hwf hinc
  by_cases hp : preciseBinIntBuiltin b
  · cases b <;> simp [preciseBinIntBuiltin] at hp
    all_goals
      first
      | exact satAgrees_binInt M .AddInteger args (by change True; trivial) (add_agrees M) hwf hinc
      | exact satAgrees_binInt M .SubtractInteger args (by change True; trivial) (sub_agrees M) hwf hinc
      | exact satAgrees_binInt M .MultiplyInteger args (by change True; trivial) (mul_agrees M) hwf hinc
      | exact satAgrees_binInt M .EqualsInteger args (by change True; trivial) (eq_agrees M) hwf hinc
      | exact satAgrees_binInt M .LessThanInteger args (by change True; trivial) (lt_agrees M) hwf hinc
      | exact satAgrees_binInt M .LessThanEqualsInteger args (by change True; trivial) (le_agrees M) hwf hinc
  · by_cases hu : smtUnsupportedBuiltin b
    · exact satAgrees_unsupported M b args hu hwf hinc
    · by_cases hpu : preciseUnaryBuiltin b
      · by_cases hb : b = .FstPair
        · subst b
          exact satAgrees_unary M .FstPair args (by change True; trivial) (fstPair_agrees M) hwf hinc
        · by_cases hb : b = .SndPair
          · subst b
            exact satAgrees_unary M .SndPair args (by change True; trivial) (sndPair_agrees M) hwf hinc
          · by_cases hb : b = .HeadList
            · subst b
              exact satAgrees_unary M .HeadList args (by change True; trivial) (headList_agrees M) hwf hinc
            · by_cases hb : b = .TailList
              · subst b
                exact satAgrees_unary M .TailList args (by change True; trivial) (tailList_agrees M) hwf hinc
              · by_cases hb : b = .NullList
                · subst b
                  exact satAgrees_unary M .NullList args (by change True; trivial)
                    (fun v _ => nullList_agrees M v) hwf hinc
                · by_cases hb : b = .IData
                  · subst b
                    exact satAgrees_unary M .IData args (by change True; trivial) (iData_agrees M) hwf hinc
                  · by_cases hb : b = .BData
                    · subst b
                      exact satAgrees_unary M .BData args (by change True; trivial) (bData_agrees M) hwf hinc
                    · by_cases hb : b = .MkNilData
                      · subst b
                        exact satAgrees_unary M .MkNilData args (by change True; trivial) (mkNilData_agrees M) hwf hinc
                      · by_cases hb : b = .MkNilPairData
                        · subst b
                          exact satAgrees_unary M .MkNilPairData args (by change True; trivial) (mkNilPairData_agrees M) hwf hinc
                        · cases b <;> simp [preciseUnaryBuiltin] at hpu
                          all_goals contradiction
      · by_cases hpm : preciseMkConsBuiltin b
        · cases b <;> simp [preciseMkConsBuiltin] at hpm
          exact satAgrees_mkCons M args hwf hinc
        · exact satAgrees_inc M b args
            (fun xs => symBuiltin_inc_of_not_precise_not_unsupported b xs hp hpu hpm hu) hwf hinc

theorem satWf (M : Model) : SatWf M := by
  intro b args hwf hinc herr
  by_cases hp : preciseBinIntBuiltin b
  · cases b <;> simp [preciseBinIntBuiltin] at hp
    all_goals
      first
      | exact satWf_binInt M .AddInteger args (by change True; trivial) (add_sat_wf M) hwf hinc herr
      | exact satWf_binInt M .SubtractInteger args (by change True; trivial) (sub_sat_wf M) hwf hinc herr
      | exact satWf_binInt M .MultiplyInteger args (by change True; trivial) (mul_sat_wf M) hwf hinc herr
      | exact satWf_binInt M .EqualsInteger args (by change True; trivial) (eq_sat_wf M) hwf hinc herr
      | exact satWf_binInt M .LessThanInteger args (by change True; trivial) (lt_sat_wf M) hwf hinc herr
      | exact satWf_binInt M .LessThanEqualsInteger args (by change True; trivial) (le_sat_wf M) hwf hinc herr
  · by_cases hu : smtUnsupportedBuiltin b
    · exact satWf_unsupported M b args hu hwf hinc herr
    · by_cases hpu : preciseUnaryBuiltin b
      · by_cases hb : b = .FstPair
        · subst b
          exact satWf_unary M .FstPair args (by change True; trivial) (fstPair_sat_wf M) hwf hinc herr
        · by_cases hb : b = .SndPair
          · subst b
            exact satWf_unary M .SndPair args (by change True; trivial) (sndPair_sat_wf M) hwf hinc herr
          · by_cases hb : b = .HeadList
            · subst b
              exact satWf_unary M .HeadList args (by change True; trivial) (headList_sat_wf M) hwf hinc herr
            · by_cases hb : b = .TailList
              · subst b
                exact satWf_unary M .TailList args (by change True; trivial) (tailList_sat_wf M) hwf hinc herr
              · by_cases hb : b = .NullList
                · subst b
                  exact satWf_unary M .NullList args (by change True; trivial) (nullList_sat_wf M) hwf hinc herr
                · by_cases hb : b = .IData
                  · subst b
                    exact satWf_unary M .IData args (by change True; trivial) (iData_sat_wf M) hwf hinc herr
                  · by_cases hb : b = .BData
                    · subst b
                      exact satWf_unary M .BData args (by change True; trivial) (bData_sat_wf M) hwf hinc herr
                    · by_cases hb : b = .MkNilData
                      · subst b
                        exact satWf_unary M .MkNilData args (by change True; trivial) (mkNilData_sat_wf M) hwf hinc herr
                      · by_cases hb : b = .MkNilPairData
                        · subst b
                          exact satWf_unary M .MkNilPairData args (by change True; trivial) (mkNilPairData_sat_wf M) hwf hinc herr
                        · cases b <;> simp [preciseUnaryBuiltin] at hpu
                          all_goals contradiction
      · by_cases hpm : preciseMkConsBuiltin b
        · cases b <;> simp [preciseMkConsBuiltin] at hpm
          exact satWf_mkCons M args hwf hinc herr
        · exact satWf_inc M b args
            (fun xs => symBuiltin_inc_of_not_precise_not_unsupported b xs hp hpu hpm hu) hwf hinc herr

/-! ## The three Stage-2 lemmas (consumed by `Soundness.lean`) -/

theorem sim_value (M : Model) (f : Nat) (ρ : SymEnv) (t : Term)
    (hwf : WFSymEnv M ρ) (hinc : denoteInc M (symEval f ρ t) = false)
    (herr : denoteErr M (symEval f ρ t) = false) :
    bigEval f (denoteEnv M ρ) t = some (denoteSymV M (symEval f ρ t).val) := by
  have h := (EvalSim M (satAgrees M) (satWf M) f ρ t hwf hinc).1 0
  simp only [Nat.add_zero, SymOut, herr] at h
  simpa using h

theorem sim_error (M : Model) (f : Nat) (ρ : SymEnv) (t : Term)
    (hwf : WFSymEnv M ρ) (hinc : denoteInc M (symEval f ρ t) = false)
    (herr : denoteErr M (symEval f ρ t) = true) :
    bigEval f (denoteEnv M ρ) t = none := by
  have h := (EvalSim M (satAgrees M) (satWf M) f ρ t hwf hinc).1 0
  simp only [Nat.add_zero, SymOut, herr] at h
  simpa using h

theorem error_stable (M : Model) (f : Nat) (ρ : SymEnv) (t : Term)
    (hwf : WFSymEnv M ρ) (hinc : denoteInc M (symEval f ρ t) = false)
    (herr : denoteErr M (symEval f ρ t) = true) :
    ∀ f', bigEval f' (denoteEnv M ρ) t = none := by
  have hf : bigEval f (denoteEnv M ρ) t = none := by
    have h := (EvalSim M (satAgrees M) (satWf M) f ρ t hwf hinc).1 0
    simp only [Nat.add_zero, SymOut, herr] at h; simpa using h
  intro f'
  rcases Nat.le_total f f' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.le.dest hle
    have h := (EvalSim M (satAgrees M) (satWf M) f ρ t hwf hinc).1 k
    simp only [SymOut, herr] at h; simpa using h
  · rcases hb : bigEval f' (denoteEnv M ρ) t with _ | v
    · rfl
    · have := Moist.Verified.BigStep.bigEval_mono_le hle hb
      rw [this] at hf; exact Option.noConfusion hf

end Moist.Verified.Smt
