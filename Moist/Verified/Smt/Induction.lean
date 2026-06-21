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
  | .ConstList cs => by simp only [constToSExpr, V.list, evalDyn_app, evalDynList, ea_VList, toV_v, WFV]; exact wf_constListToVL M cs
  | .ConstArray cs => by simp only [constToSExpr, V.arr, evalDyn_app, evalDynList, ea_VArr, toV_v, WFV]; exact wf_constListToVL M cs
  | .Pair (a, b) => by simp only [constToSExpr, V.pair, evalDyn_app, evalDynList, ea_VPair, toV_v, WFV]; exact ⟨wf_const_v M a, wf_const_v M b⟩
  | .PairData (a, b) => by simp only [constToSExpr, V.pairD, evalDyn_app, evalDynList, ea_VPairD, toV_v, WFV]; exact ⟨wf_dataToSExpr M a, wf_dataToSExpr M b⟩
theorem wf_constListToVL (M : Model) : ∀ (cs : List Const), WFVL (evalDyn M (constListToVL cs)).toVL
  | [] => by simp [constListToVL, VL.nil, WFVL]
  | c :: cs => by
      simp only [constListToVL, VL.cons, evalDyn_app, evalDynList, ea_vcons, toVL_vl, WFVL]
      exact ⟨wf_const_v M c, wf_constListToVL M cs⟩
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

/-- The `Constr` shape: `SymOut` of the list-folded result is the mapped `SymOutList`. -/
theorem symOut_constr (M : Model) (tag : Nat) (rs : List SymR) :
    SymOut M ⟨sOrs (rs.map SymR.inc), sOrs (rs.map SymR.err), .constr tag (rs.map SymR.val)⟩
      = (SymOutList M rs).map (fun vs => CekValue.VConstr tag vs) := by
  simp only [SymOut, SymOutList, denoteErr, denoteVal, denoteSymV, denoteErr_sOrs_map]
  by_cases h : rs.any (fun r => (evalDyn M r.err).toBool) = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h, denoteSymList_eq_map, List.map_map, Function.comp_def, denoteVal]

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
      have hincs : (evalDyn M (sOrs [(symEval n ρ f').inc, (symEval n ρ a).inc,
          (symApply n (symEval n ρ f').val (symEval n ρ a).val).inc])).toBool = false := by
        simpa only [symEval, denoteInc] using hinc
      have hf_inc : denoteInc M (symEval n ρ f') = false := sOrs_false M hincs _ (by simp)
      have ha_inc : denoteInc M (symEval n ρ a) = false := sOrs_false M hincs _ (by simp)
      have hap_inc : denoteInc M (symApply n (symEval n ρ f').val (symEval n ρ a).val) = false :=
        sOrs_false M hincs _ (by simp)
      obtain ⟨IHf1, IHf2⟩ := EvalSim n ρ f' hwf hf_inc
      obtain ⟨IHa1, IHa2⟩ := EvalSim n ρ a hwf ha_inc
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval, symEval]
        rw [symOut_seq3, IHf1 k]
        cases hfe : denoteErr M (symEval n ρ f') with
        | true => simp [SymOut, hfe]
        | false =>
            simp only [SymOut, hfe, Bool.false_eq_true, if_false, denoteVal, Option.some_bind]
            rw [IHa1 k]
            cases hae : denoteErr M (symEval n ρ a) with
            | true => simp [SymOut, hae]
            | false =>
                simp only [SymOut, hae, Bool.false_eq_true, if_false, denoteVal, Option.some_bind]
                obtain ⟨IHap1, _⟩ := ApplySim n (symEval n ρ f').val (symEval n ρ a).val
                  (IHf2 hfe) (IHa2 hae) hap_inc
                exact IHap1 k
      · have herrs : (evalDyn M (sOrs [(symEval n ρ f').err, (symEval n ρ a).err,
            (symApply n (symEval n ρ f').val (symEval n ρ a).val).err])).toBool = false := by
          simpa only [symEval, denoteErr] using herr
        have hrf : denoteErr M (symEval n ρ f') = false := sOrs_false M herrs _ (by simp)
        have hra : denoteErr M (symEval n ρ a) = false := sOrs_false M herrs _ (by simp)
        have hrap : denoteErr M (symApply n (symEval n ρ f').val (symEval n ρ a).val) = false :=
          sOrs_false M herrs _ (by simp)
        obtain ⟨_, IHap2⟩ := ApplySim n (symEval n ρ f').val (symEval n ρ a).val
          (IHf2 hrf) (IHa2 hra) hap_inc
        simpa only [symEval] using IHap2 hrap
  | n+1, ρ, .Force e, hwf, hinc => by
      have hinc' : (evalDyn M (SExpr.sOr (symEval n ρ e).inc
          (symForce n (symEval n ρ e).val).inc)).toBool = false := by
        simpa only [symEval, denoteInc] using hinc
      rw [evalDyn_sOr, Bool.or_eq_false_iff] at hinc'
      obtain ⟨IHt1, IHt2⟩ := EvalSim n ρ e hwf hinc'.1
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval, symEval]
        rw [symOut_seq2, IHt1 k]
        cases hte : denoteErr M (symEval n ρ e) with
        | true => simp [SymOut, hte]
        | false =>
            simp only [SymOut, hte, Bool.false_eq_true, if_false, denoteVal, Option.some_bind]
            obtain ⟨IHfo1, _⟩ := ForceSim n (symEval n ρ e).val (IHt2 hte) hinc'.2
            exact IHfo1 k
      · have herrs : (evalDyn M (SExpr.sOr (symEval n ρ e).err
            (symForce n (symEval n ρ e).val).err)).toBool = false := by
          simpa only [symEval, denoteErr] using herr
        rw [evalDyn_sOr, Bool.or_eq_false_iff] at herrs
        obtain ⟨_, IHfo2⟩ := ForceSim n (symEval n ρ e).val (IHt2 herrs.1) hinc'.2
        simpa only [symEval] using IHfo2 herrs.2
  | n+1, ρ, .Constr tag ms, hwf, hinc => by
      have hincs : (evalDyn M (sOrs ((symEvalList n ρ ms).map SymR.inc))).toBool = false := by
        simpa only [symEval, denoteInc] using hinc
      obtain ⟨IHL1, IHL2⟩ := EvalListSim n ρ ms hwf hincs
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add]
        simp only [bigEval, symEval]
        rw [symOut_constr, IHL1 k]
        cases hL : SymOutList M (symEvalList n ρ ms) <;> simp
      · have herr' : denoteErr M ⟨SExpr.bool false,
            sOrs ((symEvalList n ρ ms).map SymR.err), junk⟩ = false := by
          simpa only [symEval, denoteErr] using herr
        have hmem := IHL2 herr'
        simp only [symEval, WFSymVal]
        apply wfSymList_of_mem M
        intro v hv
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
        exact hmem r hr
  | n+1, ρ, .Case scrut alts, hwf, hinc => by
      have hinc' : (evalDyn M (SExpr.sOr (symEval n ρ scrut).inc
          (symCase n ρ alts (symEval n ρ scrut).val).inc)).toBool = false := by
        simpa only [symEval, denoteInc] using hinc
      rw [evalDyn_sOr, Bool.or_eq_false_iff] at hinc'
      obtain ⟨IHs1, IHs2⟩ := EvalSim n ρ scrut hwf hinc'.1
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · rw [Nat.succ_add, bigEval_case, IHs1 k]
        simp only [symEval]
        rw [symOut_seq2]
        cases hse : denoteErr M (symEval n ρ scrut) with
        | true => simp [SymOut, hse]
        | false =>
            simp only [SymOut, hse, Bool.false_eq_true, if_false, denoteVal, Option.some_bind]
            obtain ⟨IHc1, _⟩ := CaseSim n ρ alts (symEval n ρ scrut).val hwf (IHs2 hse) hinc'.2
            exact IHc1 k
      · have herrs : (evalDyn M (SExpr.sOr (symEval n ρ scrut).err
            (symCase n ρ alts (symEval n ρ scrut).val).err)).toBool = false := by
          simpa only [symEval, denoteErr] using herr
        rw [evalDyn_sOr, Bool.or_eq_false_iff] at herrs
        obtain ⟨_, IHc2⟩ := CaseSim n ρ alts (symEval n ρ scrut).val hwf (IHs2 herrs.1) hinc'.2
        simpa only [symEval] using IHc2 herrs.2
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
          have hinc' : (evalDyn M (SExpr.sOr (symEval m ρ alt).inc
              (symApplyList m (symEval m ρ alt).val fields).inc)).toBool = false := by
            simpa only [symCase, hat, denoteInc] using hinc
          rw [evalDyn_sOr, Bool.or_eq_false_iff] at hinc'
          obtain ⟨IHe1, IHe2⟩ := EvalSim m ρ alt hwfenv hinc'.1
          have hfields : ∀ v ∈ fields, WFSymVal M v := wfSymList_mem M hwfsv
          refine ⟨fun k => ?_, fun herr => ?_⟩
          · simp only [symCase, hat, denoteSymV, caseDispatch]
            have hfk : (m+1)+k = m+(k+1) := by omega
            rw [hfk, IHe1 (k+1), symOut_seq2]
            cases hre : denoteErr M (symEval m ρ alt) with
            | true => simp [SymOut, hre]
            | false =>
                simp only [SymOut, hre, Bool.false_eq_true, if_false, denoteVal, Option.some_bind]
                obtain ⟨IHr1, _⟩ := ApplyListSim m (symEval m ρ alt).val fields (IHe2 hre) hfields hinc'.2
                rw [denoteSymList_eq_map]; exact IHr1 (k+1)
          · have herrs : (evalDyn M (SExpr.sOr (symEval m ρ alt).err
                (symApplyList m (symEval m ρ alt).val fields).err)).toBool = false := by
              simpa only [symCase, hat, denoteErr] using herr
            rw [evalDyn_sOr, Bool.or_eq_false_iff] at herrs
            obtain ⟨_, IHr2⟩ := ApplyListSim m (symEval m ρ alt).val fields (IHe2 herrs.1) hfields hinc'.2
            simpa only [symCase, hat] using IHr2 herrs.2
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
  | m+1, ρ, alts, .fo e, hwfenv, hwfsv, hinc => by sorry
termination_by f _ _ _ => (f, 0)
theorem EvalListSim : ∀ (f : Nat) (ρ : SymEnv) (ts : List Term), WFSymEnv M ρ →
    denoteInc M ⟨sOrs ((symEvalList f ρ ts).map SymR.inc), .bool false, junk⟩ = false →
    (∀ k, bigEvalList (f + k) (denoteEnv M ρ) ts = SymOutList M (symEvalList f ρ ts)) ∧
    (denoteErr M ⟨.bool false, sOrs ((symEvalList f ρ ts).map SymR.err), junk⟩ = false →
      ∀ r ∈ symEvalList f ρ ts, WFSymVal M r.val)
  | _, _, [], _, _ => by
      refine ⟨fun k => ?_, fun _ r hr => ?_⟩
      · simp [symEvalList, bigEvalList, SymOutList]
      · simp [symEvalList] at hr
  | f, ρ, t :: ts, hwf, hinc => by
      have hinc' : (evalDyn M (SExpr.sOr (symEval f ρ t).inc
          (sOrs ((symEvalList f ρ ts).map SymR.inc)))).toBool = false := by
        simpa only [symEvalList, List.map_cons, denoteInc, sOrs] using hinc
      rw [evalDyn_sOr, Bool.or_eq_false_iff] at hinc'
      obtain ⟨IHt1, IHt2⟩ := EvalSim f ρ t hwf hinc'.1
      obtain ⟨IHr1, IHr2⟩ := EvalListSim f ρ ts hwf hinc'.2
      refine ⟨fun k => ?_, fun herr r hr => ?_⟩
      · simp only [symEvalList, bigEvalList]
        rw [IHt1 k, IHr1 k, SymOutList_cons]
        cases SymOut M (symEval f ρ t) with
        | none => rfl
        | some v =>
            simp only [Option.some_bind]
            cases SymOutList M (symEvalList f ρ ts) <;> rfl
      · have herr' : (evalDyn M (SExpr.sOr (symEval f ρ t).err
            (sOrs ((symEvalList f ρ ts).map SymR.err)))).toBool = false := by
          simpa only [symEvalList, List.map_cons, denoteErr, sOrs] using herr
        rw [evalDyn_sOr, Bool.or_eq_false_iff] at herr'
        simp only [symEvalList] at hr
        rcases List.mem_cons.1 hr with h | h
        · subst h; exact IHt2 herr'.1
        · exact IHr2 herr'.2 r h
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
      have hinc' : (evalDyn M (SExpr.sOr (symApply f vf a).inc
          (symApplyList f (symApply f vf a).val as).inc)).toBool = false := by
        simpa only [symApplyList, denoteInc] using hinc
      rw [evalDyn_sOr, Bool.or_eq_false_iff] at hinc'
      have hva : WFSymVal M a := hvs a (by simp)
      have hvas : ∀ v ∈ as, WFSymVal M v := fun v hv => hvs v (List.mem_cons_of_mem a hv)
      obtain ⟨IHa1, IHa2⟩ := ApplySim f vf a hvf hva hinc'.1
      refine ⟨fun k => ?_, fun herr => ?_⟩
      · simp only [List.map_cons, symApplyList, applyValList]
        rw [IHa1 k, symOut_seq2]
        cases hae : denoteErr M (symApply f vf a) with
        | true => simp [SymOut, hae]
        | false =>
            simp only [SymOut, hae, Bool.false_eq_true, if_false, denoteVal, Option.some_bind]
            obtain ⟨IHr1, _⟩ := ApplyListSim f (symApply f vf a).val as (IHa2 hae) hvas hinc'.2
            exact IHr1 k
      · have herrs : (evalDyn M (SExpr.sOr (symApply f vf a).err
            (symApplyList f (symApply f vf a).val as).err)).toBool = false := by
          simpa only [symApplyList, denoteErr] using herr
        rw [evalDyn_sOr, Bool.or_eq_false_iff] at herrs
        obtain ⟨_, IHr2⟩ := ApplyListSim f (symApply f vf a).val as (IHa2 herrs.1) hvas hinc'.2
        simpa only [symApplyList] using IHr2 herrs.2
termination_by f _ vs => (f, sizeOf vs)
end

end

/-! ## The builtin agreement lemmas (the "grind"; the six integer builtins are done,
the rest follow the same recipe — this is the remaining per-builtin work). -/

theorem satAgrees (M : Model) : SatAgrees M := by sorry
theorem satWf (M : Model) : SatWf M := by sorry

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
