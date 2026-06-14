import Moist.Verified.SmallStep.ValueDischarge

/-! # The builtin reflect-bridge

`Step` routes saturated builtins through the shared `evalBuiltin`, converting the
discharged value arguments back to `CekValue`s with `reflect`.  For the forward
simulation we must show this agrees with what the CEK computes directly.

The key fact is the **round-trip** `discharge (reflect (discharge v)) = discharge v`
(`discharge_reflect_discharge`): `reflect` is not a left inverse of `discharge`
(a closure forgets its environment), but discharging again recovers the same
term.  From it we derive that mapping `reflect ∘ discharge` over a builtin's
arguments leaves `evalBuiltin`'s result unchanged up to discharge
(`evalBuiltin_map_rdv`).
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term Const)
open Moist.CEK (CekValue ArgKind ExpectedArgs expectedArgs evalBuiltin evalBuiltinPassThrough
  evalBuiltinConst extractConsts evalBuiltinPassThrough_none_of_not_passthrough)

/-- `reflect ∘ discharge`: discharge a CEK value and parse the result back. -/
def rdv (v : CekValue) : CekValue := reflect (discharge v)

@[simp] theorem rdv_vcon (c : Const) : rdv (.VCon c) = .VCon c := by
  simp [rdv, discharge, reflect]

/-- Reflecting back a discharged value-list. -/
theorem reflectList_dischargeList (vs : List CekValue) :
    reflectList (dischargeList vs) = vs.map rdv := by
  rw [reflectList_eq_map, dischargeList_eq_map, List.map_map]; rfl

/-- Reflecting back a discharged builtin spine reconstructs the `VBuiltin`, with
    each stored argument run through `rdv`. -/
theorem reflect_discharge_vbuiltin {b vargs ea} (h : VBSpine b vargs ea) :
    reflect (discharge (.VBuiltin b vargs ea)) = .VBuiltin b (vargs.map rdv) ea := by
  induction h with
  | base =>
    simp only [discharge, dischargeList, consumedSteps_self, List.reverse_nil,
      dischargeSpine, reflect, List.map_nil]
  | app hsub ih =>
    rw [discharge_vbuiltin_app hsub]
    simp only [reflect, ih, List.map_cons, rdv]
  | force hsub ih =>
    rw [discharge_vbuiltin_force hsub]
    simp only [reflect, ih]

/-! ## The round-trip -/

mutual
  /-- Discharging the reflection of a discharged (well-formed) value recovers the
      original discharge. -/
  theorem discharge_reflect_discharge : ∀ {v : CekValue}, WFValue v →
      discharge (reflect (discharge v)) = discharge v
    | _, .vcon => by simp [discharge, reflect]
    | _, .vlam => by simp [discharge, reflect, dischargeEnv]
    | _, .vdelay => by simp [discharge, reflect, dischargeEnv]
    | _, .vconstr hf => by
      simp only [discharge, reflect, reflectList_dischargeList]
      rw [dischargeList_rdv hf]
    | _, .vbuiltin hsp hargs => by
      rw [reflect_discharge_vbuiltin hsp]
      simp only [discharge]
      rw [dischargeList_rdv hargs]

  /-- The list form: mapping `rdv` over a well-formed value list does not change
      its discharge. -/
  theorem dischargeList_rdv : ∀ {vs : List CekValue}, WFValueList vs →
      dischargeList (vs.map rdv) = dischargeList vs
    | _, .nil => by simp [dischargeList]
    | _, .cons hv hvs => by
      simp only [List.map_cons, dischargeList]
      rw [show discharge (rdv _) = discharge _ from discharge_reflect_discharge hv,
        dischargeList_rdv hvs]
end

/-! ## `rdv` shape lemmas and `extractConsts` preservation -/

@[simp] theorem rdv_vlam (body env) :
    rdv (.VLam body env) = .VLam (dischargeEnv env 1 body) .nil := by simp [rdv, discharge, reflect]

@[simp] theorem rdv_vdelay (body env) :
    rdv (.VDelay body env) = .VDelay (dischargeEnv env 0 body) .nil := by simp [rdv, discharge, reflect]

@[simp] theorem rdv_vconstr (tag fields) :
    rdv (.VConstr tag fields) = .VConstr tag (reflectList (dischargeList fields)) := by
  simp [rdv, discharge, reflect]

theorem rdv_vbuiltin {b args ea} (h : VBSpine b args ea) :
    rdv (.VBuiltin b args ea) = .VBuiltin b (args.map rdv) ea := reflect_discharge_vbuiltin h

/-- Mapping `rdv` over a well-formed value list does not change `extractConsts`:
    `rdv` fixes every `VCon` exactly and keeps non-`VCon`s non-`VCon`. -/
theorem extractConsts_map_rdv : ∀ {L : List CekValue}, WFValueList L →
    extractConsts (L.map rdv) = extractConsts L
  | _, .nil => by simp [extractConsts]
  | _, .cons hv hvs => by
    cases hv with
    | vcon => simp only [List.map_cons, rdv_vcon, extractConsts, extractConsts_map_rdv hvs]
    | vlam => simp only [List.map_cons, rdv_vlam, extractConsts]
    | vdelay => simp only [List.map_cons, rdv_vdelay, extractConsts]
    | vconstr _ => simp only [List.map_cons, rdv_vconstr, extractConsts]
    | vbuiltin hsp _ => simp only [List.map_cons, rdv_vbuiltin hsp, extractConsts]

/-! ## The `evalBuiltin` bridge -/

theorem wfvl_head {v vs} (h : WFValueList (v :: vs)) : WFValue v := by
  cases h with | cons hv _ => exact hv

theorem wfvl_tail {v vs} (h : WFValueList (v :: vs)) : WFValueList vs := by
  cases h with | cons _ hvs => exact hvs

/-- When the pass-through stage declines on both `L` and `L.map rdv`, the result
    is the constant-evaluation path, identical on both by `extractConsts_map_rdv`. -/
theorem evalBuiltin_rdv_const {b} {L : List CekValue} (hwf : WFValueList L)
    (h1 : evalBuiltinPassThrough b (L.map rdv) = none)
    (h2 : evalBuiltinPassThrough b L = none) :
    dischargeResult (evalBuiltin b (L.map rdv)) = dischargeResult (evalBuiltin b L) := by
  simp only [evalBuiltin, h1, h2, extractConsts_map_rdv hwf]

/-- The builtin reflect-bridge: running `evalBuiltin` on `reflect ∘ discharge`-mapped
    arguments yields a discharge-equal result. -/
theorem evalBuiltin_rdv {b : Moist.Plutus.Term.BuiltinFun} : ∀ {L : List CekValue},
    WFValueList L →
    dischargeResult (evalBuiltin b (L.map rdv)) = dischargeResult (evalBuiltin b L) := by
  intro L hwf
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨ b = .ChooseData ∨
      b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · -- IfThenElse: [elseV, thenV, VCon (Bool cond)]
      rcases L with _ | ⟨e, _ | ⟨t, _ | ⟨c, _ | ⟨y, ys⟩⟩⟩⟩
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · cases c with
        | VCon cst =>
          cases cst with
          | Integer _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ByteString _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | String _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Unit => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bool _ =>
            have he := wfvl_head hwf
            have ht := wfvl_head (wfvl_tail hwf)
            simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            rw [apply_ite discharge, apply_ite discharge]
            split
            · exact discharge_reflect_discharge ht
            · exact discharge_reflect_discharge he
          | ConstList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstPairDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Pair _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | PairData _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Data _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstArray _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G1_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G2_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_MlResult => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VBuiltin b' a' e' => cases wfvl_head (wfvl_tail (wfvl_tail hwf)) with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
        | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
    · -- ChooseUnit: [result, VCon Unit]
      rcases L with _ | ⟨r, _ | ⟨c, _ | ⟨y, ys⟩⟩⟩
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · cases c with
        | VCon cst =>
          cases cst with
          | Integer _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ByteString _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | String _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Unit =>
            have hr := wfvl_head hwf
            simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            exact discharge_reflect_discharge hr
          | Bool _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstPairDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Pair _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | PairData _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Data _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstArray _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G1_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G2_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_MlResult => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VBuiltin b' a' e' => cases wfvl_head (wfvl_tail hwf) with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
        | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
    · -- Trace: [result, VCon (String _)]
      rcases L with _ | ⟨r, _ | ⟨c, _ | ⟨y, ys⟩⟩⟩
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · cases c with
        | VCon cst =>
          cases cst with
          | Integer _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ByteString _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | String _ =>
            have hr := wfvl_head hwf
            simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            exact discharge_reflect_discharge hr
          | Unit => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bool _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstPairDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Pair _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | PairData _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Data _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstArray _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G1_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G2_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_MlResult => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VBuiltin b' a' e' => cases wfvl_head (wfvl_tail hwf) with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
        | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
    · -- ChooseData: [bCase, iCase, listCase, mapCase, constrCase, VCon (Data d)]
      rcases L with _ | ⟨bc, _ | ⟨ic, _ | ⟨lc, _ | ⟨mc, _ | ⟨cc, _ | ⟨c, _ | ⟨y, ys⟩⟩⟩⟩⟩⟩⟩
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · cases c with
        | VCon cst =>
          cases cst with
          | Integer _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ByteString _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | String _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Unit => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bool _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstPairDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Pair _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | PairData _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Data d =>
            have hbc := wfvl_head hwf
            have hic := wfvl_head (wfvl_tail hwf)
            have hlc := wfvl_head (wfvl_tail (wfvl_tail hwf))
            have hmc := wfvl_head (wfvl_tail (wfvl_tail (wfvl_tail hwf)))
            have hcc := wfvl_head (wfvl_tail (wfvl_tail (wfvl_tail (wfvl_tail hwf))))
            cases d <;> simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            · exact discharge_reflect_discharge hcc
            · exact discharge_reflect_discharge hmc
            · exact discharge_reflect_discharge hlc
            · exact discharge_reflect_discharge hic
            · exact discharge_reflect_discharge hbc
          | ConstArray _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G1_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G2_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_MlResult => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VBuiltin b' a' e' => cases wfvl_head (wfvl_tail (wfvl_tail (wfvl_tail (wfvl_tail (wfvl_tail hwf))))) with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
        | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
    · -- ChooseList: [consCase, nilCase, VCon (ConstDataList l) | VCon (ConstList l)]
      rcases L with _ | ⟨cc, _ | ⟨nc, _ | ⟨c, _ | ⟨y, ys⟩⟩⟩⟩
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · cases c with
        | VCon cst =>
          cases cst with
          | Integer _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ByteString _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | String _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Unit => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bool _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstList _ =>
            have hcc := wfvl_head hwf
            have hnc := wfvl_head (wfvl_tail hwf)
            simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            rw [apply_ite discharge, apply_ite discharge]
            split
            · exact discharge_reflect_discharge hnc
            · exact discharge_reflect_discharge hcc
          | ConstDataList _ =>
            have hcc := wfvl_head hwf
            have hnc := wfvl_head (wfvl_tail hwf)
            simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            rw [apply_ite discharge, apply_ite discharge]
            split
            · exact discharge_reflect_discharge hnc
            · exact discharge_reflect_discharge hcc
          | ConstPairDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Pair _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | PairData _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Data _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstArray _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G1_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G2_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_MlResult => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VBuiltin b' a' e' => cases wfvl_head (wfvl_tail (wfvl_tail hwf)) with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
        | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
    · -- MkCons: [VCon (ConstList tail), elem]
      rcases L with _ | ⟨c, _ | ⟨elem, _ | ⟨y, ys⟩⟩⟩
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · cases c with
        | VCon cst =>
          cases cst with
          | Integer _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ByteString _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | String _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Unit => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bool _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstList _ =>
            cases elem with
            | VCon c2 => simp only [List.map_cons, List.map_nil, rdv_vcon, evalBuiltin, evalBuiltinPassThrough, dischargeResult]
            | VBuiltin b' a' e' => cases wfvl_head (wfvl_tail hwf) with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
            | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
            | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
            | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstPairDataList _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Pair _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | PairData _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Data _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | ConstArray _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G1_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_G2_element => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
          | Bls12_381_MlResult => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VBuiltin b' a' e' => cases wfvl_head hwf with | vbuiltin hsp _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough, rdv_vbuiltin hsp]) (by simp [evalBuiltinPassThrough])
        | VLam _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VDelay _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
        | VConstr _ _ => exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
      · exact evalBuiltin_rdv_const hwf (by simp [evalBuiltinPassThrough]) (by simp [evalBuiltinPassThrough])
  · -- not a pass-through builtin: pure constant path
    simp only [not_or] at hb
    exact evalBuiltin_rdv_const hwf
      (evalBuiltinPassThrough_none_of_not_passthrough b _ hb)
      (evalBuiltinPassThrough_none_of_not_passthrough b _ hb)
/-! ## Shuffle lemmas connecting the simulation's spine to `rdv` -/

/-- The small-step saturated-force argument list, expressed via `rdv`. -/
theorem reflectList_reverse_dischargeList (vs : List CekValue) :
    (reflectList (dischargeList vs).reverse).reverse = vs.map rdv := by
  simp only [reflectList_eq_map, dischargeList_eq_map, List.map_reverse,
    List.reverse_reverse, List.map_map]; rfl

/-- The small-step saturated-apply argument list, expressed via `rdv`. -/
theorem reflectList_reverse_append (vs : List CekValue) (vx : CekValue) :
    (reflectList ((dischargeList vs).reverse ++ [discharge vx])).reverse = (vx :: vs).map rdv := by
  simp only [reflectList_eq_map, dischargeList_eq_map, List.map_append, List.map_reverse,
    List.reverse_append, List.reverse_reverse, List.map_map, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  rfl

end Moist.Verified.SmallStep
