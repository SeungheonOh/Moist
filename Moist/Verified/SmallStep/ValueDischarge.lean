import Moist.Verified.SmallStep.DischargeLemmas

/-! # `value_discharge`: every (well-formed) CEK value discharges to a `Value`

Introduces `VBSpine` (the CEK-value analogue of `BSpine`) and `WFValue`
(well-formedness of CEK values: builtin spines have a suffix signature and
matching args).  The CEK only ever produces well-formed values, and every
well-formed value discharges to a small-step `Value`.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term BuiltinFun)
open Moist.CEK (ArgKind ExpectedArgs expectedArgs CekValue CekEnv)

/-! ## Misc list helpers -/

theorem isSuffix_trans {a b c : ExpectedArgs}
    (h1 : IsSuffix a b) (h2 : IsSuffix b c) : IsSuffix a c := by
  induction h2 with
  | refl => exact h1
  | more _ ih => exact .more ih

theorem numV_append (xs ys : List ArgKind) : numV (xs ++ ys) = numV xs + numV ys := by
  induction xs with
  | nil => simp [numV]
  | cons k xs ih => cases k <;> simp only [List.cons_append, numV, ih] <;> omega

theorem dischargeList_reverse_cons (v : CekValue) (vs : List CekValue) :
    (dischargeList (v :: vs)).reverse = (dischargeList vs).reverse ++ [discharge v] := by
  simp only [dischargeList, List.reverse_cons]

theorem dischargeList_length (vs : List CekValue) :
    (dischargeList vs).length = vs.length := by
  rw [dischargeList_eq_map, List.length_map]

/-! ## `VBSpine` — well-formed builtin spine over CEK values

Mirrors `BSpine`, but at the level of `CekValue` arguments (stored
most-recent-first, exactly as `CekValue.VBuiltin`). -/

inductive VBSpine : BuiltinFun → List CekValue → ExpectedArgs → Prop
  | base {b} : VBSpine b [] (expectedArgs b)
  | app {b vargs rest v} : VBSpine b vargs (.more .argV rest) → VBSpine b (v :: vargs) rest
  | force {b vargs rest} : VBSpine b vargs (.more .argQ rest) → VBSpine b vargs rest

theorem vbspine_isSuffix {b vargs ea} (h : VBSpine b vargs ea) :
    IsSuffix ea (expectedArgs b) := by
  induction h with
  | base => exact .refl
  | app _ ih => exact isSuffix_trans (.more .refl) ih
  | force _ ih => exact isSuffix_trans (.more .refl) ih

theorem vbspine_numV {b vargs ea} (h : VBSpine b vargs ea) :
    numV (consumedSteps (expectedArgs b) ea) = vargs.length := by
  induction h with
  | base => rw [consumedSteps_self]; rfl
  | app hsub ih =>
    rw [consumedSteps_more (vbspine_isSuffix hsub), numV_append]
    simp only [numV, List.length_cons]; omega
  | force hsub ih =>
    rw [consumedSteps_more (vbspine_isSuffix hsub), numV_append]
    simp only [numV]; omega

/-! ## Discharge unfolding for builtin spines -/

theorem discharge_vbuiltin_app {b vargs rest v} (hsub : VBSpine b vargs (.more .argV rest)) :
    discharge (.VBuiltin b (v :: vargs) rest)
      = .Apply (discharge (.VBuiltin b vargs (.more .argV rest))) (discharge v) := by
  have hlen : numV (consumedSteps (expectedArgs b) (.more .argV rest))
      = ((dischargeList vargs).reverse).length := by
    rw [vbspine_numV hsub]; rw [List.length_reverse, dischargeList_length]
  simp only [discharge]
  rw [dischargeList_reverse_cons, consumedSteps_more (vbspine_isSuffix hsub),
      dischargeSpine_snoc_argV hlen]

theorem discharge_vbuiltin_force {b vargs rest} (hsub : VBSpine b vargs (.more .argQ rest)) :
    discharge (.VBuiltin b vargs rest)
      = .Force (discharge (.VBuiltin b vargs (.more .argQ rest))) := by
  have hlen : numV (consumedSteps (expectedArgs b) (.more .argQ rest))
      = ((dischargeList vargs).reverse).length := by
    rw [vbspine_numV hsub]; rw [List.length_reverse, dischargeList_length]
  simp only [discharge]
  rw [consumedSteps_more (vbspine_isSuffix hsub), dischargeSpine_snoc_argQ hlen]

/-- The discharge of a well-formed builtin spine is a `BSpine`. -/
theorem bspine_discharge : ∀ {b vargs ea}, VBSpine b vargs ea →
    ValueList (dischargeList vargs) →
    BSpine (discharge (.VBuiltin b vargs ea)) b (dischargeList vargs).reverse ea := by
  intro b vargs ea hsp
  induction hsp with
  | base =>
    intro _
    simp only [discharge, dischargeList, consumedSteps_self, List.reverse_nil, dischargeSpine]
    exact .builtin
  | app hsub ih =>
    intro hvl
    simp only [dischargeList] at hvl
    cases hvl with
    | cons hv0 hvl' =>
      rw [discharge_vbuiltin_app hsub, dischargeList_reverse_cons]
      exact .app (ih hvl') hv0
  | force hsub ih =>
    intro hvl
    rw [discharge_vbuiltin_force hsub]
    exact .force (ih hvl)

/-! ## Well-formed CEK values -/

mutual
  inductive WFValue : CekValue → Prop
    | vcon {c} : WFValue (.VCon c)
    | vlam {body env} : WFValue (.VLam body env)
    | vdelay {body env} : WFValue (.VDelay body env)
    | vconstr {tag fields} : WFValueList fields → WFValue (.VConstr tag fields)
    | vbuiltin {b vargs ea} : VBSpine b vargs ea → WFValueList vargs →
        WFValue (.VBuiltin b vargs ea)

  inductive WFValueList : List CekValue → Prop
    | nil : WFValueList []
    | cons {v vs} : WFValue v → WFValueList vs → WFValueList (v :: vs)
end

mutual
  /-- A well-formed CEK value discharges to a small-step `Value`. -/
  theorem value_discharge : ∀ {v : CekValue}, WFValue v → Value (discharge v)
    | _, .vcon => by simp only [discharge]; exact .constant
    | _, .vlam => by simp only [discharge]; exact .lam
    | _, .vdelay => by simp only [discharge]; exact .delay
    | _, .vconstr hfields => by
      simp only [discharge]; exact .constr (valueList_discharge hfields)
    | _, .vbuiltin hsp hargs => .builtin (bspine_discharge hsp (valueList_discharge hargs))

  /-- A well-formed list of CEK values discharges to a `ValueList`. -/
  theorem valueList_discharge : ∀ {vs : List CekValue}, WFValueList vs →
      ValueList (dischargeList vs)
    | _, .nil => by simp only [dischargeList]; exact .nil
    | _, .cons hv hvs => by
      simp only [dischargeList]; exact .cons (value_discharge hv) (valueList_discharge hvs)
end

end Moist.Verified.SmallStep
