import Moist.Verified.SmallStep.Simulation
import Moist.Verified.Definitions

/-! # The administrative measure and the CEK termination argument

`μ` is a measure on CEK states that strictly decreases on every *administrative*
transition — the silent reshuffling the machine performs that corresponds to **no**
small-step reduction.  Combined with the small-step path length (bounded by
determinism for a terminating term), it bounds the total number of CEK steps,
giving the backward direction of adequacy (`reach_terminal`): if small-step
reduction reaches a normal form, the CEK machine reaches a terminal state.

`step_mu` is the structural classification of a CEK step: it is a *real* reduction
(one `Step` on the discharge), an *administrative* step (discharge unchanged, `μ`
strictly down), or a transition to `error`.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK

/-! ## The measure -/

mutual
  /-- Structural size of a term (every node counts at least one). -/
  def termSize : Term → Nat
    | .Var _ => 1
    | .Constant _ => 1
    | .Builtin _ => 1
    | .Error => 1
    | .Lam _ b => 1 + termSize b
    | .Apply f x => 1 + termSize f + termSize x
    | .Force e => 1 + termSize e
    | .Delay e => 1 + termSize e
    | .Constr _ args => 1 + termSizeList args
    | .Case s alts => 1 + termSize s + termSizeList alts
  termination_by t => sizeOf t

  /-- Structural size of a term list. -/
  def termSizeList : List Term → Nat
    | [] => 0
    | t :: ts => termSize t + termSizeList ts
  termination_by ts => sizeOf ts
end

/-- The unevaluated-term content stored in a frame. -/
def Frame.tcontent : Frame → Nat
  | .arg M _ => termSize M
  | .constrField _ _ todo _ => termSizeList todo
  | _ => 0

/-- The unevaluated-term content stored along a stack. -/
def stkContent : Stack → Nat
  | [] => 0
  | f :: π => Frame.tcontent f + stkContent π

/-- The administrative measure: term content (weighted) + stack length + a phase
    bit distinguishing `ret` (1) from `compute` (0). -/
def μ : State → Nat
  | .compute π _ M => 2 * (termSize M + stkContent π) + π.length
  | .ret π _ => 2 * stkContent π + π.length + 1
  | .halt _ => 0
  | .error => 0

/-! ## Structural step classification -/

set_option maxHeartbeats 4000000 in
theorem step_mu_compute (π : Stack) (ρ : CekEnv) (M : Term)
    (hg : GoodState (.compute π ρ M)) (hc : CanonState (.compute π ρ M)) :
    Step (dischargeState (.compute π ρ M)) (dischargeState (step (.compute π ρ M)))
    ∨ (dischargeState (step (.compute π ρ M)) = dischargeState (.compute π ρ M)
        ∧ μ (step (.compute π ρ M)) < μ (.compute π ρ M))
    ∨ step (.compute π ρ M) = .error := by
  obtain ⟨hMc, hρ, _⟩ := hg
  obtain ⟨hMcanon, _, _⟩ := hc
  cases M with
  | Var n =>
    cases n with
    | zero =>
      refine Or.inr (Or.inr ?_)
      have h0 : ρ.lookup 0 = none := by cases ρ <;> rfl
      simp only [step, h0]
    | succ m =>
      have hn : m + 1 ≤ ρ.length := by simpa [closedAt] using hMc
      obtain ⟨v, hv⟩ := ρ.lookup_some_of_le_length (m + 1) (by omega) hn
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · simp only [step, hv, dischargeState, dischargeEnv_var_lookup hρ hv]
      · show μ (step (.compute π ρ (.Var (m + 1)))) < μ (.compute π ρ (.Var (m + 1)))
        simp only [step, hv, μ, termSize]; omega
  | Constant cb =>
    obtain ⟨c, bt⟩ := cb
    have hbt : bt = Moist.Plutus.Term.constType c := by rw [Canonical] at hMcanon; exact hMcanon
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeEnv_constant, discharge, hbt]
    · show μ (step (.compute π ρ (.Constant (c, bt)))) < μ (.compute π ρ (.Constant (c, bt)))
      simp only [step, μ, termSize]; omega
  | Builtin b =>
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeEnv_builtin, discharge, dischargeList,
        consumedSteps_self, List.reverse_nil, dischargeSpine]
    · show μ (step (.compute π ρ (.Builtin b))) < μ (.compute π ρ (.Builtin b))
      simp only [step, μ, termSize]; omega
  | Lam name body =>
    have hname : name = 0 := by rw [Canonical] at hMcanon; exact hMcanon.1
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeEnv_lam (goodEnv_envDischargeClosed hρ), discharge, hname]
    · show μ (step (.compute π ρ (.Lam name body))) < μ (.compute π ρ (.Lam name body))
      simp only [step, μ, termSize]; omega
  | Delay body =>
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeEnv_delay, discharge]
    · show μ (step (.compute π ρ (.Delay body))) < μ (.compute π ρ (.Delay body))
      simp only [step, μ, termSize]; omega
  | Force e =>
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_force]
    · show μ (step (.compute π ρ (.Force e))) < μ (.compute π ρ (.Force e))
      simp only [step, μ, termSize, stkContent, Frame.tcontent, List.length_cons]; omega
  | Apply f x =>
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_apply]
    · show μ (step (.compute π ρ (.Apply f x))) < μ (.compute π ρ (.Apply f x))
      simp only [step, μ, termSize, stkContent, Frame.tcontent, List.length_cons]; omega
  | Constr tag args =>
    cases args with
    | nil =>
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · simp only [step, dischargeState, dischargeEnv_constr, discharge, dischargeList, List.map_nil]
      · show μ (step (.compute π ρ (.Constr tag []))) < μ (.compute π ρ (.Constr tag []))
        simp only [step, μ, termSize, termSizeList]; omega
    | cons m ms =>
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_constr,
          dischargeList, List.reverse_nil, List.nil_append, List.map_cons]
      · show μ (step (.compute π ρ (.Constr tag (m :: ms)))) < μ (.compute π ρ (.Constr tag (m :: ms)))
        simp only [step, μ, termSize, termSizeList, stkContent, Frame.tcontent, List.length_cons]
        omega
  | Case scrut alts =>
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeStack, frameCtx, dischargeEnv_case]
    · show μ (step (.compute π ρ (.Case scrut alts))) < μ (.compute π ρ (.Case scrut alts))
      simp only [step, μ, termSize, stkContent, Frame.tcontent, List.length_cons]; omega
  | Error => exact Or.inr (Or.inr rfl)


set_option maxHeartbeats 8000000 in
theorem step_mu_ret (π : Stack) (v : CekValue)
    (hg : GoodState (.ret π v)) (hc : CanonState (.ret π v)) :
    Step (dischargeState (.ret π v)) (dischargeState (step (.ret π v)))
    ∨ (dischargeState (step (.ret π v)) = dischargeState (.ret π v)
        ∧ μ (step (.ret π v)) < μ (.ret π v))
    ∨ step (.ret π v) = .error := by
  obtain ⟨hv, hπ⟩ := hg
  obtain ⟨hvc, hπc⟩ := hc
  cases π with
  | nil =>
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · simp only [step, dischargeState, dischargeStack]
    · show μ (step (.ret [] v)) < μ (.ret [] v)
      simp only [step, μ, stkContent]; omega
  | cons f s =>
    have hf := goodStack_head hπ
    have hs := goodStack_tail hπ
    have hsw := goodStack_wfStack hs
    have hbefore : dischargeState (.ret (f :: s) v) = dischargeStack s (frameCtx f (discharge v)) := by
      simp only [dischargeState, dischargeStack]
    cases f with
    | force =>
      cases v with
      | VDelay body ρ' =>
        refine Or.inl ?_
        rw [hbefore, show frameCtx Frame.force (discharge (.VDelay body ρ'))
              = .Force (.Delay (dischargeEnv ρ' 0 body)) from by simp only [frameCtx, discharge]]
        rw [show dischargeState (step (.ret (.force :: s) (.VDelay body ρ')))
              = dischargeStack s (dischargeEnv ρ' 0 body) from by simp only [step, dischargeState]]
        exact dischargeStack_cong hsw Step.forceDelay
      | VBuiltin b args ea =>
        cases hv with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          cases ea with
          | one k => cases k with
            | argQ =>
              have hres : dischargeResult (evalBuiltin b ((reflectList ((dischargeList args).reverse)).reverse))
                  = dischargeResult (evalBuiltin b args) := by
                rw [reflectList_reverse_dischargeList]; exact evalBuiltin_rdv (goodList_wf hargs)
              have hstep := Step.satForce hbsp
              rw [hres] at hstep
              cases hev : evalBuiltin b args with
              | some w =>
                refine Or.inl ?_
                rw [hbefore, show frameCtx Frame.force (discharge (.VBuiltin b args (.one .argQ)))
                      = .Force (discharge (.VBuiltin b args (.one .argQ))) from by simp only [frameCtx]]
                rw [show dischargeState (step (.ret (.force :: s) (.VBuiltin b args (.one .argQ))))
                      = dischargeStack s (discharge w) from by
                    simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact dischargeStack_cong hsw hstep
              | none => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
            | argV => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head]))
          | more k rest => cases k with
            | argQ =>
              refine Or.inr (Or.inl ⟨?_, ?_⟩)
              · rw [hbefore, show frameCtx Frame.force (discharge (.VBuiltin b args (.more .argQ rest)))
                      = .Force (discharge (.VBuiltin b args (.more .argQ rest))) from by simp only [frameCtx]]
                rw [show dischargeState (step (.ret (.force :: s) (.VBuiltin b args (.more .argQ rest))))
                      = dischargeStack s (discharge (.VBuiltin b args rest)) from by
                    simp only [step, ExpectedArgs.head, ExpectedArgs.tail, dischargeState]]
                rw [discharge_vbuiltin_force hsp]
              · show μ (step (.ret (.force :: s) (.VBuiltin b args (.more .argQ rest))))
                    < μ (.ret (.force :: s) (.VBuiltin b args (.more .argQ rest)))
                simp only [step, ExpectedArgs.head, ExpectedArgs.tail, μ, stkContent, Frame.tcontent,
                  List.length_cons]; omega
            | argV => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head]))
      | VCon c => exact Or.inr (Or.inr (by simp only [step]))
      | VLam body ρ' => exact Or.inr (Or.inr (by simp only [step]))
      | VConstr tag fields => exact Or.inr (Or.inr (by simp only [step]))
    | arg M ρ' =>
      refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · simp only [step, dischargeState, dischargeStack, frameCtx]
      · show μ (step (.ret (.arg M ρ' :: s) v)) < μ (.ret (.arg M ρ' :: s) v)
        simp only [step, μ, stkContent, Frame.tcontent, List.length_cons]; omega
    | funV vf =>
      cases vf with
      | VLam body ρ' =>
        cases hf with
        | vlam _ heρ' =>
          refine Or.inl ?_
          rw [hbefore, show frameCtx (Frame.funV (.VLam body ρ')) (discharge v)
                = .Apply (.Lam 0 (dischargeEnv ρ' 1 body)) (discharge v) from by simp only [frameCtx, discharge]]
          rw [show dischargeState (step (.ret (.funV (.VLam body ρ') :: s) v))
                = dischargeStack s (dischargeEnv (ρ'.extend v) 0 body) from by simp only [step, dischargeState]]
          have hstep := @Step.betaLam 0 (dischargeEnv ρ' 1 body) (discharge v) (value_discharge (good_wf hv))
          rw [beta_discharge (good_discharge_closed hv) (goodEnv_envDischargeClosed heρ')] at hstep
          exact dischargeStack_cong hsw hstep
      | VBuiltin b args ea =>
        cases hf with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          cases ea with
          | one k => cases k with
            | argV =>
              have hres : dischargeResult (evalBuiltin b ((reflectList ((dischargeList args).reverse ++ [discharge v])).reverse)) = dischargeResult (evalBuiltin b (v :: args)) := by
                rw [reflectList_reverse_append]; exact evalBuiltin_rdv (.cons (good_wf hv) (goodList_wf hargs))
              have hstep := Step.satApply hbsp (value_discharge (good_wf hv))
              rw [hres] at hstep
              cases hev : evalBuiltin b (v :: args) with
              | some w =>
                refine Or.inl ?_
                rw [hbefore, show frameCtx (Frame.funV (.VBuiltin b args (.one .argV))) (discharge v) = .Apply (discharge (.VBuiltin b args (.one .argV))) (discharge v) from by simp only [frameCtx]]
                rw [show dischargeState (step (.ret (.funV (.VBuiltin b args (.one .argV)) :: s) v)) = dischargeStack s (discharge w) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact dischargeStack_cong hsw hstep
              | none => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
            | argQ => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head]))
          | more k rest => cases k with
            | argV =>
              refine Or.inr (Or.inl ⟨?_, ?_⟩)
              · rw [hbefore, show frameCtx (Frame.funV (.VBuiltin b args (.more .argV rest))) (discharge v) = .Apply (discharge (.VBuiltin b args (.more .argV rest))) (discharge v) from by simp only [frameCtx]]
                rw [show dischargeState (step (.ret (.funV (.VBuiltin b args (.more .argV rest)) :: s) v)) = dischargeStack s (discharge (.VBuiltin b (v :: args) rest)) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, dischargeState]]
                rw [discharge_vbuiltin_app hsp]
              · show μ (step (.ret (.funV (.VBuiltin b args (.more .argV rest)) :: s) v)) < μ (.ret (.funV (.VBuiltin b args (.more .argV rest)) :: s) v)
                simp only [step, ExpectedArgs.head, ExpectedArgs.tail, μ, stkContent, Frame.tcontent, List.length_cons]; omega
            | argQ => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head]))
      | VCon c => exact Or.inr (Or.inr (by simp only [step]))
      | VDelay body ρ' => exact Or.inr (Or.inr (by simp only [step]))
      | VConstr tag fields => exact Or.inr (Or.inr (by simp only [step]))
    | applyArg vx =>
      cases v with
      | VLam body ρ' =>
        cases hv with
        | vlam _ heρ' =>
          refine Or.inl ?_
          rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VLam body ρ'))
                = .Apply (.Lam 0 (dischargeEnv ρ' 1 body)) (discharge vx) from by simp only [frameCtx, discharge]]
          rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VLam body ρ')))
                = dischargeStack s (dischargeEnv (ρ'.extend vx) 0 body) from by simp only [step, dischargeState]]
          have hstep := @Step.betaLam 0 (dischargeEnv ρ' 1 body) (discharge vx) (value_discharge (good_wf hf))
          rw [beta_discharge (good_discharge_closed hf) (goodEnv_envDischargeClosed heρ')] at hstep
          exact dischargeStack_cong hsw hstep
      | VBuiltin b args ea =>
        cases hv with
        | vbuiltin hsp hargs =>
          have hbsp : BSpine (discharge (.VBuiltin b args ea)) b (dischargeList args).reverse ea :=
            bspine_discharge hsp (valueList_discharge (goodList_wf hargs))
          cases ea with
          | one k => cases k with
            | argV =>
              have hres : dischargeResult (evalBuiltin b ((reflectList ((dischargeList args).reverse ++ [discharge vx])).reverse)) = dischargeResult (evalBuiltin b (vx :: args)) := by
                rw [reflectList_reverse_append]; exact evalBuiltin_rdv (.cons (good_wf hf) (goodList_wf hargs))
              have hstep := Step.satApply hbsp (value_discharge (good_wf hf))
              rw [hres] at hstep
              cases hev : evalBuiltin b (vx :: args) with
              | some w =>
                refine Or.inl ?_
                rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VBuiltin b args (.one .argV))) = .Apply (discharge (.VBuiltin b args (.one .argV))) (discharge vx) from by simp only [frameCtx]]
                rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VBuiltin b args (.one .argV)))) = dischargeStack s (discharge w) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev, dischargeState]]
                rw [hev] at hstep; simp only [dischargeResult] at hstep
                exact dischargeStack_cong hsw hstep
              | none => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
            | argQ => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head]))
          | more k rest => cases k with
            | argV =>
              refine Or.inr (Or.inl ⟨?_, ?_⟩)
              · rw [hbefore, show frameCtx (Frame.applyArg vx) (discharge (.VBuiltin b args (.more .argV rest))) = .Apply (discharge (.VBuiltin b args (.more .argV rest))) (discharge vx) from by simp only [frameCtx]]
                rw [show dischargeState (step (.ret (.applyArg vx :: s) (.VBuiltin b args (.more .argV rest)))) = dischargeStack s (discharge (.VBuiltin b (vx :: args) rest)) from by simp only [step, ExpectedArgs.head, ExpectedArgs.tail, dischargeState]]
                rw [discharge_vbuiltin_app hsp]
              · show μ (step (.ret (.applyArg vx :: s) (.VBuiltin b args (.more .argV rest)))) < μ (.ret (.applyArg vx :: s) (.VBuiltin b args (.more .argV rest)))
                simp only [step, ExpectedArgs.head, ExpectedArgs.tail, μ, stkContent, Frame.tcontent, List.length_cons]; omega
            | argQ => exact Or.inr (Or.inr (by simp only [step, ExpectedArgs.head]))
      | VCon c => exact Or.inr (Or.inr (by simp only [step]))
      | VDelay body ρ' => exact Or.inr (Or.inr (by simp only [step]))
      | VConstr tag fields => exact Or.inr (Or.inr (by simp only [step]))
    | constrField tag done todo ρ' =>
      cases todo with
      | nil =>
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · have hlist : List.map discharge (done.reverse ++ [v])
              = (List.map discharge done).reverse ++ [discharge v] := by
            simp [List.map_append, List.map_reverse]
          rw [show dischargeState (step (.ret (.constrField tag done [] ρ' :: s) v))
                = dischargeState (.ret (.constrField tag done [] ρ' :: s) v) from by
            simp only [step, dischargeState, dischargeStack, frameCtx, discharge,
              dischargeList_eq_map, List.reverse_cons, List.map_nil, hlist]]
        · show μ (step (.ret (.constrField tag done [] ρ' :: s) v)) < μ (.ret (.constrField tag done [] ρ' :: s) v)
          simp only [step, μ, termSizeList, stkContent, Frame.tcontent, List.length_cons]; omega
      | cons m ms =>
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [show dischargeState (step (.ret (.constrField tag done (m :: ms) ρ' :: s) v))
                = dischargeState (.ret (.constrField tag done (m :: ms) ρ' :: s) v) from by
            simp only [step, dischargeState, dischargeStack, frameCtx, dischargeList,
              List.reverse_cons, List.map_cons, List.append_assoc, List.cons_append, List.nil_append]]
        · show μ (step (.ret (.constrField tag done (m :: ms) ρ' :: s) v)) < μ (.ret (.constrField tag done (m :: ms) ρ' :: s) v)
          simp only [step, μ, termSizeList, stkContent, Frame.tcontent, List.length_cons]
          omega
    | caseScrutinee alts ρ' =>
      obtain ⟨halts, heρ'⟩ := hf
      cases v with
      | VConstr tag fields =>
        cases hv with
        | vconstr hfields =>
          have hvl : ValueList (dischargeList fields) := valueList_discharge (goodList_wf hfields)
          cases halt : alts[tag]? with
          | some alt =>
            refine Or.inl ?_
            have hmap : (alts.map (dischargeEnv ρ' 0 ·))[tag]? = some (dischargeEnv ρ' 0 alt) := by
              rw [List.getElem?_map, halt]; rfl
            rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VConstr tag fields))
                  = .Case (.Constr tag (dischargeList fields)) (alts.map (dischargeEnv ρ' 0 ·)) from by
                simp only [frameCtx, discharge]]
            rw [show dischargeState (step (.ret (.caseScrutinee alts ρ' :: s) (.VConstr tag fields)))
                  = dischargeStack s (mkApps (dischargeEnv ρ' 0 alt) (dischargeList fields)) from by
                simp only [step, halt, dischargeState, dischargeStack_append, dischargeStack_applyArgFrames]]
            exact dischargeStack_cong hsw (Step.caseConstr hvl hmap)
          | none => exact Or.inr (Or.inr (by simp only [step, halt]))
      | VCon c =>
        rcases hcf : constToTagAndFields c with _ | ⟨tag, numCtors, fields⟩
        · exact Or.inr (Or.inr (by simp only [step, hcf]))
        · have hfgood := constToTagAndFields_fields_good hcf
          have hvl : ValueList (dischargeList fields) := valueList_discharge (goodList_wf hfgood)
          by_cases hchk : (numCtors > 0 && alts.length > numCtors) = true
          · exact Or.inr (Or.inr (by simp only [step, hcf]; rw [if_pos hchk]))
          · have hchk' : ¬ (numCtors > 0 ∧ alts.length > numCtors) := by
              simpa [Bool.and_eq_true, decide_eq_true_eq] using hchk
            cases halt : alts[tag]? with
            | some alt =>
              refine Or.inl ?_
              have hmap : (alts.map (dischargeEnv ρ' 0 ·))[tag]? = some (dischargeEnv ρ' 0 alt) := by
                rw [List.getElem?_map, halt]; rfl
              rw [hbefore, show frameCtx (Frame.caseScrutinee alts ρ') (discharge (.VCon c))
                    = .Case (.Constant (c, Moist.Plutus.Term.constType c)) (alts.map (dischargeEnv ρ' 0 ·)) from by
                  simp only [frameCtx, discharge]]
              rw [show dischargeState (step (.ret (.caseScrutinee alts ρ' :: s) (.VCon c)))
                    = dischargeStack s (mkApps (dischargeEnv ρ' 0 alt) (dischargeList fields)) from by
                  simp only [step, hcf]; rw [if_neg hchk]
                  simp only [halt, dischargeState, dischargeStack_append, dischargeStack_applyArgFrames]]
              have hcaseconst := @Step.caseConst c (Moist.Plutus.Term.constType c) tag numCtors fields
                (alts.map (dischargeEnv ρ' 0 ·)) (dischargeEnv ρ' 0 alt) hcf
                (by rw [List.length_map]; exact hchk') hmap
              rw [show List.map discharge fields = dischargeList fields from (dischargeList_eq_map fields).symm] at hcaseconst
              exact dischargeStack_cong hsw hcaseconst
            | none =>
              exact Or.inr (Or.inr (by simp only [step, hcf]; rw [if_neg hchk]; simp only [halt]))
      | VLam body ρ'' => exact Or.inr (Or.inr (by simp only [step]))
      | VDelay body ρ'' => exact Or.inr (Or.inr (by simp only [step]))
      | VBuiltin b args ea => exact Or.inr (Or.inr (by simp only [step]))

/-- Structural classification of a non-halted CEK step: a real reduction (one
    `Step`), an administrative step (`μ` strictly decreasing), or a transition to
    `error`. -/
theorem step_mu (s : State) (hg : GoodState s) (hc : CanonState s)
    (hnh : ¬ ∃ v, s = .halt v) :
    Step (dischargeState s) (dischargeState (step s))
    ∨ (dischargeState (step s) = dischargeState s ∧ μ (step s) < μ s)
    ∨ step s = .error := by
  cases s with
  | compute π ρ M => exact step_mu_compute π ρ M hg hc
  | ret π v => exact step_mu_ret π v hg hc
  | halt v => exact absurd ⟨v, rfl⟩ hnh
  | error => exact Or.inr (Or.inr rfl)


/-! ## The CEK terminates when small-step reduction reaches a normal form -/

open Moist.Verified.Equivalence (steps Reaches)

/-- A terminal CEK state: halted or errored. -/
def IsTerminalState (s : State) : Prop := (∃ v, s = .halt v) ∨ s = .error

/-- **Backward termination.** If the discharge of a `Good`/`Canon` state reaches a
    normal form `w` in `k` small steps, the CEK machine reaches a terminal state.
    Well-founded on `(k, μ s)`: real reductions shrink the small-step distance `k`,
    administrative steps shrink `μ`. -/
theorem reach_terminal {w : Term} (hw : Normal w) :
    ∀ (k : Nat) (s : State), GoodState s → CanonState s → StepsN k (dischargeState s) w →
    ∃ n, IsTerminalState (steps n s)
  | k, s, hg, hc, hk => by
    by_cases hterm : IsTerminalState s
    · exact ⟨0, hterm⟩
    · have hnh : ¬ ∃ v, s = .halt v := fun h => hterm (Or.inl h)
      rcases step_mu s hg hc hnh with hstep | ⟨heq, hmu⟩ | herr
      · obtain ⟨hle, htail⟩ := stepsN_align hw (StepsN.step hstep StepsN.refl) hk
        obtain ⟨n, hn⟩ := reach_terminal hw (k - 1) (step s)
          (step_preserves_good hg) (step_preserves_canon hc) htail
        exact ⟨n + 1, hn⟩
      · rw [← heq] at hk
        obtain ⟨n, hn⟩ := reach_terminal hw k (step s)
          (step_preserves_good hg) (step_preserves_canon hc) hk
        exact ⟨n + 1, hn⟩
      · exact ⟨1, Or.inr herr⟩
  termination_by k s _ _ _ => (k, μ s)
  decreasing_by
    · exact Prod.Lex.left _ _ (by omega)
    · exact Prod.Lex.right _ hmu

/-- The CEK machine from a closed canonical term terminates when the term has a
    small-step normal form. -/
theorem cek_terminates {t : Term} {k : Nat} {w : Term}
    (ht : closedAt 0 t = true) (htc : Canonical t) (hk : StepsN k t w) (hw : Normal w) :
    ∃ n, IsTerminalState (steps n (init t)) :=
  reach_terminal hw k (init t) (init_good ht) (init_canon htc)
    (by rw [dischargeState_init]; exact hk)

/-- Determinism gives unique normal forms: two normal forms reachable from the
    same term coincide. -/
theorem normal_form_unique {t a b : Term}
    (ha : Steps t a) (hna : Normal a) (hb : Steps t b) (hnb : Normal b) : a = b := by
  obtain ⟨i, hi⟩ := steps_stepsN ha
  obtain ⟨j, hj⟩ := steps_stepsN hb
  obtain ⟨_, htail⟩ := stepsN_align hnb hi hj
  cases hjk : j - i with
  | zero => rw [hjk] at htail; cases htail; rfl
  | succ m =>
    rw [hjk] at htail
    cases htail with | step hstep _ => exact absurd ⟨_, hstep⟩ hna

end Moist.Verified.SmallStep

