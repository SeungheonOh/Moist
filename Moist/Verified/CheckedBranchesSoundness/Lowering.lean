import Moist.Verified.CheckedBranchesSoundness.Builtins
import Moist.MIR.Optimize.Advanced.CheckedBranches

variable [sv : Moist.CEK.SemVariant]

/-! # Delayed list choices as a discriminator

`force (chooseList l (delay e) (delay n))` becomes `case (nullList l) [n, e]`.
Both evaluate the selector (a builtin state, by the recorded facts), then `l`,
and fail exactly when `l` is not a list; otherwise both continue with the
body of the selected branch in the same environment.
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

theorem delayedChoice_obsRefines {ρ : CekEnv} {π : Stack} {ts ti tem tne : Term}
    (hsel : Halts ρ ts (.VBuiltin .ChooseList [] (.more .argV (.more .argV (.one .argV))))) :
    ObsRefines (.compute π ρ (.Force (.Apply (.Apply (.Apply ts ti) (.Delay tem)) (.Delay tne))))
      (.compute π ρ (.Case (.Apply (.Force (.Builtin .NullList)) ti) [tne, tem])) := by
  refine obsRefines_of_reaches
    (s₁' := .compute (.funV (.VBuiltin .ChooseList [] (.more .argV (.more .argV (.one .argV)))) ::
      .arg (.Delay tem) ρ :: .arg (.Delay tne) ρ :: .force :: π) ρ ti)
    (s₂' := .compute (.funV (.VBuiltin .NullList [] (.one .argV)) :: .caseScrutinee [tne, tem] ρ :: π) ρ ti)
    ?_ ?_ ?_
  · exact reaches_trans (reaches_of_steps 4 rfl)
      (reaches_trans (halts_on_stack hsel _) (reaches_of_steps 1 rfl))
  · exact reaches_trans (reaches_of_steps 2 rfl)
      (reaches_trans (halts_on_stack (forced_builtin_halts ρ .NullList rfl) _) (reaches_of_steps 1 rfl))
  · apply obsRefines_of_continuation
    intro v _
    have hc := chooseList_eval tne ρ (.VDelay tem ρ) v
    have hn := nullList_eval v
    cases hnull : nullResult v with
    | none =>
      rw [hnull] at hn
      rw [chooseResult_none hnull] at hc
      exact obsRefines_of_errors
        ⟨7, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc]⟩
        ⟨1, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hn]⟩
    | some b =>
      rw [hnull] at hn
      rw [chooseResult_of_null hnull] at hc
      cases b with
      | true =>
        exact obsRefines_of_reaches (s₁' := .compute π ρ tem) (s₂' := .compute π ρ tem)
          ⟨8, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc]⟩
          ⟨2, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hn, constToTagAndFields]⟩
          (obsRefines_refl _)
      | false =>
        exact obsRefines_of_reaches (s₁' := .compute π ρ tne) (s₂' := .compute π ρ tne)
          ⟨8, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hc]⟩
          ⟨2, by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hn, constToTagAndFields]⟩
          (obsRefines_refl _)


theorem lowerTotalExpr_nullCase {env : List VarId} {input ne em : Expr} {ti tne tem : Term}
    (hti : lowerTotalExpr env input = some ti) (htne : lowerTotalExpr env ne = some tne)
    (htem : lowerTotalExpr env em = some tem) :
    lowerTotalExpr env (.Case (.App (.Force (.Builtin .NullList)) input) [ne, em]) =
      some (.Case (.Apply (.Force (.Builtin .NullList)) ti) [tne, tem]) := by
  rw [MIR.lowerTotalExpr_case_of_list, MIR.lowerTotalExpr_app, MIR.lowerTotalExpr_force,
    lowerTotalExpr_builtin, hti]
  simp only [Option.map_some]
  rw [MIR.lowerTotalExprList_cons, htne, MIR.lowerTotalExprList_cons, htem, MIR.lowerTotalExprList_nil]
  rfl

/-- The delayed choice rewrite under the facts of the walk. -/
theorem delayedChoice_factRel {G : VarId → Prop} {Γ : List (VarId × Expr)}
    {sel input input' em em' ne ne' : Expr}
    (hsel : resolveHead 64 Γ sel = .Force (.Force (.Builtin .ChooseList)))
    (hin : FactRel G Produces Γ input input') (hne : FactRel G Produces Γ ne ne')
    (hem : FactRel G Produces Γ em em') :
    FactRel G Produces Γ (.Force (.App (.App (.App sel input) (.Delay em)) (.Delay ne)))
      (.Case (.App (.Force (.Builtin .NullList)) input') [ne', em']) := by
  intro env t hG hd hfresh hk hs hlow
  simp only [freshIn, Bool.and_eq_true] at hfresh
  obtain ⟨⟨⟨_, hfi⟩, hfem⟩, hfne⟩ := hfresh
  obtain ⟨tx, htx, rfl⟩ := lowerTotalExpr_force_some hlow
  obtain ⟨ta, tdn, hta, htdn, rfl⟩ := lowerTotalExpr_app_some htx
  obtain ⟨tne, htne, rfl⟩ := lowerTotalExpr_delay_some htdn
  obtain ⟨tb, tde, htb, htde, rfl⟩ := lowerTotalExpr_app_some hta
  obtain ⟨tem, htem, rfl⟩ := lowerTotalExpr_delay_some htde
  obtain ⟨ts, ti, hts, hti, rfl⟩ := lowerTotalExpr_app_some htb
  obtain ⟨ti', hti', hri⟩ := hin env ti hG hd hfi hk hs hti
  obtain ⟨tne', htne', hrne⟩ := hne env tne hG hd hfne hk hs htne
  obtain ⟨tem', htem', hrem⟩ := hem env tem hG hd hfem hk hs htem
  refine ⟨_, lowerTotalExpr_nullCase hti' htne' htem', ?_⟩
  refine FactRefines.trans (t₂ := .Case (.Apply (.Force (.Builtin .NullList)) ti) [tne, tem]) ?_ ?_
  · intro ρ π _ _ _ hF
    exact delayedChoice_obsRefines (resolveHead_forced_halts 64 Γ sel hsel rfl hF hd hts)
  · have closedTi := MIR.lowerTotalExpr_closedAt hti
    have closedTi' := MIR.lowerTotalExpr_closedAt hti'
    refine factRefines_case (factRefines_apply (FactRefines.refl _ _ _) hri (by simp [closedAt])
      closedTi) ⟨hrne, hrem, trivial⟩ (by simp [closedAt, closedTi']) ?_
    simp [closedAtList, MIR.lowerTotalExpr_closedAt htne, MIR.lowerTotalExpr_closedAt htem]

theorem beq_chooseList {x : Expr} (h : (x == Expr.Force (.Force (.Builtin .ChooseList))) = true) :
    x = .Force (.Force (.Builtin .ChooseList)) := by
  cases x with
  | Force e =>
    cases e with
    | Force e' =>
      cases e' with
      | Builtin b' =>
        have : (b' == BuiltinFun.ChooseList) = true := h
        cases b' <;> first | rfl | cases this
      | _ => cases h
    | _ => cases h
  | _ => cases h

theorem lowerDelayedChoicesWalk_factRel (e : Expr) (Γ : List (VarId × Expr)) :
    FactRel (fun _ => True) Produces Γ e (lowerDelayedChoicesWalk Γ e) := by
  match e with
  | .Force body =>
    by_cases hshape : ∃ sel input em ne, body = .App (.App (.App sel input) (.Delay em)) (.Delay ne)
    · obtain ⟨sel, input, em, ne, rfl⟩ := hshape
      rw [lowerDelayedChoicesWalk.eq_1]
      split
      · rename_i hcond
        exact delayedChoice_factRel (beq_chooseList hcond) (lowerDelayedChoicesWalk_factRel input Γ)
          (lowerDelayedChoicesWalk_factRel ne Γ) (lowerDelayedChoicesWalk_factRel em Γ)
      · exact (lowerDelayedChoicesWalk_factRel _ Γ).force
    · rw [lowerDelayedChoicesWalk.eq_2 _ _ (fun s i e n h => hshape ⟨s, i, e, n, h⟩)]
      exact (lowerDelayedChoicesWalk_factRel body Γ).force
  | .Let [] body =>
    rw [lowerDelayedChoicesWalk]
    exact (lowerDelayedChoicesWalk_factRel body Γ).congr_left
      (fun env => lowerTotalExpr_let_nil env body) (fun avoid => freshIn_let_nil avoid body)
  | .Let ((x, r, er) :: rest) body =>
    rw [lowerDelayedChoicesWalk]
    exact (FactRel.let_single (lowerDelayedChoicesWalk Γ r) trivial (.inr rfl)
      (lowerDelayedChoicesWalk_factRel r Γ)
      (lowerDelayedChoicesWalk_factRel (.Let rest body) _)
      (fun _ _ _ _ _ _ hp => hp)).congr_left (fun env => lowerTotalExpr_let_cons env _ _ _)
      (fun avoid => freshIn_let_cons avoid _ _ _)
  | .Lam x b => rw [lowerDelayedChoicesWalk]; exact (lowerDelayedChoicesWalk_factRel b Γ).lam trivial
  | .Fix f b =>
    rw [lowerDelayedChoicesWalk]
    cases b with
    | Lam x inner =>
      rw [lowerDelayedChoicesWalk]
      exact (lowerDelayedChoicesWalk_factRel inner Γ).fix_lam trivial trivial (fun _ _ => trivial)
    | _ =>
      intro env t _ _ _ _ _ hlow
      rw [MIR.lowerTotalExpr_fix_nonlam_none env f _ (by intros; simp)] at hlow
      cases hlow
  | .App f a =>
    rw [lowerDelayedChoicesWalk]
    exact (lowerDelayedChoicesWalk_factRel f Γ).app (lowerDelayedChoicesWalk_factRel a Γ)
  | .Delay b => rw [lowerDelayedChoicesWalk]; exact (lowerDelayedChoicesWalk_factRel b Γ).delay
  | .Constr tag fields =>
    rw [lowerDelayedChoicesWalk]
    exact FactRel.constr (listRel_attach_map fields _ fun c _ => lowerDelayedChoicesWalk_factRel c Γ)
  | .Case scrutinee alternatives =>
    rw [lowerDelayedChoicesWalk]
    exact FactRel.case (lowerDelayedChoicesWalk_factRel scrutinee Γ)
      (listRel_attach_map alternatives _ fun c _ => lowerDelayedChoicesWalk_factRel c Γ)
  | .Var _ | .Lit _ | .Builtin _ | .Error => rw [lowerDelayedChoicesWalk]; exact FactRel.refl _ _ _ _
termination_by exprSize e
decreasing_by
  all_goals first
    | (subst_vars; simp only [exprSize, exprSizeBinds]; omega)
    | (simp only [exprSize, exprSizeBinds]; have := exprSize_pos r; omega)
    | (have := exprSize_lt_of_mem (by assumption); simp only [exprSize]; omega)

end Moist.Verified.ShapeFacts

namespace Moist.Verified.MIR

open Moist.MIR Moist.MIR.Advanced Moist.Verified.ShapeFacts

/-- Lowering delayed list choices to a discriminator refines its input. -/
theorem lowerDelayedListChoices_refines (e : Expr) : MIRCtxRefines e (lowerDelayedListChoices e) := by
  unfold lowerDelayedListChoices
  simp only
  split
  · exact mirCtxRefines_trans (Hygiene.uniqueOptimizationBinders_refines e)
      (mirCtxRefines_of_factRel (by assumption) (fun _ _ => trivial) (fun _ _ => trivial)
        (lowerDelayedChoicesWalk_factRel _ []))
  · exact Hygiene.uniqueOptimizationBinders_refines e

end Moist.Verified.MIR
