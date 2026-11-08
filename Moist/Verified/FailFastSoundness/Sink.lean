import Moist.Verified.ShapeFacts.Top

variable [sv : Moist.CEK.SemVariant]

/-! # Evaluating a terminating check before a binding

The fail-fast rewrites move a strict binding `let x = e` below a check `c`
that does not mention `x`:

  `let x = e in case c alts  ⊑  case c [let x = e in alt | alt ∈ alts]`

When `c` halts or errors in every environment this is a halting/error
refinement: if `e` errors, the target evaluates `c` and then either errors in
`c`, fails to dispatch, or reaches the moved `e`, which errors again; if `e`
diverges the source has no obligation. A binding in front of `error` can then
be dropped (`let x = e in error ⊑ error`), and a terminating binding can be
evaluated before an arbitrary one (`factRefines_swapLet`).

All statements are same-environment refinements (`FactRefines`), which the
`FactRel` congruences lift to MIR.
-/

namespace Moist.Verified.FailFast

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts

/-- `t` halts or errors in every well-formed environment of depth `d`. -/
def TerminatesAt (d : Nat) (t : Term) : Prop :=
  ∀ ρ, EnvWellFormed d ρ → d ≤ ρ.length → Errs ρ t ∨ ∃ v, Halts ρ t v

/-! ## Case dispatch -/

/-- The alternative a case frame selects for a value, with the fields it
    passes, or `none` when the dispatch fails. -/
def dispatch (alts : List Term) : CekValue → Option (Term × List CekValue)
  | .VConstr tag fields => alts[tag]?.map fun alt => (alt, fields)
  | .VCon c =>
    match constToTagAndFields c with
    | some (tag, numCtors, fields) =>
      if numCtors > 0 && alts.length > numCtors then none
      else alts[tag]?.map fun alt => (alt, fields)
    | none => none
  | _ => none

theorem step_caseScrutinee (alts : List Term) (ρ : CekEnv) (π : Stack) (v : CekValue) :
    step (.ret (.caseScrutinee alts ρ :: π) v) =
      match dispatch alts v with
      | some (alt, fields) => .compute (fields.map Frame.applyArg ++ π) ρ alt
      | none => .error := by
  cases v with
  | VConstr tag fields =>
    simp only [step, dispatch]
    cases alts[tag]? <;> rfl
  | VCon c =>
    simp only [step, dispatch]
    cases constToTagAndFields c with
    | none => rfl
    | some r =>
      obtain ⟨tag, numCtors, fields⟩ := r
      simp only []
      split
      · rfl
      · cases alts[tag]? <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl

omit sv in
theorem dispatch_map (alts : List Term) (g : Term → Term) (v : CekValue) :
    dispatch (alts.map g) v = (dispatch alts v).map fun r => (g r.1, r.2) := by
  cases v with
  | VConstr tag fields =>
    simp only [dispatch, List.getElem?_map]
    cases alts[tag]? <;> rfl
  | VCon c =>
    simp only [dispatch, List.length_map, List.getElem?_map]
    cases constToTagAndFields c with
    | none => rfl
    | some r =>
      obtain ⟨tag, numCtors, fields⟩ := r
      simp only []
      split
      · rfl
      · cases alts[tag]? <;> rfl
  | VLam _ _ => rfl
  | VDelay _ _ => rfl
  | VBuiltin _ _ _ => rfl

/-! ## Small reachability facts -/

theorem not_reaches_halt_of_error {s : State} (h : Reaches s .error) :
    ¬ ∃ v, Reaches s (.halt v) := fun ⟨_, hv⟩ => halt_not_error hv h

/-- A state on the path of `s` reaches what `s` reaches. -/
theorem obsRefines_of_reaches_right {s s' : State} (h : Reaches s s') : ObsRefines s s' :=
  obsRefines_of_reaches h (reaches_refl s') (obsRefines_refl s')

theorem obsRefines_of_left_no_halt {s₁ s₂ : State} (hhalt : ¬ ∃ v, Reaches s₁ (.halt v))
    (herr : Reaches s₂ .error) : ObsRefines s₁ s₂ :=
  ⟨fun h => absurd h hhalt, fun _ => herr⟩

/-- `(λ. error) te` never halts. -/
theorem apply_lam_error_no_halt {ρ : CekEnv} {π : Stack} {te : Term} :
    ¬ ∃ v, Reaches (.compute π ρ (.Apply (.Lam 0 .Error) te)) (.halt v) := by
  rintro ⟨u, hu⟩
  have h3 : Reaches (.compute π ρ (.Apply (.Lam 0 .Error) te))
      (.compute (.funV (.VLam .Error ρ) :: π) ρ te) := reaches_of_steps 3 rfl
  have hu' := reaches_terminal_after (.inr ⟨u, rfl⟩) h3 hu
  rcases sequence (.inr ⟨u, rfl⟩) hu' with ⟨_, h⟩ | ⟨v, _, hrest⟩
  · cases h
  · have : Reaches (.ret (.funV (.VLam .Error ρ) :: π) v) .error := reaches_of_steps 2 rfl
    exact halt_not_error hrest this

/-! ## Dropping a binding before `error` -/

theorem factRefines_letError {d : Nat} {F : CekEnv → Prop} {te : Term} :
    FactRefines d F (.Apply (.Lam 0 .Error) te) .Error := by
  intro ρ π _ _ _ _
  exact obsRefines_of_left_no_halt apply_lam_error_no_halt (reaches_of_steps 1 rfl)

/-! ## Sinking a binding into the alternatives of a terminating check -/

/-- The source, once the binding has returned `v`: the check runs under the
    extended environment. -/
private theorem source_after_binding {ρ : CekEnv} {π : Stack} {c : Term} {A : List Term}
    {v : CekValue} :
    Reaches (.ret (.funV (.VLam (.Case (renameTerm (shiftRename 1) c) A) ρ) :: π) v)
      (.compute (.caseScrutinee A (ρ.extend v) :: π) (ρ.extend v) (renameTerm (shiftRename 1) c)) :=
  reaches_of_steps 2 rfl

theorem factRefines_sinkCase {d : Nat} {F : CekEnv → Prop} {te c : Term} {A : List Term}
    (hte : closedAt d te = true) (hc : closedAt d c = true) (hA : closedAtList (d + 1) A = true)
    (hterm : TerminatesAt d c) :
    FactRefines d F (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) c) A)) te)
      (.Case c (A.map fun a => .Apply (.Lam 0 a) te)) := by
  intro ρ π henv hlen hπ _
  -- the source reaches the evaluation of the binding
  have hsrc : Reaches (.compute π ρ (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) c) A)) te))
      (.compute (.funV (.VLam (.Case (renameTerm (shiftRename 1) c) A) ρ) :: π) ρ te) :=
    reaches_of_steps 3 rfl
  -- after the binding returns `v`, the shifted check behaves like the check
  have shifted : ∀ v, Halts ρ te v →
      ObsRefines (.compute (.caseScrutinee A (ρ.extend v) :: π) (ρ.extend v)
          (renameTerm (shiftRename 1) c))
        (.compute (.caseScrutinee A (ρ.extend v) :: π) ρ c) := by
    intro v hv
    have hvwf := halts_wellFormed henv hlen hte hv
    have hframe : StackWellFormed (.caseScrutinee A (ρ.extend v) :: π) :=
      .cons (.caseScrutinee (envWellFormed_extend d henv hlen hvwf)
        (by simp [CekEnv.extend, CekEnv.length]; omega) hA) hπ
    exact (obsEq_shift v henv hframe hc).2
  -- the source cannot halt when the check, run with the source's alternatives, errors
  have no_halt : (∀ v, Halts ρ te v →
        Reaches (.compute (.caseScrutinee A (ρ.extend v) :: π) ρ c) .error) →
      ¬ ∃ u, Reaches (.compute π ρ (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) c) A)) te))
        (.halt u) := by
    rintro herr ⟨u, hu⟩
    have hu' := reaches_terminal_after (.inr ⟨u, rfl⟩) hsrc hu
    rcases sequence (.inr ⟨u, rfl⟩) hu' with ⟨_, h⟩ | ⟨v, hv, hrest⟩
    · cases h
    · have hrest' := reaches_terminal_after (.inr ⟨u, rfl⟩) source_after_binding hrest
      obtain ⟨u', hu''⟩ := (shifted v hv).halt ⟨u, hrest'⟩
      exact halt_not_error hu'' (herr v hv)
  rcases hterm ρ henv hlen with herrs | ⟨w, hw⟩
  · -- the check errors
    refine obsRefines_of_left_no_halt (no_halt fun v _ => errs_on_stack herrs _) ?_
    exact reaches_trans (reaches_of_steps 1 rfl) (errs_on_stack herrs _)
  · -- the check returns `w`
    have hcheck : ∀ (alts : List Term) (ρ' : CekEnv),
        Reaches (.compute (.caseScrutinee alts ρ' :: π) ρ c)
          (step (.ret (.caseScrutinee alts ρ' :: π) w)) := fun alts ρ' =>
      reaches_trans (halts_on_stack hw _) (reaches_of_steps 1 rfl)
    cases hd : dispatch A w with
    | none =>
      refine obsRefines_of_left_no_halt (no_halt fun v _ => ?_) ?_
      · have := hcheck A (ρ.extend v)
        rw [step_caseScrutinee, hd] at this
        exact this
      · have := hcheck (A.map fun a => .Apply (.Lam 0 a) te) ρ
        rw [step_caseScrutinee, dispatch_map, hd] at this
        exact reaches_trans (reaches_of_steps 1 rfl) this
    | some r =>
      obtain ⟨a, fields⟩ := r
      -- the target evaluates the moved binding in front of the selected alternative
      have htgt : Reaches (.compute π ρ (.Case c (A.map fun a => .Apply (.Lam 0 a) te)))
          (.compute (.funV (.VLam a ρ) :: (fields.map Frame.applyArg ++ π)) ρ te) := by
        have := hcheck (A.map fun a => .Apply (.Lam 0 a) te) ρ
        rw [step_caseScrutinee, dispatch_map, hd] at this
        exact reaches_trans (reaches_of_steps 1 rfl) (reaches_trans this (reaches_of_steps 3 rfl))
      refine obsRefines_of_reaches hsrc htgt ?_
      apply obsRefines_of_continuation
      intro v hv
      refine obsRefines_of_reaches source_after_binding (reaches_of_steps 1 rfl) ?_
      refine obsRefines_trans (shifted v hv) ?_
      apply obsRefines_of_reaches_right
      have := hcheck A (ρ.extend v)
      rw [step_caseScrutinee, hd] at this
      exact this

/-- The sinking rule with the alternatives that are `error` dropped. -/
theorem factRefines_sinkCase_drop {d : Nat} {F : CekEnv → Prop} {te c : Term} {A : List Term}
    (hte : closedAt d te = true) (hc : closedAt d c = true) (hA : closedAtList (d + 1) A = true)
    (hterm : TerminatesAt d c) :
    FactRefines d F (.Apply (.Lam 0 (.Case (renameTerm (shiftRename 1) c) A)) te)
      (.Case c (A.map fun a => if a = .Error then .Error else .Apply (.Lam 0 a) te)) := by
  refine (factRefines_sinkCase hte hc hA hterm).trans ?_
  have hA' : closedAtList d (A.map fun a => .Apply (.Lam 0 a) te) = true := by
    clear hterm
    induction A with
    | nil => simp [closedAtList]
    | cons a A ih =>
      simp only [closedAtList, Bool.and_eq_true] at hA
      simp only [List.map_cons, closedAtList, closedAt, hA.1, hte, Bool.and_self, Bool.true_and]
      exact ih hA.2
  refine factRefines_case (FactRefines.refl _ _ _) ?_ hc hA'
  clear hA hA' hterm
  induction A with
  | nil => trivial
  | cons a A ih =>
    refine ⟨?_, ih⟩
    by_cases ha : a = .Error
    · subst ha; simp only [if_true]; exact factRefines_letError
    · simp only [ha, if_false]; exact FactRefines.refl _ _ _

end Moist.Verified.FailFast
