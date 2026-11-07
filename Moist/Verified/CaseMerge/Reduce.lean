import Moist.Verified.CaseMerge.Syntax
import Moist.Verified.ContinuationRefinement
import Moist.Verified.StepWellFormed

/-! # Case on a literal constructor

`reduceConstructorCase tag fields alts` binds the non-atomic fields in order
and applies the selected alternative to the atomic arguments. In the same
well-formed environment and on the same stack its lowering is observed no
less than the lowering of `Case (Constr tag fields) alts` (`reduce_correct`).
The proof hoists one non-atomic field at a time out of the constructor
(`sameRef_hoist`) and finishes with the all-atom case (`sameRef_select`).
-/

namespace Moist.Verified.CaseMerge

open Moist.CEK
open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (closedAt closedAtList renameTerm renameTermList shiftRename)
open Moist.Verified.Equivalence (steps Reaches steps_trans steps_error ListRel ObsRefinesK
  listRel_reverse)
open Moist.Verified.Contextual (ObsRefines)
open Moist.Verified.Contextual.SoundnessRefines (EnvRefinesK ValueRefinesK StackRefK)
open Moist.Verified.BetaValueRefines (EnvWellFormed StackWellFormed ValueWellFormed
  envWellFormed_lookup envWellFormed_extend envRefinesK_refl stackRefK_refl valueRefinesK_refl)
open Moist.Verified.StepWellFormed (StateWellFormed halt_value_wf)
open Moist.Verified.MIR (IsValueTerm valueOf valueTerm_rel lowerTotalExprList
  lowerTotalExprList_nil lowerTotalExprList_cons lowerTotalExprList_append
  lowerTotalExpr_case_of_list lowerTotalExpr_constr_of_list lowerTotalExprList_prepend_unused
  lowerTotalExprList_valueTerms lowerTotalExpr_wrapLet lowerTotalExpr_closedAt
  lowerTotalList_closedAtList stackRefK_constrField_shift stackRefK_case_shift)

/-! ## Observations on one environment -/

/-- Same-environment, same-stack observational refinement at depth `d`. -/
def SameRef (d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ ρ π, EnvWellFormed d ρ → d ≤ ρ.length → StackWellFormed π →
    ObsRefines (.compute π ρ t₁) (.compute π ρ t₂)

theorem obsRefines_refl (s : State) : ObsRefines s s := ⟨id, id⟩

theorem obsRefines_trans {a b c : State} (h₁ : ObsRefines a b) (h₂ : ObsRefines b c) :
    ObsRefines a c :=
  ⟨fun h => h₂.halt (h₁.halt h), fun h => h₂.error (h₁.error h)⟩

theorem sameRef_trans {d : Nat} {a b c : Term} (h₁ : SameRef d a b) (h₂ : SameRef d b c) :
    SameRef d a c :=
  fun ρ π hρ hlen hπ => obsRefines_trans (h₁ ρ π hρ hlen hπ) (h₂ ρ π hρ hlen hπ)

theorem obsRefines_of_steps {s₁ s₂ : State} (n m : Nat)
    (h : ObsRefines (steps n s₁) (steps m s₂)) : ObsRefines s₁ s₂ := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := h.halt ⟨v, (AdvancedRefinement.reaches_after_prefix n rfl).mp hv⟩
    exact ⟨w, (AdvancedRefinement.reaches_after_prefix m rfl).mpr hw⟩
  · intro he
    exact (AdvancedRefinement.reaches_after_prefix m rfl).mpr
      (h.error ((AdvancedRefinement.reaches_after_prefix n rfl).mp he))

theorem obsRefines_of_obsRefinesK {s₁ s₂ : State} (h : ∀ k, ObsRefinesK k s₁ s₂) :
    ObsRefines s₁ s₂ := by
  constructor
  · rintro ⟨v, n, hn⟩
    exact (h n).1 v ⟨n, Nat.le_refl _, hn⟩
  · rintro ⟨n, hn⟩
    exact (h n).2 n (Nat.le_refl _) hn

theorem obsRefines_error_left {s₁ s₂ : State} (h₁ : Reaches s₁ .error) (h₂ : Reaches s₂ .error) :
    ObsRefines s₁ s₂ :=
  ⟨fun ⟨_, hv⟩ => (InlineSoundness.StrictOcc.halt_excludes_error hv h₁).elim, fun _ => h₂⟩

/-- Related continuations give related computations of one term. -/
theorem obs_compute_of_returns {π₁ π₂ : Stack}
    (h : ∀ v, ObsRefines (.ret π₁ v) (.ret π₂ v)) (ρ : CekEnv) (t : Term) :
    ObsRefines (.compute π₁ ρ t) (.compute π₂ ρ t) := by
  constructor
  · rintro ⟨v, hv⟩
    rcases InlineSoundness.Frontier.outcome_of_terminal (.inr ⟨v, rfl⟩) hv with
      ⟨w, hw⟩ | herr
    · obtain ⟨n₁, h₁⟩ := Purity.compute_to_ret_from_halt ρ t w π₁ hw
      obtain ⟨n₂, h₂⟩ := Purity.compute_to_ret_from_halt ρ t w π₂ hw
      have := (AdvancedRefinement.reaches_after_prefix n₁ rfl).mp hv
      rw [h₁] at this
      obtain ⟨u, hu⟩ := (h w).halt ⟨v, this⟩
      exact ⟨u, (AdvancedRefinement.reaches_after_prefix n₂ rfl).mpr (by rw [h₂]; exact hu)⟩
    · exact (InlineSoundness.StrictOcc.halt_excludes_error hv
        (InlineSoundness.StrictOcc.error_on_all_stacks herr π₁)).elim
  · intro he
    rcases InlineSoundness.Frontier.outcome_of_terminal (.inl rfl) he with ⟨w, hw⟩ | herr
    · obtain ⟨n₁, h₁⟩ := Purity.compute_to_ret_from_halt ρ t w π₁ hw
      obtain ⟨n₂, h₂⟩ := Purity.compute_to_ret_from_halt ρ t w π₂ hw
      have := (AdvancedRefinement.reaches_after_prefix n₁ rfl).mp he
      rw [h₁] at this
      exact (AdvancedRefinement.reaches_after_prefix n₂ rfl).mpr (by rw [h₂]; exact (h w).error this)
    · exact InlineSoundness.StrictOcc.error_on_all_stacks herr π₂

/-- `obs_compute_of_returns` needing related continuations only on well-formed values. -/
theorem obs_compute_of_returns_wf {π₁ π₂ : Stack} {ρ : CekEnv} {t : Term} {d : Nat}
    (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (ht : closedAt d t = true)
    (h : ∀ v, ValueWellFormed v → ObsRefines (.ret π₁ v) (.ret π₂ v)) :
    ObsRefines (.compute π₁ ρ t) (.compute π₂ ρ t) := by
  have hwf : StateWellFormed (.compute [] ρ t) := .compute .nil hρ hlen ht
  constructor
  · rintro ⟨v, hv⟩
    rcases InlineSoundness.Frontier.outcome_of_terminal (.inr ⟨v, rfl⟩) hv with
      ⟨w, hw⟩ | herr
    · obtain ⟨n₁, h₁⟩ := Purity.compute_to_ret_from_halt ρ t w π₁ hw
      obtain ⟨n₂, h₂⟩ := Purity.compute_to_ret_from_halt ρ t w π₂ hw
      have := (AdvancedRefinement.reaches_after_prefix n₁ rfl).mp hv
      rw [h₁] at this
      obtain ⟨n, hn⟩ := hw
      obtain ⟨u, hu⟩ := (h w (halt_value_wf hwf hn)).halt ⟨v, this⟩
      exact ⟨u, (AdvancedRefinement.reaches_after_prefix n₂ rfl).mpr (by rw [h₂]; exact hu)⟩
    · exact (InlineSoundness.StrictOcc.halt_excludes_error hv
        (InlineSoundness.StrictOcc.error_on_all_stacks herr π₁)).elim
  · intro he
    rcases InlineSoundness.Frontier.outcome_of_terminal (.inl rfl) he with ⟨w, hw⟩ | herr
    · obtain ⟨n₁, h₁⟩ := Purity.compute_to_ret_from_halt ρ t w π₁ hw
      obtain ⟨n₂, h₂⟩ := Purity.compute_to_ret_from_halt ρ t w π₂ hw
      have := (AdvancedRefinement.reaches_after_prefix n₁ rfl).mp he
      rw [h₁] at this
      obtain ⟨n, hn⟩ := hw
      exact (AdvancedRefinement.reaches_after_prefix n₂ rfl).mpr
        (by rw [h₂]; exact (h w (halt_value_wf hwf hn)).error this)
    · exact InlineSoundness.StrictOcc.error_on_all_stacks herr π₂

theorem step_applyArg (v w : CekValue) (π : Stack) :
    step (.ret (.applyArg v :: π) w) = step (.ret (.funV w :: π) v) := by
  cases w <;> rfl

/-- Applying one function value to one argument on related continuations. -/
theorem obs_funV_tail {L R : Stack} (h : ∀ u, ObsRefines (.ret L u) (.ret R u))
    (w v : CekValue) :
    ObsRefines (step (.ret (.funV w :: L) v)) (step (.ret (.funV w :: R) v)) := by
  cases w with
  | VLam b ρ' => exact obs_compute_of_returns h _ _
  | VBuiltin b args ea =>
    simp only [step]
    cases ea.head with
    | argQ => exact obsRefines_refl _
    | argV =>
      simp only []
      cases ea.tail with
      | some rest => exact h _
      | none =>
        simp only []
        cases evalBuiltin b (v :: args) with
        | some x => exact h x
        | none => exact obsRefines_refl _
  | VCon _ => exact obsRefines_refl _
  | VDelay _ _ => exact obsRefines_refl _
  | VConstr _ _ => exact obsRefines_refl _

/-! ## Evaluation of value terms -/

theorem isValueTerm_step {d : Nat} {ρ : CekEnv} (hρ : EnvWellFormed d ρ) {t : Term}
    (ht : IsValueTerm d t) : ∀ π, step (.compute π ρ t) = .ret π (valueOf ρ t) := by
  intro π
  match t, ht with
  | .Var n, ⟨hn, hnd⟩ =>
    obtain ⟨v, hv, _⟩ := envWellFormed_lookup d hρ hn hnd
    simp only [step, valueOf, hv, Option.getD_some]
  | .Constant (c, _), _ => rfl
  | .Builtin b, _ => rfl
  | .Lam _ b, _ => rfl

theorem isValueTerm_wf {d : Nat} {ρ : CekEnv} (hρ : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    {t : Term} (ht : IsValueTerm d t) : ValueWellFormed (valueOf ρ t) := by
  match t, ht with
  | .Var n, ⟨hn, hnd⟩ =>
    obtain ⟨v, hv, hwf⟩ := envWellFormed_lookup d hρ hn hnd
    simp only [valueOf, hv, Option.getD_some]; exact hwf
  | .Constant (c, _), _ => exact .vcon c
  | .Builtin b, _ => exact .vbuiltin b _ .nil
  | .Lam _ b, hb => exact .vlam hρ hlen hb

theorem steps_constrField_values {tag : Nat} {ρ : CekEnv} :
    ∀ (rest : List Term), (∀ a ∈ rest, ∀ π, step (.compute π ρ a) = .ret π (valueOf ρ a)) →
    ∀ (done : List CekValue) (v : CekValue) (π : Stack),
      steps (2 * rest.length + 1) (.ret (.constrField tag done rest ρ :: π) v) =
        .ret π (.VConstr tag ((v :: done).reverse ++ rest.map (valueOf ρ)))
  | [], _, done, v, π => by simp [steps, step]
  | a :: rest, hrest, done, v, π => by
    have h2 : steps 2 (.ret (.constrField tag done (a :: rest) ρ :: π) v) =
        .ret (.constrField tag (v :: done) rest ρ :: π) (valueOf ρ a) := by
      show step (.compute (.constrField tag (v :: done) rest ρ :: π) ρ a) = _
      rw [hrest a (.head _)]
    rw [show 2 * (a :: rest).length + 1 = 2 + (2 * rest.length + 1) by simp; omega, steps_trans,
      h2, steps_constrField_values rest (fun b hb => hrest b (.tail _ hb))]
    simp

theorem steps_constr_values {tag : Nat} {ρ : CekEnv} (args : List Term)
    (hargs : ∀ a ∈ args, ∀ π, step (.compute π ρ a) = .ret π (valueOf ρ a)) (π : Stack) :
    ∃ n, steps n (.compute π ρ (.Constr tag args)) = .ret π (.VConstr tag (args.map (valueOf ρ))) := by
  cases args with
  | nil => exact ⟨1, rfl⟩
  | cons a rest =>
    refine ⟨2 + (2 * rest.length + 1), ?_⟩
    have h2 : steps 2 (.compute π ρ (.Constr tag (a :: rest))) =
        .ret (.constrField tag [] rest ρ :: π) (valueOf ρ a) := by
      show step (.compute (.constrField tag [] rest ρ :: π) ρ a) = _
      rw [hargs a (.head _)]
    rw [steps_trans, h2, steps_constrField_values rest (fun b hb => hargs b (.tail _ hb))]
    simp

/-- Evaluating the value prefix of a constructor up to its first other field. -/
theorem steps_constr_prefix {tag : Nat} {ρ : CekEnv} :
    ∀ (pre : List Term), (∀ p ∈ pre, ∀ π, step (.compute π ρ p) = .ret π (valueOf ρ p)) →
    ∀ (f : Term) (post : List Term) (π : Stack),
      steps (2 * pre.length + 1) (.compute π ρ (.Constr tag (pre ++ f :: post))) =
        .compute (.constrField tag (pre.map (valueOf ρ)).reverse post ρ :: π) ρ f := by
  intro pre hpre f post π
  suffices h : ∀ (ps : List Term), (∀ p ∈ ps, ∀ π, step (.compute π ρ p) = .ret π (valueOf ρ p)) →
      ∀ (done : List CekValue) (v : CekValue),
        steps (2 * ps.length + 1) (.ret (.constrField tag done (ps ++ f :: post) ρ :: π) v) =
          .compute (.constrField tag ((ps.map (valueOf ρ)).reverse ++ v :: done) post ρ :: π) ρ f by
    cases pre with
    | nil => rfl
    | cons p ps =>
      have h2 : steps 2 (.compute π ρ (.Constr tag (p :: (ps ++ f :: post)))) =
          .ret (.constrField tag [] (ps ++ f :: post) ρ :: π) (valueOf ρ p) := by
        show step (.compute (.constrField tag [] (ps ++ f :: post) ρ :: π) ρ p) = _
        rw [hpre p (.head _)]
      rw [show 2 * (p :: ps).length + 1 = 2 + (2 * ps.length + 1) by simp; omega, steps_trans,
        List.cons_append, h2, h ps (fun q hq => hpre q (.tail _ hq))]
      simp
  intro ps
  induction ps with
  | nil => intro _ done v; rfl
  | cons p ps ih =>
    intro hps done v
    have h2 : steps 2 (.ret (.constrField tag done (p :: (ps ++ f :: post)) ρ :: π) v) =
        .ret (.constrField tag (v :: done) (ps ++ f :: post) ρ :: π) (valueOf ρ p) := by
      show step (.compute (.constrField tag (v :: done) (ps ++ f :: post) ρ :: π) ρ p) = _
      rw [hps p (.head _)]
    rw [show 2 * (p :: ps).length + 1 = 2 + (2 * ps.length + 1) by simp; omega, steps_trans,
      List.cons_append, h2, ih (fun q hq => hps q (.tail _ hq))]
    simp

theorem steps_foldl_apply {ρ : CekEnv} :
    ∀ (args : List Term) (f : Term) (π : Stack),
      steps args.length (.compute π ρ (args.foldl Term.Apply f)) =
        .compute (args.map (fun a => Frame.arg a ρ) ++ π) ρ f
  | [], f, π => rfl
  | a :: args, f, π => by
    rw [List.foldl_cons, List.length_cons, steps_trans, steps_foldl_apply args (.Apply f a) π]
    rfl

/-- Pending applied values against pending atomic arguments. -/
theorem obs_applyArg_arg {ρ : CekEnv} :
    ∀ (args : List Term), (∀ a ∈ args, ∀ π, step (.compute π ρ a) = .ret π (valueOf ρ a)) →
    ∀ {L R : Stack}, (∀ u, ObsRefines (.ret L u) (.ret R u)) →
    ∀ w, ObsRefines (.ret ((args.map (valueOf ρ)).map Frame.applyArg ++ L) w)
      (.ret (args.map (fun a => Frame.arg a ρ) ++ R) w)
  | [], _, _, _, h, w => h w
  | a :: args, hargs, L, R, h, w => by
    have ih := obs_applyArg_arg args (fun b hb => hargs b (.tail _ hb)) h
    simp only [List.map_cons, List.cons_append]
    refine obsRefines_of_steps 1 3 ?_
    have hR : steps 3 (.ret (.arg a ρ :: (args.map (fun a => Frame.arg a ρ) ++ R)) w) =
        step (.ret (.funV w :: (args.map (fun a => Frame.arg a ρ) ++ R)) (valueOf ρ a)) := by
      show step (step (.compute (.funV w :: (args.map (fun a => Frame.arg a ρ) ++ R)) ρ a)) = _
      rw [hargs a (.head _)]
    rw [hR]
    show ObsRefines (step _) _
    rw [step_applyArg]
    exact obs_funV_tail ih w _

/-! ## The three steps -/

/-- Constructor fields that are all values: selecting the alternative directly. -/
theorem sameRef_select {d tag : Nat} {args alts : List Term}
    (hargs : ∀ a ∈ args, IsValueTerm d a) :
    SameRef d (.Case (.Constr tag args) alts)
      (match alts[tag]? with | some a => args.foldl Term.Apply a | none => .Error) := by
  intro ρ π hρ hlen hπ
  have hstep := fun a ha => isValueTerm_step hρ (hargs a ha)
  obtain ⟨n, hn⟩ := steps_constr_values (tag := tag) args hstep (.caseScrutinee alts ρ :: π)
  have hL : steps (1 + n + 1) (.compute π ρ (.Case (.Constr tag args) alts)) =
      step (.ret (.caseScrutinee alts ρ :: π) (.VConstr tag (args.map (valueOf ρ)))) := by
    rw [steps_trans, steps_trans]
    show steps 1 (steps n (.compute (.caseScrutinee alts ρ :: π) ρ (.Constr tag args))) = _
    rw [hn]; rfl
  refine obsRefines_of_steps (1 + n + 1) 0 ?_
  rw [hL]
  show ObsRefines _ (State.compute π ρ _)
  cases h : alts[tag]? with
  | none =>
    simp only [step, h]
    exact obsRefines_error_left ⟨0, rfl⟩ ⟨1, rfl⟩
  | some alt =>
    simp only [step, h]
    refine obsRefines_of_steps 0 args.length ?_
    rw [steps_foldl_apply]
    exact obs_compute_of_returns
      (obs_applyArg_arg args hstep (fun u => obsRefines_refl _)) ρ alt

/-- `let`-body congruence. -/
theorem sameRef_let_body {d : Nat} {b₁ b₂ r : Term} (hr : closedAt d r = true)
    (h : SameRef (d + 1) b₁ b₂) :
    SameRef d (.Apply (.Lam 0 b₁) r) (.Apply (.Lam 0 b₂) r) := by
  intro ρ π hρ hlen hπ
  refine obsRefines_of_steps 3 3 ?_
  show ObsRefines (.compute (.funV (.VLam b₁ ρ) :: π) ρ r) (.compute (.funV (.VLam b₂ ρ) :: π) ρ r)
  refine obs_compute_of_returns_wf hρ hlen hr fun v hv => ?_
  refine obsRefines_of_steps 1 1 ?_
  exact h _ _ (envWellFormed_extend d hρ hlen hv) (by simp [CekEnv.extend, CekEnv.length]; omega) hπ

/-- One non-value field is bound by a `let` around the case. -/
theorem sameRef_hoist {d tag : Nat} {pre rest alts : List Term} {f : Term}
    (hpre : ∀ p ∈ pre, IsValueTerm d p) (hf : closedAt d f = true)
    (hrest : closedAtList d rest = true) (halts : closedAtList d alts = true) :
    SameRef d (.Case (.Constr tag (pre ++ f :: rest)) alts)
      (.Apply (.Lam 0 (.Case (.Constr tag (renameTermList (shiftRename 1) pre ++
          .Var 1 :: renameTermList (shiftRename 1) rest)) (renameTermList (shiftRename 1) alts))) f) := by
  intro ρ π hρ hlen hπ
  have hstep := fun p hp => isValueTerm_step hρ (hpre p hp)
  refine obsRefines_of_steps (1 + (2 * pre.length + 1)) 3 ?_
  rw [steps_trans]
  show ObsRefines (steps _ (.compute (.caseScrutinee alts ρ :: π) ρ _)) _
  rw [steps_constr_prefix pre hstep]
  show ObsRefines _ (.compute (.funV (.VLam _ ρ) :: π) ρ f)
  refine obs_compute_of_returns_wf hρ hlen hf fun v hv => ?_
  -- The right side re-evaluates the shifted prefix, then the bound variable.
  have hrel : ∀ i, ∀ p ∈ pre,
      (∀ π, step (.compute π (ρ.extend v) (renameTerm (shiftRename 1) p)) =
        .ret π (valueOf (ρ.extend v) (renameTerm (shiftRename 1) p))) ∧
      ValueRefinesK i (valueOf ρ p) (valueOf (ρ.extend v) (renameTerm (shiftRename 1) p)) :=
    fun i p hp => let h := valueTerm_rel (hpre p hp) v (envRefinesK_refl (k := i) hρ); ⟨h.2.1, h.2.2⟩
  have hpre' : ∀ p ∈ renameTermList (shiftRename 1) pre,
      ∀ π, step (.compute π (ρ.extend v) p) = .ret π (valueOf (ρ.extend v) p) := by
    intro p' hp'
    rw [MIR.renameTermList_eq_map] at hp'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
    exact (hrel 0 p hp).1
  have hR : steps (2 + (2 * (renameTermList (shiftRename 1) pre).length + 1) + 1)
      (.ret (.funV (.VLam (.Case (.Constr tag (renameTermList (shiftRename 1) pre ++
          .Var 1 :: renameTermList (shiftRename 1) rest)) (renameTermList (shiftRename 1) alts))
          ρ) :: π) v) =
      .ret (.constrField tag ((renameTermList (shiftRename 1) pre).map (valueOf (ρ.extend v))).reverse
        (renameTermList (shiftRename 1) rest) (ρ.extend v) ::
        .caseScrutinee (renameTermList (shiftRename 1) alts) (ρ.extend v) :: π) v := by
    rw [steps_trans, steps_trans]
    show steps 1 (steps _ (.compute (.caseScrutinee _ (ρ.extend v) :: π) (ρ.extend v) _)) = _
    rw [steps_constr_prefix _ hpre']
    rfl
  refine obsRefines_of_steps 0 (2 + (2 * (renameTermList (shiftRename 1) pre).length + 1) + 1) ?_
  rw [hR]
  apply obsRefines_of_obsRefinesK
  intro i
  have hl : ListRel (ValueRefinesK i) (pre.map (valueOf ρ))
      ((renameTermList (shiftRename 1) pre).map (valueOf (ρ.extend v))) := by
    rw [MIR.renameTermList_eq_map, List.map_map]
    clear hpre' hstep hpre hR
    induction pre with
    | nil => trivial
    | cons p ps ih =>
      exact ⟨(hrel i p (.head _)).2, ih (fun i q hq => hrel i q (.tail _ hq))⟩
  exact stackRefK_constrField_shift rest hrest (listRel_reverse hl) (envRefinesK_refl hρ)
    (stackRefK_case_shift halts (envRefinesK_refl hρ) (stackRefK_refl i π hπ))
    i (Nat.le_refl _) v v (valueRefinesK_refl i v hv)

/-! ## The MIR rewrite -/

theorem selectAlternative_zero (tag : Nat) (args alts : List Expr) :
    selectAlternative tag 0 args alts =
      match alts[tag]? with | some a => args.foldl Expr.App a | none => .Error := by
  unfold selectAlternative
  simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, if_false]
  cases alts[tag]? <;> rfl

theorem maxUidExprList_append_eq : ∀ (xs ys : List Expr),
    maxUidExprList (xs ++ ys) = max (maxUidExprList xs) (maxUidExprList ys)
  | [], ys => by simp [maxUidExprList]
  | x :: xs, ys => by
    rw [List.cons_append, maxUidExprList, maxUidExprList, maxUidExprList_append_eq xs ys]
    omega

theorem lowerTotalExpr_error (env : List VarId) : lowerTotalExpr env .Error = some .Error := by
  simp [lowerTotalExpr, expandFix, lowerTotal]

theorem lower_select {env : List VarId} {tag : Nat} {args alts : List Expr}
    {targs talts : List Term} (hargs : lowerTotalExprList env args = some targs)
    (halts : lowerTotalExprList env alts = some talts) :
    lowerTotalExpr env (selectAlternative tag 0 args alts) =
      some (match talts[tag]? with | some a => targs.foldl Term.Apply a | none => .Error) := by
  rw [selectAlternative_zero]
  rcases lowerTotalExprList_getElem? halts tag with ⟨e, t, he, ht, hl⟩ | ⟨he, ht⟩
  · rw [he, ht]
    simp only []
    rw [lowerTotalExpr_foldl_app, hl, hargs]; rfl
  · rw [he, ht]; exact lowerTotalExpr_error env

theorem closedAt_select {k tag : Nat} {targs talts : List Term}
    (hargs : closedAtList k targs = true) (halts : closedAtList k talts = true) :
    closedAt k (match talts[tag]? with | some a => targs.foldl Term.Apply a | none => .Error) = true := by
  cases h : talts[tag]? with
  | none => simp [closedAt]
  | some a =>
    simp only []
    rw [closedAt_foldl_apply, Contextual.BisimRef.closedAtList_get k talts tag a halts h, hargs]
    rfl

theorem lower_case_constr (env : List VarId) (tag : Nat) (fields alts : List Expr) :
    lowerTotalExpr env (.Case (.Constr tag fields) alts) =
      (lowerTotalExprList env fields).bind fun tf =>
        (lowerTotalExprList env alts).map fun ta => .Case (.Constr tag tf) ta := by
  rw [lowerTotalExpr_case_of_list, lowerTotalExpr_constr_of_list]
  cases lowerTotalExprList env fields <;> cases lowerTotalExprList env alts <;> rfl

theorem maxUidExpr_case_constr (tag : Nat) (fields alts : List Expr) :
    maxUidExpr (.Case (.Constr tag fields) alts) =
      max (maxUidExprList fields) (maxUidExprList alts) := by
  simp [maxUidExpr]

theorem caseFieldBindings_atom {next : Nat} {f : Expr} (rest : List Expr) (hf : f.isAtom = true) :
    caseFieldBindings next (f :: rest) =
      ((caseFieldBindings next rest).1, f :: (caseFieldBindings next rest).2) := by
  simp [caseFieldBindings, hf]

theorem caseFieldBindings_nonatom {next : Nat} {f : Expr} (rest : List Expr)
    (hf : f.isAtom = false) :
    caseFieldBindings next (f :: rest) =
      (({ uid := next, origin := .gen, hint := "field" }, f, false) ::
          (caseFieldBindings (next + 1) rest).1,
        .Var { uid := next, origin := .gen, hint := "field" } ::
          (caseFieldBindings (next + 1) rest).2) := by
  simp [caseFieldBindings, hf]

theorem fresh_of_maxUidList {es : List Expr} {v : VarId} (h : maxUidExprList es < v.uid) :
    ∀ e ∈ es, (freeVars e).contains v = false :=
  fun e he => maxUidExpr_fresh e v (by
    have := maxUidExpr_le_maxUidExprList_of_mem he; omega)

theorem reduceAux_correct (tag : Nat) (alts : List Expr) :
    ∀ (rest pre : List Expr) (next : Nat) (env : List VarId) (t₁ : Term),
      (∀ a ∈ pre, a.isAtom = true) →
      maxUidExpr (.Case (.Constr tag (pre ++ rest)) alts) < next →
      lowerTotalExpr env (.Case (.Constr tag (pre ++ rest)) alts) = some t₁ →
      ∃ t₂, lowerTotalExpr env (wrapLet (caseFieldBindings next rest).1
          (selectAlternative tag 0 (pre ++ (caseFieldBindings next rest).2) alts)) = some t₂ ∧
        (∀ k, closedAt k t₁ = true → closedAt k t₂ = true) ∧ SameRef env.length t₁ t₂
  | [], pre, next, env, t₁, hpre, _, h₁ => by
    simp only [List.append_nil, caseFieldBindings, wrapLet] at h₁ ⊢
    rw [lower_case_constr] at h₁
    cases hp : lowerTotalExprList env pre <;> cases ha : lowerTotalExprList env alts <;>
      simp [hp, ha] at h₁
    rename_i tpre talts
    subst h₁
    refine ⟨_, lower_select hp ha, ?_, ?_⟩
    · intro k hk
      simp only [closedAt, Bool.and_eq_true] at hk
      exact closedAt_select hk.1 hk.2
    · exact sameRef_select (lowerTotalExprList_valueTerms hpre hp)
  | f :: rest, pre, next, env, t₁, hpre, hfresh, h₁ => by
    cases hf : f.isAtom with
    | true =>
      rw [caseFieldBindings_atom rest hf]
      have e₁ : pre ++ f :: rest = (pre ++ [f]) ++ rest := by simp
      have e₂ : pre ++ f :: (caseFieldBindings next rest).2 =
          (pre ++ [f]) ++ (caseFieldBindings next rest).2 := by simp
      rw [e₂]
      rw [e₁] at hfresh h₁
      exact reduceAux_correct tag alts rest (pre ++ [f]) next env t₁
        (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hpre a ha
          · rw [List.mem_singleton.mp ha]; exact hf)
        hfresh h₁
    | false =>
      rw [caseFieldBindings_nonatom rest hf]
      let g : VarId := { uid := next, origin := .gen, hint := "field" }
      -- Freshness of the bound variable.
      rw [maxUidExpr_case_constr, maxUidExprList_append_eq] at hfresh
      have hfl : maxUidExprList (f :: rest) = max (maxUidExpr f) (maxUidExprList rest) := by
        rw [maxUidExprList]
      rw [hfl] at hfresh
      have fpre : ∀ e ∈ pre, (freeVars e).contains g = false :=
        fresh_of_maxUidList (show maxUidExprList pre < next by omega)
      have frest : ∀ e ∈ rest, (freeVars e).contains g = false :=
        fresh_of_maxUidList (show maxUidExprList rest < next by omega)
      have ff : (freeVars f).contains g = false :=
        maxUidExpr_fresh f g (show maxUidExpr f < next by omega)
      have falts : ∀ e ∈ alts, (freeVars e).contains g = false :=
        fresh_of_maxUidList (show maxUidExprList alts < next by omega)
      -- Decompose the source lowering.
      rw [lower_case_constr, lowerTotalExprList_append, lowerTotalExprList_cons] at h₁
      cases hp : lowerTotalExprList env pre <;> cases htf : lowerTotalExpr env f <;>
        cases hr : lowerTotalExprList env rest <;> cases ha : lowerTotalExprList env alts <;>
        simp [hp, htf, hr, ha] at h₁
      rename_i tpre tf trest talts
      subst h₁
      -- The body of the new binding before the remaining fields are processed.
      have hB : lowerTotalExpr (g :: env) (.Case (.Constr tag ((pre ++ [.Var g]) ++ rest)) alts) =
          some (.Case (.Constr tag (renameTermList (shiftRename 1) tpre ++
            .Var 1 :: renameTermList (shiftRename 1) trest)) (renameTermList (shiftRename 1) talts)) := by
        rw [lower_case_constr, lowerTotalExprList_append, lowerTotalExprList_append,
          lowerTotalExprList_cons, lowerTotalExprList_nil,
          lowerTotalExprList_prepend_unused env g pre fpre,
          lowerTotalExprList_prepend_unused env g rest frest,
          lowerTotalExprList_prepend_unused env g alts falts, hp, hr, ha]
        have hv : lowerTotalExpr (g :: env) (.Var g) = some (.Var 1) := by
          simp [lowerTotalExpr, expandFix, lowerTotal, envLookupT_cons_self]
        rw [hv]
        simp
      obtain ⟨t₂', hlow', hcl', hsame'⟩ := reduceAux_correct tag alts rest (pre ++ [.Var g])
        (next + 1) (g :: env) _
        (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hpre a ha
          · rw [List.mem_singleton.mp ha]; rfl)
        (by
          rw [maxUidExpr_case_constr, maxUidExprList_append_eq, maxUidExprList_append_eq]
          have h5 : maxUidExprList [Expr.Var g] = next := by
            rw [maxUidExprList, maxUidExprList, maxUidExpr]; simp [g]
          omega)
        hB
      have hY : pre ++ Expr.Var g :: (caseFieldBindings (next + 1) rest).2 =
          (pre ++ [.Var g]) ++ (caseFieldBindings (next + 1) rest).2 := by simp
      refine ⟨.Apply (.Lam 0 t₂') tf, ?_, ?_, ?_⟩
      · show lowerTotalExpr env (.Let ((g, f, false) :: _) _) = _
        rw [lowerTotalExpr_let_cons, htf, ← lowerTotalExpr_wrapLet, hY, hlow']
        rfl
      · intro k hk
        simp only [closedAt, Contextual.closedAtList_append, closedAtList, Bool.and_eq_true] at hk
        obtain ⟨⟨hkpre, hkf, hkrest⟩, hkalts⟩ := hk
        simp only [closedAt, Bool.and_eq_true]
        refine ⟨hcl' (k + 1) ?_, hkf⟩
        simp only [closedAt, Contextual.closedAtList_append, closedAtList, Bool.and_eq_true]
        refine ⟨⟨closedAtList_renameTermList_shiftRename _ k 1 (Nat.le_refl _) (by omega) hkpre,
          ⟨by simp, closedAtList_renameTermList_shiftRename _ k 1 (Nat.le_refl _)
            (by omega) hkrest⟩⟩,
          closedAtList_renameTermList_shiftRename _ k 1 (Nat.le_refl _) (by omega) hkalts⟩
      · have hvals := lowerTotalExprList_valueTerms hpre hp
        have hcf := lowerTotalExpr_closedAt htf
        exact sameRef_trans
          (sameRef_hoist hvals hcf (lowerTotalList_closedAtList env _ _ hr)
            (lowerTotalList_closedAtList env _ _ ha))
          (sameRef_let_body hcf (by simpa using hsame'))

/-- **Case on a literal constructor.** -/
theorem reduce_correct (tag : Nat) (fields alts : List Expr) (env : List VarId) (t₁ : Term)
    (h₁ : lowerTotalExpr env (.Case (.Constr tag fields) alts) = some t₁) :
    ∃ t₂, lowerTotalExpr env (reduceConstructorCase tag fields alts) = some t₂ ∧
      (∀ k, closedAt k t₁ = true → closedAt k t₂ = true) ∧ SameRef env.length t₁ t₂ := by
  have h := reduceAux_correct tag alts fields [] (maxUidExpr (.Case (.Constr tag fields) alts) + 1)
    env t₁ (fun _ h => by cases h) (by simp) (by simpa using h₁)
  simp only [List.nil_append] at h
  obtain ⟨t₂, hl, hc, hs⟩ := h
  refine ⟨t₂, ?_, hc, hs⟩
  rw [← hl]
  unfold reduceConstructorCase
  generalize caseFieldBindings (maxUidExpr (.Case (.Constr tag fields) alts) + 1) fields = r
  obtain ⟨bs, args⟩ := r
  cases bs <;> rfl

end Moist.Verified.CaseMerge
