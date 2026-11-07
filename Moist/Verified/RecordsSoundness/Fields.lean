import Moist.Verified.RecordsSoundness.Analysis

/-! # Field reads and recorded fields

A field read `case r [λ…. f]` of a value whose first alternative receives
exactly `n` fields returns the selected field (`read_reaches`). The
expression recorded for a field binder, `fieldProjection`, returns a field
only when the scrutinee supplies exactly as many fields as there are binders
(`fieldProjection_halts`), and then returns it (`fieldProjection_of_fields`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence

theorem lamsT_add : ∀ (a b : Nat) (t : Term), lamsT (a + b) t = lamsT a (lamsT b t)
  | 0, b, t => by simp [lamsT]
  | a + 1, b, t => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [lamsT, lamsT_add a b t]

/-- A single alternative receiving the fields of tag `0`. -/
theorem step_case_single {alt : Term} {ρ : CekEnv} {π : Stack} {w : CekValue} {fields : List CekValue}
    (h : CaseFields w 0 fields) :
    step (.ret (.caseScrutinee [alt] ρ :: π) w) = .compute (fields.map Frame.applyArg ++ π) ρ alt := by
  rcases h with rfl | ⟨c, numCtors, rfl, hc⟩
  · rfl
  · simp only [step, hc]
    have : ¬ (numCtors > 0 && [alt].length > numCtors) = true := by
      simp only [List.length_singleton, Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro h; omega
    simp only [this]
    rfl

theorem getElem?_reverse_lt {fields : List CekValue} {index : Nat} (h : index < fields.length) :
    ∃ u, fields.reverse[index]? = some u := by
  cases hu : fields.reverse[index]? with
  | none => rw [List.getElem?_eq_none_iff] at hu; simp at hu; omega
  | some u => exact ⟨u, rfl⟩

/-- A field read of a value supplying exactly `n` fields. -/
theorem read_reaches {ρ : CekEnv} {π : Stack} {i n index : Nat} {w u : CekValue}
    {fields : List CekValue} (hw : ρ.lookup i = some w) (hcf : CaseFields w 0 fields)
    (hlen : fields.length = n) (hu : fields.reverse[index]? = some u) :
    Reaches (.compute π ρ (.Case (.Var i) [lamsT n (.Var (index + 1))])) (.ret π u) := by
  have hindex : index < fields.length := by
    have := (List.getElem?_eq_some_iff.mp hu).1; simpa using this
  refine reaches_trans (s₂ := .ret (.caseScrutinee [lamsT n (.Var (index + 1))] ρ :: π) w)
    ⟨2, by simp [steps, step, hw]⟩ ?_
  refine reaches_trans ⟨1, by simp only [steps]; rw [step_case_single hcf]⟩ ?_
  subst hlen
  refine reaches_trans (reaches_telescope fields π ρ _) ⟨1, ?_⟩
  simp only [steps, step]
  rw [lookup_extendAll_lt ρ fields index hindex, hu]

/-- The recorded expression of a field binder returns the field. -/
theorem fieldProjection_of_fields {ρ : CekEnv} {i n index : Nat} {w u : CekValue}
    {fields : List CekValue} (hw : ρ.lookup i = some w) (hcf : CaseFields w 0 fields)
    (hlen : fields.length = n) (hu : fields.reverse[index]? = some u) :
    Halts ρ (.Case (.Case (.Var i) [lamsT n (.Constr 0 [.Var (index + 1)])]) [.Lam 0 (.Var 1)]) u := by
  have hindex : index < fields.length := by
    have := (List.getElem?_eq_some_iff.mp hu).1; simpa using this
  unfold Halts
  refine reaches_trans (s₂ := .compute [.caseScrutinee [lamsT n (.Constr 0 [.Var (index + 1)])] ρ,
    .caseScrutinee [.Lam 0 (.Var 1)] ρ] ρ (.Var i)) ⟨2, rfl⟩ ?_
  refine reaches_trans (s₂ := .ret [.caseScrutinee [lamsT n (.Constr 0 [.Var (index + 1)])] ρ,
    .caseScrutinee [.Lam 0 (.Var 1)] ρ] w) ⟨1, by simp [steps, step, hw]⟩ ?_
  refine reaches_trans ⟨1, by simp only [steps]; rw [step_case_single hcf]⟩ ?_
  subst hlen
  refine reaches_trans (reaches_telescope fields _ ρ _) ?_
  refine ⟨8, ?_⟩
  simp only [steps, step]
  rw [lookup_extendAll_lt ρ fields index hindex, hu]
  rfl

/-- Whenever the recorded expression of a field binder returns, the
    scrutinee supplied exactly `n` fields, and the result is the field. -/
theorem fieldProjection_halts {ρ : CekEnv} {i n index : Nat} {u : CekValue} (hindex : index < n)
    (h : Halts ρ (.Case (.Case (.Var i) [lamsT n (.Constr 0 [.Var (index + 1)])]) [.Lam 0 (.Var 1)]) u) :
    ∃ w fields, ρ.lookup i = some w ∧ CaseFields w 0 fields ∧ fields.length = n ∧
      fields.reverse[index]? = some u := by
  obtain ⟨w', hinner, hrest⟩ := halts_case h
  obtain ⟨w, hvar, hrest'⟩ := halts_case hinner
  have hw := halts_var hvar
  obtain ⟨tag, fields, talt, hget, hcf, hrun⟩ := case_dispatch (.inr ⟨w', rfl⟩) hrest' (by simp)
  cases tag with
  | succ _ => simp at hget
  | zero =>
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
  subst hget
  rw [List.append_nil] at hrun
  -- the outer case receives the result of the inner one
  have outer : ∀ x, w' = .VConstr 0 [x] → x = u := by
    intro x hx
    subst hx
    have h1 := reaches_halt_of_step (by simp) hrest
    simp only [step, List.getElem?_cons_zero, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append] at h1
    obtain ⟨m, hm⟩ := h1
    have : steps 4 (.compute [.applyArg x] ρ (.Lam 0 (.Var 1))) = .halt x := rfl
    have hdet := terminal_unique (s := .compute [.applyArg x] ρ (.Lam 0 (.Var 1)))
      (.inr ⟨u, rfl⟩) (.inr ⟨x, rfl⟩) ⟨m, hm⟩ ⟨4, this⟩
    cases hdet; rfl
  rcases Nat.lt_trichotomy fields.length n with hlt | heq | hgt
  · -- too few fields: the inner case returns a partial application
    obtain ⟨k, rfl⟩ : ∃ k, n = fields.length + (k + 1) := ⟨n - fields.length - 1, by omega⟩
    rw [lamsT_add] at hrun
    have hreach := reaches_telescope fields [] ρ (lamsT (k + 1) (.Constr 0 [.Var (index + 1)]))
    rw [List.append_nil] at hreach
    have hlam := reaches_terminal_after (.inr ⟨w', rfl⟩) hreach hrun
    have hval : w' = .VLam (lamsT k (.Constr 0 [.Var (index + 1)])) (extendAll ρ fields) := by
      have := terminal_unique (.inr ⟨w', rfl⟩) (.inr ⟨_, rfl⟩) hlam ⟨2, rfl⟩
      cases this; rfl
    subst hval
    have h1 := reaches_halt_of_step (by simp) hrest
    simp only [step] at h1
    exact absurd h1 (fun he => halt_not_error he ⟨0, rfl⟩)
  · refine ⟨w, fields, hw, hcf, heq, ?_⟩
    subst heq
    have hreach := reaches_telescope fields [] ρ (.Constr 0 [.Var (index + 1)])
    rw [List.append_nil] at hreach
    have hbody := reaches_terminal_after (.inr ⟨w', rfl⟩) hreach hrun
    obtain ⟨vs, rfl, hvlen, hvs⟩ := halts_constr hbody
    match vs, hvlen with
    | [x], _ =>
      have hx := hvs 0 _ x rfl rfl
      have hxu := outer x rfl
      subst hxu
      have hl := halts_var hx
      rw [lookup_extendAll_lt ρ fields index hindex] at hl
      exact hl
  · -- too many fields: the constructor is applied to the remaining ones
    obtain ⟨front, back, rfl, hfront⟩ : ∃ front back, fields = front ++ back ∧ front.length = n :=
      ⟨fields.take n, fields.drop n, by simp, by simp; omega⟩
    obtain ⟨f, fs, hback⟩ : ∃ f fs, back = f :: fs := by
      cases back with
      | nil => simp at hgt; omega
      | cons f fs => exact ⟨f, fs, rfl⟩
    subst hback
    rw [List.map_append, ← hfront] at hrun
    have hreach := reaches_telescope front ((f :: fs).map Frame.applyArg) ρ (.Constr 0 [.Var (index + 1)])
    have hbody := reaches_terminal_after (.inr ⟨w', rfl⟩) hreach hrun
    rcases sequence (.inr ⟨w', rfl⟩) hbody with ⟨_, impossible⟩ | ⟨c, hc, rest⟩
    · cases impossible
    · obtain ⟨vs, rfl, _, _⟩ := halts_constr hc
      have := ret_applyArg_constr (.inr ⟨w', rfl⟩) rest
      cases this

end Moist.Verified.ShapeFacts
