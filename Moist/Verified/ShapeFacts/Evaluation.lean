import Moist.Verified.InlineSoundness.Frontier
import Moist.Verified.StepWellFormed

variable [sv : Moist.CEK.SemVariant]

/-! # Evaluation from the empty stack

`Halts ρ t v` and `Errs ρ t` describe the outcome of evaluating `t` in `ρ`
from the empty stack. Every other stack only observes that outcome
(`sequence`), so two continuations that agree on the values `t` can return
refine each other around `t` (`obsRefines_of_continuation`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines

def Halts (ρ : CekEnv) (t : Term) (v : CekValue) : Prop :=
  Reaches (.compute [] ρ t) (.halt v)

def Errs (ρ : CekEnv) (t : Term) : Prop :=
  Reaches (.compute [] ρ t) .error

def Terminal (s : State) : Prop := s = .error ∨ ∃ v, s = .halt v

theorem Terminal.fixed {s : State} (h : Terminal s) : step s = s := by
  rcases h with rfl | ⟨v, rfl⟩ <;> rfl

theorem Terminal.steps_fixed {s : State} (h : Terminal s) (n : Nat) : steps n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [steps, h.fixed, ih]

theorem reaches_refl (s : State) : Reaches s s := ⟨0, rfl⟩

theorem reaches_trans {s₁ s₂ s₃ : State} (h₁ : Reaches s₁ s₂) (h₂ : Reaches s₂ s₃) :
    Reaches s₁ s₃ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by rw [steps_trans, hm, hn]⟩

theorem reaches_of_steps {s s' : State} (m : Nat) (h : steps m s = s') : Reaches s s' := ⟨m, h⟩

/-- A terminal state reached from `s` is also reached from every state that
    `s` reaches. -/
theorem reaches_terminal_after {s s' T : State} (term : Terminal T)
    (hs : Reaches s s') (hT : Reaches s T) : Reaches s' T := by
  obtain ⟨m, hm⟩ := hs
  have := (AdvancedRefinement.reaches_after_prefix m term.fixed).mp hT
  rwa [hm] at this

theorem terminal_unique {s T₁ T₂ : State} (t₁ : Terminal T₁) (t₂ : Terminal T₂)
    (h₁ : Reaches s T₁) (h₂ : Reaches s T₂) : T₁ = T₂ := by
  have h := reaches_terminal_after t₂ h₁ h₂
  obtain ⟨n, hn⟩ := h
  rw [t₁.steps_fixed] at hn
  exact hn

theorem halt_not_error {s : State} {v : CekValue} (hv : Reaches s (.halt v))
    (he : Reaches s .error) : False := by
  have := terminal_unique (.inr ⟨v, rfl⟩) (.inl rfl) hv he
  cases this

theorem halts_unique {ρ : CekEnv} {t : Term} {v w : CekValue}
    (hv : Halts ρ t v) (hw : Halts ρ t w) : v = w :=
  Semantics.reaches_unique hv hw

theorem halts_on_stack {ρ : CekEnv} {t : Term} {v : CekValue} (h : Halts ρ t v) (π : Stack) :
    Reaches (.compute π ρ t) (.ret π v) :=
  InlineSoundness.StrictOcc.halt_on_all_stacks h π

theorem errs_on_stack {ρ : CekEnv} {t : Term} (h : Errs ρ t) (π : Stack) :
    Reaches (.compute π ρ t) .error :=
  InlineSoundness.StrictOcc.error_on_all_stacks h π

/-- A terminating computation on any stack first evaluates the term on the
    empty stack. -/
theorem sequence {π : Stack} {ρ : CekEnv} {t : Term} {T : State} (term : Terminal T)
    (reach : Reaches (.compute π ρ t) T) :
    (Errs ρ t ∧ T = .error) ∨ ∃ v, Halts ρ t v ∧ Reaches (.ret π v) T := by
  rcases InlineSoundness.Frontier.outcome_of_terminal term reach with ⟨v, hv⟩ | he
  · exact .inr ⟨v, hv, reaches_terminal_after term (halts_on_stack hv π) reach⟩
  · exact .inl ⟨he, terminal_unique term (.inl rfl) reach (errs_on_stack he π)⟩

theorem obsRefines_refl (s : State) : ObsRefines s s := ⟨id, id⟩

theorem obsRefines_trans {s₁ s₂ s₃ : State} (h₁ : ObsRefines s₁ s₂) (h₂ : ObsRefines s₂ s₃) :
    ObsRefines s₁ s₃ :=
  ⟨fun h => h₂.halt (h₁.halt h), fun h => h₂.error (h₁.error h)⟩

theorem obsRefines_of_reaches {s₁ s₁' s₂ s₂' : State} (left : Reaches s₁ s₁') (right : Reaches s₂ s₂')
    (h : ObsRefines s₁' s₂') : ObsRefines s₁ s₂ := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw⟩ := h.halt ⟨v, reaches_terminal_after (.inr ⟨v, rfl⟩) left hv⟩
    exact ⟨w, reaches_trans right hw⟩
  · intro he
    exact reaches_trans right (h.error (reaches_terminal_after (.inl rfl) left he))

theorem obsRefines_of_steps {s₁ s₂ : State} (m n : Nat)
    (h : ObsRefines (steps m s₁) (steps n s₂)) : ObsRefines s₁ s₂ :=
  obsRefines_of_reaches ⟨m, rfl⟩ ⟨n, rfl⟩ h

theorem obsRefines_of_step {s₁ s₂ : State}
    (h : ObsRefines (step s₁) (step s₂)) : ObsRefines s₁ s₂ :=
  obsRefines_of_steps 1 1 h

/-- Two continuations that refine each other on every value the term can
    return refine each other around the term. -/
theorem obsRefines_of_continuation {ρ : CekEnv} {t : Term} {π₁ π₂ : Stack}
    (continuation : ∀ v, Halts ρ t v → ObsRefines (.ret π₁ v) (.ret π₂ v)) :
    ObsRefines (.compute π₁ ρ t) (.compute π₂ ρ t) := by
  constructor
  · rintro ⟨w, hw⟩
    rcases sequence (.inr ⟨w, rfl⟩) hw with ⟨_, impossible⟩ | ⟨v, hv, rest⟩
    · cases impossible
    · obtain ⟨w', hw'⟩ := (continuation v hv).halt ⟨w, rest⟩
      exact ⟨w', reaches_trans (halts_on_stack hv π₂) hw'⟩
  · intro he
    rcases sequence (.inl rfl) he with ⟨errs, _⟩ | ⟨v, hv, rest⟩
    · exact errs_on_stack errs π₂
    · exact reaches_trans (halts_on_stack hv π₂) ((continuation v hv).error rest)

theorem obsRefines_of_forall_k {s₁ s₂ : State} (h : ∀ k, ObsRefinesK k s₁ s₂) : ObsRefines s₁ s₂ := by
  constructor
  · rintro ⟨v, n, hn⟩
    exact (h n).1 v ⟨n, Nat.le_refl _, hn⟩
  · rintro ⟨n, hn⟩
    exact (h n).2 n (Nat.le_refl _) hn

/-! ## Well-formedness of results -/

theorem halts_wellFormed {d : Nat} {ρ : CekEnv} {t : Term} {v : CekValue}
    (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length) (hclosed : Moist.Verified.closedAt d t = true)
    (h : Halts ρ t v) : ValueWellFormed v := by
  obtain ⟨n, hn⟩ := h
  exact StepWellFormed.halt_value_wf (.compute .nil henv hlen hclosed) hn

theorem reaches_ret_wellFormed {s : State} {π : Stack} {v : CekValue}
    (hs : StepWellFormed.StateWellFormed s) (h : Reaches s (.ret π v)) :
    ValueWellFormed v ∧ StackWellFormed π := by
  obtain ⟨n, hn⟩ := h
  have := StepWellFormed.steps_preserves_wf n s hs
  rw [hn] at this
  cases this with
  | ret hπ hv => exact ⟨hv, hπ⟩

end Moist.Verified.ShapeFacts
