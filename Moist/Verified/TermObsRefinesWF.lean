import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.StepWellFormed

variable [sv : Moist.CEK.SemVariant]

/-! # Well-formedness instance of open-to-contextual soundness

`wfGuard` threads CEK well-formedness (`StateWellFormed` and friends) through
the guarded logical relation. `OpenRefinesWF` only quantifies over
well-formed environments and stacks, which is what the beta-reduction proofs
can establish; `soundness_refinesWF` is the `wfGuard` instance of
`soundness_of_openRel`.
-/

namespace Moist.Verified.TermObsRefinesWF

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.Contextual.Guarded
open Moist.Verified.BetaValueRefines
open Moist.Verified.StepWellFormed (StateWellFormed step_preserves_wf)

/-- CEK well-formedness as a guard. -/
def wfGuard : Guard where
  V := ValueWellFormed
  S := StackWellFormed
  E := EnvWellFormed
  St := StateWellFormed
  step h := step_preserves_wf _ h
  ret := ⟨fun h => by cases h with | ret hπ hv => exact ⟨hπ, hv⟩, fun h => .ret h.1 h.2⟩
  compute h := by cases h with | compute hπ _ _ _ => exact hπ
  tail h := by cases h with | cons _ h => exact h
  funV hv hπ := .cons (.funV hv) hπ
  force hπ := .cons .force hπ
  applyArg h := by cases h with | cons hf _ => cases hf with | applyArg hv => exact hv
  extend h hlen hv := envWellFormed_narrow _ (envWellFormed_extend _ h hlen hv) (Nat.le_succ _)

/-- The well-formedness-guarded value relation. -/
abbrev ValueRefinesKWF : Nat → CekValue → CekValue → Prop := ValueRel wfGuard

def StackFnKWF (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, ValueRefinesKWF j v₁ v₂ →
    ValueWellFormed v₁ → ValueWellFormed v₂ →
    ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂)

def EnvRefinesKWF (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧
      ValueRefinesKWF k v₁ v₂

def BehRefinesKWF (k : Nat) (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂,
    StackWellFormed π₁ → StackWellFormed π₂ → StackFnKWF j π₁ π₂ →
    ObsRefinesK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

def OpenRefinesKWF (k d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesKWF j d ρ₁ ρ₂ →
    EnvWellFormed d ρ₁ → d ≤ ρ₁.length →
    EnvWellFormed d ρ₂ → d ≤ ρ₂.length →
    BehRefinesKWF j ρ₁ ρ₂ t₁ t₂

def OpenRefinesWF (d : Nat) (t₁ t₂ : Term) : Prop := ∀ k, OpenRefinesKWF k d t₁ t₂

open Moist.Verified.Contextual.Soundness (dummyEnv dummyEnv_length)

omit sv in
private theorem dummyEnv_wellFormed : ∀ (n : Nat), EnvWellFormed n (dummyEnv n)
  | 0 => .zero
  | n + 1 => envWellFormed_extend n (dummyEnv_wellFormed n)
      (by rw [dummyEnv_length]; exact Nat.le_refl _) (.vcon .Unit)

theorem soundness_refinesWF {d : Nat} {t₁ t₂ : Term}
    (h_open_wf : OpenRefinesWF d t₁ t₂)
    (h_close_pres : ∀ (C : Context),
      Moist.Verified.closedAt 0 (fill C t₁) = true →
      Moist.Verified.closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ :=
  soundness_of_openRel (W := wfGuard) h_open_wf
    (fun _ h => .compute .nil (dummyEnv_wellFormed d)
      (by rw [dummyEnv_length]; exact Nat.le_refl _) (closedAt_mono h (Nat.zero_le d)))
    (dummyEnv_wellFormed d) .nil h_close_pres

end Moist.Verified.TermObsRefinesWF
