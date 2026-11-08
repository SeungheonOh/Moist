import Moist.Verified.GuardsSoundness.Context

/-! # CEK steps used by the soundness of `chk` -/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.KnownLists

/-! ## Saturated builtins -/

theorem mkCons_inert {args : List CekValue} {r : CekValue} (h : evalBuiltin .MkCons args = some r) :
    InertV r := by
  unfold evalBuiltin at h
  cases hp : evalBuiltinPassThrough .MkCons args with
  | some v =>
    rw [hp] at h; cases h
    match args, hp with
    | [], hp | [_], hp | _ :: _ :: _ :: _, hp => simp [evalBuiltinPassThrough] at hp
    | [.VCon c, e], hp =>
      cases c <;> cases e <;> simp [evalBuiltinPassThrough] at hp <;> (subst hp; trivial)
    | [.VLam _ _, _], hp | [.VDelay _ _, _], hp | [.VConstr _ _, _], hp | [.VBuiltin _ _ _, _], hp =>
      simp [evalBuiltinPassThrough] at hp
  | none =>
    rw [hp] at h
    simp only at h
    split at h
    · split at h
      · cases h; trivial
      · cases h
    · cases h

theorem builtinCovers_sound {b : BuiltinFun} {m : VMode} (hc : builtinCovers b m = true)
    {args : List CekValue} {r : CekValue} (hlen : args.length = valueArity (expectedArgs b))
    (h : evalBuiltin b args = some r) : ModeV m r := by
  cases m with
  | term => trivial
  | inert =>
    simp only [builtinCovers, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact passThrough_false_vcon hc h
    · have : b = .MkCons := by revert hc; cases b <;> decide
      subst this; exact mkCons_inert h
  | bool =>
    simp only [builtinCovers] at hc
    obtain ⟨x, rfl⟩ := booleanBuiltin_result hc hlen h
    exact ⟨x, rfl⟩
  | constrs _ => simp [builtinCovers] at hc

/-- Applying a builtin state that expects a value argument terminates. -/
theorem apply_state_ends {wf wa : CekValue} {b : BuiltinFun} {rem : ExpectedArgs}
    (hw : BuiltinState b rem wf) (hh : rem.head = .argV) {m : VMode}
    (hm : m = .term ∨ (rem.isFinal = true ∧ builtinCovers b m = true)) :
    Ends m (.ret [.funV wf] wa) := by
  obtain ⟨args, rfl, hlen⟩ := hw
  cases rem with
  | one k =>
    simp only [ExpectedArgs.head] at hh
    subst hh
    cases hev : evalBuiltin b (wa :: args) with
    | none =>
      exact .inl (reaches_of_steps 1 (by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
    | some r =>
      refine .inr ⟨r, reaches_of_steps 2 (by simp [steps, step, ExpectedArgs.head,
        ExpectedArgs.tail, hev]), ?_⟩
      rcases hm with rfl | ⟨_, hc⟩
      · trivial
      · refine builtinCovers_sound hc ?_ hev
        simp [valueArity] at hlen ⊢; omega
  | more k rest =>
    simp only [ExpectedArgs.head] at hh
    subst hh
    refine .inr ⟨_, reaches_of_steps 2 rfl, ?_⟩
    rcases hm with rfl | ⟨hf, _⟩
    · trivial
    · simp [ExpectedArgs.isFinal] at hf

/-- Forcing a builtin state that expects a type argument terminates. -/
theorem force_state_ends {w : CekValue} {b : BuiltinFun} {rem : ExpectedArgs}
    (hw : BuiltinState b rem w) (hh : rem.head = .argQ) {m : VMode}
    (hm : m = .term ∨ (rem.isFinal = true ∧ builtinCovers b m = true)) :
    Ends m (.ret [.force] w) := by
  obtain ⟨args, rfl, hlen⟩ := hw
  cases rem with
  | one k =>
    simp only [ExpectedArgs.head] at hh
    subst hh
    cases hev : evalBuiltin b args with
    | none =>
      exact .inl (reaches_of_steps 1 (by simp [steps, step, ExpectedArgs.head, ExpectedArgs.tail, hev]))
    | some r =>
      refine .inr ⟨r, reaches_of_steps 2 (by simp [steps, step, ExpectedArgs.head,
        ExpectedArgs.tail, hev]), ?_⟩
      rcases hm with rfl | ⟨_, hc⟩
      · trivial
      · refine builtinCovers_sound hc ?_ hev
        simp [valueArity] at hlen ⊢; omega
  | more k rest =>
    simp only [ExpectedArgs.head] at hh
    subst hh
    refine .inr ⟨_, reaches_of_steps 2 rfl, ?_⟩
    rcases hm with rfl | ⟨hf, _⟩
    · trivial
    · simp [ExpectedArgs.isFinal] at hf

end Moist.Verified.Guards
