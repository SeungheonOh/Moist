import Moist.Verified.BetaValueRefines

/-! # Step preservation of well-formedness

The CEK `step` function preserves a state well-formedness invariant:
if the current term is `closedAt` relative to the environment depth,
the environment entries are well-formed, and the stack frames are
well-formed, then after one step all these properties still hold.

**Main result**: `step_preserves_wf` and its corollary `steps_preserves_wf`.
-/

namespace Moist.Verified.StepWellFormed

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.Verified
open Moist.Verified.BetaValueRefines
open Moist.Verified.Equivalence (steps constToTagAndFields_fields_vcon)

inductive StateWellFormed : State → Prop
  | compute : ∀ {π ρ t k},
      StackWellFormed π → EnvWellFormed k ρ → k ≤ ρ.length →
      closedAt k t = true →
      StateWellFormed (.compute π ρ t)
  | ret : ∀ {π v},
      StackWellFormed π → ValueWellFormed v →
      StateWellFormed (.ret π v)
  | error : StateWellFormed .error
  | halt : ∀ {v}, ValueWellFormed v → StateWellFormed (.halt v)


section EvalBuiltinWF

private theorem diagonal : ∀ {args : List CekValue}, ValueListWellFormed args →
    Moist.Verified.Equivalence.ListRel (fun x y => x = y ∧ ValueWellFormed x) args args
  | [], _ => trivial
  | _ :: _, h => by cases h with | cons h hs => exact ⟨⟨rfl, h⟩, diagonal hs⟩

theorem evalBuiltin_preserves_wf {b : BuiltinFun}
    {args : List CekValue} {v : CekValue}
    (heval : evalBuiltin b args = some v)
    (hargs : ValueListWellFormed args) :
    ValueWellFormed v := by
  have rel := evalBuiltin_rel (b := b)
    (fun {c v} => ⟨fun h => h.1.symm, fun h => ⟨h.symm, .vcon c⟩⟩)
    (fun {c v} => ⟨fun h => h.1, fun h => ⟨h, h ▸ .vcon c⟩⟩) (diagonal hargs)
  rw [heval] at rel
  cases rel with
  | some r => exact r.2

end EvalBuiltinWF

section StepPreservation

/-! Well-formedness is the left projection of the shift bisimulation, and every
well-formed state is shift-related to itself at the identity renaming, so
`step` preserves well-formedness because it preserves the bisimulation. -/

open Moist.Verified.FundamentalRefines (is0preserving_id)

private theorem le_length_of_lookup {ρ : CekEnv} {n : Nat} {v : CekValue}
    (h : ρ.lookup n = some v) : n ≤ ρ.length :=
  Nat.le_of_not_gt fun gt => by rw [CekEnv.lookup_none_of_gt_length ρ n gt] at h; cases h

mutual
  private theorem wf_of_shiftState : ∀ {s₁ s₂ : State}, ShiftBisimState s₁ s₂ → StateWellFormed s₁
    | _, _, .compute _ henv hc hπ =>
      .compute (wf_of_shiftStack hπ) (wf_of_shiftEnv henv).1 (wf_of_shiftEnv henv).2 hc
    | _, _, .ret hv hπ => .ret (wf_of_shiftStack hπ) (wf_of_shiftValue hv)
    | _, _, .halt hv => .halt (wf_of_shiftValue hv)
    | _, _, .error => .error

  private theorem wf_of_shiftEnv : ∀ {σ : Nat → Nat} {d : Nat} {ρ₁ ρ₂ : CekEnv},
      ShiftBisimEnv σ d ρ₁ ρ₂ → EnvWellFormed d ρ₁ ∧ d ≤ ρ₁.length
    | _, _, _, _, .zero => ⟨.zero, Nat.zero_le _⟩
    | _, _, _, _, .succ rest found _ hv =>
      ⟨.succ (wf_of_shiftEnv rest).1 (le_length_of_lookup found) found (wf_of_shiftValue hv),
        le_length_of_lookup found⟩

  private theorem wf_of_shiftValue : ∀ {v₁ v₂ : CekValue}, ShiftBisimValue v₁ v₂ → ValueWellFormed v₁
    | _, _, .vcon c => .vcon c
    | _, _, .vlam _ henv hc => .vlam (wf_of_shiftEnv henv).1 (wf_of_shiftEnv henv).2 hc
    | _, _, .vdelay _ henv hc => .vdelay (wf_of_shiftEnv henv).1 (wf_of_shiftEnv henv).2 hc
    | _, _, .vconstr tag hs => .vconstr tag (wf_of_shiftValueList hs)
    | _, _, .vbuiltin b ea hs => .vbuiltin b ea (wf_of_shiftValueList hs)

  private theorem wf_of_shiftValueList : ∀ {vs₁ vs₂ : List CekValue},
      ShiftBisimValueList vs₁ vs₂ → ValueListWellFormed vs₁
    | _, _, .nil => .nil
    | _, _, .cons hv hs => .cons (wf_of_shiftValue hv) (wf_of_shiftValueList hs)

  private theorem wf_of_shiftStack : ∀ {π₁ π₂ : Stack}, ShiftBisimStack π₁ π₂ → StackWellFormed π₁
    | _, _, .nil => .nil
    | _, _, .cons hf hs => .cons (wf_of_shiftFrame hf) (wf_of_shiftStack hs)

  private theorem wf_of_shiftFrame : ∀ {f₁ f₂ : Frame}, ShiftBisimFrame f₁ f₂ → FrameWellFormed f₁
    | _, _, .force => .force
    | _, _, .arg _ henv hc => .arg (wf_of_shiftEnv henv).1 (wf_of_shiftEnv henv).2 hc
    | _, _, .funV hv => .funV (wf_of_shiftValue hv)
    | _, _, .applyArg hv => .applyArg (wf_of_shiftValue hv)
    | _, _, .constrField tag _ hdone henv hc =>
      .constrField tag (wf_of_shiftValueList hdone) (wf_of_shiftEnv henv).1 (wf_of_shiftEnv henv).2 hc
    | _, _, .caseScrutinee _ henv hc =>
      .caseScrutinee (wf_of_shiftEnv henv).1 (wf_of_shiftEnv henv).2 hc
end

private theorem shiftFrame_refl {f : Frame} (h : FrameWellFormed f) : ShiftBisimFrame f f := by
  cases h with
  | force => exact .force
  | arg henv _ hc =>
    simpa only [renameTerm_id] using
      ShiftBisimFrame.arg is0preserving_id (shiftBisimEnv_refl_id_aux henv) hc
  | funV hv => exact .funV (shiftBisimValue_refl_id_aux hv)
  | applyArg hv => exact .applyArg (shiftBisimValue_refl_id_aux hv)
  | constrField tag hdone henv _ hc =>
    simpa only [renameTermList_id] using
      ShiftBisimFrame.constrField tag is0preserving_id (shiftBisimValueList_refl_id_aux hdone)
        (shiftBisimEnv_refl_id_aux henv) hc
  | caseScrutinee henv _ hc =>
    simpa only [renameTermList_id] using
      ShiftBisimFrame.caseScrutinee is0preserving_id (shiftBisimEnv_refl_id_aux henv) hc

private theorem shiftStack_refl : ∀ {π : Stack}, StackWellFormed π → ShiftBisimStack π π
  | [], _ => .nil
  | _ :: _, .cons hf hs => .cons (shiftFrame_refl hf) (shiftStack_refl hs)

private theorem shiftState_refl {s : State} (h : StateWellFormed s) : ShiftBisimState s s := by
  cases h with
  | compute hπ henv _ hc =>
    simpa only [renameTerm_id] using
      ShiftBisimState.compute is0preserving_id (shiftBisimEnv_refl_id_aux henv) hc (shiftStack_refl hπ)
  | ret hπ hv => exact .ret (shiftBisimValue_refl_id_aux hv) (shiftStack_refl hπ)
  | error => exact .error
  | halt hv => exact .halt (shiftBisimValue_refl_id_aux hv)

theorem step_preserves_wf : ∀ (s : State),
    StateWellFormed s → StateWellFormed (step s) := fun _ h =>
  wf_of_shiftState (shiftBisimState_step_preserves (shiftState_refl h))

theorem steps_preserves_wf : ∀ (n : Nat) (s : State),
    StateWellFormed s → StateWellFormed (steps n s) := by
  intro n
  induction n with
  | zero => intro s hs; exact hs
  | succ m ih =>
    intro s hs
    simp [steps]
    exact ih (step s) (step_preserves_wf s hs)

theorem halt_value_wf {n : Nat} {s : State} {v : CekValue}
    (hs : StateWellFormed s) (hhalt : steps n s = .halt v) :
    ValueWellFormed v := by
  have := steps_preserves_wf n s hs
  rw [hhalt] at this
  cases this with
  | halt hv => exact hv

end StepPreservation

end Moist.Verified.StepWellFormed
