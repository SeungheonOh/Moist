import Moist.Verified.GuardsSoundness.BlockSwap

variable [sv : Moist.CEK.SemVariant]

/-! # Exchanging two strict steps

A strict step (a binding, a case with one continuing alternative, an
`ifThenElse` check) evaluates its expression, and then either fails or
continues with its body in the environment extended by some values. Two
steps whose expressions do not depend on each other's binders can be
exchanged when the second one halts or fails in every environment: if the
first one fails, the exchanged program evaluates the second one first, which
terminates, and then fails at the first one.
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast

/-- The semantics of a strict step. -/
structure SemUnit where
  arity : Nat
  plug : Term → Term → Term
  frames : CekEnv → Term → Stack
  ok : CekValue → Prop
  out : CekValue → Option (List CekValue)
  run : ∀ π ρ tE b, Reaches (.compute π ρ (plug tE b)) (.compute (frames ρ b ++ π) ρ tE)
  stop : ∀ π ρ b w, ok w → out w = none → Reaches (.ret (frames ρ b ++ π) w) .error
  go : ∀ π ρ b w fs, ok w → out w = some fs →
    Reaches (.ret (frames ρ b ++ π) w) (.compute π (extendAll ρ fs) b)
  len : ∀ w fs, ok w → out w = some fs → fs.length = arity
  wf : ∀ w fs, ok w → ValueWellFormed w → out w = some fs → ValueListWellFormed fs
  framesWF : ∀ d ρ b π, EnvWellFormed d ρ → d ≤ ρ.length → closedAt (d + arity) b = true →
    StackWellFormed π → StackWellFormed (frames ρ b ++ π)

/-- What a state reaching a terminal state did first. -/
theorem split_terminal {π : Stack} {ρ : CekEnv} {t : Term} {T : State} (term : Terminal T)
    (h : Reaches (.compute π ρ t) T) :
    (Errs ρ t ∧ T = .error) ∨ ∃ w, Halts ρ t w ∧ Reaches (.ret π w) T :=
  sequence term h

theorem reaches_det {s T₁ T₂ : State} (t₁ : Terminal T₁) (t₂ : Terminal T₂) (h₁ : Reaches s T₁)
    (h₂ : Reaches s T₂) : T₁ = T₂ := terminal_unique t₁ t₂ h₁ h₂

theorem unit_swap (A B : SemUnit) {d : Nat} {F : CekEnv → Prop} {tA tB T : Term}
    (hcA : closedAt d tA = true) (hcB : closedAt d tB = true)
    (hcT : closedAt (d + A.arity + B.arity) T = true)
    (hokA : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → ∀ w, Halts ρ tA w → A.ok w)
    (hokB : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → ∀ w, Halts ρ tB w → B.ok w)
    (htB : ∀ ρ, F ρ → EnvWellFormed d ρ → d ≤ ρ.length → Errs ρ tB ∨ ∃ w, Halts ρ tB w) :
    FactRefines d F (A.plug tA (B.plug (shiftN A.arity tB) T))
      (B.plug tB (A.plug (shiftN B.arity tA) (renameTerm (blockSwap A.arity B.arity) T))) := by
  intro ρ π henv hlen hπ hF
  let Bp := B.plug (shiftN A.arity tB) T
  let T' := renameTerm (blockSwap A.arity B.arity) T
  let Ap := A.plug (shiftN B.arity tA) T'
  have hcT' : closedAt (d + B.arity + A.arity) T' = true := by
    refine closedAt_rename _ T (d + A.arity + B.arity) (d + B.arity + A.arity) hcT fun n hn => ?_
    unfold blockSwap; split <;> (try split) <;> (try split) <;> omega
  -- evaluating `tA` and `tB` alike after the other step's binders
  have shiftA : ∀ (fs : List CekValue), ValueListWellFormed fs → fs.length = B.arity →
      ObsRefines (.compute (A.frames (extendAll ρ fs) T' ++ π) (extendAll ρ fs) (shiftN B.arity tA))
        (.compute (A.frames (extendAll ρ fs) T' ++ π) ρ tA) ∧
      ObsRefines (.compute (A.frames (extendAll ρ fs) T' ++ π) ρ tA)
        (.compute (A.frames (extendAll ρ fs) T' ++ π) (extendAll ρ fs) (shiftN B.arity tA)) := by
    intro fs hfs hl
    obtain ⟨henv', hlen'⟩ := extendAll_wf fs henv hlen hfs
    have hst := A.framesWF _ _ T' π henv' hlen' (by rw [hl]; simpa [Nat.add_assoc] using hcT') hπ
    have := obsEq_shiftN fs henv hlen hfs hst hcA
    rw [hl] at this
    exact ⟨this.2, this.1⟩
  have shiftB : ∀ (fs : List CekValue), ValueListWellFormed fs → fs.length = A.arity →
      ObsRefines (.compute (B.frames (extendAll ρ fs) T ++ π) (extendAll ρ fs) (shiftN A.arity tB))
        (.compute (B.frames (extendAll ρ fs) T ++ π) ρ tB) ∧
      ObsRefines (.compute (B.frames (extendAll ρ fs) T ++ π) ρ tB)
        (.compute (B.frames (extendAll ρ fs) T ++ π) (extendAll ρ fs) (shiftN A.arity tB)) := by
    intro fs hfs hl
    obtain ⟨henv', hlen'⟩ := extendAll_wf fs henv hlen hfs
    have hst := B.framesWF _ _ T π henv' hlen' (by rw [hl]; simpa [Nat.add_assoc] using hcT) hπ
    have := obsEq_shiftN fs henv hlen hfs hst hcB
    rw [hl] at this
    exact ⟨this.2, this.1⟩
  -- the bodies in the two environments
  have body : ∀ (fa fb : List CekValue), ValueListWellFormed fa → ValueListWellFormed fb →
      fa.length = A.arity → fb.length = B.arity →
      ObsRefines (.compute π (extendAll (extendAll ρ fa) fb) T)
        (.compute π (extendAll (extendAll ρ fb) fa) T') := by
    intro fa fb hfa hfb hla hlb
    have hbis := shiftBisimEnv_blockSwap henv hlen hfa hfb
    rw [hla, hlb] at hbis
    exact (obsRefines_of_shiftBisim (.compute (is0preserving_blockSwap A.arity B.arity) hbis hcT
      (shiftBisimStack_refl hπ))).1
  have hsrc := A.run π ρ tA Bp
  have htgt := B.run π ρ tB Ap
  constructor
  · -- the source halts
    rintro ⟨v, hv⟩
    have hv₁ := reaches_terminal_after (.inr ⟨v, rfl⟩) hsrc hv
    rcases split_terminal (.inr ⟨v, rfl⟩) hv₁ with ⟨_, h⟩ | ⟨wA, hwA, hv₂⟩
    · cases h
    have hokwA := hokA ρ hF henv hlen wA hwA
    have hwAwf := halts_wellFormed henv hlen hcA hwA
    cases hout : A.out wA with
    | none => exact absurd hv₂ (fun h => halt_not_error h (A.stop π ρ Bp wA hokwA hout))
    | some fsA =>
    have hfsA := A.wf wA fsA hokwA hwAwf hout
    have hlA := A.len wA fsA hokwA hout
    have hv₃ := reaches_terminal_after (.inr ⟨v, rfl⟩) (A.go π ρ Bp wA fsA hokwA hout) hv₂
    have hv₄ := reaches_terminal_after (.inr ⟨v, rfl⟩) (B.run π (extendAll ρ fsA) (shiftN A.arity tB) T) hv₃
    obtain ⟨v', hv₅⟩ := (shiftB fsA hfsA hlA).1.halt ⟨v, hv₄⟩
    rcases split_terminal (.inr ⟨v', rfl⟩) hv₅ with ⟨_, h⟩ | ⟨wB, hwB, hv₆⟩
    · cases h
    have hokwB := hokB ρ hF henv hlen wB hwB
    have hwBwf := halts_wellFormed henv hlen hcB hwB
    cases houtB : B.out wB with
    | none =>
      exact absurd hv₆ (fun h => halt_not_error h (B.stop π (extendAll ρ fsA) T wB hokwB houtB))
    | some fsB =>
    have hfsB := B.wf wB fsB hokwB hwBwf houtB
    have hlB := B.len wB fsB hokwB houtB
    have hv₇ := reaches_terminal_after (.inr ⟨v', rfl⟩) (B.go π (extendAll ρ fsA) T wB fsB hokwB houtB) hv₆
    obtain ⟨u, hu⟩ := (body fsA fsB hfsA hfsB hlA hlB).halt ⟨v', hv₇⟩
    -- the target runs `tB`, then `tA`, then the body
    have r₁ : Reaches (.compute π ρ (B.plug tB Ap)) (.compute π (extendAll ρ fsB) Ap) :=
      reaches_trans htgt (reaches_trans (halts_on_stack hwB _) (B.go π ρ Ap wB fsB hokwB houtB))
    have r₂ := reaches_trans r₁ (A.run π (extendAll ρ fsB) (shiftN B.arity tA) T')
    have hA : ∃ u, Reaches (.compute (A.frames (extendAll ρ fsB) T' ++ π) ρ tA) (.halt u) :=
      ⟨u, reaches_trans (halts_on_stack hwA _) (reaches_trans
        (A.go π (extendAll ρ fsB) T' wA fsA hokwA hout) hu)⟩
    obtain ⟨u', hu'⟩ := (shiftA fsB hfsB hlB).2.halt hA
    exact ⟨u', reaches_trans r₂ hu'⟩
  · -- the source fails
    intro he
    have he₁ := reaches_terminal_after (.inl rfl) hsrc he
    -- the target fails at `tA` once `tB` has continued
    have afterB : (∀ fsB, ValueListWellFormed fsB → fsB.length = B.arity →
        Reaches (.compute (A.frames (extendAll ρ fsB) T' ++ π) ρ tA) .error →
        Reaches (.compute π (extendAll ρ fsB) Ap) .error) := by
      intro fsB hfsB hlB h
      exact reaches_trans (A.run π (extendAll ρ fsB) (shiftN B.arity tA) T') ((shiftA fsB hfsB hlB).2.error h)
    rcases htB ρ hF henv hlen with hBe | ⟨wB, hwB⟩
    · exact reaches_trans htgt (errs_on_stack hBe _)
    have hokwB := hokB ρ hF henv hlen wB hwB
    have hwBwf := halts_wellFormed henv hlen hcB hwB
    have tgtB : ∀ fsB, B.out wB = some fsB →
        Reaches (.compute π ρ (B.plug tB Ap)) (.compute π (extendAll ρ fsB) Ap) := fun fsB h =>
      reaches_trans htgt (reaches_trans (halts_on_stack hwB _) (B.go π ρ Ap wB fsB hokwB h))
    cases houtB : B.out wB with
    | none => exact reaches_trans htgt (reaches_trans (halts_on_stack hwB _) (B.stop π ρ Ap wB hokwB houtB))
    | some fsB =>
    have hfsB := B.wf wB fsB hokwB hwBwf houtB
    have hlB := B.len wB fsB hokwB houtB
    refine reaches_trans (tgtB fsB houtB) (afterB fsB hfsB hlB ?_)
    rcases split_terminal (.inl rfl) he₁ with ⟨hAe, _⟩ | ⟨wA, hwA, he₂⟩
    · exact errs_on_stack hAe _
    have hokwA := hokA ρ hF henv hlen wA hwA
    have hwAwf := halts_wellFormed henv hlen hcA hwA
    refine reaches_trans (halts_on_stack hwA _) ?_
    cases hout : A.out wA with
    | none => exact A.stop π (extendAll ρ fsB) T' wA hokwA hout
    | some fsA =>
    have hfsA := A.wf wA fsA hokwA hwAwf hout
    have hlA := A.len wA fsA hokwA hout
    refine reaches_trans (A.go π (extendAll ρ fsB) T' wA fsA hokwA hout) ?_
    have he₃ := reaches_terminal_after (.inl rfl) (A.go π ρ Bp wA fsA hokwA hout) he₂
    have he₄ := reaches_terminal_after (.inl rfl) (B.run π (extendAll ρ fsA) (shiftN A.arity tB) T) he₃
    have he₅ := (shiftB fsA hfsA hlA).1.error he₄
    rcases split_terminal (.inl rfl) he₅ with ⟨hBe, _⟩ | ⟨wB', hwB', he₆⟩
    · exact absurd hwB (fun h => halt_not_error h hBe)
    have : wB' = wB := halts_unique hwB' hwB
    subst this
    have he₇ := reaches_terminal_after (.inl rfl) (B.go π (extendAll ρ fsA) T wB' fsB hokwB houtB) he₆
    exact (body fsA fsB hfsA hfsB hlA hlB).error he₇

end Moist.Verified.Guards
