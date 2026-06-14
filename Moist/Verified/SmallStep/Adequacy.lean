import Moist.Verified.SmallStep.Simulation
import Moist.Verified.SmallStep.Measure
import Moist.Verified.Definitions

/-! # Operational adequacy: CEK machine ↔ small-step reduction

The main theorems relate CEK reachability (`Moist.Verified.Equivalence.Reaches`
over `Moist.CEK.step`) to the small-step `Steps` relation, for closed canonical
terms.

* `adequacy_halt`: the CEK halts at `v` iff small-step reduction reaches the
  (canonical) value `discharge v`.
* `adequacy_error`: the CEK errors iff small-step reduction reaches a stuck
  normal form.

The forward direction (`→`) is the iterated forward simulation `sim_step`; the
backward direction (`←`) is the termination argument `reach_terminal`
(determinism of `Step` bounds the small-step path, and the administrative measure
`μ` bounds the machine's silent transitions), packaged in `Measure.lean`.
-/

namespace Moist.Verified.SmallStep

open Moist.Plutus.Term (Term)
open Moist.CEK
open Moist.Verified (closedAt)
open Moist.Verified.Equivalence (steps Reaches)

/-! ## Iterating the invariants and fixpoints -/

theorem steps_good : ∀ (n : Nat) {s : State}, GoodState s → GoodState (steps n s)
  | 0, _, h => h
  | n + 1, s, h => by rw [steps]; exact steps_good n (step_preserves_good h)

theorem steps_canon : ∀ (n : Nat) {s : State}, CanonState s → CanonState (steps n s)
  | 0, _, h => h
  | n + 1, s, h => by rw [steps]; exact steps_canon n (step_preserves_canon h)

theorem steps_error : ∀ (n : Nat), steps n .error = .error
  | 0 => rfl
  | n + 1 => by rw [steps]; exact steps_error n

theorem steps_halt : ∀ (n : Nat) (v : CekValue), steps n (.halt v) = .halt v
  | 0, _ => rfl
  | n + 1, v => by rw [steps]; exact steps_halt n v

/-- `.Error` is a stuck small-step normal form. -/
theorem stuck_error : Stuck (.Error) := ⟨fun ⟨_, h⟩ => not_step_error h, not_value_error⟩

/-! ## Forward direction (CEK ⇒ small-step) -/

/-- If the CEK reaches `halt v` in `n` steps, the discharged term reduces to the
    (canonical) value `discharge v`. -/
theorem reaches_halt_fwd : ∀ (n : Nat) {s : State} {v : CekValue}, steps n s = .halt v →
    GoodState s → CanonState s → Steps (dischargeState s) (discharge v) ∧ Value (discharge v)
  | 0, s, v, h, hg, _ => by
    cases h
    exact ⟨.refl, value_discharge (good_wf hg)⟩
  | n + 1, s, v, h, hg, hc => by
    rw [steps] at h
    rcases sim_step s hg hc with hprog | ⟨herr, _⟩
    · obtain ⟨hsteps, hval⟩ :=
        reaches_halt_fwd n h (step_preserves_good hg) (step_preserves_canon hc)
      exact ⟨Steps.trans hprog hsteps, hval⟩
    · rw [herr, steps_error] at h; cases h

/-- If the CEK reaches `error`, the discharged term reduces to a stuck normal form. -/
theorem reaches_error_fwd : ∀ (n : Nat) {s : State}, steps n s = .error →
    GoodState s → CanonState s → ∃ w, Steps (dischargeState s) w ∧ Stuck w
  | 0, s, h, _, _ => by cases h; exact ⟨.Error, .refl, stuck_error⟩
  | n + 1, s, h, hg, hc => by
    rw [steps] at h
    rcases sim_step s hg hc with hprog | ⟨_, hstuck⟩
    · obtain ⟨w, hsteps, hw⟩ :=
        reaches_error_fwd n h (step_preserves_good hg) (step_preserves_canon hc)
      exact ⟨w, Steps.trans hprog hsteps, hw⟩
    · exact ⟨dischargeState s, .refl, hstuck⟩

/-! ## Forward adequacy (the CEK ⇒ small-step half)

For a closed canonical term `t`: if the CEK machine halts at `v`, small-step
reduction reaches the canonical value `discharge v`; if it errors, small-step
reduction reaches a stuck normal form. -/

/-- **Forward halting adequacy.** -/
theorem adequacy_halt_fwd {t : Term} {v : CekValue}
    (ht : closedAt 0 t = true) (htc : Canonical t) (h : Reaches (init t) (.halt v)) :
    Steps t (discharge v) ∧ Value (discharge v) := by
  obtain ⟨n, hn⟩ := h
  have := reaches_halt_fwd n hn (init_good ht) (init_canon htc)
  rwa [dischargeState_init] at this

/-- **Forward error adequacy.** -/
theorem adequacy_error_fwd {t : Term}
    (ht : closedAt 0 t = true) (htc : Canonical t) (h : Reaches (init t) .error) :
    ∃ w, Steps t w ∧ Stuck w := by
  obtain ⟨n, hn⟩ := h
  have := reaches_error_fwd n hn (init_good ht) (init_canon htc)
  rwa [dischargeState_init] at this

/-! ## The adequacy theorems (full ↔)

The forward (`→`) directions iterate `sim_step`; the backward (`←`) directions
combine `cek_terminates` (the machine halts because the term has a small-step
normal form) with `normal_form_unique` (determinism pins down which terminal). -/

/-- **Halting adequacy.** For a closed canonical term `t`, the CEK machine halts
    iff small-step reduction reaches a value. -/
theorem adequacy_halt {t : Term} (ht : closedAt 0 t = true) (htc : Canonical t) :
    (∃ v, Reaches (init t) (.halt v)) ↔ (∃ w, Steps t w ∧ Value w) := by
  constructor
  · rintro ⟨v, hr⟩
    obtain ⟨hsteps, hval⟩ := adequacy_halt_fwd ht htc hr
    exact ⟨discharge v, hsteps, hval⟩
  · rintro ⟨w, hsteps, hval⟩
    obtain ⟨k, hk⟩ := steps_stepsN hsteps
    obtain ⟨n, hterm⟩ := cek_terminates ht htc hk (value_normal hval)
    rcases hterm with ⟨v, hv⟩ | herr
    · exact ⟨v, n, hv⟩
    · obtain ⟨w', hsteps', hstuck'⟩ := adequacy_error_fwd ht htc ⟨n, herr⟩
      have hww : w = w' := normal_form_unique hsteps (value_normal hval) hsteps' hstuck'.1
      exact absurd (hww ▸ hval) hstuck'.2

/-- **Error adequacy.** For a closed canonical term `t`, the CEK machine errors
    iff small-step reduction reaches a stuck normal form. -/
theorem adequacy_error {t : Term} (ht : closedAt 0 t = true) (htc : Canonical t) :
    Reaches (init t) .error ↔ ∃ w, Steps t w ∧ Stuck w := by
  constructor
  · exact adequacy_error_fwd ht htc
  · rintro ⟨w, hsteps, hstuck⟩
    obtain ⟨k, hk⟩ := steps_stepsN hsteps
    obtain ⟨n, hterm⟩ := cek_terminates ht htc hk hstuck.1
    rcases hterm with ⟨v, hv⟩ | herr
    · obtain ⟨hsteps', hval'⟩ := adequacy_halt_fwd ht htc ⟨n, hv⟩
      have hww : w = discharge v := normal_form_unique hsteps hstuck.1 hsteps' (value_normal hval')
      exact absurd hval' (hww ▸ hstuck.2)
    · exact ⟨n, herr⟩

end Moist.Verified.SmallStep
