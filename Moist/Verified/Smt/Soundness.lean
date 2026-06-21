import Moist.Verified.Smt.Simulation

/-! # Stage 2 — soundness of the UPLC→SMT compiler (statement + bridge)

Under any well-formed model `M`, the compiled symbolic outcome agrees with `bigEval`
(proven `≡ CEK` both ways, `Moist.Verified.BigStep.bigEval_iff_halt`), and a determinate
(`¬inc`) symbolic error means the CEK genuinely fails (never halts with a value).

The denotation defs live in `Denote.lean`; the workhorse simulation lemmas live in
`Simulation.lean`. This file states the top-level theorem and the closed-term machine
corollaries.

## The three outcomes (decision: "fails" = does not halt with a value)

For a compiled `r = symEval f ρ t`, under a well-formed model `M` with `ρ_M = denoteEnv M ρ`:

* `⟦inc⟧_M = true`  → **no claim**.
* `⟦inc⟧_M = false ∧ ⟦err⟧_M = false` → `bigEval f ρ_M t = some ⟦val⟧_M`.
* `⟦inc⟧_M = false ∧ ⟦err⟧_M = true`  → `bigEval f' ρ_M t = none` for **all** `f'`.
-/

namespace Moist.Verified.Smt

open Moist.Symbolic
open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.Verified.BigStep (bigEval bigEval_iff_halt bigEval_sound)

/-! ## The soundness theorem

The workhorse is `Simulation.lean`'s matched-fuel structural simulation `symEval ≡ bigEval`,
exposed there as `sim_value`/`sim_error`/`error_stable`. -/

/-- **Soundness (`bigEval` level).** A determinate symbolic result agrees with the reference
big-step semantics, and a determinate error is genuine (fuel-stable `none`). Since
`bigEval ≡ CEK`, this is agreement with the CEK. (Proved in `Simulation.lean`.) -/
theorem symbolic_sound (M : Model) (f : Nat) (ρ : SymEnv) (t : Term)
    (hwf : WFSymEnv M ρ)
    (hinc : denoteInc M (symEval f ρ t) = false) :
    bigEval f (denoteEnv M ρ) t
      = (if denoteErr M (symEval f ρ t) then none
         else some (denoteSymV M (symEval f ρ t).val))
    ∧ (denoteErr M (symEval f ρ t) = true →
        ∀ f', bigEval f' (denoteEnv M ρ) t = none) := by
  refine ⟨?_, ?_⟩
  · cases herr : denoteErr M (symEval f ρ t) with
    | false => simpa [herr] using sim_value M f ρ t hwf hinc herr
    | true  => simpa [herr] using sim_error M f ρ t hwf hinc herr
  · intro herr; exact error_stable M f ρ t hwf hinc herr

/-! ## Machine-level corollary (closed terms) -/

open Moist.Verified.SmallStep (init)
open Moist.Verified.Equivalence (Reaches)

/-- **SMT-pass ⟹ CEK halts at the value** (closed term). -/
theorem closed_pass_halts (M : Model) (f : Nat) (t : Term)
    (hinc : denoteInc M (symEval f [] t) = false)
    (herr : denoteErr M (symEval f [] t) = false) :
    Reaches (init t) (.halt (denoteSymV M (symEval f [] t).val)) := by
  have h := sim_value M f [] t (by simp [WFSymEnv]) hinc herr
  simpa [denoteEnv] using bigEval_sound (by simpa [denoteEnv] using h)

/-- **Determinate SMT-error ⟹ CEK never halts with a value** (closed term). -/
theorem closed_error_fails (M : Model) (f : Nat) (t : Term)
    (hinc : denoteInc M (symEval f [] t) = false)
    (herr : denoteErr M (symEval f [] t) = true) :
    ¬ ∃ v, Reaches (init t) (.halt v) := by
  rintro ⟨v, hv⟩
  obtain ⟨f', hf'⟩ := (bigEval_iff_halt).2 hv
  have := error_stable M f [] t (by simp [WFSymEnv]) hinc herr f'
  rw [denoteEnv] at this
  rw [this] at hf'
  exact Option.noConfusion hf'

end Moist.Verified.Smt
