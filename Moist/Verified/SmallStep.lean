import Moist.Verified.SmallStep.Value
import Moist.Verified.SmallStep.Discharge
import Moist.Verified.SmallStep.Step
import Moist.Verified.SmallStep.StepLemmas
import Moist.Verified.SmallStep.DischargeLemmas
import Moist.Verified.SmallStep.ValueDischarge
import Moist.Verified.SmallStep.StackDischarge
import Moist.Verified.SmallStep.Subst
import Moist.Verified.SmallStep.Determinism
import Moist.Verified.SmallStep.Closed
import Moist.Verified.SmallStep.ReflectBridge
import Moist.Verified.SmallStep.Invariant
import Moist.Verified.SmallStep.Canon
import Moist.Verified.SmallStep.Simulation
import Moist.Verified.SmallStep.Measure
import Moist.Verified.SmallStep.Adequacy
import Moist.Verified.SmallStep.Executable

/-! # Small-step UPLC semantics and CEK adequacy

Umbrella module for the port of the Plutus Core specification's small-step
contextual-reduction semantics (`untyped-reduction.tex`) and its operational
adequacy with respect to the CEK machine.  See
`docs/SmallStep-CEK-Equivalence-Plan.md`.

The headline results (`Moist.Verified.SmallStep.Adequacy`) are, for any closed,
canonical `Term` `t`:

* `adequacy_halt` : `(∃ v, Reaches (init t) (.halt v)) ↔ (∃ w, Steps t w ∧ Value w)`
* `adequacy_error`: `Reaches (init t) .error ↔ ∃ w, Steps t w ∧ Stuck w`
* `adequacy_halt_fwd` : the exact-value forward characterization
  (`Reaches (init t) (.halt v) → Steps t (discharge v) ∧ Value (discharge v)`).

with `Step` proven deterministic (`step_det`, `Moist.Verified.SmallStep.Determinism`).

An **executable, SMT/Blaster-friendly** presentation lives in
`Moist.Verified.SmallStep.Executable`: total functions `isValue : Term → Bool`,
`stepF : Term → Option Term`, and the fuel-driven `evalF : Nat → Term → Outcome`,
each proven equivalent to the relational semantics —

* `isValue_iff` : `isValue t = true ↔ Value t`
* `stepF_some_iff` : `stepF t = some t' ↔ Step t t'`  (and `stepF_none_iff` for normal forms)
* `evalF_value_iff` : `(∃ n, evalF n t = .value w) ↔ (Steps t w ∧ Value w)`
* `evalF_adequacy` : composed with `adequacy_halt`, `evalF` halts on a value iff the CEK does.

Unlike the `Prop` relations, `evalF` is a total function Blaster can symbolically
execute (the same way it runs the CEK `exec`), so a `#blaster` proof of
`evalF N t = .value …` certifies CEK halting via `evalF_adequacy`. -/
