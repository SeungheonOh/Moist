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

with `Step` proven deterministic (`step_det`, `Moist.Verified.SmallStep.Determinism`). -/
