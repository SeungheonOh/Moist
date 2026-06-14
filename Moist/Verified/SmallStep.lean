import Moist.Verified.SmallStep.Value
import Moist.Verified.SmallStep.Discharge
import Moist.Verified.SmallStep.Step
import Moist.Verified.SmallStep.StepLemmas
import Moist.Verified.SmallStep.DischargeLemmas
import Moist.Verified.SmallStep.ValueDischarge
import Moist.Verified.SmallStep.StackDischarge
import Moist.Verified.SmallStep.Subst

/-! # Small-step UPLC semantics and CEK adequacy

Umbrella module for the port of the Plutus Core specification's small-step
contextual-reduction semantics (`untyped-reduction.tex`) and its operational
adequacy with respect to the CEK machine.  See
`docs/SmallStep-CEK-Equivalence-Plan.md`. -/
