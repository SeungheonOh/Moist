import Moist.Verified.ForceDelaySoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.ForceDelaySoundness.fd_openRefines,
    ``Moist.Verified.ForceDelaySoundness.forceDelay_openRefines,
    ``Moist.Verified.ForceDelaySoundness.lower_replace,
    ``Moist.Verified.ForceDelaySoundness.mirCtxRefines_force_delay,
    ``Moist.Verified.ForceDelaySoundness.mirCtxRefines_delay_let,
    ``Moist.Verified.ForceDelaySoundness.processDelayBindings_refines,
    ``Moist.Verified.ForceDelaySoundness.forceDelayCore_refines,
    ``Moist.Verified.ForceDelaySoundness.forceDelay_refines]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
