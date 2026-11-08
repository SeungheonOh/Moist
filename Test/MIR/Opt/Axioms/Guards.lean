import Moist.Verified.GuardsSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.checksFirst_refines,
    ``Moist.Verified.MIR.sinkUnits_refines,
    ``Moist.Verified.MIR.pushAsserts_refines,
    ``Moist.Verified.Guards.push_rel,
    ``Moist.Verified.Guards.chk_sound,
    ``Moist.Verified.Guards.terminatesWith_sound,
    ``Moist.Verified.Guards.unit_swap,
    ``Moist.Verified.Guards.unit_sem,
    ``Moist.Verified.Guards.swap_rel,
    ``Moist.Verified.Guards.sinkPast_rel,
    ``Moist.Verified.Guards.sinkWalk_rel]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
