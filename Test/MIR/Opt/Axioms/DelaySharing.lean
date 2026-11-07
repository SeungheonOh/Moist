import Moist.Verified.DelaySharingSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.DelaySharing.ForceShare.closedAt_right,
    ``Moist.Verified.DelaySharing.forceShare_eval,
    ``Moist.Verified.DelaySharing.obsRefinesK_forward_right,
    ``Moist.Verified.DelaySharing.share_let_openRefines,
    ``Moist.Verified.DelaySharing.removeForces_lower,
    ``Moist.Verified.MIR.share_let_refines,
    ``Moist.Verified.MIR.shareDelayBinding_refines,
    ``Moist.Verified.MIR.shareDelayBindings_refines,
    ``Moist.Verified.MIR.shareDelaysLocal_refines,
    ``Moist.Verified.MIR.shareDelaysCore_refines,
    ``Moist.Verified.MIR.shareDelayedValues_refines,
    ``Moist.Verified.MIR.prepare_refines]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
