import Moist.Verified.PlacementSoundness
import Moist.Verified.AllocationFinishSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.Placement.halts_fixValue,
    ``Moist.Verified.Placement.isShareable_shareable,
    ``Moist.Verified.Placement.shareReplacements_refines,
    ``Moist.Verified.Placement.mapPeeled_refines,
    ``Moist.Verified.Placement.descendPlaced_refines,
    ``Moist.Verified.Placement.placeShared_refines,
    ``Moist.Verified.Placement.shareLowBody_refines,
    ``Moist.Verified.Placement.shareLow_refines,
    ``Moist.Verified.MIR.finish_refines,
    ``Moist.Verified.MIR.finish_default_refines]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
