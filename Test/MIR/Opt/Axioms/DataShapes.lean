import Moist.Verified.DataShapesSoundness
import Moist.Verified.ShapesSoundness.Pipeline
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.specializeDataChecks_refines,
    ``Moist.Verified.MIR.simplify_refines,
    ``Moist.Verified.MIR.shapeDCE_refines,
    ``Moist.Verified.ShapeFacts.dataCheckRewrite_refines,
    ``Moist.Verified.ShapeFacts.kindGuard_refines,
    ``Moist.Verified.ShapeFacts.guard_obs,
    ``Moist.Verified.ShapeFacts.shapeRewrite_factRel,
    ``Moist.Verified.ShapeFacts.roundTripInverse_factRel,
    ``Moist.Verified.ShapeFacts.knownPairDataList_sound,
    ``Moist.Verified.ShapeFacts.knownDataList_sound]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
