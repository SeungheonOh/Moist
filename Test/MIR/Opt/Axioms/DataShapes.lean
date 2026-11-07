import Moist.Verified.DataShapesSoundness
import Moist.Verified.ShapesSoundness.Pipeline
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.specializeDataChecks_refines,
    ``Moist.Verified.MIR.insertKeyBytes_refines,
    ``Moist.Verified.MIR.simplify_refines,
    ``Moist.Verified.MIR.shapeDCE_refines,
    ``Moist.Verified.ShapeFacts.dataCheckRewrite_refines,
    ``Moist.Verified.ShapeFacts.kindGuard_refines,
    ``Moist.Verified.ShapeFacts.guard_obs,
    ``Moist.Verified.ShapeFacts.insertKey_factRel,
    ``Moist.Verified.ShapeFacts.keyBytesWalk_factRel,
    ``Moist.Verified.ShapeFacts.keyBytesWalk_fresh,
    ``Moist.Verified.ShapeFacts.dataComparison_factRel,
    ``Moist.Verified.ShapeFacts.dataComparison_fresh,
    ``Moist.Verified.ShapeFacts.keyed_comparison_factRel,
    ``Moist.Verified.ShapeFacts.otherKey_values,
    ``Moist.Verified.ShapeFacts.comparison_obs,
    ``Moist.Verified.ShapeFacts.shapeRewrite_factRel]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
