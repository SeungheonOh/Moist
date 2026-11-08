import Moist.Verified.KeyGuardsSoundness
import Moist.Verified.ShapesSoundness.Pipeline
import Moist.Verified.CompilerSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.insertKeyGuards_refines,
    ``Moist.Verified.ShapeFacts.insertGuards_factRel,
    ``Moist.Verified.ShapeFacts.guards_factRefines,
    ``Moist.Verified.ShapeFacts.keyGuardWalk_factRel,
    ``Moist.Verified.ShapeFacts.keyComparison_factRel,
    ``Moist.Verified.ShapeFacts.keyComparison_fresh,
    ``Moist.Verified.ShapeFacts.keyGuard_values,
    ``Moist.Verified.ShapeFacts.guarded_data,
    ``Moist.Verified.ShapeFacts.guarded_other,
    ``Moist.Verified.ShapeFacts.compareValue_spec,
    ``Moist.Verified.ShapeFacts.compareTermWith_halts,
    ``Moist.Verified.ShapeFacts.dropList_eval,
    ``Moist.Verified.ShapeFacts.checkedRewrite_factRel,
    ``Moist.Verified.MIR.simplify_refines,
    ``Moist.Verified.Pipeline.compileOptimized_refines,
    ``Moist.Verified.Pipeline.compileOptimized_error]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
