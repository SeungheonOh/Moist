import Moist.Verified.ShapesSoundness
import Moist.Verified.CompilerSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.ShapeFacts.booleanResultCore_sound,
    ``Moist.Verified.ShapeFacts.knownBoolean_sound,
    ``Moist.Verified.ShapeFacts.lam_case_opaque,
    ``Moist.Verified.ShapeFacts.alternative_case,
    ``Moist.Verified.ShapeFacts.scrutineeFieldCounts_sound,
    ``Moist.Verified.ShapeFacts.case_dispatch_counted,
    ``Moist.Verified.ShapeFacts.telescope_prefix_halts,
    ``Moist.Verified.ShapeFacts.case_error_factRel,
    ``Moist.Verified.ShapeFacts.case_litBool_factRel,
    ``Moist.Verified.ShapeFacts.case_let_hoist_factRel,
    ``Moist.Verified.ShapeFacts.case_of_case_factRel,
    ``Moist.Verified.ShapeFacts.case_identity_factRel,
    ``Moist.Verified.ShapeFacts.pushBooleanCase_factRel,
    ``Moist.Verified.ShapeFacts.pushBooleanCase_fresh,
    ``Moist.Verified.ShapeFacts.booleanCaseRewrite_factRel,
    ``Moist.Verified.ShapeFacts.booleanCaseRewrite_fresh,
    ``Moist.Verified.ShapeFacts.checkedRewrite_factRel,
    ``Moist.Verified.ShapeFacts.shapeRewrite_factRel,
    ``Moist.Verified.MIR.shapeDCE_refines,
    ``Moist.Verified.MIR.simplify_refines,
    ``Moist.Verified.Pipeline.compileOptimized_refines,
    ``Moist.Verified.Pipeline.compileOptimized_error]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
