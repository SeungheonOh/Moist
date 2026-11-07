import Moist.Verified.LoweringSoundness
import Moist.Verified.PipelineSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.FixLowering.substLam_eval,
    ``Moist.Verified.FixLowering.fixLamWrap_forward,
    ``Moist.Verified.FixLowering.fixLamWrap_backward,
    ``Moist.Verified.LoweringSoundness.lower_correct,
    ``Moist.Verified.LoweringSoundness.lower_sound,
    ``Moist.Verified.LoweringSoundness.lower_complete,
    ``Moist.Verified.LoweringSoundness.lower_error_iff,
    ``Moist.Verified.LoweringSoundness.lowerExpr_sound,
    ``Moist.Verified.LoweringSoundness.lowerExpr_complete,
    ``Moist.Verified.LoweringSoundness.lowerExpr_error_iff,
    ``Moist.Verified.LoweringSoundness.lowerExpr_validate,
    ``Moist.Verified.LoweringSoundness.validate_ok_lowerTotalExpr,
    ``Moist.Verified.LoweringSoundness.lowerTotalExpr_validate_ok,
    ``Moist.Verified.LoweringSoundness.lower_canonical,
    ``Moist.Verified.LoweringSoundness.canon_ctxEquiv,
    ``Moist.Verified.LoweringSoundness.liftUPLC_lowerTotal,
    ``Moist.Verified.LoweringSoundness.liftUPLC_refines,
    ``Moist.Verified.LoweringSoundness.liftUPLC_lowerExpr,
    ``Moist.Verified.Pipeline.simplifyOnce_refines,
    ``Moist.Verified.Pipeline.simplifyLoop_refines,
    ``Moist.Verified.Pipeline.optimize_refines,
    ``Moist.Verified.Pipeline.optimizeExpr_refines,
    ``Moist.Verified.Pipeline.preLower_refines,
    ``Moist.Verified.Pipeline.prepareForLowering_refines,
    ``Moist.Verified.Pipeline.compileOptimized_refines_of_certificates,
    ``Moist.Verified.Pipeline.compileOptimized_refines_of,
    ``Moist.Verified.Pipeline.compileOptimized_refines_of_without_sharing,
    ``Moist.Verified.Pipeline.compileOptimized_error_of_certificates,
    ``Moist.Verified.Pipeline.compileOptimized_error_of,
    ``Moist.Verified.Pipeline.prepare_refines_of,
    ``Moist.Verified.Pipeline.simplify_refines_of,
    ``Moist.Verified.Pipeline.structural_refines_of,
    ``Moist.Verified.Pipeline.finish_refines_of]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
