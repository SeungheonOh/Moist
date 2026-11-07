import Moist.Verified.LoweringSoundness
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
    ``Moist.Verified.LoweringSoundness.liftUPLC_lowerExpr]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
