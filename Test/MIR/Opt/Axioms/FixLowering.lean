import Moist.Verified.FixLowering
import Moist.Verified.LoweringSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.FixLowering.etaU_recD,
    ``Moist.Verified.FixLowering.recD_etaU,
    ``Moist.Verified.FixLowering.fwd_eval,
    ``Moist.Verified.FixLowering.bwd_eval,
    ``Moist.Verified.FixLowering.recU_recD,
    ``Moist.Verified.FixLowering.recD_recU,
    ``Moist.Verified.FixLowering.fixLamWrap_forward,
    ``Moist.Verified.FixLowering.fixLamWrap_backward,
    ``Moist.Verified.LoweringSoundness.fixLamWrap_ctxEquiv,
    ``Moist.Verified.LoweringSoundness.envLookupT_ne_shadowed,
    ``Moist.Verified.LoweringSoundness.freeOf_substTerm_selfCall,
    ``Moist.Verified.LoweringSoundness.lower_freeOf,
    ``Moist.Verified.LoweringSoundness.lower_fix_body_freeOf,
    ``Moist.Verified.LoweringSoundness.lower_correct,
    ``Moist.Verified.LoweringSoundness.lowerExpr_sound,
    ``Moist.Verified.LoweringSoundness.lowerExpr_complete,
    ``Moist.Verified.LoweringSoundness.liftUPLC_lowerExpr]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
