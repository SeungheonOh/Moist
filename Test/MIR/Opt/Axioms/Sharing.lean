import Moist.Verified.SharedLets
import Moist.Verified.SharingSoundness
import Moist.Verified.AllocationFinishSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.SharedLets.shared_eval,
    ``Moist.Verified.SharedLets.shared_lets_obs,
    ``Moist.Verified.SharedLets.shared_lets_ctxRefines,
    ``Moist.Verified.SharedLets.pinned_of_halts,
    ``Moist.Verified.SharedLets.mkLets_steps,
    ``Moist.Verified.Sharing.replace_lower,
    ``Moist.Verified.Sharing.lowerTotalExpr_closed,
    ``Moist.Verified.Sharing.lowerTotalExpr_shared_lets,
    ``Moist.Verified.Sharing.collectMatches_pred,
    ``Moist.Verified.Sharing.collectMatches_lowers,
    ``Moist.Verified.Sharing.share_refines,
    ``Moist.Verified.Sharing.share_selected_refines,
    ``Moist.Verified.Sharing.shareClosed_refines,
    ``Moist.Verified.Sharing.hoistBuiltinStates_refines,
    ``Moist.Verified.Sharing.poolConstants_refines,
    ``Moist.Verified.MIR.finish_refines,
    ``Moist.Verified.MIR.finish_without_sharing_refines,
    ``Moist.Verified.MIR.finish_default_refines]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
