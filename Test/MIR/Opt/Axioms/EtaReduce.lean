import Moist.Verified.EtaReduceSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.EtaReduce.ctxRefines_of_openRel,
    ``Moist.Verified.EtaReduce.fundamental,
    ``Moist.Verified.EtaReduce.rename_eval,
    ``Moist.Verified.EtaReduce.termSubst_eval,
    ``Moist.Verified.EtaReduce.eta_openRel,
    ``Moist.Verified.EtaReduce.eta_ctxRefines,
    ``Moist.Verified.EtaReduce.eta_mirCtxRefines,
    ``Moist.Verified.MIR.etaRule_refines,
    ``Moist.Verified.MIR.etaReduceFuel_refines,
    ``Moist.Verified.MIR.etaReduce_refines,
    ``Moist.Verified.MIR.etaReduceFuel_size,
    ``Moist.Verified.MIR.etaReduceFuel_irrel,
    ``Moist.Verified.MIR.etaReduce_eq_fuel]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
