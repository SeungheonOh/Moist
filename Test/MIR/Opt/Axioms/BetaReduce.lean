import Moist.Verified.BetaReduceSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.BetaReduce.contract_refines,
    ``Moist.Verified.MIR.BetaReduce.contract_fresh,
    ``Moist.Verified.MIR.BetaReduce.core_fresh,
    ``Moist.Verified.MIR.BetaReduce.core_refines,
    ``Moist.Verified.MIR.BetaReduce.betaReducePass_fresh,
    ``Moist.Verified.MIR.BetaReduce.betaReducePass_refines
  ]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
