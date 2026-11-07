import Moist.Verified.CSESoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.cse_refines,
    ``Moist.Verified.CSE.cse_sound,
    ``Moist.Verified.CSE.obsUnder_reuse,
    ``Moist.Verified.CSE.reuse_ctxRefines,
    ``Moist.Verified.CSE.valueRefinesK_of_shiftBisim_rev,
    ``Moist.Verified.CSE.shifted_returns_rev,
    ``Moist.Verified.CSE.lowerTotalExpr_renameEnv,
    ``Moist.Verified.CSE.lowerTotalExprLet_merge,
    ``Moist.MIR.uniqueOptimizationBinders_nodes
  ]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
