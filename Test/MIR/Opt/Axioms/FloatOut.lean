import Moist.Verified.FloatOutSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.FloatOut.floatOut_refines,
    ``Moist.Verified.FloatOut.floatOutGo_refines,
    ``Moist.Verified.FloatOut.floatCase_refines,
    ``Moist.Verified.FloatOut.tryFloat_lam,
    ``Moist.Verified.FloatOut.tryFloat_fix,
    ``Moist.Verified.FloatOut.mirCtxRefines_reorder,
    ``Moist.Verified.FloatOut.mirCtxRefines_floatLam,
    ``Moist.Verified.FloatOut.mirCtxRefines_floatFix,
    ``Moist.Verified.FloatOut.mirCtxRefines_letSwap,
    ``Moist.Verified.FloatOut.mirCtxRefines_floatCaseAlt,
    ``Moist.Verified.FloatOut.lowerTotalExpr_lookupShift,
    ``Moist.Verified.FloatOut.openRefines_floatLam,
    ``Moist.Verified.FloatOut.openRefines_floatCase,
    ``Moist.Verified.FloatOut.ctxRefines_floatFix
  ]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
