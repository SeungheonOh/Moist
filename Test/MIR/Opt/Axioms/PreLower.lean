import Moist.Verified.PreLowerSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.PreLower.subst_redex_refines,
    ``Moist.Verified.MIR.PreLower.drop_redex_refines,
    ``Moist.Verified.MIR.PreLower.preLowerInlineFuel_sound,
    ``Moist.Verified.MIR.PreLower.preLowerInline_refines,
    ``Moist.Verified.MIR.PreLower.preLowerInlineExpr_refines,
    ``Moist.Verified.MIR.PreLower.preLower_go_refines_of,
    ``Moist.Verified.MIR.PreLower.preLower_refines_of]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
