import Moist.Verified.TagGuardSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.tagGuards_refines,
    ``Moist.Verified.TagGuard.tagGuardWalk_factRel,
    ``Moist.Verified.TagGuard.pairGuard_sound,
    ``Moist.Verified.TagGuard.pairGuard_post,
    ``Moist.Verified.TagGuard.guard_sound,
    ``Moist.Verified.TagGuard.aeval_sound,
    ``Moist.Verified.TagGuard.factRefines_pairCase,
    ``Moist.Verified.TagGuard.factRefines_sinkPair,
    ``Moist.Verified.TagGuard.factRefines_guard,
    ``Moist.Verified.FailFast.factRefines_swapLet]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
