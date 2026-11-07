import Moist.Verified.FailFastSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.failFast_refines,
    ``Moist.Verified.FailFast.failFastWalk_factRel,
    ``Moist.Verified.FailFast.sinkInto_ok,
    ``Moist.Verified.FailFast.factRefines_sinkCase,
    ``Moist.Verified.FailFast.factRefines_sinkCase_drop,
    ``Moist.Verified.FailFast.factRefines_letError,
    ``Moist.Verified.FailFast.terminates_sound,
    ``Moist.Verified.FailFast.sound_lt]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
