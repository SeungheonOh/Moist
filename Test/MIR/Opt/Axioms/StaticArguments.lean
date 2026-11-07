import Moist.Verified.StaticArgumentsSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.StaticArguments.Rel.closedAt,
    ``Moist.Verified.StaticArguments.rel_eval,
    ``Moist.Verified.StaticArguments.body_rel,
    ``Moist.Verified.StaticArguments.openRefines_static,
    ``Moist.Verified.MIR.StaticArguments.lower_var,
    ``Moist.Verified.MIR.StaticArguments.lower_call,
    ``Moist.Verified.MIR.StaticArguments.lower_rel,
    ``Moist.Verified.MIR.staticArgument_local,
    ``Moist.Verified.MIR.staticArgumentsRoot_refines,
    ``Moist.Verified.MIR.staticArgumentsFuel_refines,
    ``Moist.Verified.MIR.staticArgumentsCore_refines,
    ``Moist.Verified.MIR.staticArguments_refines]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
