import Moist.Verified.KnownListsSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.fuseKnownListCases_refines,
    ``Moist.Verified.KnownLists.knownListWalk_rel,
    ``Moist.Verified.KnownLists.KnownRel.fixApp,
    ``Moist.Verified.KnownLists.knot,
    ``Moist.Verified.KnownLists.fixApply_obs,
    ``Moist.Verified.KnownLists.partial_PR,
    ``Moist.Verified.KnownLists.calls_eval,
    ``Moist.Verified.KnownLists.spine_eval,
    ``Moist.Verified.KnownLists.lower_calls,
    ``Moist.Verified.KnownLists.lower_spine,
    ``Moist.Verified.KnownLists.listPositions_spec,
    ``Moist.Verified.ShapeFacts.KnownRel.nullFuse,
    ``Moist.Verified.ShapeFacts.KnownRel.listCase,
    ``Moist.Verified.ShapeFacts.KnownRel.let_single,
    ``Moist.Verified.ShapeFacts.KnownRel.fix_lam,
    ``Moist.Verified.ShapeFacts.KnownRel.to_factRel,
    ``Moist.Verified.ShapeFacts.knownListValue_sound,
    ``Moist.Verified.ShapeFacts.unMapData_result]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
