import Moist.Verified.PairListsSoundness
import Moist.Verified.CompilerSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.destructurePairEntries_refines,
    ``Moist.Verified.MIR.prepareHeads_refines,
    ``Moist.Verified.KnownLists.pairListWalk_rel,
    ``Moist.Verified.KnownLists.pairListWalk_fresh,
    ``Moist.Verified.KnownLists.KnownRel.pairEntryCase,
    ``Moist.Verified.KnownLists.pairKnowledge,
    ``Moist.Verified.KnownLists.pairListKnown_sound,
    ``Moist.Verified.KnownLists.pairListPositions_spec,
    ``Moist.Verified.KnownLists.letFixPairPositions_spec,
    ``Moist.Verified.KnownLists.KnownRel.fixApp,
    ``Moist.Verified.KnownLists.KnownRel.letFix,
    ``Moist.Verified.Pipeline.structural_refines,
    ``Moist.Verified.Pipeline.compileOptimized_refines,
    ``Moist.Verified.Pipeline.compileOptimized_error]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
