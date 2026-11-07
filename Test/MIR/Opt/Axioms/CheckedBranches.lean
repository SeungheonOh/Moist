import Moist.Verified.CheckedBranchesSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.lowerDelayedListChoices_refines,
    ``Moist.Verified.MIR.fuseCheckedListBranches_refines,
    ``Moist.Verified.MIR.optimizeCheckedBranches_refines,
    ``Moist.Verified.ShapeFacts.lowerDelayedChoicesWalk_factRel,
    ``Moist.Verified.ShapeFacts.delayedChoice_factRel,
    ``Moist.Verified.ShapeFacts.delayedChoice_obsRefines,
    ``Moist.Verified.ShapeFacts.checkedBranchWalk_rel,
    ``Moist.Verified.ShapeFacts.CheckedRel.to_factRel,
    ``Moist.Verified.ShapeFacts.CheckedRel.choose,
    ``Moist.Verified.ShapeFacts.CheckedRel.nullCase,
    ``Moist.Verified.ShapeFacts.CheckedRel.fusion,
    ``Moist.Verified.ShapeFacts.CheckedRel.let_single,
    ``Moist.Verified.ShapeFacts.CheckedRel.fix_lam,
    ``Moist.Verified.ShapeFacts.chooseDelay_factRefines,
    ``Moist.Verified.ShapeFacts.chooseList_eval,
    ``Moist.Verified.ShapeFacts.nullList_eval]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
