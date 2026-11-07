import Moist.Verified.CaseMergeSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.CaseMerge.caseMergePass_refines,
    ``Moist.Verified.CaseMerge.caseMerge_refines,
    ``Moist.Verified.CaseMerge.caseMerge_eval,
    ``Moist.Verified.CaseMerge.caseMergeList_eval,
    ``Moist.Verified.CaseMerge.caseMerge_lower,
    ``Moist.Verified.CaseMerge.caseMergeList_lower,
    ``Moist.Verified.CaseMerge.simple_eval,
    ``Moist.Verified.CaseMerge.reduce_correct,
    ``Moist.Verified.CaseMerge.sameRef_select,
    ``Moist.Verified.CaseMerge.sameRef_hoist,
    ``Moist.Verified.CaseMerge.atomArgs_stackRel,
    ``Moist.Verified.CaseMerge.eval_fixWrap
  ]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
