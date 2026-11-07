import Moist.Verified.TagChainsSoundness
import Moist.Verified.ShapesSoundness.Pipeline
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.caseTagChains_refines,
    ``Moist.Verified.MIR.simplify_refines,
    ``Moist.Verified.TagChains.tagChainWalk_factRel,
    ``Moist.Verified.TagChains.resolvedTagTest_sound,
    ``Moist.Verified.TagChains.tagTest_sem,
    ``Moist.Verified.TagChains.testSem_direct_left,
    ``Moist.Verified.TagChains.testSem_direct_right,
    ``Moist.Verified.TagChains.tagReturns_halts,
    ``Moist.Verified.TagChains.integerCaseRule_rewrites,
    ``Moist.Verified.TagChains.rangeRule_rewrites,
    ``Moist.Verified.TagChains.errorSpine_sound,
    ``Moist.Verified.TagChains.tagCaseRule_rewrites,
    ``Moist.Verified.TagChains.push_rewrites,
    ``Moist.Verified.TagChains.pushArgument_rewrites,
    ``Moist.Verified.TagChains.unanfCase_rewrites,
    ``Moist.Verified.TagChains.unanfApp_rewrites,
    ``Moist.Verified.TagChains.deadTag_rewrites,
    ``Moist.Verified.TagChains.tagBinding_rewrites,
    ``Moist.Verified.TagChains.tagApplication_rewrites]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
