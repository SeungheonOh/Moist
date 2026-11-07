import Moist.Verified.ShapesSoundness
import Test.MIR.Opt.ShapeCertificates
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.fuseListDestructors_refines,
    ``Moist.Verified.MIR.fuseListChoices_refines,
    ``Moist.Verified.MIR.shapeDCE_refines,
    ``Moist.Verified.MIR.simplifyChoices_refines,
    ``Moist.Verified.MIR.simplify_refines,
    ``Moist.Verified.ShapeFacts.knownBoolean_sound,
    ``Moist.Verified.ShapeFacts.booleanResultCore_sound,
    ``Moist.Verified.ShapeFacts.totalWithFacts_sound,
    ``Moist.Verified.ShapeFacts.mirCtxRefines_of_factRel,
    ``Test.MIR.Opt.ShapeCertificates.checked_binder_capture_not_refines,
    ``Test.MIR.Opt.ShapeCertificates.former_checked_binder_is_g,
    ``Test.MIR.Opt.ShapeCertificates.corrected_checked_binder_avoids_input]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
