import Moist.Verified.CompilerSoundness
import Moist.Verified.TuningSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.peelRecursion_refines,
    ``Moist.Verified.Pipeline.structural_refines,
    ``Moist.Verified.Pipeline.stageCertificates,
    ``Moist.Verified.Pipeline.preLower_refines',
    ``Moist.Verified.Pipeline.compileOptimized_refines,
    ``Moist.Verified.Pipeline.compiledProfile_refines,
    ``Moist.Verified.Pipeline.compileVariants_profiles,
    ``Moist.Verified.Pipeline.peelProfiles_effective,
    ``Moist.Verified.Pipeline.tuningCandidates_respectsPeelSearch,
    ``Moist.Verified.Pipeline.selectBest_wasScored,
    ``Moist.Verified.Pipeline.compileTuned_wasScored,
    ``Moist.Verified.Pipeline.compileTuned_respectsPeelSearch,
    ``Moist.Verified.Pipeline.compileTuned_refines,
    ``Moist.Verified.Pipeline.compileOptimized_error]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
