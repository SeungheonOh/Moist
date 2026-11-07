import Moist.Verified.ProductsSoundness
import Moist.Verified.CompilerSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.destructureProducts_refines,
    ``Moist.Verified.ShapeFacts.productWalk_factRel,
    ``Moist.Verified.ShapeFacts.unbox_factRel,
    ``Moist.Verified.ShapeFacts.unboxProjection_factRel,
    ``Moist.Verified.ShapeFacts.resolvedProjection_factRel,
    ``Moist.Verified.ShapeFacts.projectionKind_some,
    ``Moist.Verified.ShapeFacts.projectsBinder_true,
    ``Moist.Verified.ShapeFacts.replaceProjections_factRel,
    ``Moist.Verified.ShapeFacts.replaceProjections_not_free,
    ``Moist.Verified.ShapeFacts.freshIn_replaceProjections,
    ``Moist.Verified.ShapeFacts.maxUidExpr_replaceProjections,
    ``Moist.Verified.ShapeFacts.lowerTotalExpr_skipTwo,
    ``Moist.Verified.ShapeFacts.obsRefines_skipTwo,
    ``Moist.MIR.Advanced.exprSize_replaceProjections,
    ``Moist.MIR.Advanced.replaceProjections_let_shape,
    ``Moist.MIR.Advanced.projectedArgument_some,
    ``Moist.Verified.Pipeline.compileOptimized_refines,
    ``Moist.Verified.Pipeline.compileOptimized_error]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
