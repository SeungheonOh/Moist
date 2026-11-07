import Moist.Verified.ProductsSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.destructureProducts_refines,
    ``Moist.Verified.ShapeFacts.productWalk_factRel,
    ``Moist.Verified.ShapeFacts.unbox_factRel,
    ``Moist.Verified.ShapeFacts.project_factRel,
    ``Moist.Verified.ShapeFacts.knownProduct_sound,
    ``Moist.Verified.ShapeFacts.product_components,
    ``Moist.Verified.ShapeFacts.replaceProjections_factRel,
    ``Moist.Verified.ShapeFacts.replaceProjections_not_free,
    ``Moist.Verified.ShapeFacts.lowerTotalExpr_skipThird,
    ``Moist.Verified.ShapeFacts.obsRefines_skipThird,
    ``Moist.MIR.Advanced.exprSize_replaceProjections]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
