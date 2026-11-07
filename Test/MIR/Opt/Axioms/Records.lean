import Moist.Verified.RecordsSoundness
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.unpackRecords_refines,
    ``Moist.Verified.ShapeFacts.recordWalk_factRel,
    ``Moist.Verified.ShapeFacts.unpack_factRel,
    ``Moist.Verified.ShapeFacts.FactRel.case_alternatives,
    ``Moist.Verified.ShapeFacts.replaceReads_factRel,
    ``Moist.Verified.ShapeFacts.read_factRel,
    ``Moist.Verified.ShapeFacts.shapeOf_sound,
    ``Moist.Verified.ShapeFacts.isRecord_holds,
    ``Moist.Verified.ShapeFacts.atTag_constr,
    ``Moist.Verified.ShapeFacts.fieldProjection_halts,
    ``Moist.Verified.ShapeFacts.fieldProjection_of_fields,
    ``Moist.Verified.ShapeFacts.alternativeProjection_halts,
    ``Moist.Verified.ShapeFacts.obsRefines_bind_unused,
    ``Moist.MIR.Advanced.exprSize_replaceReads]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
