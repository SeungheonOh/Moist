import Moist.Verified.AdvancedRefinement
import Moist.Verified.ConstantFoldingSoundness
import Moist.Verified.DeadFixSoundness
import Moist.Verified.BuiltinStateSoundness
import Moist.Verified.ApplicationPackingSoundness
import Moist.Verified.HygieneSoundness
import Moist.Verified.AllocationFinishSoundness
import Moist.Verified.InlineSoundness.Frontier
import Moist.Verified.VerifiedOptimize
import Test.MIR.Opt.BudgetModel
import Test.MIR.Opt.StrictFrontier
import Test.MIR.Opt.FrontierCertificates
import Test.MIR.Opt.ListShapeCertificates
import Lean.Util.CollectAxioms
import Lean.Elab.Command

run_cmd do
  let checked := [
    ``Moist.Verified.MIR.finish_default_refines,
    ``Moist.Verified.MIR.finish_without_sharing_refines,
    ``Moist.Verified.ListShape.knownList_literal,
    ``Moist.Verified.ListShape.knownList_literal_returns,
    ``Test.MIR.Opt.ListShapeCertificates.annotation_only_list_fusion_not_refines,
    ``Test.MIR.Opt.ListShapeCertificates.corrected_checker_rejects_forged_list,
    ``Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_refines,
    ``Moist.Verified.MIR.Hygiene.uniqueOptimizationBinders_lower,
    ``Moist.Verified.MIR.Hygiene.freshenBinders_correct,
    ``Moist.Verified.MIR.AlphaEq.lowerTotalExpr_eq,
    ``Moist.Verified.MIR.lowerTotalExpr_fix_lam_shift,
    ``Moist.Verified.ContinuationRefinement.compute_of_returns,
    ``Moist.Verified.ApplicationPacking.argument_frames,
    ``Moist.Verified.ApplicationPacking.pack_returns,
    ``Moist.Verified.ApplicationPacking.pack_contextual,
    ``Moist.Verified.MIR.packApplicationSpine_refines,
    ``Moist.Verified.MIR.packApplicationsFuel_refines,
    ``Moist.Verified.MIR.packApplications_refines,
    ``Moist.Verified.MIR.packApplicationsFuel_irrel,
    ``Moist.Verified.MIR.packApplications_recursive_eq,
    ``Moist.Verified.MIR.packApplications_unique,
    ``Moist.Verified.MIR.mirCtxRefines_dead_application,
    ``Moist.Verified.MIR.mirCtxRefines_self_application,
    ``Moist.Verified.MIR.eliminateDeadFix_local,
    ``Moist.Verified.MIR.eliminateDeadFixRoot_refines,
    ``Moist.Verified.MIR.eliminateDeadFix_refines,
    ``Moist.Verified.MIR.eliminateDeadFix_recursive_eq,
    ``Moist.Verified.MIR.rewriteBottomUp_unique,
    ``Moist.Verified.BuiltinState.builtinRemainder_returns,
    ``Moist.Verified.BuiltinState.builtinRemainder_halts,
    ``Moist.Verified.BuiltinState.builtinRemainder_expandFix,
    ``Moist.Verified.BuiltinState.isTotalPreLowerValue_halts,
    ``Moist.Verified.BuiltinState.isTotalPreLowerValue_no_error,
    ``Moist.Verified.BuiltinState.isCallableValue_returns,
    ``Moist.Verified.InlineSoundness.Totality.TotalTerm.rename,
    ``Moist.Verified.InlineSoundness.Totality.TotalTerm.halts,
    ``Moist.Verified.InlineSoundness.Totality.TotalTerm.subst_halts,
    ``Moist.Verified.InlineSoundness.Totality.lowerTotal_total,
    ``Moist.Verified.InlineSoundness.Frontier.EvaluationPath.checked,
    ``Moist.Verified.InlineSoundness.Frontier.firstEvaluationUse_expandFix,
    ``Moist.Verified.InlineSoundness.Frontier.firstEvaluationUse_lowerTotal,
    ``Moist.Verified.InlineSoundness.Frontier.inlineGate_evaluationPath,
    ``Moist.Verified.InlineSoundness.Frontier.CheckedPath.errors,
    ``Moist.Verified.InlineSoundness.Frontier.evaluationPath_subst_errors,
    ``Moist.Verified.InlineSoundness.Frontier.beta_evaluationPath_ctxRefines,
    ``Moist.Verified.MIR.inline_refines,
    ``Moist.Verified.MIR.verifiedOptimize_refines,
    ``Test.MIR.Opt.FrontierCertificates.nested_beta_refines,
    ``Test.MIR.Opt.FrontierCertificates.case_beta_refines,
    ``Test.MIR.Opt.FrontierCertificates.zero_index_not_total,
    ``Moist.Verified.MIR.InlineGate_impure_frontier,
    ``Moist.Verified.InlineSoundness.Frontier.outcome_of_terminal,
    ``Moist.Verified.InlineSoundness.Frontier.same_env_beta_frontier_refines,
    ``Moist.Verified.InlineSoundness.Frontier.beta_frontier_ctxRefines,
    ``Moist.Verified.MIR.rewriteBottomUp_refines,
    ``Moist.Verified.MIR.rewriteBottomUp_complete,
    ``Moist.Verified.MIR.rewriteBottomUp_fuel_irrel,
    ``Moist.Verified.MIR.foldDataConstructor_refines,
    ``Moist.Verified.MIR.foldDataConstructors_refines,
    ``Moist.Verified.MIR.constantValue_evaluates,
    ``Moist.Verified.MIR.foldConstant_refines,
    ``Moist.Verified.MIR.constantFold_refines,
    ``Moist.Verified.MIR.constantFoldingSegment_refines,
    ``Moist.Verified.AdvancedRefinement.finite_join_refines,
    ``Moist.Verified.AdvancedRefinement.contextual_of_uniform_refinement,
    ``Moist.Verified.AdvancedRefinement.contextual_of_uniform_join,
    ``Moist.Verified.AdvancedRefinement.fold_mkCons_generic_data,
    ``Moist.Verified.AdvancedRefinement.fold_mkCons_specialized_data,
    ``Moist.Verified.AdvancedRefinement.fold_binary_builtin,
    ``Moist.Verified.AdvancedRefinement.boolean_choice,
    ``Moist.Verified.AdvancedRefinement.force_case_delay,
    ``Moist.Verified.AdvancedRefinement.delayed_list_choice_variable,
    ``Moist.Verified.InlineSoundness.StrictOcc.same_env_beta_single_obsRefines,
    ``Moist.Verified.InlineSoundness.StrictOcc.same_env_beta_multi_obsRefines,
    ``Moist.Verified.InlineSoundness.SubstCommute.uplc_beta_single_pure_openRefines,
    ``Moist.Verified.InlineSoundness.SubstCommute.uplc_beta_multi_pure_openRefines,
    ``Moist.Verified.MIR.anfNormalize_refines,
    ``Moist.Verified.MIR.dce_refines,
    ``Test.MIR.Opt.BudgetModel.unbounded_budget_exhaustion_is_false,
    ``Test.MIR.Opt.StrictFrontier.legacy_occurrence_accepts_divergent_predecessor,
    ``Test.MIR.Opt.StrictFrontier.strict_occurrence_alone_does_not_refine,
    ``Test.MIR.Opt.StrictFrontier.evaluation_path_rejects_divergent_predecessor]
  let permitted := [``propext, ``Classical.choice, ``Quot.sound]
  for declaration in checked do
    for axiomName in ← Lean.collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} depends on nonstandard axiom {axiomName}"
  Lean.logInfo m!"Checked {checked.length} declarations against the standard Lean axiom allowlist."
