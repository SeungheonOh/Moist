import Moist.SMT.Soundness.ResultQueries
import Moist.SMT.Compiler.ExpressionIdentity

/-!
The optimizer and the CEK endpoints for the supported (no-opaque-builtin)
fragment must remain free of project postulates and `sorryAx`.  These guarded
kernel reports intentionally permit only Lean's standard logical foundations.
-/

/--
info: 'Moist.SMT.UPLC.scriptWith_assertions' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.scriptWith_assertions

/--
info: 'Moist.SMT.UPLC.scriptWithTactic_assertions' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.scriptWithTactic_assertions

/--
info: 'Moist.SMT.UPLC.groupedAssertions_true_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.groupedAssertions_true_iff

/--
info: 'Moist.SMT.UPLC.scriptWith_assertionsTrue_iff_fullPrelude' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.scriptWith_assertionsTrue_iff_fullPrelude

/--
info: 'Moist.SMT.UPLC.Soundness.scriptWith_hasCompilerPrelude' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.scriptWith_hasCompilerPrelude

/--
info: 'Moist.SMT.Semantics.evalBool?_simplifyBool' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Semantics.evalBool?_simplifyBool

/--
info: 'Moist.SMT.Semantics.evalBoolIs_and_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Semantics.evalBoolIs_and_true

/--
info: 'Moist.SMT.Semantics.evalBoolIs_or_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Semantics.evalBoolIs_or_true

/--
info: 'Moist.SMT.Semantics.eval_and_of_bools' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Semantics.eval_and_of_bools

/--
info: 'Moist.SMT.Semantics.eval_or_of_bools' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Semantics.eval_or_of_bools

/--
info: 'Moist.SMT.UPLC.Soundness.eval_intAdd_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_intAdd_of

/--
info: 'Moist.SMT.UPLC.Soundness.eval_intSub_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_intSub_of

/--
info: 'Moist.SMT.UPLC.Soundness.eval_intMul_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_intMul_of

/--
info: 'Moist.SMT.UPLC.SExpr.same?' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.SExpr.same?

/--
info: 'Moist.SMT.UPLC.SExpr.same?_eq_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.SExpr.same?_eq_true

/--
info: 'Moist.SMT.Compiler.ExpressionIdentity.decEq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Compiler.ExpressionIdentity.decEq

/--
info: 'Moist.SMT.UPLC.Soundness.OutputAnalysis.generatedAssertionsOutputSafe_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.OutputAnalysis.generatedAssertionsOutputSafe_eq

/--
info: 'Moist.SMT.UPLC.Soundness.GeneratedOutputContract.outputAccepted_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.GeneratedOutputContract.outputAccepted_eq

/--
info: 'Moist.SMT.UPLC.Soundness.CheckedCompiler.compile_some' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.CheckedCompiler.compile_some

/--
info: 'Moist.SMT.UPLC.Soundness.GeneratedOutputContract.check_isSome' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.GeneratedOutputContract.check_isSome

/--
info: 'Moist.SMT.UPLC.Soundness.eval_reflexiveEq_int_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_reflexiveEq_int_of

/--
info: 'Moist.SMT.UPLC.Soundness.eval_reflexiveEq_bytes_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_reflexiveEq_bytes_of

/--
info: 'Moist.SMT.UPLC.Soundness.eval_reflexiveEq_string_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_reflexiveEq_string_of

/--
info: 'Moist.SMT.UPLC.Soundness.eval_reflexiveEq_data_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.eval_reflexiveEq_data_of

/--
info: 'Moist.SMT.UPLC.Soundness.evalBoolIs_anyBalanced_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBoolIs_anyBalanced_true

/--
info: 'Moist.SMT.UPLC.Soundness.evalBoolIs_any_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBoolIs_any_true

/--
info: 'Moist.SMT.UPLC.Soundness.evalBool?_any_eq_referenceLinearAny' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBool?_any_eq_referenceLinearAny

/--
info: 'Moist.SMT.UPLC.Soundness.evalBoolIs_any_eq_referenceLinearAny' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBoolIs_any_eq_referenceLinearAny

/--
info: 'Moist.SMT.UPLC.Soundness.evalBoolIs_any_true_of_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBoolIs_any_true_of_mem

/--
info: 'Moist.SMT.UPLC.Soundness.bindOk_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.bindOk_mem

/--
info: 'Moist.SMT.UPLC.Soundness.carryError_mem' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.carryError_mem

/--
info: 'Moist.SMT.UPLC.Soundness.carryTimeout_mem' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.carryTimeout_mem

/--
info: 'Moist.SMT.UPLC.Soundness.bindOut_anyOkOutcome_eq_unpruned' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.bindOut_anyOkOutcome_eq_unpruned

/--
info: 'Moist.SMT.UPLC.Soundness.bindOut_anyErrorOutcome_eq_unpruned' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.bindOut_anyErrorOutcome_eq_unpruned

/--
info: 'Moist.SMT.UPLC.Soundness.bindOut_anyTimeoutOutcome_eq_unpruned' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.bindOut_anyTimeoutOutcome_eq_unpruned

/--
info: 'Moist.SMT.UPLC.Soundness.mem_pruneFalseOutcomes_iff_of_active' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.mem_pruneFalseOutcomes_iff_of_active

/--
info: 'Moist.SMT.UPLC.SExpr.sameAtom_eq_true' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.SExpr.sameAtom_eq_true

/--
info: 'Moist.SMT.UPLC.Soundness.mergeEncodedOks_active' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.mergeEncodedOks_active

/--
info: 'Moist.SMT.UPLC.Soundness.mergeEncodedConstListOks_erase' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.mergeEncodedConstListOks_erase

/--
info: 'Moist.SMT.UPLC.Soundness.compactOutcomes_active_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.compactOutcomes_active_ok

/--
info: 'Moist.SMT.UPLC.Soundness.compactOutcomes_active_error' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.compactOutcomes_active_error

/--
info: 'Moist.SMT.UPLC.Soundness.compactOutcomes_active_timeout' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.compactOutcomes_active_timeout

/--
info: 'Moist.SMT.UPLC.Soundness.exactConstListLength_eval_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.exactConstListLength_eval_length

/--
info: 'Moist.SMT.UPLC.ConstListLengthHint.inferExact?' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.ConstListLengthHint.inferExact?

/--
info: 'Moist.SMT.UPLC.ConstListLengthHint.knownLength' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.ConstListLengthHint.knownLength

/--
info: 'Moist.SMT.UPLC.Soundness.inferExactConstListLength?_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.inferExactConstListLength?_sound

/--
info: 'Moist.SMT.UPLC.Soundness.constListBranches_complete_for_toCek' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.constListBranches_complete_for_toCek

/--
info: 'Moist.SMT.UPLC.Soundness.evalBuiltinStatic?_ok_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBuiltinStatic?_ok_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalBuiltinStatic?_error_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBuiltinStatic?_error_sound

/--
info: 'Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_value_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_value_iff

/--
info: 'Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_error_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_error_iff

/--
info: 'Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_deferred_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.GroundBuiltin.evaluateStackArguments_eq_deferred_iff

/--
info: 'Moist.SMT.UPLC.Soundness.evalBuiltinSaturated_ok_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBuiltinSaturated_ok_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalBuiltinSaturated_error_sound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalBuiltinSaturated_error_sound

/--
info: 'Moist.SMT.UPLC.Soundness.builtinOkSoundAllowed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.builtinOkSoundAllowed

/--
info: 'Moist.SMT.UPLC.Soundness.builtinErrorSoundAllowed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.builtinErrorSoundAllowed

/--
info: 'Moist.Verified.BigStep.bigEval_iff_halt_env' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.Verified.BigStep.bigEval_iff_halt_env

/--
info: 'Moist.Verified.ExactBigStep.eval_fwd' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.Verified.ExactBigStep.eval_fwd

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_active_error_noOpaque_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_active_error_noOpaque_le

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_activeOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_activeOk_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_activeError_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_activeError_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_errorCond_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_errorCond_exact

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_allFuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_allFuel

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_errorCond_allFuel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_errorCond_allFuel

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_errorCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_errorCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_okBoolTrueCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_okBoolTrueCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.okCond_eval_true_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.okCond_eval_true_mem

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_okCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_okCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.okBoolFalseCond_eval_true_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.okBoolFalseCond_eval_true_mem

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_okBoolEqCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_okBoolEqCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.okIntEqCond_eval_true_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.okIntEqCond_eval_true_mem

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_okIntEqCond_bigEval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_okIntEqCond_bigEval

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkIntEqCond_bigEval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkIntEqCond_bigEval

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkIntEqCond_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkIntEqCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_okIntEqCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_okIntEqCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.inputSymEnvSafe_decodes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.inputSymEnvSafe_decodes

/--
info: 'Moist.SMT.Semantics.evalBoolIs_val_valid_of_eval' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.Semantics.evalBoolIs_val_valid_of_eval

/--
info: 'Moist.SMT.UPLC.Soundness.valValid_decodes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.valValid_decodes

/--
info: 'Moist.SMT.UPLC.Soundness.valListValid_decodes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.valListValid_decodes

/--
info: 'Moist.SMT.UPLC.Soundness.SolverInputModel.expressionEvaluates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.SolverInputModel.expressionEvaluates

/--
info: 'Moist.SMT.UPLC.Soundness.declarationsInputSafe_decodes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.declarationsInputSafe_decodes

/--
info: 'Moist.SMT.UPLC.Soundness.CertifiedZ3Model.environmentDecodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.CertifiedZ3Model.environmentDecodes

/--
info: 'Moist.SMT.UPLC.Soundness.BoolTrueQuery.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.BoolTrueQuery.sound

/--
info: 'Moist.SMT.UPLC.Soundness.IntEqQuery.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.IntEqQuery.sound

/--
info: 'Moist.SMT.UPLC.Soundness.ErrorQuery.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.ErrorQuery.sound

/--
info: 'Moist.SMT.UPLC.scriptForWithAssertions_assertions' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.scriptForWithAssertions_assertions

/--
info: 'Moist.SMT.UPLC.Soundness.CertifiedAssertedCompilation.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.CertifiedAssertedCompilation.compile_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.CertifiedAssertionSetCompilation.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.CertifiedAssertionSetCompilation.compile_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.AssertedQuery.sound

/--
info: 'Moist.SMT.UPLC.Soundness.resultExpectation_condition_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.resultExpectation_condition_sound

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileUplcQuery_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileUplcQuery_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileUplcQuery_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileUplcQuery_sound

/--
info: 'Moist.SMT.UPLC.Soundness.uplcAssertion_condition_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.uplcAssertion_condition_sound

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionSatisfiabilityQuery.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.AssertionSatisfiabilityQuery.sound

/--
info: 'Moist.SMT.UPLC.Soundness.CertifiedAssertionQueriesCompilation.compile_map_scripts' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.CertifiedAssertionQueriesCompilation.compile_map_scripts

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compile_map_scripts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compile_map_scripts

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileUplcQuery_map_scripts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileUplcQuery_map_scripts

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileUplcQuery_target_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileUplcQuery_target_sound

/--
info: 'Moist.SMT.UPLC.Soundness.ResultQuery.compile_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.ResultQuery.compile_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.ResultQuery.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.ResultQuery.sound

/--
info: 'Moist.SMT.UPLC.Soundness.ResultQuery.compile_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.ResultQuery.compile_sound

/--
info: 'Moist.SMT.UPLC.AssertedTerm.erase_resultSatisfiesWith' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.AssertedTerm.erase_resultSatisfiesWith

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.AssertionQueryBundle.sound

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileAssertedTerm_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileAssertedTerm_sound

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileAssertedTerm_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileAssertedTerm_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileResultProgram_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileResultProgram_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileResultProgram_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileResultProgram_sound

/--
info: 'Moist.SMT.UPLC.Soundness.ResultQuery.compileResultProgram_map_script' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.ResultQuery.compileResultProgram_map_script

/--
info: 'Moist.SMT.UPLC.Soundness.ResultQuery.compileResultProgram_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.ResultQuery.compileResultProgram_sound

/--
info: 'Moist.SMT.UPLC.UplcQueryTarget.resolve_usesOpaque_of_source' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.UplcQueryTarget.resolve_usesOpaque_of_source

/--
info: 'Moist.SMT.UPLC.AssertedTerm.erase_appliedResultSatisfiesWith' does not depend on any axioms
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.AssertedTerm.erase_appliedResultSatisfiesWith

/--
info: 'Moist.SMT.UPLC.UplcQuery.erase_assertingAll' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.UplcQuery.erase_assertingAll

/--
info: 'Moist.SMT.UPLC.AssertedTerm.erase_requiringParameterChecked?_of_some' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.AssertedTerm.erase_requiringParameterChecked?_of_some

/--
info: 'Moist.SMT.UPLC.AssertedTerm.erase_appliedToDeclarationsWith' does not depend on any axioms
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.AssertedTerm.erase_appliedToDeclarationsWith

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileAssertedTerm_map_scripts' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileAssertedTerm_map_scripts

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileResultProgram_map_scripts' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileResultProgram_map_scripts

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileAssertedTerm_target_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileAssertedTerm_target_sound

/--
info: 'Moist.SMT.UPLC.Soundness.AssertedQuery.compileUplcQuery_source_noOpaque' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertedQuery.compileUplcQuery_source_noOpaque

/--
info: 'Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileResultProgram_target_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  Moist.SMT.UPLC.Soundness.AssertionQueryBundle.compileResultProgram_target_sound

/--
info: 'Moist.SMT.UPLC.AssertedTerm.erase_appliedWith' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.AssertedTerm.erase_appliedWith

/--
info: 'Moist.Plutus.Term.Term.erase_withParameterAssertion' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.Plutus.Term.Term.erase_withParameterAssertion

/--
info: 'Moist.Plutus.Term.Term.erase_queryingResultWith' does not depend on any axioms
-/
#guard_msgs in
#print axioms Moist.Plutus.Term.Term.erase_queryingResultWith
