import Moist.SMT.Soundness.SolverBoundary

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
info: 'Moist.SMT.UPLC.Soundness.bindOk_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.bindOk_mem

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
