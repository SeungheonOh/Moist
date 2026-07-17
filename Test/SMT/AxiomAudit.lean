import Moist.SMT.Soundness

/-!
The optimizer and the CEK endpoints for the supported (no-opaque-builtin)
fragment must remain free of project postulates and `sorryAx`.  These guarded
kernel reports intentionally permit only Lean's standard logical foundations.
-/

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
info: 'Moist.Verified.BigStep.bigEval_iff_halt_env' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.Verified.BigStep.bigEval_iff_halt_env

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_allFuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_allFuel

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedErrorCond_sound

/--
info: 'Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Moist.SMT.UPLC.Soundness.evalSym_simplifiedOkBoolTrueCond_sound

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
