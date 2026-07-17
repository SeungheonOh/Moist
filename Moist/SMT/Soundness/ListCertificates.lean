import Moist.SMT.Soundness.Foundations

/-!
# Certified constant-list branch pruning

This module is the proof boundary for the length certificates carried by
symbolic constant lists.  It connects their structural certificates to the
executable SMT semantics, the decoded CEK value, and the `ChooseList` branch
selector.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekValue)

@[simp] theorem symValToCek_consConstListValue
    (m : SmtSem.Model) (head : SExpr) (tail : SymVal) :
    symValToCek? m (consConstListValue head tail) =
      symValToCek? m (.const (.constList
        (.app "VCons" [head, (asConstList tail).val]) .unknown)) := by
  cases tail with
  | const c => cases c <;> rfl
  | dyn e | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ => rfl

@[simp] theorem symValToCek_tailConstListValue
    (m : SmtSem.Model) (value : SymVal) :
    symValToCek? m (tailConstListValue value) =
      symValToCek? m (.const (.constList
        (.app "vtail" [(asConstList value).val]) .unknown)) := by
  cases value with
  | const c => cases c <;> rfl
  | dyn e | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ => rfl

@[simp] theorem symValNoOpaque_consConstListValue
    (head : SExpr) (tail : SymVal) :
    symValNoOpaqueForSoundness (consConstListValue head tail) = true := by
  cases tail with
  | const c => cases c <;> rfl
  | dyn e | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ => rfl

@[simp] theorem symValNoOpaque_tailConstListValue (value : SymVal) :
    symValNoOpaqueForSoundness (tailConstListValue value) = true := by
  cases value with
  | const c => cases c <;> rfl
  | dyn e | pair _ _ | constr _ _ | lam _ _ | delay _ _ | builtin _ _ _ => rfl

/-- A cached constant-list length is a theorem about every model in which the
certified SMT expression evaluates.  This is the kernel-checked invariant that
makes branch pruning safe even for arbitrary symbolic environments. -/
theorem exactConstListLength_eval_length
    {expr : SExpr} {n : Nat} (certificate : ExactConstListLength expr n)
    (m : SmtSem.Model) {values : List SmtSem.Val}
    (hEval : SmtSem.eval m expr = some (.valList values)) :
    values.length = n := by
  change Moist.SMT.Semantics.eval m expr = some (.valList values) at hEval
  induction certificate generalizing values with
  | literal xs =>
      simp [Moist.SMT.Semantics.eval] at hEval
      subst values
      induction xs with
      | nil => rfl
      | cons x xs ih =>
          simp [Moist.SMT.Semantics.constListToVals, ih]
  | cons head certificate ih =>
      obtain ⟨headValue, tailValues, _, hTail, rfl⟩ :=
        Moist.SMT.Semantics.eval_VCons_inv hEval
      simp [ih hTail]
  | tail certificate ih =>
      obtain ⟨head, hList⟩ := Moist.SMT.Semantics.eval_vtail_inv hEval
      simpa using ih hList
  | @ite condition thenExpr elseExpr certifiedLength hThen hElse ihThen ihElse =>
      unfold SExpr.ite at hEval
      rw [Moist.SMT.Semantics.eval_ite_exact m condition thenExpr elseExpr] at hEval
      cases hCondition : Moist.SMT.Semantics.eval m condition with
      | none => simp [hCondition] at hEval
      | some conditionValue =>
          cases conditionValue <;> simp [hCondition] at hEval
          case bool conditionBool =>
            cases conditionBool
            · exact ihElse hEval
            · exact ihThen hEval

theorem knownConstListLength_eq_eval_length
    {expr : SExpr} {hint : ConstListLengthHint expr} {n : Nat}
    {m : SmtSem.Model} {values : List SmtSem.Val}
    (hKnown : knownConstListLength (.const (.constList expr hint)) = some n)
    (hEval : SmtSem.eval m expr = some (.valList values)) :
    values.length = n := by
  cases hint with
  | unknown => simp [knownConstListLength, ConstListLengthHint.knownLength,
      ConstListLengthHint.certificate?] at hKnown
  | exact certifiedLength certificate =>
      simp [knownConstListLength, ConstListLengthHint.knownLength,
        ConstListLengthHint.certificate?] at hKnown
      subst n
      exact exactConstListLength_eval_length certificate m hEval

/-- The alternative selected by the evaluated SMT list shape is never pruned. -/
theorem constListBranches_complete_for_eval
    {expr : SExpr} {hint : ConstListLengthHint expr} {m : SmtSem.Model}
    {values : List SmtSem.Val} (nilOutcome consOutcome : Outcome)
    (hEval : SmtSem.eval m expr = some (.valList values)) :
    (match values with
      | [] => nilOutcome
      | _ :: _ => consOutcome) ∈
      constListBranches
        (knownConstListLength (.const (.constList expr hint)))
        nilOutcome consOutcome := by
  cases hKnown : knownConstListLength (.const (.constList expr hint)) with
  | none => cases values <;> simp [constListBranches]
  | some n =>
      have hLength := knownConstListLength_eq_eval_length hKnown hEval
      cases values with
      | nil =>
          cases n with
          | zero => simp [constListBranches]
          | succ n => simp at hLength
      | cons value values =>
          cases n with
          | zero => simp at hLength
          | succ n => simp [constListBranches]

theorem knownConstListLength_eq_toCek_length
    {expr : SExpr} {hint : ConstListLengthHint expr} {n : Nat}
    {m : SmtSem.Model} {cs : List Const}
    (hKnown : knownConstListLength (.const (.constList expr hint)) = some n)
    (hCek : symValToCek? m (.const (.constList expr hint)) =
      some (.VCon (.ConstList cs))) :
    cs.length = n := by
  simp [symValToCek?, symConstToCek?] at hCek
  cases hEval : SmtSem.eval m expr <;> simp [hEval] at hCek
  rename_i evaluated
  cases evaluated <;> simp at hCek
  case valList values =>
    cases hConsts : semValListToConstList? values <;> simp [hConsts] at hCek
    subst cs
    exact (semValListToConstList_length hConsts).symm.trans
      (knownConstListLength_eq_eval_length hKnown hEval)

/-- The alternative selected by concrete CEK list shape is never pruned. -/
theorem constListBranches_complete_for_toCek
    {expr : SExpr} {hint : ConstListLengthHint expr} {m : SmtSem.Model}
    {cs : List Const} (nilOutcome consOutcome : Outcome)
    (hCek : symValToCek? m (.const (.constList expr hint)) =
      some (.VCon (.ConstList cs))) :
    (match cs with
      | [] => nilOutcome
      | _ :: _ => consOutcome) ∈
      constListBranches
        (knownConstListLength (.const (.constList expr hint)))
        nilOutcome consOutcome := by
  cases hKnown : knownConstListLength (.const (.constList expr hint)) with
  | none => cases cs <;> simp [constListBranches]
  | some n =>
      have hLength := knownConstListLength_eq_toCek_length hKnown hCek
      cases cs with
      | nil =>
          cases n with
          | zero => simp [constListBranches]
          | succ n => simp at hLength
      | cons value cs =>
          cases n with
          | zero => simp at hLength
          | succ n => simp [constListBranches]

end Moist.SMT.UPLC.Soundness
