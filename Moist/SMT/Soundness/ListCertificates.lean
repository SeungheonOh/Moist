import Moist.SMT.Soundness.Foundations

/-!
# Structurally checked constant-list branch pruning

This module is the proof boundary for the proof-free cached length hints
carried by symbolic constant lists.  It proves the executable structural
recheck exact, then connects an accepted hint to the SMT semantics, the
decoded CEK value, and the `ChooseList` branch selector.
-/

namespace Moist.SMT.UPLC.Soundness

open Moist.Plutus.Term
open Moist.CEK (CekValue)

/-- Proof-side characterization of the exact expression shapes recognized by
`ConstListLengthHint.inferExact?`.  This proposition is deliberately absent
from the executable compiler IR. -/
inductive ExactConstListLength : SExpr → Nat → Prop where
  | literal (xs : List Const) :
      ExactConstListLength (.constListLit xs) xs.length
  | cons (head : SExpr) {tail : SExpr} {n : Nat}
      (h : ExactConstListLength tail n) :
      ExactConstListLength (.app "VCons" [head, tail]) (n + 1)
  | tail {xs : SExpr} {n : Nat}
      (h : ExactConstListLength xs (n + 1)) :
      ExactConstListLength (.app "vtail" [xs]) n
  | ite (condition : SExpr) {thenExpr elseExpr : SExpr} {n : Nat}
      (hThen : ExactConstListLength thenExpr n)
      (hElse : ExactConstListLength elseExpr n) :
      ExactConstListLength (.ite condition thenExpr elseExpr) n

/-- A positive result from the proof-free structural checker reconstructs the
corresponding kernel proposition. -/
theorem inferExactConstListLength?_sound : ∀ expression n,
    ConstListLengthHint.inferExact? expression = some n →
      ExactConstListLength expression n
  | .constListLit xs, n, accepted => by
      simp only [ConstListLengthHint.inferExact?, Option.some.injEq] at accepted
      subst n
      exact .literal xs
  | .app name arguments, n, accepted => by
      cases arguments with
      | nil => simp [ConstListLengthHint.inferExact?] at accepted
      | cons first rest =>
          cases rest with
          | nil =>
              by_cases isTail : name = "vtail"
              · subst name
                simp only [ConstListLengthHint.inferExact?] at accepted
                cases inferred : ConstListLengthHint.inferExact? first with
                | none => simp [inferred] at accepted
                | some inferredLength =>
                    cases inferredLength with
                    | zero => simp [inferred] at accepted
                    | succ tailLength =>
                        simp only [inferred, Option.some.injEq] at accepted
                        subst n
                        exact .tail
                          (inferExactConstListLength?_sound first
                            (tailLength + 1) inferred)
              · simp [ConstListLengthHint.inferExact?, isTail] at accepted
          | cons second remaining =>
              cases remaining with
              | nil =>
                  by_cases isCons : name = "VCons"
                  · subst name
                    simp only [ConstListLengthHint.inferExact?] at accepted
                    cases inferred : ConstListLengthHint.inferExact? second with
                    | none => simp [inferred] at accepted
                    | some tailLength =>
                        simp only [inferred, Option.map_some,
                          Option.some.injEq] at accepted
                        subst n
                        exact .cons first
                          (inferExactConstListLength?_sound second tailLength inferred)
                  · simp [ConstListLengthHint.inferExact?, isCons] at accepted
              | cons third remaining =>
                  simp [ConstListLengthHint.inferExact?] at accepted
  | .ite condition thenExpr elseExpr, n, accepted => by
      change (match ConstListLengthHint.inferExact? thenExpr,
          ConstListLengthHint.inferExact? elseExpr with
        | some thenLength, some elseLength =>
            if thenLength == elseLength then some thenLength else none
        | _, _ => none) = some n at accepted
      cases thenInferred : ConstListLengthHint.inferExact? thenExpr with
      | none => simp [thenInferred] at accepted
      | some thenLength =>
          cases elseInferred : ConstListLengthHint.inferExact? elseExpr with
          | none => simp [thenInferred, elseInferred] at accepted
          | some elseLength =>
              simp only [thenInferred, elseInferred] at accepted
              split at accepted
              next sameLength =>
                simp only [Option.some.injEq] at accepted
                have lengthsEqual : thenLength = elseLength := by
                  simpa only [beq_iff_eq] using sameLength
                subst elseLength
                subst n
                exact .ite condition
                  (inferExactConstListLength?_sound thenExpr thenLength thenInferred)
                  (inferExactConstListLength?_sound elseExpr thenLength elseInferred)
              next differentLengths => simp at accepted
  | .sym _, n, accepted
  | .int _, n, accepted
  | .bytes _, n, accepted
  | .dataLit _, n, accepted
  | .dataListLit _, n, accepted
  | .dataPairListLit _, n, accepted
  | .bool _, n, accepted
  | .str _, n, accepted => by
      simp [ConstListLengthHint.inferExact?] at accepted
termination_by expression _ _ => sizeOf expression
decreasing_by
  all_goals subst_vars
  all_goals
    simp
    omega

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

/-- A structurally reconstructed constant-list length is a theorem about every
model in which the SMT expression evaluates.  This is the kernel-checked
invariant that makes branch pruning safe even for arbitrary symbolic
environments. -/
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
    {expr : SExpr} {hint : ConstListLengthHint} {n : Nat}
    {m : SmtSem.Model} {values : List SmtSem.Val}
    (hKnown : knownConstListLength (.const (.constList expr hint)) = some n)
    (hEval : SmtSem.eval m expr = some (.valList values)) :
    values.length = n := by
  cases hint with
  | unknown =>
      simp [knownConstListLength, ConstListLengthHint.knownLength] at hKnown
  | exact hintedLength =>
      simp only [knownConstListLength, ConstListLengthHint.knownLength] at hKnown
      split at hKnown
      next accepted =>
        simp only [Option.some.injEq] at hKnown
        subst n
        have inferred : ConstListLengthHint.inferExact? expr = some hintedLength := by
          simpa only [beq_iff_eq] using accepted
        exact exactConstListLength_eval_length
          (inferExactConstListLength?_sound expr hintedLength inferred) m hEval
      next rejected => simp at hKnown

/-- The alternative selected by the evaluated SMT list shape is never pruned. -/
theorem constListBranches_complete_for_eval
    {expr : SExpr} {hint : ConstListLengthHint} {m : SmtSem.Model}
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
    {expr : SExpr} {hint : ConstListLengthHint} {n : Nat}
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
    {expr : SExpr} {hint : ConstListLengthHint} {m : SmtSem.Model}
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
