import Moist.SMT.Soundness.Foundations

/-!
# False-path carry pruning

`bindOut` does not retain errors or timeouts whose path condition is the
literal `false`.  This file compares that optimization with the former
unpruned sequencing rule at the executable SMT-model boundary.

For every internal SMT model, input outcome list, and continuation, pruning
preserves all three observable outcome kinds: the first decoded successful CEK
value, existence of an active error, and existence of an active timeout.
-/

namespace Moist.SMT.UPLC.Soundness

/-- Reference sequencing rule before unreachable carried errors and timeouts
were pruned. -/
def bindOutUnpruned (xs : List Outcome)
    (k : SymVal → List Outcome) : List Outcome :=
  xs.flatMap fun
    | .ok pc v => bindOk pc v k
    | .error pc => [.error pc]
    | .timeout pc => [.timeout pc]

/-- Whether a list contains a timeout active in the supplied executable SMT
model. -/
def anyTimeoutOutcome (m : SmtSem.Model) : List Outcome → Bool
  | [] => false
  | .timeout pc :: outs => pcHolds m pc || anyTimeoutOutcome m outs
  | _ :: outs => anyTimeoutOutcome m outs

@[simp] theorem pcHolds_false (m : SmtSem.Model) :
    pcHolds m (.bool false) = false := by
  simpa [pcHolds, Moist.SMT.Expr.falseE] using
    Moist.SMT.Semantics.evalBoolIs_falseE m

/-- The optimized carried-error representation is exactly the former
singleton, except when its path is the literal `false`. -/
theorem carryError_eq (pc : SExpr) :
    carryError pc =
      match pc with
      | .bool false => []
      | _ => [.error pc] := by
  cases pc <;> try rfl
  case bool b => cases b <;> rfl

/-- The optimized carried-timeout representation is exactly the former
singleton, except when its path is the literal `false`. -/
theorem carryTimeout_eq (pc : SExpr) :
    carryTimeout pc =
      match pc with
      | .bool false => []
      | _ => [.timeout pc] := by
  cases pc <;> try rfl
  case bool b => cases b <;> rfl

private theorem anyOkOutcome_append_congr (m : SmtSem.Model)
    (pre left right : List Outcome)
    (h : anyOkOutcome? m left = anyOkOutcome? m right) :
    anyOkOutcome? m (pre ++ left) =
      anyOkOutcome? m (pre ++ right) := by
  induction pre with
  | nil => exact h
  | cons out pre ih =>
      simp only [List.cons_append, anyOkOutcome?]
      cases outcomeOkSym? m out <;> simp_all

private theorem anyErrorOutcome_append_congr (m : SmtSem.Model)
    (pre left right : List Outcome)
    (h : anyErrorOutcome m left = anyErrorOutcome m right) :
    anyErrorOutcome m (pre ++ left) =
      anyErrorOutcome m (pre ++ right) := by
  induction pre with
  | nil => exact h
  | cons out pre ih =>
      simp only [List.cons_append, anyErrorOutcome]
      rw [ih]

private theorem anyTimeoutOutcome_append_congr (m : SmtSem.Model)
    (pre left right : List Outcome)
    (h : anyTimeoutOutcome m left = anyTimeoutOutcome m right) :
    anyTimeoutOutcome m (pre ++ left) =
      anyTimeoutOutcome m (pre ++ right) := by
  induction pre with
  | nil => exact h
  | cons out pre ih =>
      cases out <;> simp only [List.cons_append, anyTimeoutOutcome] <;>
        simp_all

/-- Literal-false error/timeout pruning preserves the successful CEK value
decoded by the executable SMT semantics. -/
theorem bindOut_anyOkOutcome_eq_unpruned (m : SmtSem.Model)
    (xs : List Outcome) (k : SymVal → List Outcome) :
    anyOkOutcome? m (bindOut xs k) =
      anyOkOutcome? m (bindOutUnpruned xs k) := by
  induction xs with
  | nil => rfl
  | cons out xs ih =>
      cases out with
      | ok pc v =>
          apply anyOkOutcome_append_congr m (bindOk pc v k)
          exact ih
      | error pc =>
          rw [show bindOut (Outcome.error pc :: xs) k =
              carryError pc ++ bindOut xs k by rfl]
          rw [show bindOutUnpruned (Outcome.error pc :: xs) k =
              [Outcome.error pc] ++ bindOutUnpruned xs k by rfl]
          rw [carryError_eq]
          cases pc <;> simp [anyOkOutcome?, outcomeOkSym?, ih]
          case bool b => cases b <;> simp [anyOkOutcome?, outcomeOkSym?, ih]
      | timeout pc =>
          rw [show bindOut (Outcome.timeout pc :: xs) k =
              carryTimeout pc ++ bindOut xs k by rfl]
          rw [show bindOutUnpruned (Outcome.timeout pc :: xs) k =
              [Outcome.timeout pc] ++ bindOutUnpruned xs k by rfl]
          rw [carryTimeout_eq]
          cases pc <;> simp [anyOkOutcome?, outcomeOkSym?, ih]
          case bool b => cases b <;> simp [anyOkOutcome?, outcomeOkSym?, ih]

/-- Literal-false error/timeout pruning preserves whether the executable SMT
semantics observes a runtime error. -/
theorem bindOut_anyErrorOutcome_eq_unpruned (m : SmtSem.Model)
    (xs : List Outcome) (k : SymVal → List Outcome) :
    anyErrorOutcome m (bindOut xs k) =
      anyErrorOutcome m (bindOutUnpruned xs k) := by
  induction xs with
  | nil => rfl
  | cons out xs ih =>
      cases out with
      | ok pc v =>
          apply anyErrorOutcome_append_congr m (bindOk pc v k)
          exact ih
      | error pc =>
          rw [show bindOut (Outcome.error pc :: xs) k =
              carryError pc ++ bindOut xs k by rfl]
          rw [show bindOutUnpruned (Outcome.error pc :: xs) k =
              [Outcome.error pc] ++ bindOutUnpruned xs k by rfl]
          rw [carryError_eq]
          cases pc <;> simp [anyErrorOutcome, outcomeErrorActive, ih]
          case bool b => cases b <;>
            simp [anyErrorOutcome, outcomeErrorActive, ih]
      | timeout pc =>
          rw [show bindOut (Outcome.timeout pc :: xs) k =
              carryTimeout pc ++ bindOut xs k by rfl]
          rw [show bindOutUnpruned (Outcome.timeout pc :: xs) k =
              [Outcome.timeout pc] ++ bindOutUnpruned xs k by rfl]
          rw [carryTimeout_eq]
          cases pc <;> simp [anyErrorOutcome, outcomeErrorActive, ih]
          case bool b => cases b <;>
            simp [anyErrorOutcome, outcomeErrorActive, ih]

/-- Literal-false error/timeout pruning preserves whether the executable SMT
semantics observes a fuel timeout. -/
theorem bindOut_anyTimeoutOutcome_eq_unpruned (m : SmtSem.Model)
    (xs : List Outcome) (k : SymVal → List Outcome) :
    anyTimeoutOutcome m (bindOut xs k) =
      anyTimeoutOutcome m (bindOutUnpruned xs k) := by
  induction xs with
  | nil => rfl
  | cons out xs ih =>
      cases out with
      | ok pc v =>
          apply anyTimeoutOutcome_append_congr m (bindOk pc v k)
          exact ih
      | error pc =>
          rw [show bindOut (Outcome.error pc :: xs) k =
              carryError pc ++ bindOut xs k by rfl]
          rw [show bindOutUnpruned (Outcome.error pc :: xs) k =
              [Outcome.error pc] ++ bindOutUnpruned xs k by rfl]
          rw [carryError_eq]
          cases pc <;> simp [anyTimeoutOutcome, ih]
          case bool b => cases b <;> simp [anyTimeoutOutcome, ih]
      | timeout pc =>
          rw [show bindOut (Outcome.timeout pc :: xs) k =
              carryTimeout pc ++ bindOut xs k by rfl]
          rw [show bindOutUnpruned (Outcome.timeout pc :: xs) k =
              [Outcome.timeout pc] ++ bindOutUnpruned xs k by rfl]
          rw [carryTimeout_eq]
          cases pc <;> simp [anyTimeoutOutcome, ih]
          case bool b => cases b <;> simp [anyTimeoutOutcome, ih]

end Moist.SMT.UPLC.Soundness
