import Moist.SMT.Syntax
import Moist.Plutus.DecidableEq

/-!
# Exact expression identity for compiler caches

Compiler caches may reuse a result only when their input expressions are
identical.  `decEq` supplies that decision together with a kernel-checked
proof.  Its native implementation applies Lean's safe `withPtrEqDecEq`
shortcut at every recursive expression and argument-list node, so shared
immutable DAGs are compared without repeatedly traversing their shared
subtrees.  The logical implementation remains ordinary structural equality.
-/

namespace Moist.SMT.Compiler.ExpressionIdentity

mutual
  private def structuralEq : Expr → Expr → Bool
    | .sym left, .sym right => decide (left = right)
    | .int left, .int right => decide (left = right)
    | .bytes left, .bytes right => decide (left = right)
    | .dataLit left, .dataLit right => decide (left = right)
    | .dataListLit left, .dataListLit right => decide (left = right)
    | .dataPairListLit left, .dataPairListLit right => decide (left = right)
    | .constListLit left, .constListLit right => decide (left = right)
    | .bool left, .bool right => decide (left = right)
    | .str left, .str right => decide (left = right)
    | .app leftName leftArgs, .app rightName rightArgs =>
        decide (leftName = rightName) && structuralListEq leftArgs rightArgs
    | .ite leftCondition leftThen leftElse,
        .ite rightCondition rightThen rightElse =>
        structuralEq leftCondition rightCondition &&
          structuralEq leftThen rightThen &&
          structuralEq leftElse rightElse
    | _, _ => false

  private def structuralListEq : List Expr → List Expr → Bool
    | [], [] => true
    | left :: lefts, right :: rights =>
        structuralEq left right && structuralListEq lefts rights
    | _, _ => false
end

mutual
  private theorem structuralEq_self (expression : Expr) :
      structuralEq expression expression = true := by
    cases expression with
    | sym name => simp [structuralEq]
    | int value => simp [structuralEq]
    | bytes value => simp [structuralEq]
    | dataLit value => simp [structuralEq]
    | dataListLit value => simp [structuralEq]
    | dataPairListLit value => simp [structuralEq]
    | constListLit value => simp [structuralEq]
    | bool value => simp [structuralEq]
    | str value => simp [structuralEq]
    | app name arguments =>
        simp [structuralEq, structuralListEq_self arguments]
    | ite condition thenBranch elseBranch =>
        simp [structuralEq, structuralEq_self condition,
          structuralEq_self thenBranch, structuralEq_self elseBranch]

  private theorem structuralListEq_self (expressions : List Expr) :
      structuralListEq expressions expressions = true := by
    cases expressions with
    | nil => rfl
    | cons expression expressions =>
        simp [structuralListEq, structuralEq_self expression,
          structuralListEq_self expressions]
end

mutual
  private theorem structuralEq_eq_true :
      (left right : Expr) → structuralEq left right = true → left = right
    | .sym left, .sym right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .int left, .int right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .bytes left, .bytes right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .dataLit left, .dataLit right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .dataListLit left, .dataListLit right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .dataPairListLit left, .dataPairListLit right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .constListLit left, .constListLit right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .bool left, .bool right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .str left, .str right, equal => by
        simp only [structuralEq, decide_eq_true_eq] at equal
        cases equal
        rfl
    | .app leftName leftArgs, .app rightName rightArgs, equal => by
        simp only [structuralEq, Bool.and_eq_true,
          decide_eq_true_eq] at equal
        cases equal.1
        cases structuralListEq_eq_true leftArgs rightArgs equal.2
        rfl
    | .ite leftCondition leftThen leftElse,
        .ite rightCondition rightThen rightElse, equal => by
        change (structuralEq leftCondition rightCondition &&
          structuralEq leftThen rightThen &&
          structuralEq leftElse rightElse) = true at equal
        simp only [Bool.and_eq_true] at equal
        cases structuralEq_eq_true leftCondition rightCondition equal.1.1
        cases structuralEq_eq_true leftThen rightThen equal.1.2
        cases structuralEq_eq_true leftElse rightElse equal.2
        rfl
    | left, right, equal => by
        cases left <;> cases right <;> simp_all [structuralEq]
        · exact structuralListEq_eq_true _ _ equal.2
        · exact
            ⟨ structuralEq_eq_true _ _ equal.1.1
            , structuralEq_eq_true _ _ equal.1.2
            , structuralEq_eq_true _ _ equal.2 ⟩

  private theorem structuralListEq_eq_true :
      (left right : List Expr) →
        structuralListEq left right = true → left = right
    | [], [], _ => rfl
    | left :: lefts, right :: rights, equal => by
        simp only [structuralListEq, Bool.and_eq_true] at equal
        cases structuralEq_eq_true left right equal.1
        cases structuralListEq_eq_true lefts rights equal.2
        rfl
    | left, right, equal => by
        cases left <;> cases right <;> simp_all [structuralListEq]
        exact
          ⟨ structuralEq_eq_true _ _ equal.1
          , structuralListEq_eq_true _ _ equal.2 ⟩
end

private def structuralDecEq (left right : Expr) : Decidable (left = right) :=
  if equal : structuralEq left right = true then
    isTrue (structuralEq_eq_true left right equal)
  else
    isFalse fun proposition => by
      cases proposition
      exact equal (structuralEq_self left)

mutual
  /-- Decide exact structural identity.  A positive result contains the
  equality proof consumed by a cache-hit branch. -/
  def decEq (left right : Expr) : Decidable (left = right) :=
    withPtrEqDecEq left right fun _ =>
      match left, right with
      | .app leftName leftArgs, .app rightName rightArgs =>
          if namesEqual : leftName = rightName then
            match listDecEq leftArgs rightArgs with
            | isTrue argsEqual => isTrue (by
                cases namesEqual
                cases argsEqual
                rfl)
            | isFalse argsDifferent => isFalse (by
                intro expressionsEqual
                cases expressionsEqual
                exact argsDifferent rfl)
          else
            isFalse (by
              intro expressionsEqual
              cases expressionsEqual
              exact namesEqual rfl)
      | .ite leftCondition leftThen leftElse,
          .ite rightCondition rightThen rightElse =>
          match decEq leftCondition rightCondition with
          | isFalse conditionDifferent => isFalse (by
              intro expressionsEqual
              cases expressionsEqual
              exact conditionDifferent rfl)
          | isTrue conditionEqual =>
              match decEq leftThen rightThen with
              | isFalse thenDifferent => isFalse (by
                  intro expressionsEqual
                  cases expressionsEqual
                  exact thenDifferent rfl)
              | isTrue thenEqual =>
                  match decEq leftElse rightElse with
                  | isFalse elseDifferent => isFalse (by
                      intro expressionsEqual
                      cases expressionsEqual
                      exact elseDifferent rfl)
                  | isTrue elseEqual => isTrue (by
                      cases conditionEqual
                      cases thenEqual
                      cases elseEqual
                      rfl)
      | left, right => structuralDecEq left right

  private def listDecEq (left right : List Expr) : Decidable (left = right) :=
    withPtrEqDecEq left right fun _ =>
      match left, right with
      | [], [] => isTrue rfl
      | left :: lefts, right :: rights =>
          match decEq left right with
          | isFalse headDifferent => isFalse (by
              intro expressionsEqual
              cases expressionsEqual
              exact headDifferent rfl)
          | isTrue headEqual =>
              match listDecEq lefts rights with
              | isFalse tailDifferent => isFalse (by
                  intro expressionsEqual
                  cases expressionsEqual
                  exact tailDifferent rfl)
              | isTrue tailEqual => isTrue (by
                  cases headEqual
                  cases tailEqual
                  rfl)
      | [], _ :: _ => isFalse List.noConfusion
      | _ :: _, [] => isFalse List.noConfusion
end

end Moist.SMT.Compiler.ExpressionIdentity
