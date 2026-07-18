import Moist.SMT.Optimize
import Moist.SMT.Semantics

namespace Moist.SMT

/-! Semantic preservation proofs for the executable Boolean optimizer. -/

namespace Semantics

set_option linter.unusedSimpArgs false

theorem isTrue_eq_true {e : Expr} : Expr.isTrue e = true ↔ e = .bool true := by
  cases e <;> simp [Expr.isTrue]
  case bool b => cases b <;> simp [Expr.isTrue]

theorem isFalse_eq_true {e : Expr} : Expr.isFalse e = true ↔ e = .bool false := by
  cases e <;> simp [Expr.isFalse]
  case bool b => cases b <;> simp [Expr.isFalse]

private theorem evalBool?_and_true_left (m : Model) (b : Expr) :
    evalBool? m b = evalBool? m (.app "and" [.bool true, b]) := by
  rw [evalBool?_app_and_strong]
  cases h : evalBool? m b with
  | none => simp [strongAnd, evalBool?, eval, h]
  | some b => cases b <;> simp [strongAnd, evalBool?, eval, h]

private theorem evalBool?_and_true_right (m : Model) (a : Expr) :
    evalBool? m a = evalBool? m (.app "and" [a, .bool true]) := by
  rw [evalBool?_app_and_strong]
  cases h : evalBool? m a with
  | none => simp [strongAnd, evalBool?, eval, h]
  | some a => cases a <;> simp [strongAnd, evalBool?, eval, h]

private theorem evalBool?_or_false_left (m : Model) (b : Expr) :
    evalBool? m b = evalBool? m (.app "or" [.bool false, b]) := by
  rw [evalBool?_app_or_strong]
  cases h : evalBool? m b with
  | none => simp [strongOr, evalBool?, eval, h]
  | some b => cases b <;> simp [strongOr, evalBool?, eval, h]

private theorem evalBool?_or_false_right (m : Model) (a : Expr) :
    evalBool? m a = evalBool? m (.app "or" [a, .bool false]) := by
  rw [evalBool?_app_or_strong]
  cases h : evalBool? m a with
  | none => simp [strongOr, evalBool?, eval, h]
  | some a => cases a <;> simp [strongOr, evalBool?, eval, h]

private theorem evalBool?_not_eq (m : Model) (a : Expr) :
    evalBool? m (.app "not" [a]) = (!·) <$> evalBool? m a := by
  cases h : eval m a <;> simp [evalBool?, eval, h]
  rename_i v
  cases v <;> simp [evalBool?, eval, h]

private theorem evalBool?_and_eq (m : Model) (a b : Expr) :
    evalBool? m (.app "and" [a, b]) =
      strongAnd (evalBool? m a) (evalBool? m b) := by
  exact evalBool?_app_and_strong m a b

private theorem evalBool?_or_eq (m : Model) (a b : Expr) :
    evalBool? m (.app "or" [a, b]) =
      strongOr (evalBool? m a) (evalBool? m b) := by
  exact evalBool?_app_or_strong m a b

private theorem evalBool?_ite_eq (m : Model) (c t e : Expr) :
    evalBool? m (.ite c t e) = (do
      let bc ← evalBool? m c
      if bc then evalBool? m t else evalBool? m e) := by
  cases hc : eval m c <;> simp [evalBool?, eval, hc]
  rename_i vc
  cases vc <;> simp [evalBool?, eval, hc]
  case bool bc =>
    cases bc <;> simp [evalBool?, eval, hc]

private theorem evalBool?_ite_true (m : Model) (t e : Expr) :
    evalBool? m t = evalBool? m (.ite (.bool true) t e) := by
  simp [evalBool?, eval]

private theorem evalBool?_ite_false (m : Model) (t e : Expr) :
    evalBool? m e = evalBool? m (.ite (.bool false) t e) := by
  simp [evalBool?, eval]

private theorem evalBool?_ite_identity (m : Model) (c : Expr) :
    evalBool? m c = evalBool? m (.ite c (.bool true) (.bool false)) := by
  cases h : eval m c <;> simp [evalBool?, eval, h]
  rename_i v
  cases v <;> simp [evalBool?, eval, h]
  case bool b => cases b <;> simp [evalBool?, eval, h]

theorem evalBool?_smartNot (m : Model) (a : Expr) :
    evalBool? m (Expr.smartNot a) = evalBool? m (.app "not" [a]) := by
  cases a <;> simp [Expr.smartNot, evalBool?, eval]
  case app f args =>
    by_cases hf : f = "not"
    · subst f
      cases args with
      | nil => simp [Expr.smartNot, evalBool?, eval]
      | cons x xs =>
          cases xs with
          | nil =>
              simp only [Expr.smartNot]
              cases h : eval m x <;> simp [evalBool?, eval, h]
              rename_i v
              cases v <;> simp [evalBool?, eval, h]
          | cons y ys => simp [Expr.smartNot, evalBool?, eval]
    · simp [Expr.smartNot, evalBool?, eval, hf]

private theorem evalBool?_ite_negation (m : Model) (c : Expr) :
    evalBool? m (Expr.smartNot c) =
      evalBool? m (.ite c (.bool false) (.bool true)) := by
  rw [evalBool?_smartNot]
  cases h : eval m c <;> simp [evalBool?, eval, h]
  rename_i v
  cases v <;> simp [evalBool?, eval, h]
  case bool b => cases b <;> simp [evalBool?, eval, h]

theorem evalBool?_smartAnd (m : Model) (a b : Expr) :
    evalBool? m (Expr.smartAnd a b) = evalBool? m (.app "and" [a, b]) := by
  by_cases ha : Expr.isTrue a = true
  · rw [isTrue_eq_true] at ha
    subst a
    simpa [Expr.smartAnd, Expr.isTrue] using evalBool?_and_true_left m b
  · by_cases hb : Expr.isTrue b = true
    · rw [isTrue_eq_true] at hb
      subst b
      simpa [Expr.smartAnd, ha] using evalBool?_and_true_right m a
    · simp [Expr.smartAnd, ha, hb]

theorem evalBool?_smartOr (m : Model) (a b : Expr) :
    evalBool? m (Expr.smartOr a b) = evalBool? m (.app "or" [a, b]) := by
  by_cases ha : Expr.isFalse a = true
  · rw [isFalse_eq_true] at ha
    subst a
    simpa [Expr.smartOr, Expr.isFalse] using evalBool?_or_false_left m b
  · by_cases hb : Expr.isFalse b = true
    · rw [isFalse_eq_true] at hb
      subst b
      simpa [Expr.smartOr, ha] using evalBool?_or_false_right m a
    · simp [Expr.smartOr, ha, hb]

theorem evalBool?_smartIte (m : Model) (c t e : Expr) :
    evalBool? m (Expr.smartIte c t e) = evalBool? m (.ite c t e) := by
  by_cases hcT : Expr.isTrue c = true
  · rw [isTrue_eq_true] at hcT
    subst c
    simpa [Expr.smartIte, Expr.isTrue] using evalBool?_ite_true m t e
  · by_cases hcF : Expr.isFalse c = true
    · rw [isFalse_eq_true] at hcF
      subst c
      simpa [Expr.smartIte, hcT] using evalBool?_ite_false m t e
    · by_cases htT : Expr.isTrue t = true
      · by_cases heF : Expr.isFalse e = true
        · rw [isTrue_eq_true] at htT
          rw [isFalse_eq_true] at heF
          subst t
          subst e
          simpa [Expr.smartIte, hcT, hcF] using evalBool?_ite_identity m c
        · simp [Expr.smartIte, hcT, hcF, htT, heF]
      · by_cases htF : Expr.isFalse t = true
        · by_cases heT : Expr.isTrue e = true
          · rw [isFalse_eq_true] at htF
            rw [isTrue_eq_true] at heT
            subst t
            subst e
            simpa [Expr.smartIte, hcT, hcF, htT] using evalBool?_ite_negation m c
          · simp [Expr.smartIte, hcT, hcF, htT, htF, heT]
        · simp [Expr.smartIte, hcT, hcF, htT, htF]

theorem evalBool?_simplifyBool (m : Model) (e : Expr) :
    evalBool? m (Expr.simplifyBool e) = evalBool? m e := by
  cases e with
  | sym s | int s | bytes s | dataLit s | dataListLit s | dataPairListLit s
  | constListLit s | bool s | str s => rfl
  | ite c t e =>
      simp only [Expr.simplifyBool]
      rw [evalBool?_smartIte, evalBool?_ite_eq, evalBool?_ite_eq,
        evalBool?_simplifyBool, evalBool?_simplifyBool, evalBool?_simplifyBool]
  | app f args =>
      by_cases hnot : f = "not"
      · subst f
        cases args with
        | nil => rfl
        | cons a rest =>
            cases rest with
            | nil =>
                simp only [Expr.simplifyBool]
                rw [evalBool?_smartNot, evalBool?_not_eq, evalBool?_not_eq,
                  evalBool?_simplifyBool]
            | cons b rest => rfl
      · by_cases hand : f = "and"
        · subst f
          cases args with
          | nil => rfl
          | cons a rest =>
              cases rest with
              | nil => rfl
              | cons b rest =>
                  cases rest with
                  | nil =>
                      simp only [Expr.simplifyBool]
                      rw [evalBool?_smartAnd, evalBool?_and_eq, evalBool?_and_eq,
                        evalBool?_simplifyBool, evalBool?_simplifyBool]
                  | cons c rest => rfl
        · by_cases hor : f = "or"
          · subst f
            cases args with
            | nil => rfl
            | cons a rest =>
                cases rest with
                | nil => rfl
                | cons b rest =>
                    cases rest with
                    | nil =>
                        simp only [Expr.simplifyBool]
                        rw [evalBool?_smartOr, evalBool?_or_eq, evalBool?_or_eq,
                          evalBool?_simplifyBool, evalBool?_simplifyBool]
                    | cons c rest => rfl
          · simp [Expr.simplifyBool, hnot, hand, hor]
termination_by sizeOf e
decreasing_by all_goals simp_wf; omega

/-- Boolean observation is exactly preserved, for either expected truth value. -/
theorem evalBoolIs_simplifyBool (m : Model) (e : Expr) (b : Bool) :
    evalBoolIs m (Expr.simplifyBool e) b = evalBoolIs m e b := by
  unfold evalBoolIs
  rw [evalBool?_simplifyBool]

end Semantics

end Moist.SMT
