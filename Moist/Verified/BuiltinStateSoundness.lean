import Moist.Verified.Purity
import Moist.MIR.Optimize.Safety
import Moist.MIR.Optimize.PreLower

namespace Moist.Verified.BuiltinState

open Moist.MIR Moist.Plutus.Term Moist.CEK
open Moist.Verified.Semantics

theorem builtinRemainder_returns (expression : Expr) (environment : List VarId)
    (term : Term) (remaining : ExpectedArgs)
    (checked : builtinRemainder expression = some remaining)
    (lowered : lowerTotal environment expression = some term)
    (runtime : CekEnv) (sized : WellSizedEnv environment.length runtime) :
    ∃ builtin arguments, ∀ stack, ∃ fuel,
      steps fuel (.compute stack runtime term) = .ret stack (.VBuiltin builtin arguments remaining) := by
  match expression with
  | .Builtin builtin =>
    simp only [builtinRemainder] at checked
    cases checked
    simp only [lowerTotal] at lowered
    cases lowered
    exact ⟨builtin, [], fun _ => ⟨1, rfl⟩⟩
  | .Force inner =>
    simp only [builtinRemainder, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨state, innerChecked, checked⟩ := checked
    split at checked
    · rename_i headChecked
      cases state with
      | one kind => simp [ExpectedArgs.tail] at checked
      | more kind rest =>
        simp only [ExpectedArgs.tail] at checked
        cases checked
        cases kind with
        | argV => exact absurd headChecked (by change ¬(ArgKind.argV == ArgKind.argQ) = true; decide)
        | argQ =>
          simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
          obtain ⟨innerTerm, innerLowered, equal⟩ := lowered
          cases equal
          obtain ⟨builtin, arguments, returns⟩ := builtinRemainder_returns inner environment innerTerm
            (.more .argQ remaining) innerChecked innerLowered runtime sized
          refine ⟨builtin, arguments, ?_⟩
          intro stack
          obtain ⟨fuel, returns⟩ := returns (.force :: stack)
          refine ⟨1 + fuel + 1, ?_⟩
          rw [show 1 + fuel + 1 = 1 + (fuel + 1) by omega, steps_trans]
          change steps (fuel + 1) (.compute (.force :: stack) runtime innerTerm) = _
          rw [steps_trans, returns]
          rfl
    · contradiction
  | .App function argument =>
    simp only [builtinRemainder, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨state, functionChecked, checked⟩ := checked
    split at checked
    · rename_i safe
      have safe' := Bool.and_eq_true_iff.mp safe
      cases state with
      | one kind => simp [ExpectedArgs.tail] at checked
      | more kind rest =>
        simp only [ExpectedArgs.tail] at checked
        cases checked
        cases kind with
        | argQ => exact absurd safe'.1 (by change ¬(ArgKind.argQ == ArgKind.argV) = true; decide)
        | argV =>
          simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
          obtain ⟨functionTerm, functionLowered, argumentTerm, argumentLowered, equal⟩ := lowered
          cases equal
          obtain ⟨builtin, arguments, returns⟩ := builtinRemainder_returns function environment functionTerm
            (.more .argV remaining) functionChecked functionLowered runtime sized
          obtain ⟨value, halts⟩ := Purity.isPure_halts argument argumentTerm environment runtime safe'.2 argumentLowered sized
          refine ⟨builtin, value :: arguments, ?_⟩
          intro stack
          obtain ⟨functionFuel, functionReturns⟩ := returns (.arg argumentTerm runtime :: stack)
          obtain ⟨argumentFuel, argumentReturns⟩ := Purity.compute_to_ret_from_halt runtime argumentTerm value
            (.funV (.VBuiltin builtin arguments (.more .argV remaining)) :: stack) halts
          refine ⟨1 + functionFuel + 1 + argumentFuel + 1, ?_⟩
          rw [show 1 + functionFuel + 1 + argumentFuel + 1 =
            1 + (functionFuel + (1 + (argumentFuel + 1))) by omega, steps_trans]
          change steps (functionFuel + (1 + (argumentFuel + 1)))
            (.compute (.arg argumentTerm runtime :: stack) runtime functionTerm) = _
          rw [steps_trans, functionReturns, steps_trans]
          change steps (argumentFuel + 1)
            (.compute (.funV (.VBuiltin builtin arguments (.more .argV remaining)) :: stack)
              runtime argumentTerm) = _
          rw [steps_trans, argumentReturns]
          rfl
    · contradiction
  | .Var _ | .Lit _ | .Error | .Lam _ _ | .Fix _ _ | .Delay _ | .Constr _ _ | .Case _ _ | .Let _ _ =>
    simp [builtinRemainder] at checked
termination_by sizeOf expression

theorem builtinRemainder_halts (expression : Expr) (environment : List VarId)
    (term : Term) (remaining : ExpectedArgs)
    (checked : builtinRemainder expression = some remaining)
    (lowered : lowerTotal environment expression = some term)
    (runtime : CekEnv) (sized : WellSizedEnv environment.length runtime) :
    ∃ value, Reaches (.compute [] runtime term) (.halt value) := by
  obtain ⟨builtin, arguments, returns⟩ :=
    builtinRemainder_returns expression environment term remaining checked lowered runtime sized
  obtain ⟨fuel, returns⟩ := returns []
  exact ⟨.VBuiltin builtin arguments remaining, fuel + 1, by rw [steps_trans, returns]; rfl⟩

theorem builtinRemainder_expandFix (expression : Expr) (remaining : ExpectedArgs)
    (checked : builtinRemainder expression = some remaining) :
    builtinRemainder (expandFix expression) = some remaining := by
  match expression with
  | .Builtin _ => simpa only [expandFix] using checked
  | .Force inner =>
    simp only [builtinRemainder, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨state, innerChecked, checked⟩ := checked
    simp only [expandFix, builtinRemainder, Option.bind_eq_bind,
      builtinRemainder_expandFix inner state innerChecked, Option.bind_some]
    exact checked
  | .App function argument =>
    simp only [builtinRemainder, Option.bind_eq_bind, Option.bind_eq_some_iff] at checked
    obtain ⟨state, functionChecked, checked⟩ := checked
    split at checked
    · rename_i safe
      have safe' := Bool.and_eq_true_iff.mp safe
      simp only [expandFix, builtinRemainder, Option.bind_eq_bind,
        builtinRemainder_expandFix function state functionChecked, Option.bind_some,
        safe'.1, Purity.isPure_expandFix argument safe'.2, Bool.and_self, if_true]
      exact checked
    · contradiction
  | .Var _ | .Lit _ | .Error | .Lam _ _ | .Fix _ _ | .Delay _ | .Constr _ _ | .Case _ _ | .Let _ _ =>
    simp [builtinRemainder] at checked
termination_by sizeOf expression

theorem isTotalPreLowerValue_halts (expression : Expr) (environment : List VarId) (term : Term)
    (checked : isTotalPreLowerValue expression = true)
    (lowered : lowerTotalExpr environment expression = some term)
    (runtime : CekEnv) (sized : WellSizedEnv environment.length runtime) :
    ∃ value, Reaches (.compute [] runtime term) (.halt value) := by
  rcases Bool.or_eq_true_iff.mp checked with pure | state
  · exact Purity.isPure_halts (expandFix expression) term environment runtime
      (Purity.isPure_expandFix expression pure) lowered sized
  · cases remainder : builtinRemainder expression with
    | none => simp [remainder] at state
    | some remaining =>
      exact builtinRemainder_halts (expandFix expression) environment term remaining
        (builtinRemainder_expandFix expression remaining remainder) lowered runtime sized

theorem isTotalPreLowerValue_no_error (expression : Expr) (environment : List VarId) (term : Term)
    (checked : isTotalPreLowerValue expression = true)
    (lowered : lowerTotalExpr environment expression = some term)
    (runtime : CekEnv) (sized : WellSizedEnv environment.length runtime) :
    ¬Reaches (.compute [] runtime term) .error := by
  obtain ⟨value, haltFuel, halts⟩ := isTotalPreLowerValue_halts expression environment term checked lowered runtime sized
  rintro ⟨errorFuel, errors⟩
  have haltAfter : steps (haltFuel + errorFuel) (.compute [] runtime term) = .halt value := by
    rw [steps_trans, halts, steps_halt]
  have errorAfter : steps (errorFuel + haltFuel) (.compute [] runtime term) = .error := by
    rw [steps_trans, errors, steps_error]
  rw [Nat.add_comm] at haltAfter
  rw [haltAfter] at errorAfter
  contradiction

def Callable : CekValue → Prop
  | .VLam _ _ => True
  | .VBuiltin _ _ remaining => remaining.head = .argV
  | _ => False

theorem isCallableValue_returns (expression : Expr) (environment : List VarId) (term : Term)
    (checked : isCallableValue expression = true)
    (lowered : lowerTotal environment expression = some term)
    (runtime : CekEnv) (sized : WellSizedEnv environment.length runtime) :
    ∃ value, Callable value ∧ ∀ stack, ∃ fuel,
      steps fuel (.compute stack runtime term) = .ret stack value := by
  unfold isCallableValue at checked
  split at checked
  · simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
    obtain ⟨body, _, equal⟩ := lowered
    cases equal
    exact ⟨.VLam body runtime, trivial, fun _ => ⟨1, rfl⟩⟩
  · cases remainder : builtinRemainder expression with
    | none => simp [remainder] at checked
    | some remaining =>
      simp only [remainder, Option.any_some] at checked
      obtain ⟨builtin, arguments, returns⟩ :=
        builtinRemainder_returns expression environment term remaining remainder lowered runtime sized
      refine ⟨.VBuiltin builtin arguments remaining, ?_, returns⟩
      change remaining.head = .argV
      cases headEqual : remaining.head with
      | argV => rfl
      | argQ => rw [headEqual] at checked; contradiction

end Moist.Verified.BuiltinState
