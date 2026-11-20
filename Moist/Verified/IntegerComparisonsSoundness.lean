import Moist.MIR.Optimize.Advanced.IntegerComparisons
import Moist.Verified.ContinuationRefinement
import Moist.Verified.AdvancedTraversal

namespace Moist.Verified.MIR

open Moist.CEK Moist.MIR Moist.MIR.Advanced Moist.Plutus.Term
open Moist.Verified.Equivalence Moist.Verified.Contextual Moist.Verified.ContinuationRefinement

private theorem strictRight (left right : Int) : (left < right) = (left ≤ right - 1) := by
  apply propext
  constructor <;> intro related <;> omega

private theorem strictLeft (left right : Int) : (left < right) = (left + 1 ≤ right) := by
  apply propext
  constructor <;> intro related <;> omega

variable [sv : SemVariant]

private theorem compareRightResult (argument : CekValue) (k : Int)
    (fits : oneWordThreshold k (k - 1) = true) :
    evalBuiltin .LessThanInteger [.VCon (.Integer k), argument] =
      evalBuiltin .LessThanEqualsInteger [.VCon (.Integer (k - 1)), argument] := by
  have ⟨original, shifted⟩ : k.natAbs < 2 ^ 64 ∧ (k - 1).natAbs < 2 ^ 64 := by
    simpa [oneWordThreshold] using fits
  cases argument with
  | VCon value =>
    cases value
    case Integer n =>
      have source := evalBuiltin_consts .LessThanInteger [.Integer k, .Integer n] rfl
      have target := evalBuiltin_consts .LessThanEqualsInteger [.Integer (k - 1), .Integer n] rfl
      simp only [List.map_cons, List.map_nil] at source target
      rw [source, target]
      change (if cIntegerOk sv n && cIntegerOk sv k then some (.Bool (decide (n < k))) else none).map
          CekValue.VCon =
        (if cIntegerOk sv n && cIntegerOk sv (k - 1) then some (.Bool (decide (n ≤ k - 1))) else none).map
          CekValue.VCon
      simp only [cIntegerOk_of_natAbs_lt sv k original,
        cIntegerOk_of_natAbs_lt sv (k - 1) shifted, Bool.and_true, strictRight n k]
    all_goals rfl
  | _ => rfl

private theorem compareLeftResult (argument : CekValue) (k : Int)
    (fits : oneWordThreshold k (k + 1) = true) :
    evalBuiltin .LessThanInteger [argument, .VCon (.Integer k)] =
      evalBuiltin .LessThanEqualsInteger [argument, .VCon (.Integer (k + 1))] := by
  have ⟨original, shifted⟩ : k.natAbs < 2 ^ 64 ∧ (k + 1).natAbs < 2 ^ 64 := by
    simpa [oneWordThreshold] using fits
  cases argument with
  | VCon value =>
    cases value
    case Integer n =>
      have source := evalBuiltin_consts .LessThanInteger [.Integer n, .Integer k] rfl
      have target := evalBuiltin_consts .LessThanEqualsInteger [.Integer n, .Integer (k + 1)] rfl
      simp only [List.map_cons, List.map_nil] at source target
      rw [source, target]
      change (if cIntegerOk sv k && cIntegerOk sv n then some (.Bool (decide (k < n))) else none).map
          CekValue.VCon =
        (if cIntegerOk sv (k + 1) && cIntegerOk sv n then some (.Bool (decide (k + 1 ≤ n))) else none).map
          CekValue.VCon
      simp only [cIntegerOk_of_natAbs_lt sv k original,
        cIntegerOk_of_natAbs_lt sv (k + 1) shifted, Bool.true_and, strictLeft k n]
    all_goals rfl
  | _ => rfl

private def integerConstant (k : Int) : Term := .Constant (.Integer k, .AtomicType .TypeInteger)

private def comparisonTerm (b : BuiltinFun) (left right : Term) : Term := .Apply (.Apply (.Builtin b) left) right

omit sv in
private theorem lowerBuiltin (environment : List VarId) (b : BuiltinFun) :
    lowerTotalExpr environment (.Builtin b) = some (.Builtin b) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal]

omit sv in
private theorem lowerInteger (environment : List VarId) (k : Int) :
    lowerTotalExpr environment (.Lit (.Integer k, .AtomicType .TypeInteger)) = some (integerConstant k) := by
  simp only [lowerTotalExpr, expandFix, lowerTotal, integerConstant]

private theorem compareRightTerm (scope : Nat) (argument : Term) (k : Int)
    (closed : Moist.Verified.closedAt scope argument = true)
    (fits : oneWordThreshold k (k - 1) = true) :
    CtxRefines (comparisonTerm .LessThanInteger argument (integerConstant k))
      (comparisonTerm .LessThanEqualsInteger argument (integerConstant (k - 1))) := by
  apply AdvancedRefinement.contextual_of_uniform_refinement (depth := scope)
  · simp [comparisonTerm, integerConstant, Moist.Verified.closedAt, closed]
  · intro depth source
    simpa [comparisonTerm, integerConstant, Moist.Verified.closedAt] using source
  intro environment stack
  apply TerminalRefines.obs
  apply TerminalRefines.prefix 4 4
  apply compute_of_returns
  intro value
  apply TerminalRefines.prefix 4 4
  change TerminalRefines
    (match evalBuiltin .LessThanInteger [.VCon (.Integer k), value] with
      | some answer => .ret stack answer | none => .error)
    (match evalBuiltin .LessThanEqualsInteger [.VCon (.Integer (k - 1)), value] with
      | some answer => .ret stack answer | none => .error)
  rw [compareRightResult value k fits]
  exact TerminalRefines.refl _

private theorem compareLeftTerm (scope : Nat) (argument : Term) (k : Int)
    (closed : Moist.Verified.closedAt scope argument = true)
    (fits : oneWordThreshold k (k + 1) = true) :
    CtxRefines (comparisonTerm .LessThanInteger (integerConstant k) argument)
      (comparisonTerm .LessThanEqualsInteger (integerConstant (k + 1)) argument) := by
  apply AdvancedRefinement.contextual_of_uniform_refinement (depth := scope)
  · simp [comparisonTerm, integerConstant, Moist.Verified.closedAt, closed]
  · intro depth source
    simpa [comparisonTerm, integerConstant, Moist.Verified.closedAt] using source
  intro environment stack
  apply TerminalRefines.obs
  apply TerminalRefines.prefix 7 7
  apply compute_of_returns
  intro value
  apply TerminalRefines.prefix 1 1
  change TerminalRefines
    (match evalBuiltin .LessThanInteger [value, .VCon (.Integer k)] with
      | some answer => .ret stack answer | none => .error)
    (match evalBuiltin .LessThanEqualsInteger [value, .VCon (.Integer (k + 1))] with
      | some answer => .ret stack answer | none => .error)
  rw [compareLeftResult value k fits]
  exact TerminalRefines.refl _

private theorem compareRightExpr (argument : Expr) (k : Int)
    (fits : oneWordThreshold k (k - 1) = true) :
    MIRCtxRefines (.App (.App (.Builtin .LessThanInteger) argument)
        (.Lit (.Integer k, .AtomicType .TypeInteger)))
      (.App (.App (.Builtin .LessThanEqualsInteger) argument)
        (.Lit (.Integer (k - 1), .AtomicType .TypeInteger))) := by
  intro environment
  simp only [lowerTotalExpr_app, lowerBuiltin, lowerInteger]
  cases lowered : lowerTotalExpr environment argument with
  | none => simp
  | some term =>
    refine ⟨fun _ => rfl, ?_⟩
    exact compareRightTerm environment.length term k (lowerTotalExpr_closedAt lowered) fits

private theorem compareLeftExpr (argument : Expr) (k : Int)
    (fits : oneWordThreshold k (k + 1) = true) :
    MIRCtxRefines (.App (.App (.Builtin .LessThanInteger)
        (.Lit (.Integer k, .AtomicType .TypeInteger))) argument)
      (.App (.App (.Builtin .LessThanEqualsInteger)
        (.Lit (.Integer (k + 1), .AtomicType .TypeInteger))) argument) := by
  intro environment
  simp only [lowerTotalExpr_app, lowerBuiltin, lowerInteger]
  cases lowered : lowerTotalExpr environment argument with
  | none => simp
  | some term =>
    refine ⟨fun _ => rfl, ?_⟩
    exact compareLeftTerm environment.length term k (lowerTotalExpr_closedAt lowered) fits

private theorem integerComparisonRoot_refines (expression : Expr) :
    MIRCtxRefines expression (integerComparisonRoot expression) := by
  unfold integerComparisonRoot
  split
  · split
    · exact compareRightExpr _ _ (by assumption)
    · exact mirCtxRefines_refl _
  · split
    · exact compareLeftExpr _ _ (by assumption)
    · exact mirCtxRefines_refl _
  · exact mirCtxRefines_refl _

theorem normalizeIntegerComparisons_refines (expression : Expr) :
    MIRCtxRefines expression (normalizeIntegerComparisons expression) := by
  apply rewriteBottomUp_refines integerComparisonRoot integerComparisonRoot_refines
  intro binder body
  rfl

end Moist.Verified.MIR
