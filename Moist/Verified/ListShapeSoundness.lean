import Moist.MIR.Optimize.Advanced.Shapes
import Moist.Verified.ContinuationRefinement

namespace Moist.Verified.ListShape

open Moist.MIR Moist.MIR.Advanced Moist.CEK Moist.Plutus.Term
open Moist.Verified.Equivalence

def ListValue : CekValue → Prop
  | .VCon (.ConstList _) | .VCon (.ConstDataList _) | .VCon (.ConstPairDataList _) => True
  | _ => False

theorem knownList_literal (fuel : Nat) (facts : List (VarId × Expr)) (literal : Const × BuiltinType)
    (accepted : knownList fuel facts (.Lit literal) = true) : ListValue (.VCon literal.1) := by
  cases fuel with
  | zero => simp [knownList] at accepted
  | succ fuel =>
    obtain ⟨constant, annotation⟩ := literal
    cases constant <;> try trivial
    all_goals cases annotation <;> simp_all [knownList]

theorem knownList_literal_returns (fuel : Nat) (facts : List (VarId × Expr))
    (literal : Const × BuiltinType) (accepted : knownList fuel facts (.Lit literal) = true)
    (environment : CekEnv) (stack : Stack) :
    ∃ value, ListValue value ∧ steps 1 (.compute stack environment (.Constant literal)) = .ret stack value :=
  ⟨.VCon literal.1, knownList_literal fuel facts literal accepted, by cases literal; rfl⟩

end Moist.Verified.ListShape
