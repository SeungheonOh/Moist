import Moist.Verified.InlineSoundness.FrontierError

namespace Test.MIR.Opt.FrontierCertificates

open Moist.Plutus.Term Moist.Verified
open Moist.Verified.InlineSoundness.Frontier
open Moist.Verified.InlineSoundness.StrictOcc
open Moist.Verified.InlineSoundness.Totality

def unitTerm : Term := .Constant (.Unit, .AtomicType .TypeUnit)

def nestedBody : Term :=
  .Apply (.Lam 0 (.Constr 0 [unitTerm, .Apply (.Lam 0 (.Var 1)) (.Var 2)]))
    (.Force (.Delay unitTerm))

theorem nested_path : EvaluationPath 1 nestedBody :=
  .letBody (.forceDelay .constant)
    (.constr (.tail .constant (.head (.applyRight .lam .var))))

theorem nested_single : StrictSingleOcc 1 nestedBody := by
  apply StrictSingleOcc.let_body
  · apply StrictSingleOcc.constr
    apply StrictSingleOccList.tail
    · simp [freeOf, unitTerm]
    · apply StrictSingleOccList.head
      · exact .apply_r (by simp [freeOf]) .var
      · simp [freeOfList]
  · simp [freeOf, unitTerm]

theorem nested_beta_refines (depth : Nat) (rhs : Term) (closed : closedAt depth rhs = true) :
    Contextual.CtxRefines (.Apply (.Lam 0 nestedBody) rhs) (substTerm 1 rhs nestedBody) := by
  apply beta_evaluationPath_ctxRefines nested_path nested_single
  · simp [nestedBody, unitTerm, closedAt, closedAtList]
  · exact closed

def caseBody : Term := .Case (.Force (.Var 1)) [unitTerm, .Error]

theorem case_beta_refines (depth : Nat) (rhs : Term) (closed : closedAt depth rhs = true) :
    Contextual.CtxRefines (.Apply (.Lam 0 caseBody) rhs) (substTerm 1 rhs caseBody) := by
  apply beta_evaluationPath_ctxRefines (.caseScrutinee (.force .var))
    (.case_scrut (.force .var) (by simp [freeOfList, freeOf, unitTerm]))
  · simp [unitTerm, closedAt, closedAtList]
  · exact closed

theorem zero_index_not_total : ¬TotalTerm (.Var 0) := by
  intro total
  cases total with | var positive => omega

end Test.MIR.Opt.FrontierCertificates
