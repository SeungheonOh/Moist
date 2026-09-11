import Moist.Verified.ListShapeSoundness

namespace Test.MIR.Opt.ListShapeCertificates

open Moist.CEK Moist.Plutus.Term Moist.Verified.Equivalence
open Moist.Verified.ContinuationRefinement

def forgedList : Term := .Constant (.Integer 0, .TypeOperator (.TypeList (.AtomicType .TypeInteger)))

def original : Term := .Apply (.Lam 0 (.Apply (.Lam 0 (.Constant (.Integer 42, .AtomicType .TypeInteger)))
    (.Apply (.Force (.Builtin .TailList)) forgedList)))
  (.Apply (.Force (.Builtin .HeadList)) forgedList)

def unsoundFusion : Term := .Case forgedList [.Lam 0 (.Lam 0 (.Constant (.Integer 42, .AtomicType .TypeInteger))), .Error]

theorem original_errors : Reaches (.compute [] .nil original) .error := ⟨10, rfl⟩

theorem unsoundFusion_halts : Reaches (.compute [] .nil unsoundFusion)
    (.halt (.VLam (.Lam 0 (.Constant (.Integer 42, .AtomicType .TypeInteger))) .nil)) := ⟨5, rfl⟩

theorem annotation_only_list_fusion_not_refines :
    ¬Moist.Verified.Contextual.CtxRefines original unsoundFusion := by
  intro refines
  have errors := (refines .Hole (by simp [Moist.Verified.Contextual.fill, original, forgedList,
    Moist.Verified.closedAt])).2.error original_errors
  change Reaches (.compute [] .nil unsoundFusion) .error at errors
  have halts := unsoundFusion_halts
  obtain ⟨fuel, returned⟩ := halts
  have after := (Moist.Verified.AdvancedRefinement.reaches_after_prefix fuel rfl).mp errors
  rw [returned] at after
  obtain ⟨remaining, impossible⟩ := after
  have fixed : ∀ count value, steps count (.halt value) = .halt value := by
    intro count value
    induction count with
    | zero => rfl
    | succ count inductionHypothesis => exact inductionHypothesis
  rw [fixed] at impossible
  contradiction

theorem corrected_checker_rejects_forged_list (fuel : Nat) (facts : List (Moist.MIR.VarId × Moist.MIR.Expr)) :
    Moist.MIR.Advanced.knownList fuel facts
      (.Lit (.Integer 0, .TypeOperator (.TypeList (.AtomicType .TypeInteger)))) = false := by
  cases fuel <;> rfl

end Test.MIR.Opt.ListShapeCertificates
