import Moist.MIR.Optimize.RecursionPeeling
import Moist.Verified.AdvancedRefinement
import Moist.Verified.Contextual.Congruence
import Moist.Verified.InlineSoundness.FrontierError
import Moist.Verified.LoweringSoundness

namespace Moist.Verified.MIR

open Moist.CEK Moist.Plutus.Term
open Moist.MIR.RecursionPeeling
open Moist.Verified.Equivalence (ListRel steps)
open Moist.Verified.Contextual
open Moist.Verified.InlineSoundness.Frontier (beta_total_ctxRefines)
open Moist.Verified.LoweringSoundness (closedAt_of_ctxRefines)

variable [sv : SemVariant]

private theorem listCongruence {wrap : List Term → Term} {left right : List Term}
    (replace : ∀ head tail {a b}, CtxRefines a b →
      CtxRefines (wrap (head ++ a :: tail)) (wrap (head ++ b :: tail)))
    (related : ListRel CtxRefines left right) :
    CtxRefines (wrap left) (wrap right) := by
  have go : ∀ (left right head : List Term), ListRel CtxRefines left right →
      CtxRefines (wrap (head ++ left)) (wrap (head ++ right)) := by
    intro left
    induction left with
    | nil =>
      intro right head related
      cases right with
      | nil => exact ctxRefines_refl _
      | cons _ _ => cases related
    | cons a left ih =>
      intro right head related
      cases right with
      | nil => cases related
      | cons b right =>
        exact ctxRefines_trans (replace head left related.1)
          (by simpa [List.append_assoc] using ih right (head ++ [b]) related.2)
  exact go left right [] related

private theorem constructorRefines {tag : Nat} {left right : List Term}
    (related : ListRel CtxRefines left right) :
    CtxRefines (.Constr tag left) (.Constr tag right) := by
  apply listCongruence (wrap := .Constr tag) _ related
  intro head tail _ _ h
  simpa [fill, List.append_assoc] using ctxRefines_fill h (.Constr tag head .Hole tail)

private theorem caseRefines {left right : Term} {leftAlts rightAlts : List Term}
    (scrutinee : CtxRefines left right) (branches : ListRel CtxRefines leftAlts rightAlts) :
    CtxRefines (.Case left leftAlts) (.Case right rightAlts) := by
  apply ctxRefines_trans (t₂ := .Case right leftAlts)
  · simpa [fill] using ctxRefines_fill scrutinee (.Case .Hole leftAlts)
  · apply listCongruence (wrap := .Case right) _ branches
    intro head tail _ _ h
    simpa [fill, List.append_assoc] using ctxRefines_fill h (.CaseAlt right head .Hole tail)

omit sv in
private theorem selfApplication_closed (scope : Nat) (worker : Term) :
    closedAt scope (selfApplication worker) = closedAt (scope + 1) worker := by
  simp [selfApplication, closedAt]

omit sv in
private theorem fixedPoint_closed (scope : Nat) (worker : Term) :
    closedAt scope (fixedPoint worker) = closedAt (scope + 1) worker := by
  simp [fixedPoint, closedAt]

private theorem fixedPointSteps (stack : Stack) (environment : CekEnv) (worker : Term) :
    steps 10 (.compute stack environment (fixedPoint worker)) =
      steps 5 (.compute stack environment (selfApplication worker)) := rfl

private theorem fixedPoint_refines_selfApplication (scope : Nat) (worker : Term)
    (closed : closedAt (scope + 1) worker = true) :
    CtxRefines (fixedPoint worker) (selfApplication worker) := by
  apply AdvancedRefinement.contextual_of_uniform_join (depth := scope)
  · simpa only [fixedPoint_closed] using closed
  · intro depth h
    simpa only [selfApplication_closed, fixedPoint_closed] using h
  · intro environment stack
    exact ⟨10, 5, fixedPointSteps stack environment worker⟩

private theorem selfApplication_refines_fixedPoint (scope : Nat) (worker : Term)
    (closed : closedAt (scope + 1) worker = true) :
    CtxRefines (selfApplication worker) (fixedPoint worker) := by
  apply AdvancedRefinement.contextual_of_uniform_join (depth := scope)
  · simpa only [selfApplication_closed] using closed
  · intro depth h
    simpa only [selfApplication_closed, fixedPoint_closed] using h
  · intro environment stack
    exact ⟨5, 10, (fixedPointSteps stack environment worker).symm⟩

private theorem contractArgument_refines (scope : Nat) (function argument : Term) :
    CtxRefines (.Apply function argument) (contractArgument scope function argument) := by
  unfold contractArgument
  split
  · rename_i body index
    split
    · rename_i valid
      exact beta_total_ctxRefines (.var valid.1) valid.2.2 (by simpa [closedAt] using valid.2.1)
    · exact ctxRefines_refl _
  · exact ctxRefines_refl _

mutual
  private theorem peelSelf_refines (count scope : Nat) (worker term : Term)
      (closed : closedAt scope term = true) :
      CtxRefines term (peelSelf count scope worker term) := by
    rw [peelSelf.eq_def]
    split
    · rename_i same
      subst term
      have workerClosed : closedAt (scope + 1) worker = true := by
        simpa only [selfApplication_closed] using closed
      cases count with
      | zero => exact selfApplication_refines_fixedPoint scope worker workerClosed
      | succ count =>
        simp only [workerClosed, ↓reduceIte]
        have rhsClosed : closedAt scope (.Lam 0 worker) = true := by
          simpa only [closedAt] using workerClosed
        have beta : CtxRefines (selfApplication worker) (substTerm 1 (.Lam 0 worker) worker) :=
          beta_total_ctxRefines .lam workerClosed rhsClosed
        exact ctxRefines_trans beta (peelSelf_refines count scope worker _ (closedAt_of_ctxRefines beta closed))
    · cases term with
      | Lam name body =>
        exact ctxRefines_lam name (peelSelf_refines count (scope + 1) _ body (by simpa only [closedAt] using closed))
      | Apply function argument =>
        have childrenClosed : closedAt scope function = true ∧ closedAt scope argument = true := by
          simpa only [closedAt, Bool.and_eq_true] using closed
        have children := ctxRefines_app
          (peelSelf_refines count scope worker function childrenClosed.1)
          (peelSelf_refines count scope worker argument childrenClosed.2)
        let function' := peelSelf count scope worker function
        let argument' := peelSelf count scope worker argument
        change CtxRefines (.Apply function argument)
          (if function' = function then .Apply function' argument' else contractArgument scope function' argument')
        by_cases same : function' = function
        · rw [if_pos same]
          exact children
        · rw [if_neg same]
          exact ctxRefines_trans children (contractArgument_refines scope function' argument')
      | Force body =>
        simpa [fill] using ctxRefines_fill
          (peelSelf_refines count scope worker body (by simpa only [closedAt] using closed)) (.Force .Hole)
      | Delay body =>
        simpa [fill] using ctxRefines_fill
          (peelSelf_refines count scope worker body (by simpa only [closedAt] using closed)) (.Delay .Hole)
      | Constr tag fields =>
        exact constructorRefines (peelSelfList_refines count scope worker fields (by simpa only [closedAt] using closed))
      | Case scrutinee branches =>
        have childrenClosed : closedAt scope scrutinee = true ∧ closedAtList scope branches = true := by
          simpa only [closedAt, Bool.and_eq_true] using closed
        exact caseRefines (peelSelf_refines count scope worker scrutinee childrenClosed.1)
          (peelSelfList_refines count scope worker branches childrenClosed.2)
      | Var _ | Constant _ | Builtin _ | Error => exact ctxRefines_refl _
  termination_by (count, sizeOf term)

  private theorem peelSelfList_refines (count scope : Nat) (worker : Term) (terms : List Term)
      (closed : closedAtList scope terms = true) :
      ListRel CtxRefines terms (peelSelfList count scope worker terms) := by
    cases terms with
    | nil =>
      rw [peelSelfList]
      trivial
    | cons term rest =>
      have childrenClosed : closedAt scope term = true ∧ closedAtList scope rest = true := by
        simpa only [closedAtList, Bool.and_eq_true] using closed
      rw [peelSelfList]
      exact ⟨peelSelf_refines count scope worker term childrenClosed.1,
        peelSelfList_refines count scope worker rest childrenClosed.2⟩
  termination_by (count, sizeOf terms)
end

private theorem peelRoot_refines (count scope : Nat) (term : Term) (closed : closedAt scope term = true) :
    CtxRefines term (peelRoot count scope term) := by
  unfold peelRoot
  split
  · rename_i n name body
    split
    · have h : closedAt (scope + 1) (.Lam name body) = true := by
        simpa only [fixedPoint_closed] using (show closedAt scope (fixedPoint (.Lam name body)) = true from closed)
      have join := fixedPoint_refines_selfApplication scope (.Lam name body) h
      exact ctxRefines_trans join (peelSelf_refines (n + 1) scope (.Lam name body) _
        (closedAt_of_ctxRefines join closed))
    · exact ctxRefines_refl _
  · exact ctxRefines_refl _

mutual
  private theorem peelTerm_refines (count scope : Nat) (term : Term)
      (closed : closedAt scope term = true) :
      CtxRefines term (peelTerm count scope term) := by
    rw [peelTerm.eq_def]
    have finish (rewritten : Term) (related : CtxRefines term rewritten) :
        CtxRefines term (peelRoot count scope rewritten) :=
      ctxRefines_trans related (peelRoot_refines count scope rewritten (closedAt_of_ctxRefines related closed))
    apply finish
    cases term with
    | Lam name body =>
      exact ctxRefines_lam name (peelTerm_refines count (scope + 1) body (by simpa only [closedAt] using closed))
    | Apply function argument =>
      have childrenClosed : closedAt scope function = true ∧ closedAt scope argument = true := by
        simpa only [closedAt, Bool.and_eq_true] using closed
      exact ctxRefines_app (peelTerm_refines count scope function childrenClosed.1)
        (peelTerm_refines count scope argument childrenClosed.2)
    | Force body =>
      simpa [fill] using ctxRefines_fill (peelTerm_refines count scope body (by simpa only [closedAt] using closed))
        (.Force .Hole)
    | Delay body =>
      simpa [fill] using ctxRefines_fill (peelTerm_refines count scope body (by simpa only [closedAt] using closed))
        (.Delay .Hole)
    | Constr _ fields => exact constructorRefines (peelTermList_refines count scope fields (by simpa only [closedAt] using closed))
    | Case scrutinee branches =>
      have childrenClosed : closedAt scope scrutinee = true ∧ closedAtList scope branches = true := by
        simpa only [closedAt, Bool.and_eq_true] using closed
      exact caseRefines (peelTerm_refines count scope scrutinee childrenClosed.1)
        (peelTermList_refines count scope branches childrenClosed.2)
    | Var _ | Constant _ | Builtin _ | Error => exact ctxRefines_refl _
  termination_by sizeOf term

  private theorem peelTermList_refines (count scope : Nat) (terms : List Term)
      (closed : closedAtList scope terms = true) :
      ListRel CtxRefines terms (peelTermList count scope terms) := by
    cases terms with
    | nil =>
      rw [peelTermList]
      trivial
    | cons term rest =>
      have childrenClosed : closedAt scope term = true ∧ closedAtList scope rest = true := by
        simpa only [closedAtList, Bool.and_eq_true] using closed
      rw [peelTermList]
      exact ⟨peelTerm_refines count scope term childrenClosed.1,
        peelTermList_refines count scope rest childrenClosed.2⟩
  termination_by sizeOf terms
end

/-- Fixed-point peeling contextually refines the original UPLC at every depth. -/
theorem peelRecursion_refines (count : Nat) (term : Term) :
    CtxRefines term (Moist.MIR.peelRecursion count term) := by
  unfold Moist.MIR.peelRecursion
  split
  · rename_i eligible
    exact peelTerm_refines count 0 term eligible.2
  · exact ctxRefines_refl _

end Moist.Verified.MIR
