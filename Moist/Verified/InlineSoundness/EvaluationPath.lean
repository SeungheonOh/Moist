import Moist.Verified.InlineSoundness.Totality
import Moist.Verified.InlineSoundness.OccBridge
import Moist.MIR.Optimize.Safety

set_option maxHeartbeats 800000

namespace Moist.Verified.InlineSoundness.Frontier

open Moist.CEK Moist.Plutus.Term Moist.MIR
open Moist.Verified.InlineSoundness.Totality

mutual
  inductive EvaluationPath : Nat → Term → Prop where
    | var : EvaluationPath position (.Var position)
    | applyLeft : EvaluationPath position function → EvaluationPath position (.Apply function argument)
    | applyRight : TotalTerm function → EvaluationPath position argument →
        EvaluationPath position (.Apply function argument)
    | force : EvaluationPath position body → EvaluationPath position (.Force body)
    | constr : EvaluationPaths position fields → EvaluationPath position (.Constr tag fields)
    | caseScrutinee : EvaluationPath position scrutinee → EvaluationPath position (.Case scrutinee alternatives)
    | letBody : TotalTerm rhs → EvaluationPath (position + 1) body →
        EvaluationPath position (.Apply (.Lam 0 body) rhs)

  inductive EvaluationPaths : Nat → List Term → Prop where
    | head : EvaluationPath position head → EvaluationPaths position (head :: tail)
    | tail : TotalTerm head → EvaluationPaths position tail → EvaluationPaths position (head :: tail)
end

mutual
  inductive CheckedPath : Nat → Term → Prop where
    | var : CheckedPath position (.Var position)
    | applyLeft : CheckedPath position function → CheckedPath position (.Apply function argument)
    | applyRight : TotalTerm function → StrictOcc.freeOf position function = true →
        CheckedPath position argument → CheckedPath position (.Apply function argument)
    | force : CheckedPath position body → CheckedPath position (.Force body)
    | constr : CheckedPaths position fields → CheckedPath position (.Constr tag fields)
    | caseScrutinee : CheckedPath position scrutinee → CheckedPath position (.Case scrutinee alternatives)
    | letBody : TotalTerm rhs → StrictOcc.freeOf position rhs = true → CheckedPath (position + 1) body →
        CheckedPath position (.Apply (.Lam 0 body) rhs)

  inductive CheckedPaths : Nat → List Term → Prop where
    | head : CheckedPath position head → CheckedPaths position (head :: tail)
    | tail : TotalTerm head → StrictOcc.freeOf position head = true →
        CheckedPaths position tail → CheckedPaths position (head :: tail)
end

mutual
  theorem EvaluationPath.not_free {position : Nat} {term : Term} (path : EvaluationPath position term) :
      StrictOcc.freeOf position term = false := by
    cases path with
    | var => simp [StrictOcc.freeOf]
    | applyLeft inner => simp [StrictOcc.freeOf, inner.not_free]
    | applyRight _ inner => simp [StrictOcc.freeOf, inner.not_free]
    | force inner => simp [StrictOcc.freeOf, inner.not_free]
    | constr fields => simp [StrictOcc.freeOf, fields.not_free]
    | caseScrutinee inner => simp [StrictOcc.freeOf, inner.not_free]
    | letBody _ inner => simp [StrictOcc.freeOf, inner.not_free]
  termination_by sizeOf term

  theorem EvaluationPaths.not_free {position : Nat} {terms : List Term} (path : EvaluationPaths position terms) :
      StrictOcc.freeOfList position terms = false := by
    cases path with
    | head inner => simp [StrictOcc.freeOfList, inner.not_free]
    | tail _ inner => simp [StrictOcc.freeOfList, inner.not_free]
  termination_by sizeOf terms
end

mutual
  theorem EvaluationPath.checked {position : Nat} {term : Term}
      (path : EvaluationPath position term) (single : StrictOcc.StrictSingleOcc position term) :
      CheckedPath position term := by
    cases path with
    | var => exact .var
    | applyLeft inner =>
      cases single with
      | apply_l single _ => exact .applyLeft (inner.checked single)
      | apply_r absent _ => rw [inner.not_free] at absent; contradiction
      | let_body _ _ => cases inner
    | applyRight total inner =>
      cases single with
      | apply_l _ absent => rw [inner.not_free] at absent; contradiction
      | apply_r absent single => exact .applyRight total absent (inner.checked single)
      | let_body _ absent => rw [inner.not_free] at absent; contradiction
    | force inner => cases single with | force single => exact .force (inner.checked single)
    | constr fields => cases single with | constr single => exact .constr (fields.checked single)
    | caseScrutinee inner =>
      cases single with | case_scrut single _ => exact .caseScrutinee (inner.checked single)
    | letBody total inner =>
      cases single with
      | apply_l impossible _ => cases impossible
      | apply_r absent _ => simp [StrictOcc.freeOf, inner.not_free] at absent
      | let_body single absent => exact .letBody total absent (inner.checked single)
  termination_by sizeOf term

  theorem EvaluationPaths.checked {position : Nat} {terms : List Term}
      (path : EvaluationPaths position terms) (single : StrictOcc.StrictSingleOccList position terms) :
      CheckedPaths position terms := by
    cases path with
    | head inner =>
      cases single with
      | head single _ => exact .head (inner.checked single)
      | tail absent _ => rw [inner.not_free] at absent; contradiction
    | tail total inner =>
      cases single with
      | head _ absent => rw [inner.not_free] at absent; contradiction
      | tail absent single => exact .tail total absent (inner.checked single)
  termination_by sizeOf terms
end

mutual
  theorem firstEvaluationUse_expandFix (identifier : VarId) (expression : Expr)
      (frontier : firstEvaluationUse identifier expression = true) :
      firstEvaluationUse identifier (expandFix expression) = true := by
    cases expression with
    | Var _ => simpa only [expandFix] using frontier
    | Lit _ | Builtin _ | Error | Lam _ _ | Fix _ _ | Delay _ => simp [firstEvaluationUse] at frontier
    | App function argument =>
      simp only [firstEvaluationUse, Bool.or_eq_true, Bool.and_eq_true] at frontier
      simp only [expandFix, firstEvaluationUse, Bool.or_eq_true, Bool.and_eq_true]
      rcases frontier with left | ⟨pure, right⟩
      · exact .inl (firstEvaluationUse_expandFix identifier function left)
      · exact .inr ⟨Purity.isPure_expandFix function pure,
          firstEvaluationUse_expandFix identifier argument right⟩
    | Force inner =>
      simpa only [expandFix, firstEvaluationUse] using firstEvaluationUse_expandFix identifier inner
        (by simpa only [firstEvaluationUse] using frontier)
    | Constr tag fields =>
      simpa only [expandFix, firstEvaluationUse] using firstEvaluationUseList_expandFix identifier fields
        (by simpa only [firstEvaluationUse] using frontier)
    | Case scrutinee _ =>
      simpa only [expandFix, firstEvaluationUse] using firstEvaluationUse_expandFix identifier scrutinee
        (by simpa only [firstEvaluationUse] using frontier)
    | Let bindings body =>
      simpa only [expandFix, firstEvaluationUse] using firstEvaluationUseBindings_expandFix identifier bindings body
        (by simpa only [firstEvaluationUse] using frontier)
  termination_by sizeOf expression

  theorem firstEvaluationUseList_expandFix (identifier : VarId) (expressions : List Expr)
      (frontier : firstEvaluationUseList identifier expressions = true) :
      firstEvaluationUseList identifier (expandFixList expressions) = true := by
    cases expressions with
    | nil => simp [firstEvaluationUseList] at frontier
    | cons head tail =>
      simp only [firstEvaluationUseList, Bool.or_eq_true, Bool.and_eq_true] at frontier
      simp only [expandFixList, firstEvaluationUseList, Bool.or_eq_true, Bool.and_eq_true]
      rcases frontier with left | ⟨pure, right⟩
      · exact .inl (firstEvaluationUse_expandFix identifier head left)
      · exact .inr ⟨Purity.isPure_expandFix head pure,
          firstEvaluationUseList_expandFix identifier tail right⟩
  termination_by sizeOf expressions

  theorem firstEvaluationUseBindings_expandFix (identifier : VarId)
      (bindings : List (VarId × Expr × Bool)) (body : Expr)
      (frontier : firstEvaluationUseBindings identifier bindings body = true) :
      firstEvaluationUseBindings identifier (expandFixBinds bindings) (expandFix body) = true := by
    match bindings with
    | [] =>
      simpa only [expandFixBinds, firstEvaluationUseBindings] using firstEvaluationUse_expandFix identifier body
        (by simpa only [firstEvaluationUseBindings] using frontier)
    | (binder, rhs, erased) :: rest =>
      simp only [firstEvaluationUseBindings, Bool.or_eq_true, Bool.and_eq_true] at frontier
      simp only [expandFixBinds, firstEvaluationUseBindings, Bool.or_eq_true, Bool.and_eq_true]
      rcases frontier with left | ⟨⟨different, pure⟩, right⟩
      · exact .inl (firstEvaluationUse_expandFix identifier rhs left)
      · exact .inr ⟨⟨different, Purity.isPure_expandFix rhs pure⟩,
          firstEvaluationUseBindings_expandFix identifier rest body right⟩
  termination_by sizeOf bindings + sizeOf body
end

mutual
  theorem firstEvaluationUse_lowerTotal (identifier : VarId) (leftEnv rightEnv : List VarId)
      (expression : Expr) (term : Term)
      (lowered : lowerTotal (leftEnv ++ identifier :: rightEnv) expression = some term)
      (frontier : firstEvaluationUse identifier expression = true)
      (unshadowed : leftEnv.findIdx? (· == identifier) = none) :
      EvaluationPath (leftEnv.length + 1) term := by
    cases expression with
    | Var other =>
      have lookup := OccBridge.envLookupT_split_beq leftEnv identifier rightEnv other
        (OccBridge.varid_beq_symm (by simpa only [firstEvaluationUse] using frontier)) unshadowed
      simp only [lowerTotal, lookup] at lowered
      cases lowered; exact .var
    | Lit _ | Builtin _ | Error | Lam _ _ | Fix _ _ | Delay _ => simp [firstEvaluationUse] at frontier
    | App function argument =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨functionTerm, functionLowered, argumentTerm, argumentLowered, equal⟩ := lowered
      cases equal
      simp only [firstEvaluationUse, Bool.or_eq_true, Bool.and_eq_true] at frontier
      rcases frontier with left | ⟨pure, right⟩
      · exact .applyLeft (firstEvaluationUse_lowerTotal identifier leftEnv rightEnv function functionTerm
          functionLowered left unshadowed)
      · exact .applyRight (lowerTotal_total function _ functionTerm pure functionLowered)
          (firstEvaluationUse_lowerTotal identifier leftEnv rightEnv argument argumentTerm
            argumentLowered right unshadowed)
    | Force inner =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨innerTerm, innerLowered, equal⟩ := lowered
      cases equal
      exact .force (firstEvaluationUse_lowerTotal identifier leftEnv rightEnv inner innerTerm
        innerLowered (by simpa only [firstEvaluationUse] using frontier) unshadowed)
    | Constr tag fields =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨terms, fieldsLowered, equal⟩ := lowered
      cases equal
      exact .constr (firstEvaluationUseList_lowerTotal identifier leftEnv rightEnv fields terms
        fieldsLowered (by simpa only [firstEvaluationUse] using frontier) unshadowed)
    | Case scrutinee alternatives =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨scrutineeTerm, scrutineeLowered, terms, _, equal⟩ := lowered
      cases equal
      exact .caseScrutinee (firstEvaluationUse_lowerTotal identifier leftEnv rightEnv scrutinee scrutineeTerm
        scrutineeLowered (by simpa only [firstEvaluationUse] using frontier) unshadowed)
    | Let bindings body =>
      exact firstEvaluationUseBindings_lowerTotal identifier leftEnv rightEnv bindings body term
        (by simpa only [lowerTotal] using lowered)
        (by simpa only [firstEvaluationUse] using frontier) unshadowed
  termination_by sizeOf expression
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega

  theorem firstEvaluationUseList_lowerTotal (identifier : VarId) (leftEnv rightEnv : List VarId)
      (expressions : List Expr) (terms : List Term)
      (lowered : lowerTotalList (leftEnv ++ identifier :: rightEnv) expressions = some terms)
      (frontier : firstEvaluationUseList identifier expressions = true)
      (unshadowed : leftEnv.findIdx? (· == identifier) = none) :
      EvaluationPaths (leftEnv.length + 1) terms := by
    cases expressions with
    | nil => simp [firstEvaluationUseList] at frontier
    | cons head tail =>
      simp only [lowerTotalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨headTerm, headLowered, tailTerms, tailLowered, equal⟩ := lowered
      cases equal
      simp only [firstEvaluationUseList, Bool.or_eq_true, Bool.and_eq_true] at frontier
      rcases frontier with left | ⟨pure, right⟩
      · exact .head (firstEvaluationUse_lowerTotal identifier leftEnv rightEnv head headTerm
          headLowered left unshadowed)
      · exact .tail (lowerTotal_total head _ headTerm pure headLowered)
          (firstEvaluationUseList_lowerTotal identifier leftEnv rightEnv tail tailTerms
            tailLowered right unshadowed)
  termination_by sizeOf expressions
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega

  theorem firstEvaluationUseBindings_lowerTotal (identifier : VarId) (leftEnv rightEnv : List VarId)
      (bindings : List (VarId × Expr × Bool)) (body : Expr) (term : Term)
      (lowered : lowerTotalLet (leftEnv ++ identifier :: rightEnv) bindings body = some term)
      (frontier : firstEvaluationUseBindings identifier bindings body = true)
      (unshadowed : leftEnv.findIdx? (· == identifier) = none) :
      EvaluationPath (leftEnv.length + 1) term := by
    match bindings with
    | [] =>
      exact firstEvaluationUse_lowerTotal identifier leftEnv rightEnv body term
        (by simpa only [lowerTotalLet] using lowered)
        (by simpa only [firstEvaluationUseBindings] using frontier) unshadowed
    | (binder, rhs, erased) :: rest =>
      simp only [lowerTotalLet, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨rhsTerm, rhsLowered, bodyTerm, bodyLowered, equal⟩ := lowered
      cases equal
      simp only [firstEvaluationUseBindings, Bool.or_eq_true, Bool.and_eq_true] at frontier
      rcases frontier with left | ⟨⟨different, pure⟩, right⟩
      · exact .applyRight .lam (firstEvaluationUse_lowerTotal identifier leftEnv rightEnv rhs rhsTerm
          rhsLowered left unshadowed)
      · apply EvaluationPath.letBody (lowerTotal_total rhs _ rhsTerm pure rhsLowered)
        have unshadowed' : (binder :: leftEnv).findIdx? (· == identifier) = none := by
          rw [List.findIdx?_eq_none_iff] at unshadowed ⊢
          intro other member
          cases member with
          | head => simpa only [bne, Bool.not_eq_true'] using different
          | tail _ member => exact unshadowed other member
        exact firstEvaluationUseBindings_lowerTotal identifier (binder :: leftEnv) rightEnv rest body bodyTerm
          (by simpa only [List.cons_append] using bodyLowered) right unshadowed'
  termination_by sizeOf bindings + sizeOf body
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega
end

theorem inlineGate_evaluationPath (identifier : VarId) (environment : List VarId)
    (bindings : List (VarId × Expr × Bool)) (body : Expr) (term : Term)
    (lowered : lowerTotalLet (identifier :: environment) (expandFixBinds bindings) (expandFix body) = some term)
    (frontier : firstEvaluationUse identifier (.Let bindings body) = true) :
    EvaluationPath 1 term :=
  firstEvaluationUseBindings_lowerTotal identifier [] environment _ _ term lowered
    (firstEvaluationUseBindings_expandFix identifier bindings body
      (by simpa only [firstEvaluationUse] using frontier)) rfl

end Moist.Verified.InlineSoundness.Frontier
