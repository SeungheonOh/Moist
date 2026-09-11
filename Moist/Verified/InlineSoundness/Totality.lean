import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.Purity

namespace Moist.Verified.InlineSoundness.Totality

open Moist.CEK Moist.Plutus.Term
open Moist.Verified Moist.Verified.Semantics
open Moist.MIR (Expr VarId lowerTotal lowerTotalList lowerTotalLet isPure isPureList isPureBinds isForceable)

mutual
  inductive TotalTerm : Term → Prop where
    | var : 1 ≤ index → TotalTerm (.Var index)
    | constant : TotalTerm (.Constant constant)
    | builtin : TotalTerm (.Builtin builtin)
    | lam : TotalTerm (.Lam name body)
    | delay : TotalTerm (.Delay body)
    | forceDelay : TotalTerm body → TotalTerm (.Force (.Delay body))
    | forceBuiltin : expectedArgs builtin = .more .argQ remaining →
        TotalTerm (.Force (.Builtin builtin))
    | forceForceBuiltin : expectedArgs builtin = .more .argQ (.more .argQ remaining) →
        TotalTerm (.Force (.Force (.Builtin builtin)))
    | constr : TotalTerms fields → TotalTerm (.Constr tag fields)
    | letBody : TotalTerm rhs → TotalTerm body → TotalTerm (.Apply (.Lam name body) rhs)

  inductive TotalTerms : List Term → Prop where
    | nil : TotalTerms []
    | cons : TotalTerm head → TotalTerms tail → TotalTerms (head :: tail)
end

mutual
  theorem TotalTerm.rename {term : Term} (total : TotalTerm term) (rename : Nat → Nat)
      (positive : ∀ index, 1 ≤ index → 1 ≤ rename index) :
      TotalTerm (renameTerm rename term) := by
    cases total with
    | var bound => exact .var (positive _ bound)
    | constant => exact .constant
    | builtin => exact .builtin
    | lam => exact .lam
    | delay => exact .delay
    | forceDelay inner => exact .forceDelay (inner.rename rename positive)
    | forceBuiltin signature => exact .forceBuiltin signature
    | forceForceBuiltin signature => exact .forceForceBuiltin signature
    | constr fields => exact .constr (fields.rename rename positive)
    | letBody rhs body =>
      apply TotalTerm.letBody (rhs.rename rename positive)
      apply body.rename (liftRename rename)
      intro index bound
      cases index with
      | zero => omega
      | succ index => cases index <;> simp [liftRename]
  termination_by sizeOf term

  theorem TotalTerms.rename {terms : List Term} (total : TotalTerms terms) (rename : Nat → Nat)
      (positive : ∀ index, 1 ≤ index → 1 ≤ rename index) :
      TotalTerms (renameTermList rename terms) := by
    cases total with
    | nil => exact .nil
    | cons head tail => exact .cons (head.rename rename positive) (tail.rename rename positive)
  termination_by sizeOf terms
end

mutual
  theorem TotalTerm.halts {term : Term} (total : TotalTerm term)
      (depth : Nat) (environment : CekEnv) (closed : closedAt depth term = true)
      (sized : WellSizedEnv depth environment) :
      ∃ value, Reaches (.compute [] environment term) (.halt value) := by
    cases total with
    | var bound =>
      simp only [closedAt, decide_eq_true_eq] at closed
      obtain ⟨value, lookup⟩ := sized _ bound closed
      exact ⟨value, 2, by simp [steps, step, lookup]⟩
    | constant => exact ⟨_, 2, rfl⟩
    | builtin => exact ⟨_, 2, rfl⟩
    | lam => exact ⟨_, 2, rfl⟩
    | delay => exact ⟨_, 2, rfl⟩
    | forceDelay inner =>
      obtain ⟨value, fuel, returns⟩ := inner.halts depth environment (by simpa [closedAt] using closed) sized
      exact ⟨value, 3 + fuel, by rw [steps_trans]; exact returns⟩
    | forceBuiltin signature =>
      rename_i builtin remaining
      refine ⟨.VBuiltin builtin [] remaining, 4, ?_⟩
      simp [steps, step, signature, ExpectedArgs.head, ExpectedArgs.tail]
    | forceForceBuiltin signature =>
      rename_i builtin remaining
      refine ⟨.VBuiltin builtin [] remaining, 6, ?_⟩
      simp [steps, step, signature, ExpectedArgs.head, ExpectedArgs.tail]
    | constr fields =>
      exact Purity.constr_halts_of_all_halt environment _ _
        (fields.halts depth environment (by simpa [closedAt] using closed) sized)
    | letBody rhs body =>
      simp only [closedAt, Bool.and_eq_true] at closed
      obtain ⟨value, returns⟩ := rhs.halts depth environment closed.2 sized
      obtain ⟨result, finishes⟩ := body.halts (depth + 1) (environment.extend value)
        closed.1 (wellSizedEnv_extend sized value)
      exact ⟨result, StepLift.beta_apply_from_inner environment _ _ _ value _ returns finishes⟩
  termination_by sizeOf term

  theorem TotalTerms.halts {terms : List Term} (total : TotalTerms terms)
      (depth : Nat) (environment : CekEnv) (closed : closedAtList depth terms = true)
      (sized : WellSizedEnv depth environment) :
      ∀ term, term ∈ terms → ∃ value, Reaches (.compute [] environment term) (.halt value) := by
    cases total with
    | nil => intro term member; cases member
    | cons head tail =>
      simp only [closedAtList, Bool.and_eq_true] at closed
      intro term member
      cases member with
      | head => exact head.halts depth environment closed.1 sized
      | tail _ member => exact tail.halts depth environment closed.2 sized term member
  termination_by sizeOf terms
  decreasing_by all_goals simp_all <;> omega
end

theorem TotalTerm.subst_halts {term rhs : Term} (total : TotalTerm term)
    {position depth : Nat} (positive : 1 ≤ position) (bound : position ≤ depth + 1)
    (absent : StrictOcc.freeOf position term = true)
    (closed : closedAt (depth + 1) term = true) (rhsClosed : closedAt depth rhs = true)
    (environment : CekEnv) (sized : WellSizedEnv depth environment) :
    ∃ value, Reaches (.compute [] environment (substTerm position rhs term)) (.halt value) := by
  have substitutedClosed := BetaValueRefines.closedAt_substTerm position rhs term depth
    positive bound rhsClosed closed
  rw [StrictOcc.freeOf_substTerm_eq_renameTerm positive absent] at substitutedClosed ⊢
  exact (total.rename _ (fun _ bound => StrictOcc.unshiftRename_ge1 positive bound)).halts
    depth environment substitutedClosed sized

private theorem force_builtin_total (builtin : BuiltinFun)
    (pure : isPure (.Force (.Builtin builtin)) = true) :
    TotalTerm (.Force (.Builtin builtin)) := by
  cases builtin <;>
    first | exact .forceBuiltin rfl |
      (simp only [isPure, isForceable, expectedArgs, ExpectedArgs.head, Bool.and_true] at pure
       exact absurd pure (by decide))

private theorem force_force_builtin_total (builtin : BuiltinFun)
    (pure : isPure (.Force (.Force (.Builtin builtin))) = true) :
    TotalTerm (.Force (.Force (.Builtin builtin))) := by
  cases builtin <;>
    first | exact .forceForceBuiltin rfl |
      (simp only [isPure, isForceable, expectedArgs, ExpectedArgs.head, Bool.and_true] at pure
       exact absurd pure (by decide))

mutual
  theorem lowerTotal_total (expression : Expr) (environment : List VarId) (term : Term)
      (pure : isPure expression = true) (lowered : lowerTotal environment expression = some term) :
      TotalTerm term := by
    match expression with
    | .Var binder =>
      simp only [lowerTotal] at lowered
      split at lowered
      · cases lowered; exact .var (by omega)
      · contradiction
    | .Lit constant => cases constant; simp only [lowerTotal] at lowered; cases lowered; exact .constant
    | .Builtin builtin => simp only [lowerTotal] at lowered; cases lowered; exact .builtin
    | .Lam binder body =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨inner, _, equal⟩ := lowered
      cases equal; exact .lam
    | .Delay body =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨inner, _, equal⟩ := lowered
      cases equal; exact .delay
    | .Force (.Delay body) =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨inner, ⟨bodyTerm, bodyLowered, innerEqual⟩, termEqual⟩ := lowered
      cases innerEqual; cases termEqual
      exact .forceDelay (lowerTotal_total body environment bodyTerm (by simpa [isPure] using pure) bodyLowered)
    | .Force (.Builtin builtin) =>
      simp [lowerTotal] at lowered; subst term
      exact force_builtin_total builtin pure
    | .Force (.Force (.Builtin builtin)) =>
      simp [lowerTotal] at lowered; subst term
      exact force_force_builtin_total builtin pure
    | .Force (.Var _) | .Force (.Lit _) | .Force (.Lam _ _) | .Force (.Fix _ _)
    | .Force (.App _ _) | .Force (.Constr _ _) | .Force (.Case _ _)
    | .Force (.Let _ _) | .Force .Error
    | .Force (.Force (.Var _)) | .Force (.Force (.Lit _)) | .Force (.Force (.Lam _ _))
    | .Force (.Force (.Fix _ _)) | .Force (.Force (.App _ _)) | .Force (.Force (.Constr _ _))
    | .Force (.Force (.Case _ _)) | .Force (.Force (.Let _ _)) | .Force (.Force .Error)
    | .Force (.Force (.Delay _)) | .Force (.Force (.Force _)) => simp [isPure, isForceable] at pure
    | .Constr tag fields =>
      simp only [lowerTotal, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨terms, fieldsLowered, equal⟩ := lowered
      cases equal
      exact .constr (lowerTotalList_total fields environment terms (by simpa [isPure] using pure) fieldsLowered)
    | .Let bindings body =>
      simp only [isPure, Bool.and_eq_true] at pure
      exact lowerTotalLet_total bindings body environment term pure.1 pure.2
        (by simpa only [lowerTotal] using lowered)
    | .App _ _ | .Case _ _ | .Fix _ _ | .Error => simp [isPure] at pure
  termination_by sizeOf expression
  decreasing_by all_goals simp_all <;> omega

  theorem lowerTotalList_total (expressions : List Expr) (environment : List VarId) (terms : List Term)
      (pure : isPureList expressions = true) (lowered : lowerTotalList environment expressions = some terms) :
      TotalTerms terms := by
    cases expressions with
    | nil => simp only [lowerTotalList] at lowered; cases lowered; exact .nil
    | cons head tail =>
      simp only [isPureList, Bool.and_eq_true] at pure
      simp only [lowerTotalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨headTerm, headLowered, tailTerms, tailLowered, equal⟩ := lowered
      cases equal
      exact .cons (lowerTotal_total head environment headTerm pure.1 headLowered)
        (lowerTotalList_total tail environment tailTerms pure.2 tailLowered)
  termination_by sizeOf expressions
  decreasing_by all_goals simp_all <;> omega

  theorem lowerTotalLet_total (bindings : List (VarId × Expr × Bool)) (body : Expr)
      (environment : List VarId) (term : Term) (bindingsPure : isPureBinds bindings = true)
      (bodyPure : isPure body = true) (lowered : lowerTotalLet environment bindings body = some term) :
      TotalTerm term := by
    match bindings with
    | [] => exact lowerTotal_total body environment term bodyPure (by simpa only [lowerTotalLet] using lowered)
    | (binder, rhs, erased) :: rest =>
      simp only [isPureBinds, Bool.and_eq_true] at bindingsPure
      simp only [lowerTotalLet, Option.bind_eq_bind, Option.bind_eq_some_iff] at lowered
      obtain ⟨rhsTerm, rhsLowered, bodyTerm, bodyLowered, equal⟩ := lowered
      cases equal
      exact .letBody (lowerTotal_total rhs environment rhsTerm bindingsPure.1 rhsLowered)
        (lowerTotalLet_total rest body (binder :: environment) bodyTerm bindingsPure.2 bodyPure bodyLowered)
  termination_by sizeOf bindings + sizeOf body
  decreasing_by all_goals simp_all <;> omega
end

end Moist.Verified.InlineSoundness.Totality
