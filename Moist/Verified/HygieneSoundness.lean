import Moist.Verified.MIR.AlphaEq
import Moist.Verified.InlineSoundness

namespace Moist.Verified.MIR

open Moist.MIR Moist.Plutus.Term

theorem lowerTotalExpr_fix_lam_shift (environment : List VarId) (recursive parameter : VarId) (body : Expr) :
    lowerTotalExpr environment (.Fix recursive (.Lam parameter body)) =
      (lowerTotalExpr (parameter :: recursive :: environment) body).map
        (fun term => fixLamWrapUplc (renameTerm (shiftRename 3) term)) := by
  rw [lowerTotalExpr_fix_lam_canonical]
  let fresh : VarId := ⟨maxUidExpr (expandFix body) + 1, .gen, "s"⟩
  have unused := maxUidExpr_fresh (expandFix body) fresh (Nat.lt_succ_self _)
  cases lowered : lowerTotal (parameter :: recursive :: environment) (expandFix body) with
  | none =>
    have extended := lowerTotal_prepend_unused_none_gen [parameter, recursive] environment fresh
      (expandFix body) (.inl unused) lowered
    simp only [List.cons_append, List.nil_append] at extended
    simp [fresh] at extended
    simp only [lowerTotalExpr, lowered, extended, Option.map_none]
  | some term =>
    have extended := lowerTotal_prepend_unused_gen [parameter, recursive] environment fresh
      (expandFix body) (.inl unused) term lowered
    simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at extended
    dsimp only [fresh] at extended
    simp only [lowerTotalExpr, lowered, extended, Option.map_some]

theorem lowerTotalExpr_let_cons_eq (environment : List VarId) (binder : VarId) (rhs : Expr)
    (erased : Bool) (bindings : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr environment (.Let ((binder, rhs, erased) :: bindings) body) = (do
      let rhsTerm ← lowerTotalExpr environment rhs
      let bodyTerm ← lowerTotalExpr (binder :: environment) (.Let bindings body)
      pure (Term.Apply (.Lam 0 bodyTerm) rhsTerm)) := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds, lowerTotal, lowerTotalLet, Option.bind_eq_bind]
  rfl

namespace AlphaEq

mutual
  theorem lowerTotalExpr_eq {leftEnv rightEnv : List VarId} {left right : Expr}
      (related : AlphaEq leftEnv rightEnv left right) :
      lowerTotalExpr leftEnv left = lowerTotalExpr rightEnv right := by
    cases related with
    | var lookups => simp only [lowerTotalExpr, expandFix, lowerTotal, lookups]
    | lit => rename_i literal; cases literal; simp [lowerTotalExpr, expandFix, lowerTotal]
    | builtin => simp [lowerTotalExpr, expandFix, lowerTotal]
    | error => simp [lowerTotalExpr, expandFix, lowerTotal]
    | lam body => rw [lowerTotalExpr_lam, lowerTotalExpr_lam, lowerTotalExpr_eq body]
    | app function argument =>
      rw [lowerTotalExpr_app, lowerTotalExpr_app, lowerTotalExpr_eq function, lowerTotalExpr_eq argument]
    | force body => rw [lowerTotalExpr_force, lowerTotalExpr_force, lowerTotalExpr_eq body]
    | delay body => rw [lowerTotalExpr_delay, lowerTotalExpr_delay, lowerTotalExpr_eq body]
    | constr fields =>
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list, lowerTotalExprList_eq fields]
    | case_ scrutinee alternatives =>
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        lowerTotalExpr_eq scrutinee, lowerTotalExprList_eq alternatives]
    | let_ bindings => exact lowerTotalExprLet_eq bindings
    | fix body =>
      cases body with
      | lam inner => rw [lowerTotalExpr_fix_lam_shift, lowerTotalExpr_fix_lam_shift, lowerTotalExpr_eq inner]
      | _ => simp [lowerTotalExpr, expandFix, lowerTotal]
  termination_by sizeOf left

  theorem lowerTotalExprList_eq {leftEnv rightEnv : List VarId} {left right : List Expr}
      (related : AlphaEqList leftEnv rightEnv left right) :
      lowerTotalExprList leftEnv left = lowerTotalExprList rightEnv right := by
    cases related with
    | nil => simp [lowerTotalExprList_nil]
    | cons head tail =>
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons, lowerTotalExpr_eq head, lowerTotalExprList_eq tail]
  termination_by sizeOf left

  theorem lowerTotalExprLet_eq {leftEnv rightEnv : List VarId}
      {left right : List (VarId × Expr × Bool)} {leftBody rightBody : Expr}
      (related : AlphaEqBinds leftEnv rightEnv left right leftBody rightBody) :
      lowerTotalExpr leftEnv (.Let left leftBody) = lowerTotalExpr rightEnv (.Let right rightBody) := by
    cases related with
    | nil body => rw [lowerTotalExpr_let_nil_eq, lowerTotalExpr_let_nil_eq]; exact lowerTotalExpr_eq body
    | cons rhs rest =>
      rw [lowerTotalExpr_let_cons_eq, lowerTotalExpr_let_cons_eq]
      rw [lowerTotalExpr_eq rhs, lowerTotalExprLet_eq rest]
  termination_by sizeOf left + sizeOf leftBody
end

end AlphaEq

namespace Hygiene

open AlphaEq

def RangeBelow (bound next : Nat) (substitutions : List (VarId × VarId)) : Prop :=
  ∀ identifier, identifier.uid < bound → (substLookup substitutions identifier).uid < next

def LookupMatches (bound : Nat) (substitutions : List (VarId × VarId))
    (source target : List VarId) : Prop :=
  ∀ identifier, identifier.uid < bound →
    envLookupT source identifier = envLookupT target (substLookup substitutions identifier)

theorem RangeBelow.mono {bound first second : Nat} {substitutions : List (VarId × VarId)}
    (range : RangeBelow bound first substitutions) (increases : first ≤ second) :
    RangeBelow bound second substitutions := by
  intro identifier bounded
  exact Nat.lt_of_lt_of_le (range identifier bounded) increases

theorem RangeBelow.extend {bound next : Nat} {substitutions : List (VarId × VarId)}
    (range : RangeBelow bound next substitutions) (old fresh : VarId) (freshUid : fresh.uid = next) :
    RangeBelow bound (next + 1) ((old, fresh) :: substitutions) := by
  intro identifier bounded
  simp only [substLookup]
  split
  · omega
  · have previous := range identifier bounded; omega

theorem LookupMatches.extend {bound next : Nat} {substitutions : List (VarId × VarId)}
    {source target : List VarId} (lookups : LookupMatches bound substitutions source target)
    (range : RangeBelow bound next substitutions) (old fresh : VarId) (freshUid : fresh.uid = next) :
    LookupMatches bound ((old, fresh) :: substitutions) (old :: source) (fresh :: target) := by
  intro identifier bounded
  simp only [substLookup]
  split
  · rename_i same
    rw [envLookupT_cons_self]
    simp only [envLookupT, envLookupT.go, same, if_pos]
  · rename_i different
    have different' : (old == identifier) = false := by
      cases equal : old == identifier <;> simp_all
    have freshDifferent : (fresh == substLookup substitutions identifier) = false := by
      rw [VarId.beq_false_iff]
      exact .inr (by have smaller := range identifier bounded; omega)
    rw [envLookupT_cons_neq _ _ _ different', envLookupT_cons_neq _ _ _ freshDifferent, lookups identifier bounded]

mutual
  theorem freshenBinders_correct (bound : Nat) (expression : Expr) (substitutions : List (VarId × VarId))
      (state : FreshState) (source target : List VarId) (bounded : maxUidExpr expression < bound)
      (range : RangeBelow bound state.next substitutions) (lookups : LookupMatches bound substitutions source target) :
      state.next ≤ (freshenBinders substitutions expression state).2.next ∧
        AlphaEq source target expression (freshenBinders substitutions expression state).1 := by
    cases expression with
    | Var identifier => exact ⟨Nat.le_refl _, .var (lookups identifier (by simpa [maxUidExpr] using bounded))⟩
    | Lit literal => exact ⟨Nat.le_refl _, .lit⟩
    | Builtin builtin => exact ⟨Nat.le_refl _, .builtin⟩
    | Error => exact ⟨Nat.le_refl _, .error⟩
    | Lam binder body | Fix binder body =>
      let fresh : VarId := ⟨state.next, .gen, binder.hint⟩
      have bodyBounded : maxUidExpr body < bound := by simp only [maxUidExpr] at bounded; omega
      have result := freshenBinders_correct bound body ((binder, fresh) :: substitutions) ⟨state.next + 1⟩
        (binder :: source) (fresh :: target) bodyBounded (range.extend binder fresh rfl)
        (lookups.extend range binder fresh rfl)
      first
      | exact ⟨Nat.le_trans (Nat.le_succ _) result.1, .lam result.2⟩
      | exact ⟨Nat.le_trans (Nat.le_succ _) result.1, .fix result.2⟩
    | App function argument =>
      have functionBounded : maxUidExpr function < bound := by simp only [maxUidExpr] at bounded; omega
      have argumentBounded : maxUidExpr argument < bound := by simp only [maxUidExpr] at bounded; omega
      have first := freshenBinders_correct bound function substitutions state source target functionBounded range lookups
      have second := freshenBinders_correct bound argument substitutions (freshenBinders substitutions function state).2
        source target argumentBounded (range.mono first.1) lookups
      exact ⟨Nat.le_trans first.1 second.1, .app first.2 second.2⟩
    | Force body =>
      have result := freshenBinders_correct bound body substitutions state source target
        (by simpa [maxUidExpr] using bounded) range lookups
      exact ⟨result.1, .force result.2⟩
    | Delay body =>
      have result := freshenBinders_correct bound body substitutions state source target
        (by simpa [maxUidExpr] using bounded) range lookups
      exact ⟨result.1, .delay result.2⟩
    | Constr tag fields =>
      have result := freshenList_correct bound fields substitutions state source target
        (by simpa [maxUidExpr] using bounded) range lookups
      exact ⟨result.1, .constr result.2⟩
    | Case scrutinee alternatives =>
      have scrutineeBounded : maxUidExpr scrutinee < bound := by simp only [maxUidExpr] at bounded; omega
      have alternativesBounded : maxUidExprList alternatives < bound := by simp only [maxUidExpr] at bounded; omega
      have first := freshenBinders_correct bound scrutinee substitutions state source target scrutineeBounded range lookups
      have second := freshenList_correct bound alternatives substitutions (freshenBinders substitutions scrutinee state).2
        source target alternativesBounded (range.mono first.1) lookups
      exact ⟨Nat.le_trans first.1 second.1, .case_ first.2 second.2⟩
    | Let bindings body =>
      have bindingsBounded : maxUidExprBinds bindings < bound := by simp only [maxUidExpr] at bounded; omega
      have bodyBounded : maxUidExpr body < bound := by simp only [maxUidExpr] at bounded; omega
      obtain ⟨increases, finalSource, finalTarget, finalRange, finalLookups, related⟩ :=
        freshenBindings_correct bound bindings substitutions state source target bindingsBounded range lookups
      have bodyResult := freshenBinders_correct bound body (freshenBindings substitutions bindings state).1.2
        (freshenBindings substitutions bindings state).2 finalSource finalTarget bodyBounded finalRange finalLookups
      exact ⟨Nat.le_trans increases bodyResult.1, .let_ (related _ _ bodyResult.2)⟩
  termination_by sizeOf expression

  theorem freshenList_correct (bound : Nat) (expressions : List Expr) (substitutions : List (VarId × VarId))
      (state : FreshState) (source target : List VarId) (bounded : maxUidExprList expressions < bound)
      (range : RangeBelow bound state.next substitutions) (lookups : LookupMatches bound substitutions source target) :
      state.next ≤ (freshenList substitutions expressions state).2.next ∧
        AlphaEqList source target expressions (freshenList substitutions expressions state).1 := by
    cases expressions with
    | nil => exact ⟨Nat.le_refl _, .nil⟩
    | cons expression expressions =>
      have headBounded : maxUidExpr expression < bound := by simp only [maxUidExprList] at bounded; omega
      have tailBounded : maxUidExprList expressions < bound := by simp only [maxUidExprList] at bounded; omega
      have first := freshenBinders_correct bound expression substitutions state source target headBounded range lookups
      have second := freshenList_correct bound expressions substitutions (freshenBinders substitutions expression state).2
        source target tailBounded (range.mono first.1) lookups
      exact ⟨Nat.le_trans first.1 second.1, .cons first.2 second.2⟩
  termination_by sizeOf expressions

  theorem freshenBindings_correct (bound : Nat) (bindings : List (VarId × Expr × Bool))
      (substitutions : List (VarId × VarId)) (state : FreshState) (source target : List VarId)
      (bounded : maxUidExprBinds bindings < bound) (range : RangeBelow bound state.next substitutions)
      (lookups : LookupMatches bound substitutions source target) :
      state.next ≤ (freshenBindings substitutions bindings state).2.next ∧
        ∃ finalSource finalTarget,
          RangeBelow bound (freshenBindings substitutions bindings state).2.next (freshenBindings substitutions bindings state).1.2 ∧
          LookupMatches bound (freshenBindings substitutions bindings state).1.2 finalSource finalTarget ∧
          ∀ sourceBody targetBody, AlphaEq finalSource finalTarget sourceBody targetBody →
            AlphaEqBinds source target bindings (freshenBindings substitutions bindings state).1.1 sourceBody targetBody := by
    match bindings with
    | [] => exact ⟨Nat.le_refl _, source, target, range, lookups, fun _ _ related => .nil related⟩
    | (binder, rhs, erased) :: bindings =>
      have rhsBounded : maxUidExpr rhs < bound := by simp only [maxUidExprBinds] at bounded; omega
      have tailBounded : maxUidExprBinds bindings < bound := by simp only [maxUidExprBinds] at bounded; omega
      have first := freshenBinders_correct bound rhs substitutions state source target rhsBounded range lookups
      let middle := (freshenBinders substitutions rhs state).2
      let fresh : VarId := ⟨middle.next, .gen, binder.hint⟩
      obtain ⟨increases, finalSource, finalTarget, finalRange, finalLookups, related⟩ :=
        freshenBindings_correct bound bindings ((binder, fresh) :: substitutions) ⟨middle.next + 1⟩
          (binder :: source) (fresh :: target) tailBounded ((range.mono first.1).extend binder fresh rfl)
          (lookups.extend (range.mono first.1) binder fresh rfl)
      exact ⟨Nat.le_trans first.1 (Nat.le_trans (Nat.le_succ _) increases), finalSource, finalTarget,
        finalRange, finalLookups, fun _ _ bodyRelated => .cons first.2 (related _ _ bodyRelated)⟩
  termination_by sizeOf bindings
  decreasing_by all_goals subst_vars <;> simp_wf <;> omega
end

theorem uniqueOptimizationBinders_lower (environment : List VarId) (expression : Expr) :
    lowerTotalExpr environment (uniqueOptimizationBinders expression) = lowerTotalExpr environment expression := by
  unfold uniqueOptimizationBinders
  split
  · rfl
  · have result := freshenBinders_correct (maxUidExpr expression + 1) expression [] ⟨maxUidExpr expression + 1⟩
      environment environment (Nat.lt_succ_self _) (fun _ smaller => smaller) (fun _ _ => rfl)
    exact (AlphaEq.lowerTotalExpr_eq result.2).symm

theorem uniqueOptimizationBinders_refines (expression : Expr) :
    MIRCtxRefines expression (uniqueOptimizationBinders expression) :=
  mirCtxRefines_of_lowerEq (fun environment => (uniqueOptimizationBinders_lower environment expression).symm)

end Hygiene
end Moist.Verified.MIR
