import Moist.Verified.FloatOut.Semantic
import Moist.Verified.InlineSoundness.Rename

/-! # Lowering under a permuted environment

Lowering resolves names to de Bruijn indices through the environment, so two
environments whose lookups differ by an index renaming `σ` produce lowerings
that differ by `renameTerm σ` (`lowerTotalExpr_lookupShift`). The instance
used by float-out is the exchange of two adjacent distinct names
(`lowerTotalExpr_swap`). -/

namespace Moist.Verified.FloatOut

open Moist.MIR
open Moist.Plutus.Term (Term)
open Moist.Verified (renameTerm renameTermList liftRename)
open Moist.Verified.MIR (lowerTotalExprList lowerTotalExprList_nil lowerTotalExprList_cons
  lowerTotalExpr_lam lowerTotalExpr_app lowerTotalExpr_force lowerTotalExpr_delay
  lowerTotalExpr_constr_of_list lowerTotalExpr_case_of_list)
open Moist.Verified.InlineSoundness.Rename (lowerTotalExpr_var lowerTotalExpr_let_nil
  lowerTotalExpr_let_cons lowerTotalExpr_fix_lam beq_comm)

private theorem envLookupT_cons_of_beq {a x : VarId} (h : (a == x) = true) (env : List VarId) :
    envLookupT (a :: env) x = some 0 := by
  simp only [envLookupT, envLookupT.go, h, if_true]

/-- Every name resolves in `l₂` to the `σ`-image of its index in `l₁`
    (indices taken 1-based, as in the lowered term). -/
def LookupShift (σ : Nat → Nat) (l₁ l₂ : List VarId) : Prop :=
  ∀ z, (envLookupT l₂ z).map (· + 1) = (envLookupT l₁ z).map (fun i => σ (i + 1))

theorem lookupShift_cons {σ : Nat → Nat} {l₁ l₂ : List VarId} (x : VarId)
    (h : LookupShift σ l₁ l₂) : LookupShift (liftRename σ) (x :: l₁) (x :: l₂) := by
  intro z
  cases hxz : (x == z) with
  | true => rw [envLookupT_cons_of_beq hxz, envLookupT_cons_of_beq hxz]; rfl
  | false =>
    rw [envLookupT_cons_neq x z l₁ hxz, envLookupT_cons_neq x z l₂ hxz]
    have := h z
    cases h₁ : envLookupT l₁ z <;> cases h₂ : envLookupT l₂ z <;>
      simp only [h₁, h₂, Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq] at this ⊢
    show _ + 1 + 1 = σ (_ + 1) + 1
    rw [this]

theorem lookupShift_swap {a b : VarId} (hab : (a == b) = false) (Γ : List VarId) :
    LookupShift swapRename (a :: b :: Γ) (b :: a :: Γ) := by
  intro z
  cases haz : (a == z) <;> cases hbz : (b == z)
  · rw [envLookupT_cons_neq a z _ haz, envLookupT_cons_neq b z _ hbz,
      envLookupT_cons_neq b z _ hbz, envLookupT_cons_neq a z _ haz]
    cases envLookupT Γ z <;> rfl
  · rw [envLookupT_cons_neq a z _ haz, envLookupT_cons_of_beq hbz, envLookupT_cons_of_beq hbz]
    rfl
  · rw [envLookupT_cons_of_beq haz, envLookupT_cons_neq b z _ hbz, envLookupT_cons_of_beq haz]
    rfl
  · have : (a == b) = true := VarId.beq_trans _ _ _ haz (by rw [beq_comm]; exact hbz)
    rw [hab] at this; cases this

private theorem renameTerm_fixLamWrapUplc (σ : Nat → Nat) (t : Term) :
    renameTerm σ (fixLamWrapUplc t) =
      fixLamWrapUplc (renameTerm (liftRename (liftRename (liftRename σ))) t) := rfl

mutual
  theorem lowerTotalExpr_lookupShift : ∀ (e : Expr) {σ : Nat → Nat} {l₁ l₂ : List VarId},
      LookupShift σ l₁ l₂ → lowerTotalExpr l₂ e = (lowerTotalExpr l₁ e).map (renameTerm σ)
    | .Var x, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_var, lowerTotalExpr_var]
      have := h x
      cases h₁ : envLookupT l₁ x <;> cases h₂ : envLookupT l₂ x <;>
        simp only [h₁, h₂, Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at this ⊢
      rw [this]; rfl
    | .Lit (_, _), _, _, _, _ | .Builtin _, _, _, _, _ | .Error, _, _, _, _ => by
      simp [lowerTotalExpr, expandFix, lowerTotal, renameTerm]
    | .Lam x body, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_lam, lowerTotalExpr_lam,
        lowerTotalExpr_lookupShift body (lookupShift_cons x h)]
      cases lowerTotalExpr (x :: l₁) body <;> rfl
    | .Fix f body, σ, l₁, l₂, h => by
      cases body with
      | Lam x inner =>
        let s : VarId := ⟨maxUidExpr (expandFix inner) + 1, .gen, "s"⟩
        rw [lowerTotalExpr_fix_lam l₁ f x inner s (Nat.lt_succ_self _),
          lowerTotalExpr_fix_lam l₂ f x inner s (Nat.lt_succ_self _),
          lowerTotalExpr_lookupShift inner
            (lookupShift_cons x (lookupShift_cons f (lookupShift_cons s h)))]
        cases lowerTotalExpr (x :: f :: s :: l₁) inner <;> rfl
      | _ => simp [lowerTotalExpr, expandFix, lowerTotal]
    | .App f a, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_app, lowerTotalExpr_app, lowerTotalExpr_lookupShift f h,
        lowerTotalExpr_lookupShift a h]
      cases lowerTotalExpr l₁ f <;> cases lowerTotalExpr l₁ a <;> rfl
    | .Force e, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_force, lowerTotalExpr_force, lowerTotalExpr_lookupShift e h]
      cases lowerTotalExpr l₁ e <;> rfl
    | .Delay e, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_delay, lowerTotalExpr_delay, lowerTotalExpr_lookupShift e h]
      cases lowerTotalExpr l₁ e <;> rfl
    | .Constr tag args, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list,
        lowerTotalExprList_lookupShift args h]
      cases lowerTotalExprList l₁ args <;> rfl
    | .Case scrut alts, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list,
        lowerTotalExpr_lookupShift scrut h, lowerTotalExprList_lookupShift alts h]
      cases lowerTotalExpr l₁ scrut <;> cases lowerTotalExprList l₁ alts <;> rfl
    | .Let [] body, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_let_nil, lowerTotalExpr_let_nil]
      exact lowerTotalExpr_lookupShift body h
    | .Let ((x, rhs, er) :: rest) body, σ, l₁, l₂, h => by
      rw [lowerTotalExpr_let_cons, lowerTotalExpr_let_cons, lowerTotalExpr_lookupShift rhs h,
        lowerTotalExpr_lookupShift (.Let rest body) (lookupShift_cons x h)]
      cases lowerTotalExpr l₁ rhs <;> cases lowerTotalExpr (x :: l₁) (.Let rest body) <;> rfl
  termination_by e => sizeOf e

  theorem lowerTotalExprList_lookupShift : ∀ (es : List Expr) {σ : Nat → Nat}
      {l₁ l₂ : List VarId}, LookupShift σ l₁ l₂ →
      lowerTotalExprList l₂ es = (lowerTotalExprList l₁ es).map (renameTermList σ)
    | [], _, _, _, _ => by rw [lowerTotalExprList_nil, lowerTotalExprList_nil]; rfl
    | e :: es, σ, l₁, l₂, h => by
      rw [lowerTotalExprList_cons, lowerTotalExprList_cons, lowerTotalExpr_lookupShift e h,
        lowerTotalExprList_lookupShift es h]
      cases lowerTotalExpr l₁ e <;> cases lowerTotalExprList l₁ es <;> rfl
  termination_by es => sizeOf es
end

/-- Exchanging two adjacent distinct names renames the lowering by
    `swapRename`, under any prefix of binders. -/
theorem lowerTotalExpr_swap {a b : VarId} (hab : (a == b) = false) (Γ : List VarId) (e : Expr) :
    lowerTotalExpr (b :: a :: Γ) e =
      (lowerTotalExpr (a :: b :: Γ) e).map (renameTerm swapRename) :=
  lowerTotalExpr_lookupShift e (lookupShift_swap hab Γ)

end Moist.Verified.FloatOut
