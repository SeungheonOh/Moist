import Moist.Verified.Semantics
import Moist.MIR.LowerTotal
import Moist.Verified.ValueEq

/-! # Let Flattening ≡ Let Nesting

This module proves that flat multi-binding `Let` and nested single-binding
`Let` are semantically equivalent in both directions:

    `Let (binds₁ ++ binds₂) body  ≋  Let binds₁ (Let binds₂ body)`

The proof is purely syntactic: both forms lower to the **exact same UPLC
term** via `lowerTotalLet`, so behavioral equivalence follows by reflexivity
of `ValueEq` — no bisimulation or step-counting needed.
-/

namespace Moist.Verified.LetFlatten

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.Verified.Semantics

/-! ## Core lowering lemma -/

/-- Splitting a `lowerTotalLet` binding list at any point is the same as
    nesting a `Let` at that point. This is the key observation: the
    recursive structure of `lowerTotalLet` processes one binding at a time,
    extending the environment, so it doesn't matter whether the bindings
    are presented as one flat list or split into two with a `Let` boundary.

    Proof by induction on `binds₁`:
    - Base: `lowerTotalLet env [] (Let binds₂ body) = lowerTotal env (Let binds₂ body)
            = lowerTotalLet env binds₂ body`.
    - Step: both sides unfold to `do rhs' ← ..; rest' ← ..; some (Apply (Lam 0 rest') rhs')`,
            and the IH equates the `rest'` subterms. -/
theorem lowerTotalLet_append (env : List VarId)
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalLet env (binds₁ ++ binds₂) body =
    lowerTotalLet env binds₁ (.Let binds₂ body) := by
  induction binds₁ generalizing env with
  | nil =>
    simp only [List.nil_append, lowerTotalLet.eq_1, lowerTotal.eq_11]
  | cons b rest ih =>
    obtain ⟨x, rhs, er⟩ := b
    simp only [List.cons_append, lowerTotalLet.eq_2, ih (x :: env)]

/-- Wrapper at the `lowerTotal` level: flattening or nesting `Let` bindings
    produces the same UPLC term for every MIR environment. -/
theorem lowerTotal_let_flatten (env : List VarId)
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotal env (.Let (binds₁ ++ binds₂) body) =
    lowerTotal env (.Let binds₁ (.Let binds₂ body)) := by
  simp only [lowerTotal.eq_11, lowerTotalLet_append]

/-! ## BehEq from identical lowering -/

/-- If two MIR expressions lower to the same UPLC term in every environment,
    they are behaviorally equivalent. Since the lowered term is literally
    identical, error/halt agreement is `Iff.rfl` and value agreement follows
    from `valueEq_refl` + `reaches_unique`. -/
theorem behEq_of_lowerTotalExpr_eq (m₁ m₂ : Expr)
    (h : ∀ env, lowerTotalExpr env m₁ = lowerTotalExpr env m₂) : m₁ ≋ m₂ := by
  unfold BehEq; intro env
  rw [h env]
  cases lowerTotalExpr env m₂ with
  | none => trivial
  | some t =>
    intro _ _
    refine ⟨Iff.rfl, Iff.rfl, ?_⟩
    intro k v₁ v₂ h₁ h₂
    exact reaches_unique h₁ h₂ ▸ valueEq_refl k v₁

/-! ## Main theorems -/

/-- Flat multi-binding `Let` is behaviorally equivalent to nested `Let`. -/
private theorem expandFixBinds_append (b1 b2 : List (VarId × Expr × Bool)) :
    expandFixBinds (b1 ++ b2) = expandFixBinds b1 ++ expandFixBinds b2 := by
  induction b1 with
  | nil => simp [expandFixBinds]
  | cons h t ih =>
    obtain ⟨v, rhs, er⟩ := h
    simp only [List.cons_append, expandFixBinds, ih, List.cons_append]

private theorem lowerTotalExpr_let_flatten (env : List VarId)
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) =
    lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) := by
  simp only [lowerTotalExpr, expandFix, expandFixBinds_append]
  exact lowerTotal_let_flatten env (expandFixBinds binds₁) (expandFixBinds binds₂) (expandFix body)

theorem let_flatten_behEq (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    .Let (binds₁ ++ binds₂) body ≋ .Let binds₁ (.Let binds₂ body) :=
  behEq_of_lowerTotalExpr_eq _ _ (fun env => lowerTotalExpr_let_flatten env binds₁ binds₂ body)

/-- Flat → nested refinement. -/
theorem let_flatten_refines (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    Refines (.Let (binds₁ ++ binds₂) body) (.Let binds₁ (.Let binds₂ body)) :=
  ⟨fun env h => by rw [← lowerTotalExpr_let_flatten]; exact h,
   let_flatten_behEq binds₁ binds₂ body⟩

/-- Nested → flat refinement (inverse direction). -/
theorem let_unflatten_refines (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    Refines (.Let binds₁ (.Let binds₂ body)) (.Let (binds₁ ++ binds₂) body) :=
  ⟨fun env h => by rw [lowerTotalExpr_let_flatten]; exact h,
   behEq_of_lowerTotalExpr_eq _ _ (fun env => (lowerTotalExpr_let_flatten env binds₁ binds₂ body).symm)⟩

end Moist.Verified.LetFlatten
