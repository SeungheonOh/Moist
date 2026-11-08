import Moist.Verified.MIR.Primitives.Shared

variable [sv : Moist.CEK.SemVariant]

/-! # Nested `let`s lower like one `let`

`let bs₁ in let bs₂ in e` and `let bs₁ ++ bs₂ in e` have the same lowering. -/

namespace Moist.Verified.MIR

open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal lowerTotalLet expandFix expandFixBinds)

omit sv in
private theorem expandFixBinds_append :
    ∀ (b₁ b₂ : List (VarId × Expr × Bool)),
      expandFixBinds (b₁ ++ b₂) = expandFixBinds b₁ ++ expandFixBinds b₂
  | [], _ => by simp [expandFixBinds]
  | (v, rhs, er) :: rest, b₂ => by
    simp only [List.cons_append, expandFixBinds, expandFixBinds_append rest b₂]

omit sv in
private theorem lowerTotalLet_append :
    ∀ (b₁ b₂ : List (VarId × Expr × Bool)) (env : List VarId) (body : Expr),
      lowerTotalLet env (b₁ ++ b₂) body = lowerTotalLet env b₁ (.Let b₂ body)
  | [], _, _, _ => by simp [lowerTotalLet, lowerTotal]
  | (x, _, _) :: rest, b₂, env, body => by
    simp only [List.cons_append, lowerTotalLet, lowerTotalLet_append rest b₂ (x :: env) body]

omit sv in
theorem lowerTotalExpr_let_flatten_body
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) =
      lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) := by
  rw [lowerTotalExpr_let env binds₁ (.Let binds₂ body), lowerTotalExpr_let env (binds₁ ++ binds₂) body]
  simp only [expandFix, expandFixBinds_append, lowerTotalLet_append]

end Moist.Verified.MIR
