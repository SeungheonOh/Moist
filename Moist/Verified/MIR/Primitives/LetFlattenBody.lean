import Moist.Verified.MIR.Primitives.Shared

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFixBinds)
open Moist.Verified
  (closedAt closedAtList renameTerm shiftRename liftRename liftRename_shiftRename renameTermList
   renameTermList_getElem renameTermList_length shiftRename_ge shiftRename_lt)
open Moist.Verified.Equivalence
  (steps_error steps_halt constToTagAndFields_fields_vcon listRel_reverse ListRel ObsEq
   ObsRefinesK steps Reaches obsRefinesK_mono obsRefinesK_zero_ret listRel_mono)
open Moist.Verified.Contextual
  (closedAtList_append Context fill ObsRefines CtxEq CtxRefines ctxEq_refl ctxRefines_refl
   ctxRefines_trans ctxEq_lam ctxEq_app ctxRefines_lam ctxRefines_app)
open Moist.Verified.FundamentalRefines
  (envRefinesK_to_renameEnvRef_shift Is0Preserving RenameEnvRef renameRefines_shift1 ftlr
   renameRefines renameRefinesR renameRefinesR_shift1 is0preserving_id is0preserving_shiftRename
   RenameEnvRefR envRefinesK_to_renameEnvRefR_shift renameEnvRefR_mono)
open Moist.Verified.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK valueRefinesK_mono evalBuiltin_compat_refines
   obsRefinesK_error stackRefK_mono listRel_valueRefinesK_mono applyArgFrames_stackRefK
   listRel_refl_vcon_refines)

/-! ## Section 4. Let-flatten primitive (definitional) -/

/-- `expandFixBinds` distributes over list append. -/
private theorem expandFixBinds_append :
    ∀ (b₁ b₂ : List (VarId × Expr × Bool)),
      expandFixBinds (b₁ ++ b₂) =
        expandFixBinds b₁ ++ expandFixBinds b₂
  | [], _ => by simp [expandFixBinds]
  | (v, rhs, er) :: rest, b₂ => by
    simp only [List.cons_append, expandFixBinds, expandFixBinds_append rest b₂]

/-- `lowerTotalLet` of an appended bind list equals running the prefix
    against an inner `.Let`-wrapped body. -/
private theorem lowerTotalLet_append_eq :
    ∀ (b₁ b₂ : List (VarId × Expr × Bool)) (env : List VarId) (body : Expr),
      lowerTotalLet env (b₁ ++ b₂) body = lowerTotalLet env b₁ (.Let b₂ body)
  | [], _, _, _ => by simp [lowerTotalLet, lowerTotal]
  | (x, _, _) :: rest, b₂, env, body => by
    simp only [List.cons_append, lowerTotalLet]
    rw [lowerTotalLet_append_eq rest b₂ (x :: env) body]

/-- **Let-flatten (body side)**: nested let in body equals appended bindings. -/
theorem lowerTotalExpr_let_flatten_body
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) (env : List VarId) :
    lowerTotalExpr env (.Let binds₁ (.Let binds₂ body)) =
      lowerTotalExpr env (.Let (binds₁ ++ binds₂) body) := by
  rw [lowerTotalExpr_let env binds₁ (.Let binds₂ body),
      lowerTotalExpr_let env (binds₁ ++ binds₂) body]
  simp only [expandFix, expandFixBinds_append,
    lowerTotalLet_append_eq (expandFixBinds binds₁) (expandFixBinds binds₂) env (expandFix body)]

theorem mirCtxRefines_let_flatten_body_fwd
    (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr) :
    MIRCtxRefines (.Let binds₁ (.Let binds₂ body)) (.Let (binds₁ ++ binds₂) body) :=
  mirCtxRefines_of_lowerEq (lowerTotalExpr_let_flatten_body binds₁ binds₂ body)

end Moist.Verified.MIR
