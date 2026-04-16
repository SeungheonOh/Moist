import Moist.Verified.MIR.Primitives.Shared

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFixBinds envLookupT_cons_self)
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

/-! ## Section 2. Lowering shape lemmas

`lowerTotalExpr` decomposition for the shapes appearing in ANF primitives.
These pin down exactly what each `.Let`/`.Force`/`.App`/`.Case`/`.Constr`
node lowers to so that the MIRRefines proofs have concrete UPLC terms to
work with. -/

/-- Specialized form: when `e` lowers to `t` in `env`, then
    `let x = e in Var x` lowers to `Apply (Lam 0 (Var 1)) t`. -/
private theorem lowerTotalExpr_let_var_self_some
    {env : List VarId} (x : VarId) {e : Expr} {t : Term}
    (h : lowerTotalExpr env e = some t) :
    lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) =
      some (.Apply (.Lam 0 (.Var 1)) t) := by
  have hexp : lowerTotal env (expandFix e) = some t := h
  show lowerTotal env (expandFix (.Let [(x, e, false)] (.Var x))) = _
  simp [expandFix, expandFixBinds, lowerTotal, lowerTotalLet, envLookupT_cons_self, hexp]

/-- Specialized form: when `e` does *not* lower in `env`, neither does
    `let x = e in Var x`. -/
private theorem lowerTotalExpr_let_var_self_none
    {env : List VarId} (x : VarId) {e : Expr}
    (h : lowerTotalExpr env e = none) :
    lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = none := by
  have hexp : lowerTotal env (expandFix e) = none := h
  show lowerTotal env (expandFix (.Let [(x, e, false)] (.Var x))) = none
  simp [expandFix, expandFixBinds, lowerTotal, lowerTotalLet, hexp]

/-- Unified form: `lowerTotalExpr` of `.Let [(x, e, false)] (.Var x)` is
    the identity-application wrapper of `lowerTotalExpr` of `e`. -/
private theorem lowerTotalExpr_let_var_self
    (env : List VarId) (x : VarId) (e : Expr) :
    lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) =
      (lowerTotalExpr env e).map (fun t => .Apply (.Lam 0 (.Var 1)) t) := by
  cases h : lowerTotalExpr env e with
  | none => rw [lowerTotalExpr_let_var_self_none x h]; rfl
  | some t => rw [lowerTotalExpr_let_var_self_some x h]; rfl

/-! ## Section 3. Atomize primitive (e ≈ let x = e in Var x) -/

/-- Closedness preservation for atomize: the wrapped form `Apply (Lam 0 (Var 1)) t`
    is closed at `k` iff `t` is. -/
private theorem closedAt_atomize_iff (k : Nat) (t : Term) :
    closedAt k (.Apply (.Lam 0 (.Var 1)) t) = closedAt k t := by
  simp only [closedAt, decide_eq_true (show (1 : Nat) ≤ k + 1 from by omega), Bool.true_and]

/-- **MIRRefines for atomize (forward direction)**: `e ⊑ᴹ let x = e in Var x`.

    The let form lowers to `Apply (Lam 0 (Var 1)) t` where `t` is the
    lowering of `e`. After 3 admin steps, the right-hand side reaches
    `compute (funV (VLam (Var 1) ρ₂) :: π₂) ρ₂ t`, which differs from
    the left-hand state only in the funV frame on the stack. The funV
    frame is absorbed via `stackRefK_funV_id_augment`, then `ftlr`
    closes the goal: same `t` in related envs and stacks. -/
theorem mirRefines_atomize_fwd (e : Expr) (x : VarId) :
    MIRRefines e (.Let [(x, e, false)] (.Var x)) := by
  refine ⟨fun env hsome => by
    rw [lowerTotalExpr_let_var_self env x e, Option.isSome_map]; exact hsome, ?_⟩
  intro d k env hlen
  cases ht : lowerTotalExpr env e with
  | none =>
    rw [lowerTotalExpr_let_var_self_none x ht]; trivial
  | some t₁ =>
    rw [lowerTotalExpr_let_var_self_some x ht]
    simp only
    intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    have h_steps :
        steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Var 1)) t₁)) =
          State.compute (.funV (.VLam (.Var 1) ρ₂) :: π₂) ρ₂ t₁ := rfl
    subst hlen
    exact obsRefinesK_of_steps_right h_steps <|
      ftlr env.length t₁ (lowerTotal_closedAt env (expandFix e) t₁ ht)
        j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi _ _ (stackRefK_funV_id_augment_right hπ)

/-- **MIRRefines for atomize (backward direction)**: `let x = e in Var x ⊑ᴹ e`.

    Symmetric to the forward direction: the LHS takes 3 admin steps to
    reach `compute (funV ... :: π₁) ρ₁ t`, and we need this to refine
    `compute π₂ ρ₂ t`. We do this by showing the funV frame is also
    transparent on the *left* — so the goal reduces to `t in extended
    stack ⊑ t in plain stack`, again via FTLR with a stack relation. -/
theorem mirRefines_atomize_bwd (e : Expr) (x : VarId) :
    MIRRefines (.Let [(x, e, false)] (.Var x)) e := by
  refine ⟨fun env hsome => by
    rw [lowerTotalExpr_let_var_self env x e, Option.isSome_map] at hsome; exact hsome, ?_⟩
  intro d k env hlen
  cases ht : lowerTotalExpr env e with
  | none =>
    rw [lowerTotalExpr_let_var_self_none x ht]; trivial
  | some t₁ =>
    rw [lowerTotalExpr_let_var_self_some x ht]
    simp only
    intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    have h_steps :
        steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Var 1)) t₁)) =
          State.compute (.funV (.VLam (.Var 1) ρ₁) :: π₁) ρ₁ t₁ := rfl
    subst hlen
    exact obsRefinesK_of_steps_left h_steps <|
      ftlr env.length t₁ (lowerTotal_closedAt env (expandFix e) t₁ ht)
        j j (Nat.le_refl _) ρ₁ ρ₂ henv i hi _ _ (stackRefK_funV_id_augment_left hπ)

/-- Closedness preservation suffices for the atomize direction
    `e ↦ let x = e in Var x`: the wrapper is closed iff the body is. -/
private theorem atomize_close_pres_fwd (e : Expr) (x : VarId) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env e = some t₁ →
      lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env _ _ _ h₁ h₂ hc
  rw [lowerTotalExpr_let_var_self env x e, h₁] at h₂
  cases h₂; rw [closedAt_atomize_iff]; exact hc

private theorem atomize_close_pres_bwd (e : Expr) (x : VarId) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(x, e, false)] (.Var x)) = some t₁ →
      lowerTotalExpr env e = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env _ _ _ h₁ h₂ hc
  rw [lowerTotalExpr_let_var_self env x e, h₂] at h₁
  cases h₁; rwa [closedAt_atomize_iff] at hc

/-- **MIRCtxRefines for atomize**, both directions. -/
theorem mirCtxRefines_atomize_fwd (e : Expr) (x : VarId) :
    MIRCtxRefines e (.Let [(x, e, false)] (.Var x)) :=
  mirRefines_to_mirCtxRefines (mirRefines_atomize_fwd e x) (atomize_close_pres_fwd e x)

theorem mirCtxRefines_atomize_bwd (e : Expr) (x : VarId) :
    MIRCtxRefines (.Let [(x, e, false)] (.Var x)) e :=
  mirRefines_to_mirCtxRefines (mirRefines_atomize_bwd e x) (atomize_close_pres_bwd e x)
end Moist.Verified.MIR
