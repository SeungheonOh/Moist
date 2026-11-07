import Moist.Verified.Equivalence
import Moist.Verified.ClosedAt
import Moist.Verified.Contextual
import Moist.Verified.Contextual.Congruence
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Definitions.MIR
import Moist.MIR.LowerTotal

/-! # MIR-level refinement

Lifts UPLC refinement to MIR expressions via `lowerTotalExpr`:
reflexivity/transitivity of `MIRCtxRefines`, the `MIRRefines → MIRCtxRefines`
bridge (`mirRefines_to_mirCtxRefines`, through `obsRefines_of_openRefines`),
and `lowerTotalExpr` decomposition lemmas used by the congruences.
-/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.Verified (closedAt)
open Moist.Verified.Contextual
  (Context fill closedAt_mono fill_closedAt_iff ObsRefines CtxRefines
   ctxRefines_refl ctxRefines_trans ctxRefines_fill)
open Moist.Verified.Equivalence (ListRel)

open Moist.Verified.Contextual.SoundnessRefines
  (EnvRefinesK BehRefinesK ValueRefinesK StackRefK OpenRefinesK OpenRefines
   soundness_refines obsRefines_of_openRefines)

/-! ## `lowerTotal` preserves `closedAt`

Bridging lemmas connecting `Moist.MIR.lowerTotal` with the
`Moist.Verified.closedAt` predicate. Used by `lowerTotalExpr_closedAt`
below (and indirectly by the dead-let refinement proof). -/

open Moist.MIR (envLookupT_bound lowerTotalList) in
mutual
  theorem lowerTotal_closedAt (env : List VarId) (e : Expr) (t : Moist.Plutus.Term.Term)
      (h : Moist.MIR.lowerTotal env e = some t) : closedAt env.length t = true := by
    match e with
    | .Var x =>
      simp only [Moist.MIR.lowerTotal.eq_1] at h; split at h
      · rename_i idx hlook; injection h with h; subst h; simp [closedAt]
        have := envLookupT_bound env x idx hlook; omega
      · injection h
    | .Lit (c, ty) =>
      simp only [Moist.MIR.lowerTotal.eq_2] at h; injection h with h; subst h; simp [closedAt]
    | .Builtin b =>
      simp only [Moist.MIR.lowerTotal.eq_3] at h; injection h with h; subst h; simp [closedAt]
    | .Error =>
      simp only [Moist.MIR.lowerTotal.eq_4] at h; injection h with h; subst h; simp [closedAt]
    | .Lam x body =>
      simp only [Moist.MIR.lowerTotal.eq_5, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨body', hbody, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; have := lowerTotal_closedAt (x :: env) body body' hbody
      simp at this; exact this
    | .App f x =>
      simp only [Moist.MIR.lowerTotal.eq_6, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f', hf, x', hx, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env f f' hf, lowerTotal_closedAt env x x' hx⟩
    | .Force inner =>
      simp only [Moist.MIR.lowerTotal.eq_7, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Delay inner =>
      simp only [Moist.MIR.lowerTotal.eq_8, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨inner', hinner, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotal_closedAt env inner inner' hinner
    | .Constr tag args =>
      simp only [Moist.MIR.lowerTotal.eq_9, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨args', hargs, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt]; exact lowerTotalList_closedAtList env args args' hargs
    | .Case scrut alts =>
      simp only [Moist.MIR.lowerTotal.eq_10, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨scrut', hscrut, alts', halts, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env scrut scrut' hscrut,
             lowerTotalList_closedAtList env alts alts' halts⟩
    | .Let binds body =>
      simp only [Moist.MIR.lowerTotal.eq_11] at h; exact lowerTotalLet_closedAt env binds body t h
    | .Fix _ _ => simp only [Moist.MIR.lowerTotal.eq_12] at h; injection h
  termination_by sizeOf e

  theorem lowerTotalList_closedAtList (env : List VarId) (es : List Expr)
      (ts : List Moist.Plutus.Term.Term) (h : Moist.MIR.lowerTotalList env es = some ts) :
      Moist.Verified.closedAtList env.length ts = true := by
    match es with
    | [] => simp only [Moist.MIR.lowerTotalList.eq_1] at h; injection h with h; subst h; simp [Moist.Verified.closedAtList]
    | e :: rest =>
      simp only [Moist.MIR.lowerTotalList.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ts', hts, heq⟩ := h; injection heq with heq; subst heq
      simp only [Moist.Verified.closedAtList, Bool.and_eq_true]
      exact ⟨lowerTotal_closedAt env e t ht, lowerTotalList_closedAtList env rest ts' hts⟩
  termination_by sizeOf es

  theorem lowerTotalLet_closedAt (env : List VarId)
      (binds : List (VarId × Expr × Bool)) (body : Expr) (t : Moist.Plutus.Term.Term)
      (h : Moist.MIR.lowerTotalLet env binds body = some t) :
      closedAt env.length t = true := by
    match binds with
    | [] => simp only [Moist.MIR.lowerTotalLet.eq_1] at h; exact lowerTotal_closedAt env body t h
    | (x, rhs, _) :: rest =>
      simp only [Moist.MIR.lowerTotalLet.eq_2, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨rhs', hrhs, rest', hrest, heq⟩ := h; injection heq with heq; subst heq
      simp only [closedAt, Bool.and_eq_true]
      have := lowerTotalLet_closedAt (x :: env) rest body rest' hrest
      simp at this; exact ⟨this, lowerTotal_closedAt env rhs rhs' hrhs⟩
  termination_by sizeOf binds + sizeOf body
end

/-- Lift `lowerTotal_closedAt` through `lowerTotalExpr`'s extra `expandFix`
    step: if `lowerTotalExpr env e = some t`, then `t` is closed at
    `env.length`. -/
theorem lowerTotalExpr_closedAt {env : List VarId} {e : Expr} {t : Moist.Plutus.Term.Term}
    (h : lowerTotalExpr env e = some t) : closedAt env.length t = true := by
  simp only [Moist.MIR.lowerTotalExpr] at h
  exact lowerTotal_closedAt env (Moist.MIR.expandFix e) t h

--------------------------------------------------------------------------------
-- 3. BASIC PROPERTIES OF MIRCtxRefines
--------------------------------------------------------------------------------

/-- Reflexivity of `MIRCtxRefines`. -/
theorem mirCtxRefines_refl (m : Expr) : MIRCtxRefines m m := by
  intro env
  refine ⟨id, ?_⟩
  cases h : lowerTotalExpr env m with
  | none => trivial
  | some _ => exact ctxRefines_refl _

/-- Transitivity of `MIRCtxRefines`. Thanks to the new `CtxRefines` shape
    (closedness preservation bundled into the relation), this is a clean
    composition — no middle-closedness side condition needed. -/
theorem mirCtxRefines_trans {m₁ m₂ m₃ : Expr} :
    MIRCtxRefines m₁ m₂ → MIRCtxRefines m₂ m₃ → MIRCtxRefines m₁ m₃ := by
  intro h12 h23 env
  obtain ⟨hsome12, hctx12⟩ := h12 env
  obtain ⟨hsome23, hctx23⟩ := h23 env
  refine ⟨hsome23 ∘ hsome12, ?_⟩
  cases h₁ : lowerTotalExpr env m₁ with
  | none => trivial
  | some t₁ =>
    cases h₃ : lowerTotalExpr env m₃ with
    | none => trivial
    | some t₃ =>
      have hsome2 : (lowerTotalExpr env m₂).isSome := hsome12 (by rw [h₁]; trivial)
      cases h₂ : lowerTotalExpr env m₂ with
      | none => rw [h₂] at hsome2; exact absurd hsome2 (by simp)
      | some t₂ =>
        rw [h₁, h₂] at hctx12
        rw [h₂, h₃] at hctx23
        -- hctx12 : CtxRefines t₁ t₂, hctx23 : CtxRefines t₂ t₃
        show CtxRefines t₁ t₃
        exact ctxRefines_trans hctx12 hctx23

--------------------------------------------------------------------------------
-- 5. BRIDGE: `MIRRefines` → `MIRCtxRefines`.
--
-- `MIRRefines` is unidirectional and provides `MIROpenRef d` at every
-- depth. For each env, we extract `MIROpenRef env.length`, derive
-- `OpenRefines env.length` on the `env`-lowerings, and feed it through
-- `obsRefines_of_openRefines` to obtain `ObsRefines` under any closing context.
--------------------------------------------------------------------------------

/-- From `MIRRefines m₁ m₂` to `MIRCtxRefines m₁ m₂`, via
    `obsRefines_of_openRefines` at depth `env.length`. Requires an external
    closedness-preservation hypothesis since `MIRRefines` is a purely
    semantic relation and the new `MIRCtxRefines` (backed by the strict
    `CtxRefines`) bundles closedness preservation into its observation
    clause.

    The closedness-preservation hypothesis is stated at the "free-variable
    horizon" (a depth `k : Nat`) rather than over contexts, since
    `closedAt 0 (fill C t) ↔ C.closedAt 0 ∧ closedAt C.binders t`
    (from `fill_closedAt_iff`) — the `C` drops out and what matters is
    that `closedAt k t₁ → closedAt k t₂` at every depth `k`. -/
theorem mirRefines_to_mirCtxRefines {m₁ m₂ : Expr} (h : MIRRefines m₁ m₂)
    (h_close_pres : ∀ env k t₁ t₂,
      lowerTotalExpr env m₁ = some t₁ → lowerTotalExpr env m₂ = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  refine ⟨h.1 env, ?_⟩
  cases hlow₁ : lowerTotalExpr env m₁ with
  | none => trivial
  | some t₁ =>
    cases hlow₂ : lowerTotalExpr env m₂ with
    | none => trivial
    | some t₂ =>
      show CtxRefines t₁ t₂
      intro C hC1
      -- Split hC1 into `C.closedAt 0` and `closedAt C.binders t₁`,
      -- transport the latter through `h_close_pres` at k = C.binders,
      -- then rebuild `closedAt 0 (fill C t₂)`.
      have hd1 := (fill_closedAt_iff C t₁ 0).mp hC1
      simp only [Nat.zero_add] at hd1
      have hC_outer := hd1.1
      have ht₂ : closedAt C.binders t₂ = true :=
        h_close_pres env C.binders t₁ t₂ hlow₁ hlow₂ hd1.2
      have hC2 : closedAt 0 (fill C t₂) = true :=
        (fill_closedAt_iff C t₂ 0).mpr ⟨hC_outer, by simpa [Nat.zero_add] using ht₂⟩
      refine ⟨hC2, ?_⟩
      have hopenRef : MIROpenRef env.length m₁ m₂ := h.2 env.length
      have h_open : OpenRefines env.length t₁ t₂ := by
        intro k j hj ρ₁ ρ₂ henv
        have := hopenRef k env rfl
        rw [hlow₁, hlow₂] at this
        exact this j hj ρ₁ ρ₂ henv
      exact obsRefines_of_openRefines h_open C hC1 hC2

--------------------------------------------------------------------------------
-- 6. Helpers for MIR-level congruences (the congruences themselves are in
-- `Moist.Verified.MIR.Congruence`)
--------------------------------------------------------------------------------

/-! ### 6a. `lowerTotalExpr` compositional decomposition -/

/-- `lowerTotalExpr` commutes with `.Force`. -/
theorem lowerTotalExpr_force (env : List VarId) (t : Expr) :
    lowerTotalExpr env (.Force t) = (lowerTotalExpr env t).map .Force := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotal env (Moist.MIR.expandFix t) <;> rfl

/-- `lowerTotalExpr` commutes with `.Delay`. -/
theorem lowerTotalExpr_delay (env : List VarId) (t : Expr) :
    lowerTotalExpr env (.Delay t) = (lowerTotalExpr env t).map .Delay := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotal env (Moist.MIR.expandFix t) <;> rfl

/-- `lowerTotalExpr` commutes with `.Lam` (shifting `x` onto the env). -/
theorem lowerTotalExpr_lam (env : List VarId) (x : VarId) (body : Expr) :
    lowerTotalExpr env (.Lam x body) =
      (lowerTotalExpr (x :: env) body).map (.Lam 0) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotal (x :: env) (Moist.MIR.expandFix body) <;> rfl

/-- `lowerTotalExpr` commutes with `.App`. -/
theorem lowerTotalExpr_app (env : List VarId) (f a : Expr) :
    lowerTotalExpr env (.App f a) =
      (do let f' ← lowerTotalExpr env f
          let a' ← lowerTotalExpr env a
          some (.Apply f' a')) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

/-- `lowerTotalExpr` commutes with `.Constr`. -/
theorem lowerTotalExpr_constr (env : List VarId) (tag : Nat) (args : List Expr) :
    lowerTotalExpr env (.Constr tag args) =
      (Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList args)).map (.Constr tag) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  cases Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList args) <;> rfl

/-- `lowerTotalExpr` commutes with `.Case`. -/
theorem lowerTotalExpr_case (env : List VarId) (scrut : Expr) (alts : List Expr) :
    lowerTotalExpr env (.Case scrut alts) =
      (do let s ← lowerTotalExpr env scrut
          let a ← Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList alts)
          some (.Case s a)) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

/-! ### 6d. List-level helpers for Constr/Case congruences -/

/-- Unwrapped `lowerTotalList ∘ expandFixList` — the list counterpart of
    `lowerTotalExpr`. -/
def lowerTotalExprList (env : List VarId) (es : List Expr) : Option (List Moist.Plutus.Term.Term) :=
  Moist.MIR.lowerTotalList env (Moist.MIR.expandFixList es)

theorem lowerTotalExprList_nil (env : List VarId) :
    lowerTotalExprList env [] = some [] := by
  simp only [lowerTotalExprList, Moist.MIR.expandFixList, Moist.MIR.lowerTotalList]

theorem lowerTotalExprList_cons (env : List VarId) (e : Expr) (es : List Expr) :
    lowerTotalExprList env (e :: es) =
      (do let t ← lowerTotalExpr env e
          let ts ← lowerTotalExprList env es
          some (t :: ts)) := by
  simp only [lowerTotalExprList, lowerTotalExpr,
             Moist.MIR.expandFixList, Moist.MIR.lowerTotalList]

/-! ### 6e. Constr / Case congruences -/

/-- `lowerTotalExpr` on `.Constr` in terms of `lowerTotalExprList`. -/
theorem lowerTotalExpr_constr_of_list (env : List VarId) (tag : Nat)
    (args : List Expr) :
    lowerTotalExpr env (.Constr tag args) =
      (lowerTotalExprList env args).map (.Constr tag) := by
  rw [lowerTotalExpr_constr]; rfl

/-- `lowerTotalExpr` on `.Case` in terms of `lowerTotalExprList`. -/
theorem lowerTotalExpr_case_of_list (env : List VarId) (scrut : Expr)
    (alts : List Expr) :
    lowerTotalExpr env (.Case scrut alts) =
      (do let s ← lowerTotalExpr env scrut
          let a ← lowerTotalExprList env alts
          some (.Case s a)) := by
  rw [lowerTotalExpr_case]; rfl

--------------------------------------------------------------------------------
-- 7. Projections and list helpers for `MIRCtxRefines`
--------------------------------------------------------------------------------

/-! ## Generic refinement helpers -/

/-- Expressions with identical lowerings in every environment refine each other. -/
theorem mirCtxRefines_of_lowerEq {m₁ m₂ : Expr}
    (h : ∀ env, lowerTotalExpr env m₁ = lowerTotalExpr env m₂) :
    MIRCtxRefines m₁ m₂ := by
  intro env
  rw [h env]
  refine ⟨id, ?_⟩
  cases lowerTotalExpr env m₂ with
  | none => trivial
  | some t => exact ctxRefines_refl t

/-- A source that never lowers refines anything. -/
theorem mirCtxRefines_of_lhs_none {m₁ m₂ : Expr}
    (h : ∀ env, lowerTotalExpr env m₁ = none) : MIRCtxRefines m₁ m₂ := by
  intro env
  rw [h env]
  exact ⟨by simp, trivial⟩

/-- `Fix` whose body is not a lambda never lowers. -/
theorem lowerTotalExpr_fix_nonlam_none (env : List VarId) (f : VarId) (body : Expr)
    (h : ∀ (x : VarId) (inner : Expr), body ≠ .Lam x inner) :
    lowerTotalExpr env (.Fix f body) = none := by
  cases body <;>
    first
    | exact absurd rfl (h _ _)
    | simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

theorem mirCtxRefines_fix_nonlam_lhs {f : VarId} {body target : Expr}
    (h : ∀ (x : VarId) (inner : Expr), body ≠ .Lam x inner) :
    MIRCtxRefines (.Fix f body) target :=
  mirCtxRefines_of_lhs_none (fun env => lowerTotalExpr_fix_nonlam_none env f body h)

theorem mirCtxRefines_fix_nonlam_both {f₁ f₂ : VarId} {body₁ body₂ : Expr}
    (h₁ : ∀ (x : VarId) (inner : Expr), body₁ ≠ .Lam x inner)
    (_h₂ : ∀ (x : VarId) (inner : Expr), body₂ ≠ .Lam x inner) :
    MIRCtxRefines (.Fix f₁ body₁) (.Fix f₂ body₂) :=
  mirCtxRefines_fix_nonlam_lhs h₁

end Moist.Verified.MIR
