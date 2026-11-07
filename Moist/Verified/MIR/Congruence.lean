import Moist.Verified.MIR

/-! # MIR-level congruence lemmas for `MIRCtxRefines`

Each lemma has the shape `R a b → R (F a) (F b)` for a MIR constructor `F`.
The one-hole cases are instances of `mirCtxRefines_of_context`: both sides
lower to the same UPLC context around the lowered children, so
`ctxRefines_fill` applies. -/

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.Verified (closedAt)
open Moist.Verified.Contextual
  (Context fill closedAt_mono fill_closedAt_iff ObsRefines
   CtxEq CtxRefines
   ctxEq_refl ctxEq_symm ctxEq_trans ctxRefines_refl ctxRefines_trans
   ctxEq_lam ctxEq_delay ctxEq_force ctxEq_app
   ctxEq_constr_one ctxEq_constr ctxEq_case_scrut ctxEq_case_one_alt ctxEq_case
   ctxRefines_lam ctxRefines_delay ctxRefines_force ctxRefines_app
   ctxRefines_constr_one ctxRefines_constr ctxRefines_case_scrut
   ctxRefines_case_one_alt ctxRefines_case ctxRefines_fill)
open Moist.Verified.Equivalence (ObsEq ListRel)

/-! ## One-hole congruence -/

/-- If in every environment either the left side fails to lower, or both sides
    lower to one context `C` filled with the lowerings of `m₁`/`m₂` in a common
    environment, then `MIRCtxRefines m₁ m₂` lifts to the two sides. -/
theorem mirCtxRefines_of_context {m₁ m₂ n₁ n₂ : Expr} (h : MIRCtxRefines m₁ m₂)
    (hlow : ∀ env, lowerTotalExpr env n₁ = none ∨ ∃ env' C,
      lowerTotalExpr env n₁ = (lowerTotalExpr env' m₁).map (fill C) ∧
      lowerTotalExpr env n₂ = (lowerTotalExpr env' m₂).map (fill C)) :
    MIRCtxRefines n₁ n₂ := by
  intro env
  rcases hlow env with hnone | ⟨env', C, h₁, h₂⟩
  · rw [hnone]; exact ⟨by simp, trivial⟩
  · rw [h₁, h₂]
    refine ⟨by simpa only [Option.isSome_map] using (h env').1, ?_⟩
    have href := (h env').2
    revert href
    cases lowerTotalExpr env' m₁ <;> cases lowerTotalExpr env' m₂ <;>
      simp only [Option.map_some, Option.map_none] <;>
      first | exact fun _ => trivial | exact fun h => ctxRefines_fill h C

/-- Same-environment instance of `mirCtxRefines_of_context`. -/
private theorem mirCtxRefines_of_map {m₁ m₂ n₁ n₂ : Expr} (h : MIRCtxRefines m₁ m₂)
    (shift : List VarId → List VarId) (C : Context)
    (h₁ : ∀ env, lowerTotalExpr env n₁ = (lowerTotalExpr (shift env) m₁).map (fill C))
    (h₂ : ∀ env, lowerTotalExpr env n₂ = (lowerTotalExpr (shift env) m₂).map (fill C)) :
    MIRCtxRefines n₁ n₂ :=
  mirCtxRefines_of_context h fun env => .inr ⟨shift env, C, h₁ env, h₂ env⟩

theorem mirCtxRefines_force {t₁ t₂ : Expr} (h : MIRCtxRefines t₁ t₂) :
    MIRCtxRefines (.Force t₁) (.Force t₂) :=
  mirCtxRefines_of_map h id (.Force .Hole) (lowerTotalExpr_force · t₁) (lowerTotalExpr_force · t₂)

theorem mirCtxRefines_delay {t₁ t₂ : Expr} (h : MIRCtxRefines t₁ t₂) :
    MIRCtxRefines (.Delay t₁) (.Delay t₂) :=
  mirCtxRefines_of_map h id (.Delay .Hole) (lowerTotalExpr_delay · t₁) (lowerTotalExpr_delay · t₂)

theorem mirCtxRefines_lam {x : VarId} {body₁ body₂ : Expr} (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Lam x body₁) (.Lam x body₂) :=
  mirCtxRefines_of_map h (x :: ·) (.Lam 0 .Hole)
    (lowerTotalExpr_lam · x body₁) (lowerTotalExpr_lam · x body₂)

/-- Lowering of `App f a` as a context around `f` (or failure). -/
private theorem lowerTotalExpr_app_left (env : List VarId) (a : Expr) :
    (∀ f, lowerTotalExpr env (.App f a) = none) ∨ ∃ ta, ∀ f,
      lowerTotalExpr env (.App f a) = (lowerTotalExpr env f).map (fill (.AppLeft .Hole ta)) := by
  cases ha : lowerTotalExpr env a with
  | none => exact .inl fun f => by rw [lowerTotalExpr_app, ha]; cases lowerTotalExpr env f <;> rfl
  | some ta => exact .inr ⟨ta, fun f => by rw [lowerTotalExpr_app, ha]; cases lowerTotalExpr env f <;> rfl⟩

theorem mirCtxRefines_app {f₁ f₂ a₁ a₂ : Expr}
    (hf : MIRCtxRefines f₁ f₂) (ha : MIRCtxRefines a₁ a₂) :
    MIRCtxRefines (.App f₁ a₁) (.App f₂ a₂) := by
  refine mirCtxRefines_trans (m₂ := .App f₂ a₁)
    (mirCtxRefines_of_context hf fun env => ?_) (mirCtxRefines_of_context ha fun env => ?_)
  · rcases lowerTotalExpr_app_left env a₁ with hnone | ⟨ta, hta⟩
    · exact .inl (hnone f₁)
    · exact .inr ⟨env, _, hta f₁, hta f₂⟩
  · cases hf₂ : lowerTotalExpr env f₂ with
    | none => exact .inl (by rw [lowerTotalExpr_app, hf₂]; rfl)
    | some tf =>
      refine .inr ⟨env, .AppRight tf .Hole, ?_, ?_⟩ <;>
        (rw [lowerTotalExpr_app, hf₂]; cases lowerTotalExpr env _ <;> rfl)

/-! ## Constr / Case congruences -/

/-- Constr congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_constr {tag : Nat} {m₁ m₂ : Expr} {ms₁ ms₂ : List Expr}
    (hm : MIRCtxRefines m₁ m₂) (hms : ListRel MIRCtxRefines ms₁ ms₂) :
    MIRCtxRefines (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  intro env
  have hrel : ListRel MIRCtxRefines (m₁ :: ms₁) (m₂ :: ms₂) := ⟨hm, hms⟩
  have hlist_imp := listRel_mirCtxRefines_isSome_imp hrel env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    simp only [Option.isSome_map]
    exact hlist_imp
  · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
    cases hlow₁ : lowerTotalExprList env (m₁ :: ms₁) with
    | none => simp
    | some ts₁ =>
      cases hlow₂ : lowerTotalExprList env (m₂ :: ms₂) with
      | none => simp
      | some ts₂ =>
        show CtxRefines (.Constr tag ts₁) (.Constr tag ts₂)
        rw [lowerTotalExprList_cons] at hlow₁ hlow₂
        cases ht_m₁ : lowerTotalExpr env m₁ with
        | none => rw [ht_m₁] at hlow₁; simp at hlow₁
        | some t_m₁ =>
          cases ht_ms₁ : lowerTotalExprList env ms₁ with
          | none => rw [ht_m₁, ht_ms₁] at hlow₁; simp at hlow₁
          | some t_ms₁ =>
            cases ht_m₂ : lowerTotalExpr env m₂ with
            | none => rw [ht_m₂] at hlow₂; simp at hlow₂
            | some t_m₂ =>
              cases ht_ms₂ : lowerTotalExprList env ms₂ with
              | none => rw [ht_m₂, ht_ms₂] at hlow₂; simp at hlow₂
              | some t_ms₂ =>
                rw [ht_m₁, ht_ms₁] at hlow₁
                rw [ht_m₂, ht_ms₂] at hlow₂
                cases hlow₁; cases hlow₂
                exact ctxRefines_constr (hm.toCtxRefines ht_m₁ ht_m₂)
                  (listRel_mirCtxRefines_toListCtxRefines hms ht_ms₁ ht_ms₂)

/-- General Case congruence for `MIRCtxRefines`. -/
theorem mirCtxRefines_case {scrut₁ scrut₂ : Expr} {alts₁ alts₂ : List Expr}
    (hscrut : MIRCtxRefines scrut₁ scrut₂)
    (halts : ListRel MIRCtxRefines alts₁ alts₂) :
    MIRCtxRefines (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  intro env
  refine ⟨?_, ?_⟩
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    have h_scrut_imp := hscrut.toImp env
    have h_alts_imp := listRel_mirCtxRefines_isSome_imp halts env
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some _ =>
      have : (lowerTotalExpr env scrut₂).isSome := h_scrut_imp (by rw [h_s₁]; rfl)
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => rw [h_s₂] at this; exact absurd this (by simp)
      | some _ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some _ =>
          have : (lowerTotalExprList env alts₂).isSome := h_alts_imp (by rw [h_a₁]; rfl)
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => rw [h_a₂] at this; exact absurd this (by simp)
          | some _ => simp
  · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
    cases h_s₁ : lowerTotalExpr env scrut₁ with
    | none => simp
    | some ts₁ =>
      cases h_s₂ : lowerTotalExpr env scrut₂ with
      | none => simp
      | some ts₂ =>
        cases h_a₁ : lowerTotalExprList env alts₁ with
        | none => simp
        | some t_a₁ =>
          cases h_a₂ : lowerTotalExprList env alts₂ with
          | none => simp
          | some t_a₂ =>
            show CtxRefines (.Case ts₁ t_a₁) (.Case ts₂ t_a₂)
            have hlist_ctx : ListRel CtxRefines t_a₁ t_a₂ :=
              listRel_mirCtxRefines_toListCtxRefines halts h_a₁ h_a₂
            exact ctxRefines_case (hscrut.toCtxRefines h_s₁ h_s₂) hlist_ctx

/-- Fix-Lam congruence: both sides lower to the Z-combinator wrapper around
    the body, lowered under a common fresh self variable. -/
theorem mirCtxRefines_fix_lam {f x : VarId} {body₁ body₂ : Expr}
    (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Fix f (.Lam x body₁)) (.Fix f (.Lam x body₂)) := by
  refine mirCtxRefines_of_context h fun env => .inr ?_
  -- A fresh `s` avoiding both expanded bodies gives a common inner environment.
  let s : VarId := ⟨max (Moist.MIR.maxUidExpr (Moist.MIR.expandFix body₁))
    (Moist.MIR.maxUidExpr (Moist.MIR.expandFix body₂)) + 1, .gen, "s"⟩
  refine ⟨x :: f :: s :: env,
    .AppRight (.Lam 0 (.Apply (.Var 1) (.Var 1)))
      (.Lam 0 (.AppLeft (.Lam 0 (.Lam 0 .Hole))
        (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1))))), ?_, ?_⟩ <;>
  exact Moist.MIR.lowerTotalExpr_fix_lam_with_fresh env f x _ s
    (Moist.MIR.maxUidExpr_fresh _ s (by simp [s]; omega))

/-! ## Let congruences -/

section LetCongruence

open Moist.MIR (lowerTotal lowerTotalLet)

/-- Unconditional decomposition: `lowerTotalExpr env (.Let binds body)` equals
    `lowerTotalLet env (expandFixBinds binds) (expandFix body)`. Holds for any
    binds/body, including those containing Fix nodes. The expansion happens
    inside `expandFix` on the Let constructor. -/
theorem lowerTotalExpr_let (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let binds body) =
      lowerTotalLet env (Moist.MIR.expandFixBinds binds) (Moist.MIR.expandFix body) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

/-- The bindings of a `Let` either always fail to lower, or lower to a fixed
    context around the body, which is lowered in an extended environment. -/
theorem lowerTotalLet_context :
    ∀ (binds : List (VarId × Expr × Bool)) (env : List VarId),
      (∀ body, lowerTotalLet env binds body = none) ∨
      ∃ env' C, ∀ body, lowerTotalLet env binds body = (lowerTotal env' body).map (fill C)
  | [], env => .inr ⟨env, .Hole, fun body => by
      simp only [lowerTotalLet]; cases lowerTotal env body <;> rfl⟩
  | (x, rhs, _) :: rest, env => by
    cases hr : lowerTotal env rhs with
    | none => exact .inl fun body => by simp [lowerTotalLet, hr]
    | some r =>
      rcases lowerTotalLet_context rest (x :: env) with hnone | ⟨env', C, hC⟩
      · exact .inl fun body => by simp [lowerTotalLet, hr, hnone]
      · refine .inr ⟨env', .AppLeft (.Lam 0 C) r, fun body => ?_⟩
        simp only [lowerTotalLet, hr, hC, Option.bind_eq_bind, Option.bind_some]
        cases lowerTotal env' body <;> rfl

theorem mirCtxRefines_let_body
    {binds : List (VarId × Expr × Bool)} {body₁ body₂ : Expr}
    (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Let binds body₁) (.Let binds body₂) := by
  refine mirCtxRefines_of_context h fun env => ?_
  rw [lowerTotalExpr_let, lowerTotalExpr_let]
  rcases lowerTotalLet_context (Moist.MIR.expandFixBinds binds) env with hnone | ⟨env', C, hC⟩
  · exact .inl (hnone _)
  · exact .inr ⟨env', C, hC _, hC _⟩

theorem mirCtxRefines_let_rhs_head
    {x : VarId} {rhs₁ rhs₂ : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : MIRCtxRefines rhs₁ rhs₂) :
    MIRCtxRefines (.Let ((x, rhs₁, er) :: rest) body)
                  (.Let ((x, rhs₂, er) :: rest) body) := by
  refine mirCtxRefines_of_context h fun env => ?_
  rw [lowerTotalExpr_let, lowerTotalExpr_let]
  simp only [Moist.MIR.expandFixBinds, lowerTotalLet, Option.bind_eq_bind]
  cases hinner : lowerTotalLet (x :: env) (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
  | none => exact .inl (by cases lowerTotal env (Moist.MIR.expandFix rhs₁) <;> rfl)
  | some inner =>
    refine .inr ⟨env, .AppRight (.Lam 0 inner) .Hole, ?_, ?_⟩ <;>
      (show _ = (lowerTotal env (Moist.MIR.expandFix _)).map _
       cases lowerTotal env (Moist.MIR.expandFix _) <;> rfl)

--------------------------------------------------------------------------------
-- 5. Empty let collapse
--------------------------------------------------------------------------------

/-- `lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body` definitionally
    via `lowerTotalExpr → lowerTotal ∘ expandFix → lowerTotal on .Let → lowerTotalLet`
    → nil case → `lowerTotal env (expandFix body)` = `lowerTotalExpr env body`. -/
theorem lowerTotalExpr_let_nil_eq (env : List VarId) (body : Expr) :
    lowerTotalExpr env (.Let [] body) = lowerTotalExpr env body := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal,
    Moist.MIR.lowerTotalLet]

/-- An empty `.Let [] body` is `MIRCtxRefines`-equivalent to `body`. -/
theorem mirCtxRefines_let_nil {body : Expr} :
    MIRCtxRefines (.Let [] body) body :=
  mirCtxRefines_of_lowerEq (lowerTotalExpr_let_nil_eq · body)

--------------------------------------------------------------------------------
-- Binds-list congruence for .Let
--
-- Given per-rhs `MIRCtxRefines` pairings between `binds₁` and `binds₂`
-- (matching names and `er` flags), swap the binds in a `.Let`. Proved by
-- induction on `binds₁`, using `mirCtxRefines_let_rhs_head` at each step to
-- swap the head rhs, then a body swap via `mirCtxRefines_let_body` applied
-- with a recursive inner-Let swap.
--------------------------------------------------------------------------------

/-- Per-binding rhs swap congruence for `.Let`. Pass-through proof using the
    head-rhs and body helpers. -/
theorem mirCtxRefines_let_binds_congr :
    ∀ (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr),
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                            MIRCtxRefines b₁.2.1 b₂.2.1) binds₁ binds₂ →
      MIRCtxRefines (.Let binds₁ body) (.Let binds₂ body)
  | [], [], _, _ => mirCtxRefines_refl _
  | [], _ :: _, _, hrel => absurd hrel id
  | _ :: _, [], _, hrel => absurd hrel id
  | (v₁, rhs₁, er₁) :: rest₁, (v₂, rhs₂, er₂) :: rest₂, body, hrel => by
    obtain ⟨⟨hname, her, hrhs_ref⟩, hrel_rest⟩ := hrel
    subst hname; subst her
    -- Step 1: swap head rhs from rhs₁ to rhs₂.
    have h_step1 : MIRCtxRefines (.Let ((v₁, rhs₁, er₁) :: rest₁) body)
                                  (.Let ((v₁, rhs₂, er₁) :: rest₁) body) :=
      mirCtxRefines_let_rhs_head hrhs_ref
    -- Step 2: swap body via inner Let-body swap.
    have hrest_ref : MIRCtxRefines (.Let rest₁ body) (.Let rest₂ body) :=
      mirCtxRefines_let_binds_congr rest₁ rest₂ body hrel_rest
    have h_single_swap :
        MIRCtxRefines (.Let [(v₁, rhs₂, er₁)] (.Let rest₁ body))
                      (.Let [(v₁, rhs₂, er₁)] (.Let rest₂ body)) :=
      mirCtxRefines_let_body hrest_ref
    -- Identical lowerings between the two forms.
    have hlow_eq : ∀ (rest_x : List (VarId × Expr × Bool)) env,
        lowerTotalExpr env (.Let ((v₁, rhs₂, er₁) :: rest_x) body) =
        lowerTotalExpr env (.Let [(v₁, rhs₂, er₁)] (.Let rest_x body)) := by
      intro rest_x env
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds,
        Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
    have hunroll := mirCtxRefines_of_lowerEq (hlow_eq rest₁)
    have hreroll := mirCtxRefines_of_lowerEq (fun env => (hlow_eq rest₂ env).symm)
    exact mirCtxRefines_trans h_step1
      (mirCtxRefines_trans hunroll
        (mirCtxRefines_trans h_single_swap hreroll))
termination_by binds₁ _ _ _ => List.length binds₁

end LetCongruence

end Moist.Verified.MIR
