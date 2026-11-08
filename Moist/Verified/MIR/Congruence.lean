import Moist.Verified.MIR

variable [sv : Moist.CEK.SemVariant]

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
  (Context fill closedAt_mono fill_closedAt_iff ObsRefines CtxRefines
   ctxRefines_refl ctxRefines_trans ctxRefines_fill)
open Moist.Verified.Equivalence (ListRel)

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

omit sv in
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

omit sv in
/-- Lowering a list with one distinguished position. -/
theorem lowerTotalExprList_split (env : List VarId) (x : Expr) (post : List Expr) :
    ∀ pre : List Expr, lowerTotalExprList env (pre ++ x :: post) =
      (lowerTotalExprList env pre).bind fun preT =>
      (lowerTotalExprList env post).bind fun postT =>
      (lowerTotalExpr env x).map fun t => preT ++ t :: postT
  | [] => by
    rw [List.nil_append, lowerTotalExprList_cons, lowerTotalExprList_nil]
    cases lowerTotalExpr env x <;> cases lowerTotalExprList env post <;> rfl
  | p :: pre => by
    rw [List.cons_append, lowerTotalExprList_cons, lowerTotalExprList_cons,
      lowerTotalExprList_split env x post pre]
    cases lowerTotalExpr env p <;> cases lowerTotalExprList env pre <;>
      cases lowerTotalExprList env post <;> cases lowerTotalExpr env x <;> rfl

omit sv in
/-- Swapping one position of a list whose other positions lower to fixed terms. -/
private theorem list_context {env : List VarId} {pre post : List Expr} {a b : Expr}
    {F : List Moist.Plutus.Term.Term → Moist.Plutus.Term.Term}
    (C : List Moist.Plutus.Term.Term → List Moist.Plutus.Term.Term → Context)
    (hC : ∀ preT postT t, fill (C preT postT) t = F (preT ++ t :: postT)) :
    ((lowerTotalExprList env (pre ++ a :: post)).map F = none) ∨ ∃ env' C',
      (lowerTotalExprList env (pre ++ a :: post)).map F = (lowerTotalExpr env' a).map (fill C') ∧
      (lowerTotalExprList env (pre ++ b :: post)).map F = (lowerTotalExpr env' b).map (fill C') := by
  rw [lowerTotalExprList_split, lowerTotalExprList_split]
  cases lowerTotalExprList env pre with
  | none => exact .inl rfl
  | some preT =>
    cases lowerTotalExprList env post with
    | none => exact .inl rfl
    | some postT =>
      refine .inr ⟨env, C preT postT, ?_, ?_⟩ <;>
        (simp only [Option.bind_some]; cases lowerTotalExpr env _ <;> simp [hC])

private theorem mirCtxRefines_constr_from {tag : Nat} :
    ∀ (pre : List Expr) {xs ys : List Expr}, ListRel MIRCtxRefines xs ys →
      MIRCtxRefines (.Constr tag (pre ++ xs)) (.Constr tag (pre ++ ys))
  | _, [], [], _ => mirCtxRefines_refl _
  | _, [], _ :: _, h | _, _ :: _, [], h => absurd h id
  | pre, x :: xs, y :: ys, h => by
    refine mirCtxRefines_trans (m₂ := .Constr tag (pre ++ y :: xs))
      (mirCtxRefines_of_context h.1 fun env => ?_) ?_
    · rw [lowerTotalExpr_constr_of_list, lowerTotalExpr_constr_of_list]
      exact list_context (Context.Constr tag · .Hole ·) fun _ _ _ => by simp [fill]
    · simpa using mirCtxRefines_constr_from (pre ++ [y]) h.2

theorem mirCtxRefines_constr {tag : Nat} {m₁ m₂ : Expr} {ms₁ ms₂ : List Expr}
    (hm : MIRCtxRefines m₁ m₂) (hms : ListRel MIRCtxRefines ms₁ ms₂) :
    MIRCtxRefines (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) :=
  mirCtxRefines_constr_from (tag := tag) [] ⟨hm, hms⟩

private theorem mirCtxRefines_case_from {scrut : Expr} :
    ∀ (pre : List Expr) {xs ys : List Expr}, ListRel MIRCtxRefines xs ys →
      MIRCtxRefines (.Case scrut (pre ++ xs)) (.Case scrut (pre ++ ys))
  | _, [], [], _ => mirCtxRefines_refl _
  | _, [], _ :: _, h | _, _ :: _, [], h => absurd h id
  | pre, x :: xs, y :: ys, h => by
    refine mirCtxRefines_trans (m₂ := .Case scrut (pre ++ y :: xs))
      (mirCtxRefines_of_context h.1 fun env => ?_) ?_
    · rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
      cases hs : lowerTotalExpr env scrut with
      | none => exact .inl rfl
      | some st =>
        have h := list_context (env := env) (pre := pre) (post := xs) (a := x) (b := y)
          (F := Moist.Plutus.Term.Term.Case st) (Context.CaseAlt st · .Hole ·)
          fun _ _ _ => by simp [fill]
        simpa only [Option.bind_some, Option.bind_eq_bind, Option.map_eq_bind] using h
    · simpa using mirCtxRefines_case_from (pre ++ [y]) h.2

theorem mirCtxRefines_case {scrut₁ scrut₂ : Expr} {alts₁ alts₂ : List Expr}
    (hscrut : MIRCtxRefines scrut₁ scrut₂)
    (halts : ListRel MIRCtxRefines alts₁ alts₂) :
    MIRCtxRefines (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  refine mirCtxRefines_trans (m₂ := .Case scrut₂ alts₁)
    (mirCtxRefines_of_context hscrut fun env => ?_) (mirCtxRefines_case_from [] halts)
  rw [lowerTotalExpr_case_of_list, lowerTotalExpr_case_of_list]
  cases ha : lowerTotalExprList env alts₁ with
  | none => left; cases lowerTotalExpr env scrut₁ <;> rfl
  | some altsT =>
    refine .inr ⟨env, .Case .Hole altsT, ?_, ?_⟩ <;>
      (cases lowerTotalExpr env _ <;> rfl)

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

omit sv in
/-- Unconditional decomposition: `lowerTotalExpr env (.Let binds body)` equals
    `lowerTotalLet env (expandFixBinds binds) (expandFix body)`. Holds for any
    binds/body, including those containing Fix nodes. The expansion happens
    inside `expandFix` on the Let constructor. -/
theorem lowerTotalExpr_let (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr) :
    lowerTotalExpr env (.Let binds body) =
      lowerTotalLet env (Moist.MIR.expandFixBinds binds) (Moist.MIR.expandFix body) := by
  simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]

omit sv in
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

omit sv in
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
