import Moist.VerifiedNewNew.MIR
import Moist.VerifiedNewNew.DeadLetRefines
import Moist.MIR.Optimize.DCE

/-! # Soundness of MIR Dead Code Elimination

Proves `MIRCtxRefines t (dce t).1` for every fix-free MIR expression `t`:
the optimized program refines the original one (halt-preserving,
error-preserving) under any closing context at every env.

## Proof structure

Structural induction on `t` with a `fixCount t = 0` precondition. For the
leaf and structural-recursion cases we compose the IH through the
corresponding `mirCtxRefines_*` congruence. The `.Fix` case is vacuous
(contradicts `fixCount = 0`). The `.Let` case uses:

  1. Recursively simplified every RHS and the body via per-rhs and body
     congruences.
  2. Removed dead pure bindings via `dead_let_mirRefines` + the
     `mirRefines_to_mirCtxRefines` bridge with a closedness-preservation
     witness derived from `closedAt_shiftRename_unshift`.
  3. Collapsed an empty-binding `Let` into its body.
-/

namespace Moist.VerifiedNewNew.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId dce dceList dceBinds filterBindings
   fixCount fixCountList fixCountBinds
   isPure isPureBinds freeVars
   lowerTotalExpr lowerTotalExpr_eq_lowerTotal lowerTotal lowerTotalLet
   lowerTotal_prepend_unused lowerTotal_prepend_unused_none)
open Moist.VerifiedNewNew (closedAt)
open Moist.VerifiedNewNew.Contextual
  (Context fill ObsRefines CtxRefines
   closedAt_mono
   ctxRefines_refl ctxRefines_trans
   ctxRefines_lam ctxRefines_app
   fill_closedAt_iff)
open Moist.VerifiedNewNew.Equivalence (ListRel)
open Moist.VerifiedNewNew.DeadLet (MIRDeadLetCond lowerTotal_closedAt)
open Moist.VerifiedNewNew.DeadLetRefines (dead_let_mirRefines)

--------------------------------------------------------------------------------
-- 1. closedAt_shiftRename_unshift: inverse of the shift lemma for closedAt
--------------------------------------------------------------------------------

mutual

/-- If a term that has been shifted by `shiftRename c` is closed at `k+1`,
    then the original term is closed at `k` (provided `1 ≤ c ≤ k+1`). The
    cutoff `c` grows by one each time we descend under a binder; starting at
    `c = 1` at depth `k`, the invariant is automatically maintained. -/
private theorem closedAt_shiftRename_unshift :
    ∀ (k c : Nat) (t : Term),
      1 ≤ c → c ≤ k + 1 →
      closedAt (k + 1) (Moist.Verified.renameTerm (Moist.Verified.shiftRename c) t) = true →
      closedAt k t = true
  | k, c, .Var n, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt, decide_eq_true_eq] at h
    simp only [closedAt, decide_eq_true_eq]
    by_cases hn : n ≥ c
    · rw [Moist.Verified.shiftRename_ge hn] at h
      omega
    · have hn' : n < c := Nat.not_le.mp hn
      rw [Moist.Verified.shiftRename_lt hn'] at h
      omega
  | k, c, .Lam _ body, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h
    simp only [closedAt]
    have hlift : Moist.Verified.liftRename (Moist.Verified.shiftRename c) =
        Moist.Verified.shiftRename (c + 1) :=
      Moist.Verified.liftRename_shiftRename hc1
    rw [hlift] at h
    exact closedAt_shiftRename_unshift (k + 1) (c + 1) body (by omega) (by omega) h
  | k, c, .Apply f x, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt, Bool.and_eq_true] at h
    simp only [closedAt, Bool.and_eq_true]
    exact ⟨closedAt_shiftRename_unshift k c f hc1 hc h.1,
           closedAt_shiftRename_unshift k c x hc1 hc h.2⟩
  | k, c, .Force e, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h
    simp only [closedAt]
    exact closedAt_shiftRename_unshift k c e hc1 hc h
  | k, c, .Delay e, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h
    simp only [closedAt]
    exact closedAt_shiftRename_unshift k c e hc1 hc h
  | k, c, .Constr _ args, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt] at h
    simp only [closedAt]
    exact closedAtList_shiftRename_unshift k c args hc1 hc h
  | k, c, .Case scrut alts, hc1, hc, h => by
    simp only [Moist.Verified.renameTerm, closedAt, Bool.and_eq_true] at h
    simp only [closedAt, Bool.and_eq_true]
    exact ⟨closedAt_shiftRename_unshift k c scrut hc1 hc h.1,
           closedAtList_shiftRename_unshift k c alts hc1 hc h.2⟩
  | _, _, .Constant _, _, _, _ => by simp [closedAt]
  | _, _, .Builtin _, _, _, _ => by simp [closedAt]
  | _, _, .Error, _, _, _ => by simp [closedAt]
termination_by _ _ t => sizeOf t

/-- List version of `closedAt_shiftRename_unshift`. -/
private theorem closedAtList_shiftRename_unshift :
    ∀ (k c : Nat) (ts : List Term),
      1 ≤ c → c ≤ k + 1 →
      Moist.VerifiedNewNew.closedAtList (k + 1)
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename c) ts) = true →
      Moist.VerifiedNewNew.closedAtList k ts = true
  | _, _, [], _, _, _ => by simp [Moist.VerifiedNewNew.closedAtList]
  | k, c, t :: rest, hc1, hc, h => by
    simp only [Moist.Verified.renameTermList, Moist.VerifiedNewNew.closedAtList,
      Bool.and_eq_true] at h
    simp only [Moist.VerifiedNewNew.closedAtList, Bool.and_eq_true]
    exact ⟨closedAt_shiftRename_unshift k c t hc1 hc h.1,
           closedAtList_shiftRename_unshift k c rest hc1 hc h.2⟩
termination_by _ _ ts => sizeOf ts

end

--------------------------------------------------------------------------------
-- 2. dce preserves fix-freeness
--------------------------------------------------------------------------------

/-- Appending a single binding is additive on `fixCountBinds`. -/
private theorem fixCountBinds_append_singleton
    (bs : List (VarId × Expr × Bool)) (b : VarId × Expr × Bool) :
    fixCountBinds (bs ++ [b]) = fixCountBinds bs + fixCount b.2.1 := by
  induction bs with
  | nil =>
    obtain ⟨_, _, _⟩ := b
    simp [fixCountBinds]
  | cons head rest ih =>
    obtain ⟨_, _, _⟩ := head
    simp only [List.cons_append, fixCountBinds]
    rw [ih]
    omega

/-- `List.reverse` preserves `fixCountBinds`. -/
private theorem fixCountBinds_reverse (bs : List (VarId × Expr × Bool)) :
    fixCountBinds bs.reverse = fixCountBinds bs := by
  induction bs with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨_, _, _⟩ := head
    simp only [List.reverse_cons, fixCountBinds]
    rw [fixCountBinds_append_singleton rest.reverse _, ih]
    simp only
    omega

/-- `filterBindings` preserves fix-freeness. -/
private theorem filterBindings_preserves_fixCountBinds :
    ∀ (xs : List (VarId × Expr × Bool)) (body : Expr),
      fixCountBinds xs = 0 →
      fixCountBinds (Moist.MIR.filterBindings xs body) = 0
  | [], _, _ => by simp [Moist.MIR.filterBindings, fixCountBinds]
  | (v, rhs, er) :: rest, body, hxs => by
    simp only [fixCountBinds] at hxs
    have hrhs : fixCount rhs = 0 := by omega
    have hrest : fixCountBinds rest = 0 := by omega
    simp only [Moist.MIR.filterBindings]
    have hrest' := filterBindings_preserves_fixCountBinds rest body hrest
    split
    · simp only [fixCountBinds]; omega
    · exact hrest'

mutual

/-- `dce` preserves fix-freeness: if `fixCount e = 0`, then `fixCount (dce e).1 = 0`. -/
private theorem dce_preserves_fixCount : ∀ (e : Expr), fixCount e = 0 → fixCount (dce e).1 = 0
  | .Var _, _ => by simp [dce, fixCount]
  | .Lit _, _ => by simp [dce, fixCount]
  | .Builtin _, _ => by simp [dce, fixCount]
  | .Error, _ => by simp [dce, fixCount]
  | .Lam _ body, h => by
    simp only [fixCount] at h
    simp only [dce, fixCount]
    exact dce_preserves_fixCount body h
  | .Fix _ body, h => by simp only [fixCount] at h; omega
  | .App f a, h => by
    simp only [fixCount] at h
    have hf : fixCount f = 0 := by omega
    have ha : fixCount a = 0 := by omega
    simp only [dce, fixCount]
    have hf' := dce_preserves_fixCount f hf
    have ha' := dce_preserves_fixCount a ha
    omega
  | .Force inner, h => by
    simp only [fixCount] at h
    simp only [dce, fixCount]
    exact dce_preserves_fixCount inner h
  | .Delay inner, h => by
    simp only [fixCount] at h
    simp only [dce, fixCount]
    exact dce_preserves_fixCount inner h
  | .Constr _ args, h => by
    simp only [fixCount] at h
    simp only [dce, fixCount]
    exact dceList_preserves_fixCountList args h
  | .Case scrut alts, h => by
    simp only [fixCount] at h
    have hs : fixCount scrut = 0 := by omega
    have ha : fixCountList alts = 0 := by omega
    simp only [dce, fixCount]
    have hs' := dce_preserves_fixCount scrut hs
    have ha' := dceList_preserves_fixCountList alts ha
    omega
  | .Let binds body, h => by
    simp only [fixCount] at h
    have hbinds : fixCountBinds binds = 0 := by omega
    have hbody : fixCount body = 0 := by omega
    have hbinds' := dceBinds_preserves_fixCountBinds binds hbinds
    have hbody' := dce_preserves_fixCount body hbody
    simp only [dce]
    have hfilter := filterBindings_preserves_fixCountBinds
      (dceBinds binds).1 (dce body).1 hbinds'
    match hfilt : Moist.MIR.filterBindings (dceBinds binds).1 (dce body).1 with
    | [] =>
      rw [hfilt] at hfilter
      exact hbody'
    | s :: rest =>
      rw [hfilt] at hfilter
      simp only [fixCount]
      omega
termination_by e => sizeOf e

private theorem dceList_preserves_fixCountList :
    ∀ (es : List Expr), fixCountList es = 0 → fixCountList (dceList es).1 = 0
  | [], _ => by simp [dceList, fixCountList]
  | e :: rest, h => by
    simp only [fixCountList] at h
    have he : fixCount e = 0 := by omega
    have hr : fixCountList rest = 0 := by omega
    simp only [dceList, fixCountList]
    have he' := dce_preserves_fixCount e he
    have hr' := dceList_preserves_fixCountList rest hr
    omega
termination_by es => sizeOf es

private theorem dceBinds_preserves_fixCountBinds :
    ∀ (bs : List (VarId × Expr × Bool)),
      fixCountBinds bs = 0 → fixCountBinds (dceBinds bs).1 = 0
  | [], _ => by simp [dceBinds, fixCountBinds]
  | (_, rhs, _) :: rest, h => by
    simp only [fixCountBinds] at h
    have hr : fixCount rhs = 0 := by omega
    have hrest : fixCountBinds rest = 0 := by omega
    simp only [dceBinds, fixCountBinds]
    have hr' := dce_preserves_fixCount rhs hr
    have hrest' := dceBinds_preserves_fixCountBinds rest hrest
    omega
termination_by bs => sizeOf bs

end

--------------------------------------------------------------------------------
-- 3. `lowerTotalExpr` on `.Let` when fix-free
--------------------------------------------------------------------------------

/-- `lowerTotalExpr` commutes with `.Let` when the expression is fix-free. -/
private theorem lowerTotalExpr_let_ff (env : List VarId)
    (binds : List (VarId × Expr × Bool)) (body : Expr)
    (hbinds : fixCountBinds binds = 0) (hbody : fixCount body = 0) :
    lowerTotalExpr env (.Let binds body) = lowerTotalLet env binds body := by
  have hfc : fixCount (.Let binds body) = 0 := by
    simp only [fixCount]; omega
  rw [lowerTotalExpr_eq_lowerTotal env _ hfc]
  simp [Moist.MIR.lowerTotal]

--------------------------------------------------------------------------------
-- 4. Helpers for `lowerTotalLet` body swap
--
-- Given `MIRCtxRefines body₁ body₂` and fix-free sub-expressions, swap the
-- body inside any `.Let binds body_i`. Proved via structural induction on
-- `binds`, with `ctxRefines_app` / `ctxRefines_lam` wrapping at each level.
--------------------------------------------------------------------------------

/-- Compile-preservation direction for body swap inside `lowerTotalLet`. -/
private theorem lowerTotalLet_some_body_swap :
    ∀ (binds : List (VarId × Expr × Bool)) (env : List VarId)
      (body₁ body₂ : Expr),
      fixCount body₁ = 0 → fixCount body₂ = 0 →
      MIRCtxRefines body₁ body₂ →
      (lowerTotalLet env binds body₁).isSome →
      (lowerTotalLet env binds body₂).isSome
  | [], env, body₁, body₂, hb₁, hb₂, h, hsome => by
    simp only [lowerTotalLet] at hsome ⊢
    rw [← lowerTotalExpr_eq_lowerTotal env body₁ hb₁] at hsome
    have := h.toImp env hsome
    rwa [← lowerTotalExpr_eq_lowerTotal env body₂ hb₂]
  | (x, rhs, er) :: rest, env, body₁, body₂, hb₁, hb₂, h, hsome => by
    simp only [lowerTotalLet, Option.bind_eq_bind] at hsome ⊢
    cases hrhs : lowerTotal env rhs with
    | none => rw [hrhs] at hsome; simp at hsome
    | some r =>
      rw [hrhs] at hsome
      simp only [Option.bind_some] at hsome
      cases hinner₁ : lowerTotalLet (x :: env) rest body₁ with
      | none => rw [hinner₁] at hsome; simp at hsome
      | some inner₁ =>
        have hinner_some :
            (lowerTotalLet (x :: env) rest body₁).isSome := by rw [hinner₁]; rfl
        have hinner₂_some :=
          lowerTotalLet_some_body_swap rest (x :: env) body₁ body₂ hb₁ hb₂ h hinner_some
        cases hinner₂ : lowerTotalLet (x :: env) rest body₂ with
        | none => rw [hinner₂] at hinner₂_some; exact absurd hinner₂_some (by simp)
        | some inner₂ => simp

/-- CtxRefines-preservation direction for body swap inside `lowerTotalLet`. -/
private theorem lowerTotalLet_ctxRefines_body_swap :
    ∀ (binds : List (VarId × Expr × Bool)) (env : List VarId)
      (body₁ body₂ : Expr),
      fixCount body₁ = 0 → fixCount body₂ = 0 →
      MIRCtxRefines body₁ body₂ →
      ∀ t₁ t₂,
        lowerTotalLet env binds body₁ = some t₁ →
        lowerTotalLet env binds body₂ = some t₂ →
        CtxRefines t₁ t₂
  | [], env, body₁, body₂, hb₁, hb₂, h, t₁, t₂, hlow₁, hlow₂ => by
    simp only [lowerTotalLet] at hlow₁ hlow₂
    have ⟨_, hobs⟩ := h env
    rw [← lowerTotalExpr_eq_lowerTotal env body₁ hb₁] at hlow₁
    rw [← lowerTotalExpr_eq_lowerTotal env body₂ hb₂] at hlow₂
    rw [hlow₁, hlow₂] at hobs
    exact hobs
  | (x, rhs, er) :: rest, env, body₁, body₂, hb₁, hb₂, h, t₁, t₂, hlow₁, hlow₂ => by
    simp only [lowerTotalLet, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlow₁ hlow₂
    obtain ⟨r₁, hr₁, inner₁, hinner₁, heq₁⟩ := hlow₁
    obtain ⟨r₂, hr₂, inner₂, hinner₂, heq₂⟩ := hlow₂
    have hreq : r₁ = r₂ := by rw [hr₁] at hr₂; injection hr₂
    subst hreq
    injection heq₁ with heq₁
    injection heq₂ with heq₂
    subst heq₁; subst heq₂
    have ih_inner := lowerTotalLet_ctxRefines_body_swap rest (x :: env) body₁ body₂ hb₁ hb₂ h
      inner₁ inner₂ hinner₁ hinner₂
    exact ctxRefines_app (ctxRefines_lam 0 ih_inner) (ctxRefines_refl _)

/-- MIR-level body swap congruence for `.Let` under a fix-free binding list. -/
private theorem mirCtxRefines_let_body_ff
    {binds : List (VarId × Expr × Bool)} {body₁ body₂ : Expr}
    (hbinds : fixCountBinds binds = 0)
    (hbody₁ : fixCount body₁ = 0) (hbody₂ : fixCount body₂ = 0)
    (h : MIRCtxRefines body₁ body₂) :
    MIRCtxRefines (.Let binds body₁) (.Let binds body₂) := by
  intro env
  rw [lowerTotalExpr_let_ff env binds body₁ hbinds hbody₁,
      lowerTotalExpr_let_ff env binds body₂ hbinds hbody₂]
  refine ⟨?_, ?_⟩
  · exact lowerTotalLet_some_body_swap binds env body₁ body₂ hbody₁ hbody₂ h
  · cases h₁ : lowerTotalLet env binds body₁ with
    | none => trivial
    | some t₁ =>
      cases h₂ : lowerTotalLet env binds body₂ with
      | none => trivial
      | some t₂ =>
        exact lowerTotalLet_ctxRefines_body_swap binds env body₁ body₂ hbody₁ hbody₂ h
          t₁ t₂ h₁ h₂

--------------------------------------------------------------------------------
-- 5. MIR-level head-rhs congruence for `.Let`
--------------------------------------------------------------------------------

/-- MIR-level head-rhs swap congruence for `.Let` under a fix-free binding
    list and body. -/
private theorem mirCtxRefines_let_rhs_head_ff
    {x : VarId} {rhs₁ rhs₂ : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (hrhs₁ : fixCount rhs₁ = 0) (hrhs₂ : fixCount rhs₂ = 0)
    (hrest : fixCountBinds rest = 0) (hbody : fixCount body = 0)
    (h : MIRCtxRefines rhs₁ rhs₂) :
    MIRCtxRefines (.Let ((x, rhs₁, er) :: rest) body)
                  (.Let ((x, rhs₂, er) :: rest) body) := by
  intro env
  have hbinds₁ : fixCountBinds ((x, rhs₁, er) :: rest) = 0 := by
    simp only [fixCountBinds]; omega
  have hbinds₂ : fixCountBinds ((x, rhs₂, er) :: rest) = 0 := by
    simp only [fixCountBinds]; omega
  rw [lowerTotalExpr_let_ff env _ body hbinds₁ hbody,
      lowerTotalExpr_let_ff env _ body hbinds₂ hbody]
  simp only [lowerTotalLet, Option.bind_eq_bind]
  refine ⟨?_, ?_⟩
  · -- Compile preservation: rhs₁ lowers ⇒ rhs₂ lowers (via `h`),
    -- the inner `rest + body` lowering is identical.
    intro hsome
    cases hrhs₁_low : lowerTotal env rhs₁ with
    | none => rw [hrhs₁_low] at hsome; simp at hsome
    | some r₁ =>
      rw [hrhs₁_low] at hsome; simp only [Option.bind_some] at hsome
      have hrhs₁_exp : (lowerTotalExpr env rhs₁).isSome := by
        rw [lowerTotalExpr_eq_lowerTotal env rhs₁ hrhs₁, hrhs₁_low]; rfl
      have hrhs₂_exp : (lowerTotalExpr env rhs₂).isSome := h.toImp env hrhs₁_exp
      rw [lowerTotalExpr_eq_lowerTotal env rhs₂ hrhs₂] at hrhs₂_exp
      cases hrhs₂_low : lowerTotal env rhs₂ with
      | none => rw [hrhs₂_low] at hrhs₂_exp; exact absurd hrhs₂_exp (by simp)
      | some r₂ =>
        simp only [Option.bind_some]
        cases hinner : lowerTotalLet (x :: env) rest body with
        | none => rw [hinner] at hsome; simp at hsome
        | some inner => simp
  · cases hrhs₁_low : lowerTotal env rhs₁ with
    | none => simp
    | some r₁ =>
      simp only [Option.bind_some]
      cases hrhs₂_low : lowerTotal env rhs₂ with
      | none => simp
      | some r₂ =>
        simp only [Option.bind_some]
        cases hinner : lowerTotalLet (x :: env) rest body with
        | none => simp
        | some inner =>
          simp only [Option.bind_some]
          -- Goal: CtxRefines (Apply (Lam 0 inner) r₁) (Apply (Lam 0 inner) r₂)
          -- via h.toCtxRefines on rhs.
          have hr_ref : CtxRefines r₁ r₂ := by
            have ⟨_, hobs⟩ := h env
            rw [lowerTotalExpr_eq_lowerTotal env rhs₁ hrhs₁,
                lowerTotalExpr_eq_lowerTotal env rhs₂ hrhs₂,
                hrhs₁_low, hrhs₂_low] at hobs
            exact hobs
          exact ctxRefines_app (ctxRefines_refl _) hr_ref

--------------------------------------------------------------------------------
-- 6. Empty let collapse
--------------------------------------------------------------------------------

/-- An empty `.Let [] body` is `MIRCtxRefines`-equivalent to `body` (when
    `body` is fix-free). The two expressions lower to the same UPLC term. -/
private theorem mirCtxRefines_let_nil_ff {body : Expr} (hbody : fixCount body = 0) :
    MIRCtxRefines (.Let [] body) body := by
  intro env
  rw [lowerTotalExpr_let_ff env [] body (by simp [fixCountBinds]) hbody]
  simp only [lowerTotalLet]
  rw [← lowerTotalExpr_eq_lowerTotal env body hbody]
  refine ⟨id, ?_⟩
  cases hlow : lowerTotalExpr env body with
  | none => trivial
  | some t => exact ctxRefines_refl t

--------------------------------------------------------------------------------
-- 7. Dead let bridge: MIRDeadLetCond → MIRCtxRefines
--
-- Uses `dead_let_mirRefines` (which gives `MIRRefines`) + the
-- `mirRefines_to_mirCtxRefines` bridge. The required closedness
-- preservation uses `closedAt_shiftRename_unshift` to strip the extra
-- `Apply (Lam 0 body_shifted) rhs` wrapper.
--------------------------------------------------------------------------------

/-- The `er` flag in a let binding doesn't affect the lowering, so any
    let with arbitrary `er` is `MIRCtxRefines`-equivalent to the same let
    with `er := false`. -/
private theorem lowerTotalLet_er_eq (env : List VarId) (x : VarId) (e body : Expr) (er : Bool) :
    lowerTotalLet env [(x, e, er)] body = lowerTotalLet env [(x, e, false)] body := by
  simp only [lowerTotalLet]

private theorem mirCtxRefines_let_er_normalize
    (x : VarId) (e body : Expr) (er : Bool)
    (he : fixCount e = 0) (hbody : fixCount body = 0) :
    MIRCtxRefines (.Let [(x, e, er)] body) (.Let [(x, e, false)] body) := by
  intro env
  have hbinds_er : fixCountBinds [(x, e, er)] = 0 := by
    simp only [fixCountBinds]; omega
  have hbinds_false : fixCountBinds [(x, e, false)] = 0 := by
    simp only [fixCountBinds]; omega
  rw [lowerTotalExpr_let_ff env _ body hbinds_er hbody,
      lowerTotalExpr_let_ff env _ body hbinds_false hbody,
      lowerTotalLet_er_eq env x e body er]
  refine ⟨id, ?_⟩
  cases h : lowerTotalLet env [(x, e, false)] body with
  | none => trivial
  | some t => exact ctxRefines_refl t

private theorem dead_let_mirCtxRefines {x : VarId} {e body : Expr}
    (hcond : MIRDeadLetCond x e body) :
    MIRCtxRefines (.Let [(x, e, false)] body) body := by
  refine mirRefines_to_mirCtxRefines (dead_let_mirRefines hcond) ?_
  intro env k t₁ t₂ hlow₁ hlow₂ hclosed
  -- `.Let [(x, e, false)] body` lowers to `Apply (Lam 0 body_shifted) e_t`,
  -- where `body_shifted = renameTerm (shiftRename 1) body_t` and body_t is
  -- the lowering of body under env. We need closedAt k t₂.
  have hunused := hcond.unused
  have hfix_sum := hcond.fixFree
  have hfix_e : fixCount e = 0 := by omega
  have hfix_body : fixCount body = 0 := by omega
  have hfc_let : fixCount (.Let [(x, e, false)] body) = 0 := by
    simp only [fixCount, fixCountBinds]; omega
  rw [lowerTotalExpr_eq_lowerTotal env _ hfc_let] at hlow₁
  rw [lowerTotalExpr_eq_lowerTotal env body hfix_body] at hlow₂
  -- hlow₁ : lowerTotal env (.Let [(x, e, false)] body) = some t₁
  -- Unfold: it's lowerTotalLet env [(x, e, false)] body
  simp only [Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hlow₁
  obtain ⟨e_t, he_t, rest_t, hrest_t, heq⟩ := hlow₁
  -- hrest_t : lowerTotal (x :: env) body = some rest_t
  -- heq : some (Apply (Lam 0 rest_t) e_t) = some t₁
  injection heq with heq
  subst heq
  -- Now t₁ = Apply (Lam 0 rest_t) e_t
  -- Body lowered under (x :: env), and since x is unused in body:
  have hshift := lowerTotal_prepend_unused env x body hunused t₂ hlow₂
  -- hshift : lowerTotal (x :: env) body = some (renameTerm (shiftRename 1) t₂)
  rw [hrest_t] at hshift
  injection hshift with hshift
  -- hshift : rest_t = renameTerm (shiftRename 1) t₂
  subst hshift
  -- Now goal: closedAt k t₂
  -- From hclosed: closedAt k (Apply (Lam 0 (renameTerm (shiftRename 1) t₂)) e_t)
  simp only [closedAt, Bool.and_eq_true] at hclosed
  -- hclosed.1 : closedAt (k + 1) (renameTerm (shiftRename 1) t₂)
  -- hclosed.2 : closedAt k e_t
  -- We need closedAt k t₂, using closedAt_shiftRename_unshift.
  -- The invariant `c ≤ k + 1` with c = 1 is always satisfied (k ≥ 0).
  exact closedAt_shiftRename_unshift k 1 t₂ (by omega) (by omega) hclosed.1

--------------------------------------------------------------------------------
-- 8. Binds-list congruence for .Let
--
-- Given per-rhs `MIRCtxRefines` pairings between `binds₁` and `binds₂`
-- (matching names, same `er`, fix-free), swap the binds in a `.Let`.
-- Proved by induction on `binds₁`, using `mirCtxRefines_let_rhs_head_ff`
-- at each step to swap the head rhs, then a body swap via
-- `mirCtxRefines_let_body_ff` applied with a recursive inner-Let swap.
--------------------------------------------------------------------------------

/-- Swap the head rhs's rhs in a `.Let`, with compile preservation. -/
private theorem mirCtxRefines_let_binds_congr_ff :
    ∀ (binds₁ binds₂ : List (VarId × Expr × Bool)) (body : Expr),
      fixCountBinds binds₁ = 0 → fixCountBinds binds₂ = 0 → fixCount body = 0 →
      ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                            MIRCtxRefines b₁.2.1 b₂.2.1) binds₁ binds₂ →
      MIRCtxRefines (.Let binds₁ body) (.Let binds₂ body)
  | [], [], body, _, _, _, _ => mirCtxRefines_refl _
  | [], _ :: _, _, _, _, _, hrel => absurd hrel id
  | _ :: _, [], _, _, _, _, hrel => absurd hrel id
  | (v₁, rhs₁, er₁) :: rest₁, (v₂, rhs₂, er₂) :: rest₂, body,
    hb₁, hb₂, hbody, hrel => by
    simp only [fixCountBinds] at hb₁ hb₂
    have hrhs₁ : fixCount rhs₁ = 0 := by omega
    have hrhs₂ : fixCount rhs₂ = 0 := by omega
    have hrest₁ : fixCountBinds rest₁ = 0 := by omega
    have hrest₂ : fixCountBinds rest₂ = 0 := by omega
    obtain ⟨⟨hname, her, hrhs_ref⟩, hrel_rest⟩ := hrel
    subst hname; subst her
    -- Step 1: swap head rhs from rhs₁ to rhs₂.
    have h_step1 : MIRCtxRefines (.Let ((v₁, rhs₁, er₁) :: rest₁) body)
                                  (.Let ((v₁, rhs₂, er₁) :: rest₁) body) :=
      mirCtxRefines_let_rhs_head_ff hrhs₁ hrhs₂ hrest₁ hbody hrhs_ref
    -- Step 2: swap body from `.Let rest₁ body` to `.Let rest₂ body` inside
    -- the single-binding Let, via unroll + body swap + reroll.
    -- Unroll and reroll are via `mirCtxRefines_refl` on identical lowerings
    -- (which is handled implicitly by treating `.Let ((v, r, er) :: rest) body`
    -- and `.Let [(v, r, er)] (.Let rest body)` as having the same lowering).
    -- We use `mirCtxRefines_let_body_ff` on the outer single-binding Let.
    have hrest_ref : MIRCtxRefines (.Let rest₁ body) (.Let rest₂ body) :=
      mirCtxRefines_let_binds_congr_ff rest₁ rest₂ body hrest₁ hrest₂ hbody hrel_rest
    have hrest_body₁ : fixCount (Expr.Let rest₁ body) = 0 := by
      simp only [fixCount]; omega
    have hrest_body₂ : fixCount (Expr.Let rest₂ body) = 0 := by
      simp only [fixCount]; omega
    -- A single-binding let with body `.Let rest₁ body` swapped to `.Let rest₂ body`.
    have h_single_swap :
        MIRCtxRefines (.Let [(v₁, rhs₂, er₁)] (.Let rest₁ body))
                      (.Let [(v₁, rhs₂, er₁)] (.Let rest₂ body)) :=
      mirCtxRefines_let_body_ff (by simp [fixCountBinds, hrhs₂])
        hrest_body₁ hrest_body₂ hrest_ref
    -- Identical lowerings between `.Let ((v, r, er) :: rest) body` and
    -- `.Let [(v, r, er)] (.Let rest body)`.
    have hlow_eq : ∀ (rest_x : List (VarId × Expr × Bool)) env,
        fixCountBinds rest_x = 0 → fixCount body = 0 →
        lowerTotalExpr env (.Let ((v₁, rhs₂, er₁) :: rest_x) body) =
        lowerTotalExpr env (.Let [(v₁, rhs₂, er₁)] (.Let rest_x body)) := by
      intro rest_x env hrest_x hbody_x
      have hbinds_cons : fixCountBinds ((v₁, rhs₂, er₁) :: rest_x) = 0 := by
        simp only [fixCountBinds]; omega
      have hrest_body_x : fixCount (Expr.Let rest_x body) = 0 := by
        simp only [fixCount]; omega
      rw [lowerTotalExpr_let_ff env _ _ hbinds_cons hbody_x,
          lowerTotalExpr_let_ff env [(v₁, rhs₂, er₁)] _
            (by simp [fixCountBinds, hrhs₂]) hrest_body_x]
      show lowerTotalLet env ((v₁, rhs₂, er₁) :: rest_x) body =
           lowerTotalLet env [(v₁, rhs₂, er₁)] (.Let rest_x body)
      simp only [lowerTotalLet, Moist.MIR.lowerTotal]
    have hunroll : MIRCtxRefines (.Let ((v₁, rhs₂, er₁) :: rest₁) body)
                                  (.Let [(v₁, rhs₂, er₁)] (.Let rest₁ body)) := by
      intro env
      rw [hlow_eq rest₁ env hrest₁ hbody]
      refine ⟨id, ?_⟩
      cases h : lowerTotalExpr env (.Let [(v₁, rhs₂, er₁)] (.Let rest₁ body)) with
      | none => trivial
      | some t => exact ctxRefines_refl t
    have hreroll : MIRCtxRefines (.Let [(v₁, rhs₂, er₁)] (.Let rest₂ body))
                                  (.Let ((v₁, rhs₂, er₁) :: rest₂) body) := by
      intro env
      rw [← hlow_eq rest₂ env hrest₂ hbody]
      refine ⟨id, ?_⟩
      cases h : lowerTotalExpr env (.Let ((v₁, rhs₂, er₁) :: rest₂) body) with
      | none => trivial
      | some t => exact ctxRefines_refl t
    -- Chain all steps via transitivity.
    exact mirCtxRefines_trans h_step1
      (mirCtxRefines_trans hunroll
        (mirCtxRefines_trans h_single_swap hreroll))
termination_by binds₁ _ _ _ _ _ _ => List.length binds₁

--------------------------------------------------------------------------------
-- 9. Let-list split: `.Let (xs ++ ys) body ≈ .Let xs (.Let ys body)`
--
-- Both sides have identical UPLC lowerings (when fix-free).
--------------------------------------------------------------------------------

/-- `fixCountBinds` is additive over `++`. -/
private theorem fixCountBinds_append :
    ∀ (xs ys : List (VarId × Expr × Bool)),
      fixCountBinds (xs ++ ys) = fixCountBinds xs + fixCountBinds ys
  | [], _ => by simp [fixCountBinds]
  | (v, rhs, er) :: rest, ys => by
    simp only [List.cons_append, fixCountBinds]
    rw [fixCountBinds_append rest ys]
    omega

private theorem lowerTotalLet_append :
    ∀ (xs ys : List (VarId × Expr × Bool)) (env : List VarId) (body : Expr),
      lowerTotalLet env (xs ++ ys) body =
      lowerTotalLet env xs (.Let ys body)
  | [], ys, env, body => by
    simp only [List.nil_append, lowerTotalLet, Moist.MIR.lowerTotal]
  | (x, rhs, er) :: rest, ys, env, body => by
    simp only [List.cons_append, lowerTotalLet]
    have ih := lowerTotalLet_append rest ys (x :: env) body
    rw [ih]

private theorem mirCtxRefines_let_append
    (xs ys : List (VarId × Expr × Bool)) (body : Expr)
    (hxs : fixCountBinds xs = 0) (hys : fixCountBinds ys = 0)
    (hbody : fixCount body = 0) :
    MIRCtxRefines (.Let (xs ++ ys) body) (.Let xs (.Let ys body)) := by
  intro env
  have hbinds_app : fixCountBinds (xs ++ ys) = 0 := by
    rw [fixCountBinds_append]; omega
  have hlet_ys : fixCount (Expr.Let ys body) = 0 := by
    simp only [fixCount]; omega
  rw [lowerTotalExpr_let_ff env (xs ++ ys) body hbinds_app hbody,
      lowerTotalExpr_let_ff env xs _ hxs hlet_ys,
      lowerTotalLet_append xs ys env body]
  refine ⟨id, ?_⟩
  cases h : lowerTotalLet env xs (.Let ys body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

private theorem mirCtxRefines_let_unappend
    (xs ys : List (VarId × Expr × Bool)) (body : Expr)
    (hxs : fixCountBinds xs = 0) (hys : fixCountBinds ys = 0)
    (hbody : fixCount body = 0) :
    MIRCtxRefines (.Let xs (.Let ys body)) (.Let (xs ++ ys) body) := by
  intro env
  have hbinds_app : fixCountBinds (xs ++ ys) = 0 := by
    rw [fixCountBinds_append]; omega
  have hlet_ys : fixCount (Expr.Let ys body) = 0 := by
    simp only [fixCount]; omega
  rw [lowerTotalExpr_let_ff env (xs ++ ys) body hbinds_app hbody,
      lowerTotalExpr_let_ff env xs _ hxs hlet_ys,
      lowerTotalLet_append xs ys env body]
  refine ⟨id, ?_⟩
  cases h : lowerTotalLet env xs (.Let ys body) with
  | none => trivial
  | some t => exact ctxRefines_refl t

--------------------------------------------------------------------------------
-- 10. filterBindings walk: simulates filterBindings via dead_let_mirCtxRefines
--------------------------------------------------------------------------------

private theorem filterBindings_mirCtxRefines :
    ∀ (binds : List (VarId × Expr × Bool)) (body : Expr),
      fixCountBinds binds = 0 → fixCount body = 0 →
      MIRCtxRefines (.Let binds body)
        (match Moist.MIR.filterBindings binds body with
         | [] => body
         | s :: rest => .Let (s :: rest) body)
  | [], body, _, hbody => by
    simp only [Moist.MIR.filterBindings]
    exact mirCtxRefines_let_nil_ff hbody
  | (v, rhs, er) :: rest, body, hbinds, hbody => by
    simp only [fixCountBinds] at hbinds
    have hrhs : fixCount rhs = 0 := by omega
    have hrest : fixCountBinds rest = 0 := by omega
    -- Recurse on rest
    have ih := filterBindings_mirCtxRefines rest body hrest hbody
    -- Compute the filtered tail
    have hrest_filt : fixCountBinds (Moist.MIR.filterBindings rest body) = 0 :=
      filterBindings_preserves_fixCountBinds rest body hrest
    -- Step 1: unroll head: .Let ((v, rhs, er) :: rest) body ≈ .Let [(v, rhs, er)] (.Let rest body)
    have hrest_body : fixCount (Expr.Let rest body) = 0 := by
      simp only [fixCount]; omega
    have hbinds_singleton : fixCountBinds [(v, rhs, er)] = 0 := by
      simp only [fixCountBinds]; omega
    have hbinds_cons : fixCountBinds ((v, rhs, er) :: rest) = 0 := by
      simp only [fixCountBinds]; omega
    have hunroll :
        MIRCtxRefines (.Let ((v, rhs, er) :: rest) body)
                      (.Let [(v, rhs, er)] (.Let rest body)) := by
      have hlow_eq : ∀ env,
          lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
          lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) := by
        intro env
        rw [lowerTotalExpr_let_ff env _ _ hbinds_cons hbody,
            lowerTotalExpr_let_ff env _ _ hbinds_singleton hrest_body]
        show lowerTotalLet env ((v, rhs, er) :: rest) body =
             lowerTotalLet env [(v, rhs, er)] (.Let rest body)
        simp only [lowerTotalLet, Moist.MIR.lowerTotal]
      intro env
      rw [hlow_eq env]
      refine ⟨id, ?_⟩
      cases h : lowerTotalExpr env (.Let [(v, rhs, er)] (.Let rest body)) with
      | none => trivial
      | some t => exact ctxRefines_refl t
    -- Step 2: swap inner body via IH
    -- We have: ih : MIRCtxRefines (.Let rest body) (filterResult rest body)
    -- We want: MIRCtxRefines (.Let [(v, rhs, er)] (.Let rest body)) (.Let [(v, rhs, er)] filterResult)
    -- Use mirCtxRefines_let_body_ff applied to the singleton-binding outer Let.
    -- Cases on filterBindings rest body to determine the inner shape.
    cases hrest_filt_eq : Moist.MIR.filterBindings rest body with
    | nil =>
      have ih' : MIRCtxRefines (.Let rest body) body := by
        rw [hrest_filt_eq] at ih; exact ih
      have h_inner_swap :
          MIRCtxRefines (.Let [(v, rhs, er)] (.Let rest body))
                        (.Let [(v, rhs, er)] body) := by
        exact mirCtxRefines_let_body_ff hbinds_singleton hrest_body hbody ih'
      simp only [Moist.MIR.filterBindings, hrest_filt_eq]
      cases hfree : (freeVars (Expr.Let [] body)).contains v with
      | true =>
        simp only [Bool.true_or, ↓reduceIte]
        exact mirCtxRefines_trans hunroll h_inner_swap
      | false =>
        cases hpure_check : isPure rhs with
        | true =>
          simp only [Bool.false_or, Bool.not_true]
          have hcond_v : (freeVars body).contains v = false := by
            have hh : (freeVars (Expr.Let [] body)).contains v = false := hfree
            show (freeVars body).contains v = false
            simp only [freeVars, Moist.MIR.freeVarsLet] at hh
            exact hh
          have h_er_norm :
              MIRCtxRefines (.Let [(v, rhs, er)] body) (.Let [(v, rhs, false)] body) :=
            mirCtxRefines_let_er_normalize v rhs body er hrhs hbody
          have h_dead :
              MIRCtxRefines (.Let [(v, rhs, false)] body) body := by
            apply dead_let_mirCtxRefines
            exact { unused := hcond_v
                    fixFree := by omega
                    safe := hpure_check }
          exact mirCtxRefines_trans hunroll
            (mirCtxRefines_trans h_inner_swap
              (mirCtxRefines_trans h_er_norm h_dead))
        | false =>
          simp only [Bool.false_or, Bool.not_false, ↓reduceIte]
          exact mirCtxRefines_trans hunroll h_inner_swap
    | cons s' rest' =>
      -- ih : MIRCtxRefines (.Let rest body) (.Let (s' :: rest') body)
      have ih' : MIRCtxRefines (.Let rest body) (.Let (s' :: rest') body) := by
        rw [hrest_filt_eq] at ih; exact ih
      have hfilt_ne_eq := hrest_filt_eq
      have hsr_fc : fixCountBinds (s' :: rest') = 0 := by
        rw [← hrest_filt_eq]; exact hrest_filt
      have hsr_let_fc : fixCount (Expr.Let (s' :: rest') body) = 0 := by
        simp only [fixCount]; omega
      have h_inner_swap :
          MIRCtxRefines (.Let [(v, rhs, er)] (.Let rest body))
                        (.Let [(v, rhs, er)] (.Let (s' :: rest') body)) := by
        exact mirCtxRefines_let_body_ff hbinds_singleton hrest_body hsr_let_fc ih'
      -- Step 3: reroll: .Let [(v, rhs, er)] (.Let (s' :: rest') body) ≈ .Let ((v, rhs, er) :: s' :: rest') body
      have hreroll :
          MIRCtxRefines (.Let [(v, rhs, er)] (.Let (s' :: rest') body))
                        (.Let ((v, rhs, er) :: s' :: rest') body) := by
        intro env
        have hbinds_cons' : fixCountBinds ((v, rhs, er) :: s' :: rest') = 0 := by
          simp only [fixCountBinds]; omega
        have hlow_eq :
            lowerTotalExpr env (.Let [(v, rhs, er)] (.Let (s' :: rest') body)) =
            lowerTotalExpr env (.Let ((v, rhs, er) :: s' :: rest') body) := by
          rw [lowerTotalExpr_let_ff env _ _ hbinds_singleton hsr_let_fc,
              lowerTotalExpr_let_ff env _ _ hbinds_cons' hbody]
          show lowerTotalLet env [(v, rhs, er)] (.Let (s' :: rest') body) =
               lowerTotalLet env ((v, rhs, er) :: s' :: rest') body
          simp only [lowerTotalLet, Moist.MIR.lowerTotal]
        rw [hlow_eq]
        refine ⟨id, ?_⟩
        cases h : lowerTotalExpr env (.Let ((v, rhs, er) :: s' :: rest') body) with
        | none => trivial
        | some t => exact ctxRefines_refl t
      simp only [Moist.MIR.filterBindings, hrest_filt_eq]
      cases hfree : (freeVars (Expr.Let (s' :: rest') body)).contains v with
      | true =>
        simp only [Bool.true_or, ↓reduceIte]
        exact mirCtxRefines_trans hunroll
          (mirCtxRefines_trans h_inner_swap hreroll)
      | false =>
        cases hpure_check : isPure rhs with
        | true =>
          simp only [Bool.false_or, Bool.not_true]
          have h_er_norm :
              MIRCtxRefines (.Let [(v, rhs, er)] (.Let (s' :: rest') body))
                            (.Let [(v, rhs, false)] (.Let (s' :: rest') body)) :=
            mirCtxRefines_let_er_normalize v rhs (.Let (s' :: rest') body) er hrhs hsr_let_fc
          have h_dead :
              MIRCtxRefines (.Let [(v, rhs, false)] (.Let (s' :: rest') body))
                            (.Let (s' :: rest') body) := by
            apply dead_let_mirCtxRefines
            exact { unused := hfree
                    fixFree := by omega
                    safe := hpure_check }
          exact mirCtxRefines_trans hunroll
            (mirCtxRefines_trans h_inner_swap
              (mirCtxRefines_trans h_er_norm h_dead))
        | false =>
          simp only [Bool.false_or, Bool.not_false, ↓reduceIte]
          exact mirCtxRefines_trans hunroll
            (mirCtxRefines_trans h_inner_swap hreroll)
termination_by binds _ _ _ => List.length binds

--------------------------------------------------------------------------------
-- 11. Main theorem: dce soundness
--------------------------------------------------------------------------------

mutual

/-- `dce` is sound: it preserves `MIRCtxRefines`. The `fixCount t = 0`
    precondition makes the `.Fix` case vacuous (the lowering of `Fix` requires
    `expandFix` machinery that we don't reason about here). -/
theorem dce_mirCtxRefines : ∀ (t : Expr), fixCount t = 0 → MIRCtxRefines t (dce t).1
  | .Var _, _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Lit _, _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Builtin _, _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Error, _ => by simp only [dce]; exact mirCtxRefines_refl _
  | .Lam x body, h => by
    simp only [fixCount] at h
    simp only [dce]
    exact mirCtxRefines_lam (dce_mirCtxRefines body h)
  | .Force inner, h => by
    simp only [fixCount] at h
    simp only [dce]
    exact mirCtxRefines_force (dce_mirCtxRefines inner h)
  | .Delay inner, h => by
    simp only [fixCount] at h
    simp only [dce]
    exact mirCtxRefines_delay (dce_mirCtxRefines inner h)
  | .App fn arg, h => by
    simp only [fixCount] at h
    have hf : fixCount fn = 0 := by omega
    have ha : fixCount arg = 0 := by omega
    simp only [dce]
    exact mirCtxRefines_app (dce_mirCtxRefines fn hf) (dce_mirCtxRefines arg ha)
  | .Fix _ body, h => by
    simp only [fixCount] at h
    omega
  | .Constr tag args, h => by
    simp only [fixCount] at h
    simp only [dce]
    cases args with
    | nil =>
      simp only [dceList]
      exact mirCtxRefines_refl _
    | cons e rest =>
      simp only [dceList]
      simp only [fixCountList] at h
      have he : fixCount e = 0 := by omega
      have hr : fixCountList rest = 0 := by omega
      exact mirCtxRefines_constr (dce_mirCtxRefines e he) (dceList_listRel rest hr)
  | .Case scrut alts, h => by
    simp only [fixCount] at h
    have hs : fixCount scrut = 0 := by omega
    have ha : fixCountList alts = 0 := by omega
    simp only [dce]
    cases alts with
    | nil =>
      simp only [dceList]
      exact mirCtxRefines_case (dce_mirCtxRefines scrut hs) True.intro
    | cons a rest =>
      simp only [dceList]
      simp only [fixCountList] at ha
      have hae : fixCount a = 0 := by omega
      have har : fixCountList rest = 0 := by omega
      exact mirCtxRefines_case
        (dce_mirCtxRefines scrut hs)
        ⟨dce_mirCtxRefines a hae, dceList_listRel rest har⟩
  | .Let binds body, h => by
    simp only [fixCount] at h
    have hbinds : fixCountBinds binds = 0 := by omega
    have hbody : fixCount body = 0 := by omega
    have hbody' : fixCount (dce body).1 = 0 := dce_preserves_fixCount body hbody
    have hbinds' : fixCountBinds (dceBinds binds).1 = 0 :=
      dceBinds_preserves_fixCountBinds binds hbinds
    -- Step 1: swap each rhs via dceBinds (binds congruence)
    have h_binds_swap :
        MIRCtxRefines (.Let binds body) (.Let (dceBinds binds).1 body) := by
      apply mirCtxRefines_let_binds_congr_ff binds (dceBinds binds).1 body
        hbinds hbinds' hbody
      exact dceBinds_listRel binds hbinds
    -- Step 2: swap body via dce
    have h_body_swap :
        MIRCtxRefines (.Let (dceBinds binds).1 body) (.Let (dceBinds binds).1 (dce body).1) :=
      mirCtxRefines_let_body_ff hbinds' hbody hbody' (dce_mirCtxRefines body hbody)
    -- Step 3: filterBindings walk
    have h_filter :
        MIRCtxRefines (.Let (dceBinds binds).1 (dce body).1)
          (match Moist.MIR.filterBindings (dceBinds binds).1 (dce body).1 with
           | [] => (dce body).1
           | s :: rest => .Let (s :: rest) (dce body).1) :=
      filterBindings_mirCtxRefines (dceBinds binds).1 (dce body).1 hbinds' hbody'
    -- Step 4: equate the filter result with `(dce (.Let binds body)).1`
    simp only [dce]
    cases hfilt : Moist.MIR.filterBindings (dceBinds binds).1 (dce body).1 with
    | nil =>
      have h_filter' :
          MIRCtxRefines (.Let (dceBinds binds).1 (dce body).1) (dce body).1 := by
        rw [hfilt] at h_filter; exact h_filter
      simp only
      exact mirCtxRefines_trans h_binds_swap (mirCtxRefines_trans h_body_swap h_filter')
    | cons s rest =>
      have h_filter' :
          MIRCtxRefines (.Let (dceBinds binds).1 (dce body).1)
                        (.Let (s :: rest) (dce body).1) := by
        rw [hfilt] at h_filter; exact h_filter
      simp only
      exact mirCtxRefines_trans h_binds_swap (mirCtxRefines_trans h_body_swap h_filter')
  termination_by t => sizeOf t

/-- List-level DCE soundness: every element pair is `MIRCtxRefines`. -/
theorem dceList_listRel : ∀ (ts : List Expr),
    fixCountList ts = 0 →
    ListRel MIRCtxRefines ts (dceList ts).1
  | [], _ => by simp only [dceList]; exact True.intro
  | e :: rest, h => by
    simp only [fixCountList] at h
    have he : fixCount e = 0 := by omega
    have hr : fixCountList rest = 0 := by omega
    simp only [dceList]
    exact ⟨dce_mirCtxRefines e he, dceList_listRel rest hr⟩
  termination_by ts => sizeOf ts

/-- Per-binding DCE soundness: each rhs's pair is `MIRCtxRefines`,
    names and `er` flags are preserved. -/
theorem dceBinds_listRel : ∀ (bs : List (VarId × Expr × Bool)),
    fixCountBinds bs = 0 →
    ListRel (fun b₁ b₂ => b₁.1 = b₂.1 ∧ b₁.2.2 = b₂.2.2 ∧
                          MIRCtxRefines b₁.2.1 b₂.2.1) bs (dceBinds bs).1
  | [], _ => by simp only [dceBinds]; exact True.intro
  | (v, rhs, er) :: rest, h => by
    simp only [fixCountBinds] at h
    have hr : fixCount rhs = 0 := by omega
    have hrest : fixCountBinds rest = 0 := by omega
    simp only [dceBinds]
    refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
    · exact dce_mirCtxRefines rhs hr
    · exact dceBinds_listRel rest hrest
  termination_by bs => sizeOf bs

end

end Moist.VerifiedNewNew.MIR
