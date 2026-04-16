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

/-! ## Section 5. Let-hoist-force primitive

`.Force (.Let [(v, rhs, false)] body) ≈ .Let [(v, rhs, false)] (.Force body)`.

The non-trivial direction is the stack-frame helper that bridges the
asymmetry: the LHS has a `funV (VLam body' ρ) :: force :: π` stack, while
the RHS has a `funV (VLam (.Force body') ρ) :: π` stack. Both fire on a
value to land in `compute (.force :: π_i) (ρ_i.extend v_i) body'`. -/

/-- Stack-frame helper for the let-hoist-force primitive. The two `funV`
    frames are *not* identical — the LHS body is `body'` with a `.force`
    frame underneath, while the RHS body is `.Force body'` with no extra
    frame underneath. They both fire to `compute (.force :: π_i)
    (ρ_i.extend v_i) body'`. -/
private theorem stackRefK_funV_force_body {i d : Nat} {body : Term}
    {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed : closedAt (d + 1) body = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam body ρ₁) :: .force :: π₁)
      (.funV (.VLam (.Force body) ρ₂) :: π₂) := by
  intro j hj v₁ v₂ hv
  -- LHS: 1 step to compute (.force :: π₁) (ρ₁.extend v₁) body
  have h_lhs :
      steps 1 (State.ret (.funV (.VLam body ρ₁) :: .force :: π₁) v₁) =
        State.compute (.force :: π₁) (ρ₁.extend v₁) body := rfl
  -- RHS: 2 steps to compute (.force :: π₂) (ρ₂.extend v₂) body
  have h_rhs :
      steps 2 (State.ret (.funV (.VLam (.Force body) ρ₂) :: π₂) v₂) =
        State.compute (.force :: π₂) (ρ₂.extend v₂) body := rfl
  exact obsRefinesK_of_steps_left h_lhs <|
    obsRefinesK_of_steps_right h_rhs <|
      ftlr (d + 1) body hclosed j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
        (envRefinesK_extend (envRefinesK_mono hj henv) hv) j (Nat.le_refl _) _ _
        (stackRefK_force_augment (stackRefK_mono hj hπ))

/-- Symmetric: `funV (VLam (.Force body) ρ₁) :: π₁` on the left related to
    `funV (VLam body ρ₂) :: force :: π₂` on the right. -/
private theorem stackRefK_funV_body_force {i d : Nat} {body : Term}
    {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed : closedAt (d + 1) body = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam (.Force body) ρ₁) :: π₁)
      (.funV (.VLam body ρ₂) :: .force :: π₂) := by
  intro j hj v₁ v₂ hv
  have h_lhs :
      steps 2 (State.ret (.funV (.VLam (.Force body) ρ₁) :: π₁) v₁) =
        State.compute (.force :: π₁) (ρ₁.extend v₁) body := rfl
  have h_rhs :
      steps 1 (State.ret (.funV (.VLam body ρ₂) :: .force :: π₂) v₂) =
        State.compute (.force :: π₂) (ρ₂.extend v₂) body := rfl
  exact obsRefinesK_of_steps_left h_lhs <|
    obsRefinesK_of_steps_right h_rhs <|
      ftlr (d + 1) body hclosed j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
        (envRefinesK_extend (envRefinesK_mono hj henv) hv) j (Nat.le_refl _) _ _
        (stackRefK_force_augment (stackRefK_mono hj hπ))

/-- Lowering shape lemma: `.Force (.Let [(v, rhs, false)] body)` lowers
    iff both `rhs` and `body` lower, and the result is
    `.Force (.Apply (.Lam 0 t_body) t_rhs)`. -/
private theorem lowerTotalExpr_force_let {env : List VarId} (v : VarId)
    {rhs body : Expr} {t_rhs t_body : Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) =
      some (.Force (.Apply (.Lam 0 t_body) t_rhs)) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  show lowerTotal env (expandFix (.Force (.Let [(v, rhs, false)] body))) = _
  simp [expandFix, expandFixBinds, lowerTotal, lowerTotalLet, h_rhs', h_body']

/-- Lowering shape lemma: `.Let [(v, rhs, false)] (.Force body)` lowers
    to `.Apply (.Lam 0 (.Force t_body)) t_rhs` when both lower. -/
private theorem lowerTotalExpr_let_force {env : List VarId} (v : VarId)
    {rhs body : Expr} {t_rhs t_body : Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) =
      some (.Apply (.Lam 0 (.Force t_body)) t_rhs) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  show lowerTotal env (expandFix (.Let [(v, rhs, false)] (.Force body))) = _
  simp [expandFix, expandFixBinds, lowerTotal, lowerTotalLet, h_rhs', h_body']

/-- The `.Force (.Let ...)` lowering succeeds iff both rhs and body lower. -/
private theorem lowerTotalExpr_force_let_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) :
    (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  refine ⟨fun hsome => ?_, fun ⟨hr, hb⟩ => ?_⟩
  · have h : (lowerTotal env (expandFix
        (.Force (.Let [(v, rhs, false)] body)))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal, lowerTotalLet,
      Option.bind_eq_bind] at h
    cases hr : lowerTotal env (expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      cases hb : lowerTotal (v :: env) (expandFix body) with
      | none => rw [hr, hb] at h; simp at h
      | some t_b =>
        have hr' : lowerTotalExpr env rhs = some t_r := hr
        have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
        exact ⟨hr' ▸ rfl, hb' ▸ rfl⟩
  · cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some _ => rw [lowerTotalExpr_force_let v hr' hb']; rfl

/-- The `.Let ... (.Force ...)` lowering succeeds iff both rhs and body lower. -/
private theorem lowerTotalExpr_let_force_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome := by
  refine ⟨fun hsome => ?_, fun ⟨hr, hb⟩ => ?_⟩
  · have h : (lowerTotal env (expandFix
        (.Let [(v, rhs, false)] (.Force body)))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal, lowerTotalLet,
      Option.bind_eq_bind] at h
    cases hr : lowerTotal env (expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      cases hb : lowerTotal (v :: env) (expandFix body) with
      | none => rw [hr, hb] at h; simp at h
      | some t_b =>
        have hr' : lowerTotalExpr env rhs = some t_r := hr
        have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
        exact ⟨hr' ▸ rfl, hb' ▸ rfl⟩
  · cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some _ => rw [lowerTotalExpr_let_force v hr' hb']; rfl

/-- Helper: show LHS lowers to none when either sub-expression fails to lower. -/
private theorem lowerTotalExpr_force_let_eq_none (env : List VarId) (v : VarId)
    (rhs body : Expr)
    (h : lowerTotalExpr env rhs = none ∨ lowerTotalExpr (v :: env) body = none) :
    lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = none := by
  cases hlhs : lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hr, hb⟩ := (lowerTotalExpr_force_let_isSome env v rhs body).mp hs
    rcases h with h | h
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)

private theorem lowerTotalExpr_let_force_eq_none (env : List VarId) (v : VarId)
    (rhs body : Expr)
    (h : lowerTotalExpr env rhs = none ∨ lowerTotalExpr (v :: env) body = none) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = none := by
  cases hlhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hr, hb⟩ := (lowerTotalExpr_let_force_isSome env v rhs body).mp hs
    rcases h with h | h
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)

/-- **MIRRefines for let-hoist-force (forward)**:
    `.Force (.Let [(v, rhs, false)] body) ⊑ᴹ .Let [(v, rhs, false)] (.Force body)`. -/
theorem mirRefines_let_hoist_force_fwd (v : VarId) (rhs body : Expr) :
    MIRRefines (.Force (.Let [(v, rhs, false)] body))
               (.Let [(v, rhs, false)] (.Force body)) := by
  refine ⟨fun env hsome => by
    rw [(lowerTotalExpr_force_let_isSome env v rhs body).mp hsome |>
      (lowerTotalExpr_let_force_isSome env v rhs body).mpr], ?_⟩
  intro d k env hlen
  cases hr : lowerTotalExpr env rhs with
  | none =>
    rw [lowerTotalExpr_force_let_eq_none env v rhs body (Or.inl hr)]; trivial
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none =>
      rw [lowerTotalExpr_force_let_eq_none env v rhs body (Or.inr hb)]; trivial
    | some t_b =>
      rw [lowerTotalExpr_force_let v hr hb, lowerTotalExpr_let_force v hr hb]
      simp only
      intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
      have h_steps_lhs :
          steps 4 (State.compute π₁ ρ₁ (.Force (.Apply (.Lam 0 t_b) t_r))) =
            State.compute (.funV (.VLam t_b ρ₁) :: .force :: π₁) ρ₁ t_r := rfl
      have h_steps_rhs :
          steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Force t_b)) t_r)) =
            State.compute (.funV (.VLam (.Force t_b) ρ₂) :: π₂) ρ₂ t_r := rfl
      have hclosed_b : closedAt (env.length + 1) t_b := by
        simpa [List.length_cons] using lowerTotal_closedAt (v :: env) _ t_b hb
      subst hlen
      have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := fun n hn hnd => by
        obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
        exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
      exact obsRefinesK_of_steps_left h_steps_lhs <|
        obsRefinesK_of_steps_right h_steps_rhs <|
          ftlr env.length t_r (lowerTotal_closedAt env _ t_r hr) j j (Nat.le_refl _)
            ρ₁ ρ₂ henv i hi _ _ (stackRefK_funV_force_body hclosed_b henv_i hπ)

/-- **MIRRefines for let-hoist-force (backward)**:
    `.Let [(v, rhs, false)] (.Force body) ⊑ᴹ .Force (.Let [(v, rhs, false)] body)`. -/
theorem mirRefines_let_hoist_force_bwd (v : VarId) (rhs body : Expr) :
    MIRRefines (.Let [(v, rhs, false)] (.Force body))
               (.Force (.Let [(v, rhs, false)] body)) := by
  refine ⟨fun env hsome => by
    rw [(lowerTotalExpr_let_force_isSome env v rhs body).mp hsome |>
      (lowerTotalExpr_force_let_isSome env v rhs body).mpr], ?_⟩
  intro d k env hlen
  cases hr : lowerTotalExpr env rhs with
  | none =>
    rw [lowerTotalExpr_let_force_eq_none env v rhs body (Or.inl hr)]; trivial
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none =>
      rw [lowerTotalExpr_let_force_eq_none env v rhs body (Or.inr hb)]; trivial
    | some t_b =>
      rw [lowerTotalExpr_let_force v hr hb, lowerTotalExpr_force_let v hr hb]
      simp only
      intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
      have h_steps_lhs :
          steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Force t_b)) t_r)) =
            State.compute (.funV (.VLam (.Force t_b) ρ₁) :: π₁) ρ₁ t_r := rfl
      have h_steps_rhs :
          steps 4 (State.compute π₂ ρ₂ (.Force (.Apply (.Lam 0 t_b) t_r))) =
            State.compute (.funV (.VLam t_b ρ₂) :: .force :: π₂) ρ₂ t_r := rfl
      have hclosed_b : closedAt (env.length + 1) t_b := by
        simpa [List.length_cons] using lowerTotal_closedAt (v :: env) _ t_b hb
      subst hlen
      have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := fun n hn hnd => by
        obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
        exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
      exact obsRefinesK_of_steps_left h_steps_lhs <|
        obsRefinesK_of_steps_right h_steps_rhs <|
          ftlr env.length t_r (lowerTotal_closedAt env _ t_r hr) j j (Nat.le_refl _)
            ρ₁ ρ₂ henv i hi _ _ (stackRefK_funV_body_force hclosed_b henv_i hπ)

private theorem let_hoist_force_close_pres_fwd (v : VarId) (rhs body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some⟩ :=
    (lowerTotalExpr_force_let_isSome env v rhs body).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      rw [lowerTotalExpr_force_let v hr hb] at h₁
      rw [lowerTotalExpr_let_force v hr hb] at h₂
      cases h₁
      cases h₂
      -- Both forms have closedAt k = closedAt (k+1) t_b && closedAt k t_r
      simp only [closedAt, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, hc.2⟩

private theorem let_hoist_force_close_pres_bwd (v : VarId) (rhs body : Expr) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body)) = some t₁ →
      lowerTotalExpr env (.Force (.Let [(v, rhs, false)] body)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Force body))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some⟩ :=
    (lowerTotalExpr_let_force_isSome env v rhs body).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      rw [lowerTotalExpr_let_force v hr hb] at h₁
      rw [lowerTotalExpr_force_let v hr hb] at h₂
      cases h₁
      cases h₂
      simp only [closedAt, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, hc.2⟩

theorem mirCtxRefines_let_hoist_force_fwd (v : VarId) (rhs body : Expr) :
    MIRCtxRefines (.Force (.Let [(v, rhs, false)] body))
                  (.Let [(v, rhs, false)] (.Force body)) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_force_fwd v rhs body)
    (let_hoist_force_close_pres_fwd v rhs body)

theorem mirCtxRefines_let_hoist_force_bwd (v : VarId) (rhs body : Expr) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.Force body))
                  (.Force (.Let [(v, rhs, false)] body)) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_force_bwd v rhs body)
    (let_hoist_force_close_pres_bwd v rhs body)
end Moist.Verified.MIR
