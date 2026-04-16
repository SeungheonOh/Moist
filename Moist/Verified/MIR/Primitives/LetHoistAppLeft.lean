import Moist.Verified.MIR.Primitives.Shared

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFix_freeVars_not_contains expandFixBinds lowerTotal_prepend_unused
   lowerTotal_prepend_unused_none)
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

/-! ## Section 6. Let-hoist-app-left primitive

`.App (.Let [(v, rhs, false)] body) xArg ≈ .Let [(v, rhs, false)] (.App body xArg)`
when `v ∉ freeVars xArg`.

The crux: the RHS lowers `xArg` under an extended env (since it's now under
the let binder), which by `lowerTotal_prepend_unused` produces the **shifted**
lowering of `xArg`. The forward direction needs `renameRefinesR (shiftRename 1)`
to relate the LHS's plain `xArg` lowering to the RHS's shifted form. -/

/-- Builds a `funV :: π` stack from a value relation and a stack relation. -/
theorem stackRefK_funV_top_aug {i : Nat} {vf₁ vf₂ : CekValue}
    {π₁ π₂ : Stack} (hvf : ValueRefinesK i vf₁ vf₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    -- Demote hvf to index n+1 to get useful structure
    have hvf' : ValueRefinesK (n + 1) vf₁ vf₂ := valueRefinesK_mono hj _ _ hvf
    match vf₁, vf₂, hvf' with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂', hvf' =>
      simp only [step]
      simp only [ValueRefinesK] at hvf'
      exact hvf' n (by omega) w₁ w₂ (valueRefinesK_mono (by omega) w₁ w₂ hw)
        n (Nat.le_refl _) π₁ π₂
        (stackRefK_mono (by omega) hπ)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂, hvf' =>
      simp only [ValueRefinesK] at hvf'
      obtain ⟨rfl, rfl, hargs⟩ := hvf'
      simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (n + 1)
              (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
            simp only [ValueRefinesK]
            refine ⟨trivial, trivial, ?_⟩
            exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                   listRel_valueRefinesK_mono (by omega) hargs⟩
          exact obsRefinesK_mono (by omega : n ≤ n + 1)
            (stackRefK_mono (by omega) hπ
              (n + 1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines
            ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
             listRel_valueRefinesK_mono (by omega) hargs⟩
            (stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _, _ => simp only [step]; exact obsRefinesK_error _
    | .VDelay _ _, .VDelay _ _, _ => simp only [step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _, _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _, hvf' | .VCon _, .VDelay _ _, hvf'
    | .VCon _, .VConstr _ _, hvf' | .VCon _, .VBuiltin _ _ _, hvf'
    | .VLam _ _, .VCon _, hvf' | .VLam _ _, .VDelay _ _, hvf'
    | .VLam _ _, .VConstr _ _, hvf' | .VLam _ _, .VBuiltin _ _ _, hvf'
    | .VDelay _ _, .VCon _, hvf' | .VDelay _ _, .VLam _ _, hvf'
    | .VDelay _ _, .VConstr _ _, hvf' | .VDelay _ _, .VBuiltin _ _ _, hvf'
    | .VConstr _ _, .VCon _, hvf' | .VConstr _ _, .VLam _ _, hvf'
    | .VConstr _ _, .VDelay _ _, hvf' | .VConstr _ _, .VBuiltin _ _ _, hvf'
    | .VBuiltin _ _ _, .VCon _, hvf' | .VBuiltin _ _ _, .VLam _ _, hvf'
    | .VBuiltin _ _ _, .VDelay _ _, hvf' | .VBuiltin _ _ _, .VConstr _ _, hvf' =>
      simp only [ValueRefinesK] at hvf'

/-- Forward stack-frame helper: relates the augmented stacks at the
    `arg`-frame layer (after the funVs fire). -/
private theorem stackRefK_arg_shift_fwd {i d : Nat}
    {t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₂ : CekValue}
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.arg t_x ρ₁ :: π₁)
      (.arg (renameTerm (shiftRename 1) t_x)
            (ρ₂.extend v₂) :: π₂) := by
  intro j hj vf₁ vf₂ hvf
  -- LHS step 1: arg fires → funV vf₁ :: π₁, compute ρ₁ t_x
  have h_lhs : steps 1 (State.ret (.arg t_x ρ₁ :: π₁) vf₁) =
               State.compute (.funV vf₁ :: π₁) ρ₁ t_x := rfl
  have h_rhs : steps 1 (State.ret (.arg (renameTerm
                          (shiftRename 1) t_x) (ρ₂.extend v₂) :: π₂) vf₂) =
               State.compute (.funV vf₂ :: π₂) (ρ₂.extend v₂)
                 (renameTerm (shiftRename 1) t_x) := rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  -- Augment the stack with the new funV frames (which are vf-related).
  have hπ_funV : StackRefK ValueRefinesK j (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) :=
    stackRefK_funV_top_aug hvf (stackRefK_mono hj hπ)
  -- Now apply renameRefinesR for t_x with ρ₁ and ρ₂.extend v₂
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := envRefinesK_mono hj henv
  have henv_R : RenameEnvRefR (shiftRename 1) j d ρ₁ (ρ₂.extend v₂) :=
    envRefinesK_to_renameEnvRefR_shift henv_j
  exact renameRefinesR_shift1 d t_x hclosed_x j j (Nat.le_refl _) ρ₁ (ρ₂.extend v₂)
    henv_R j (Nat.le_refl _) (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) hπ_funV

/-- Forward augmented stack helper for the let-hoist-app-left primitive
    at the funV-on-top layer. -/
private theorem stackRefK_letHoistAppLeft_fwd {i d : Nat}
    {t_b t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_b : closedAt (d + 1) t_b = true)
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁)
      (.funV (.VLam (.Apply t_b
        (renameTerm (shiftRename 1) t_x)) ρ₂) :: π₂) := by
  intro j hj v₁ v₂ hv
  -- LHS: funV fires (1 step) → compute (.arg t_x ρ₁ :: π₁) (ρ₁.extend v₁) t_b
  have h_lhs : steps 1 (State.ret (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁) v₁) =
               State.compute (.arg t_x ρ₁ :: π₁) (ρ₁.extend v₁) t_b := rfl
  -- RHS: funV fires (1 step) then Apply unfolds (1 step) → arg shifted_x :: π₂, compute t_b
  have h_rhs : steps 2 (State.ret (.funV (.VLam (.Apply t_b
                  (renameTerm (shiftRename 1) t_x)) ρ₂) :: π₂) v₂) =
               State.compute (.arg (renameTerm
                  (shiftRename 1) t_x) (ρ₂.extend v₂) :: π₂)
                 (ρ₂.extend v₂) t_b := rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  -- Both compute t_b. Apply ftlr with augmented arg-stacks.
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := envRefinesK_mono hj henv
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_arg : StackRefK ValueRefinesK j
      (.arg t_x ρ₁ :: π₁)
      (.arg (renameTerm (shiftRename 1) t_x) (ρ₂.extend v₂) :: π₂) :=
    stackRefK_arg_shift_fwd hclosed_x henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_b hclosed_b j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_arg

/-- Backward stack-frame helper: relates the augmented stacks at the
    `arg`-frame layer for the backward direction. The shift is now on the LHS. -/
private theorem stackRefK_arg_shift_bwd {i d : Nat}
    {t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₁ : CekValue}
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.arg (renameTerm (shiftRename 1) t_x)
            (ρ₁.extend v₁) :: π₁)
      (.arg t_x ρ₂ :: π₂) := by
  intro j hj vf₁ vf₂ hvf
  have h_lhs : steps 1 (State.ret (.arg (renameTerm
                          (shiftRename 1) t_x) (ρ₁.extend v₁) :: π₁) vf₁) =
               State.compute (.funV vf₁ :: π₁) (ρ₁.extend v₁)
                 (renameTerm (shiftRename 1) t_x) := rfl
  have h_rhs : steps 1 (State.ret (.arg t_x ρ₂ :: π₂) vf₂) =
               State.compute (.funV vf₂ :: π₂) ρ₂ t_x := rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have hπ_funV : StackRefK ValueRefinesK j (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) :=
    stackRefK_funV_top_aug hvf (stackRefK_mono hj hπ)
  -- Apply renameRefines (shiftRename 1) — backward direction places shift on LHS
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := envRefinesK_mono hj henv
  have henv_RL : RenameEnvRef
      (shiftRename 1) j d (ρ₁.extend v₁) ρ₂ :=
    envRefinesK_to_renameEnvRef_shift henv_j
  exact renameRefines_shift1 d t_x hclosed_x j j
    (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL j (Nat.le_refl _)
    (.funV vf₁ :: π₁) (.funV vf₂ :: π₂) hπ_funV

/-- Backward augmented stack helper for the let-hoist-app-left primitive. -/
private theorem stackRefK_letHoistAppLeft_bwd {i d : Nat}
    {t_b t_x : Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_b : closedAt (d + 1) t_b = true)
    (hclosed_x : closedAt d t_x = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam (.Apply t_b
        (renameTerm (shiftRename 1) t_x)) ρ₁) :: π₁)
      (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) := by
  intro j hj v₁ v₂ hv
  have h_lhs : steps 2 (State.ret (.funV (.VLam (.Apply t_b
                  (renameTerm (shiftRename 1) t_x)) ρ₁) :: π₁) v₁) =
               State.compute (.arg (renameTerm
                  (shiftRename 1) t_x) (ρ₁.extend v₁) :: π₁)
                 (ρ₁.extend v₁) t_b := rfl
  have h_rhs : steps 1 (State.ret (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) v₂) =
               State.compute (.arg t_x ρ₂ :: π₂) (ρ₂.extend v₂) t_b := rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := envRefinesK_mono hj henv
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_arg : StackRefK ValueRefinesK j
      (.arg (renameTerm (shiftRename 1) t_x) (ρ₁.extend v₁) :: π₁)
      (.arg t_x ρ₂ :: π₂) :=
    stackRefK_arg_shift_bwd hclosed_x henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_b hclosed_b j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_arg

/-- Lowering shape lemma: `App (Let [(v, rhs, false)] body) xArg` lowers
    to `Apply (Apply (Lam 0 t_body) t_rhs) t_xArg`. -/
private theorem lowerTotalExpr_app_let {env : List VarId} (v : VarId)
    {rhs body xArg : Expr} {t_rhs t_body t_xArg : Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_xArg : lowerTotalExpr env xArg = some t_xArg) :
    lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) =
      some (.Apply (.Apply (.Lam 0 t_body) t_rhs) t_xArg) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  have h_xArg' : lowerTotal env (expandFix xArg) = some t_xArg := h_xArg
  show lowerTotal env (expandFix (.App (.Let [(v, rhs, false)] body) xArg)) =
    some (.Apply (.Apply (.Lam 0 t_body) t_rhs) t_xArg)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_xArg']

/-- Lowering shape lemma for the RHS form `Let [(v, rhs, false)] (App body xArg)`,
    using the shifted xArg from `lowerTotal_prepend_unused`. -/
private theorem lowerTotalExpr_let_app {env : List VarId} (v : VarId)
    {rhs body xArg : Expr} {t_rhs t_body t_xArg : Term}
    (hfresh : (freeVars xArg).contains v = false)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_xArg : lowerTotalExpr env xArg = some t_xArg) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) =
      some (.Apply (.Lam 0 (.Apply t_body
        (renameTerm (shiftRename 1) t_xArg))) t_rhs) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  have h_xArg' : lowerTotal env (expandFix xArg) = some t_xArg := h_xArg
  -- Use lowerTotal_prepend_unused to relate lowerTotal (v :: env) xArg to shifted t_xArg.
  have hfresh_exp : (freeVars (expandFix xArg)).contains v = false :=
    expandFix_freeVars_not_contains xArg v hfresh
  have h_xArg_shift :
      lowerTotal (v :: env) (expandFix xArg) =
        some (renameTerm (shiftRename 1) t_xArg) :=
    lowerTotal_prepend_unused env v _ hfresh_exp t_xArg h_xArg'
  show lowerTotal env (expandFix (.Let [(v, rhs, false)] (.App body xArg))) =
    some (.Apply (.Lam 0 (.Apply t_body
      (renameTerm (shiftRename 1) t_xArg))) t_rhs)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_xArg_shift]

private theorem lowerTotalExpr_app_let_isSome (env : List VarId) (v : VarId)
    (rhs body xArg : Expr) :
    (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalExpr env xArg).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.App (.Let [(v, rhs, false)] body) xArg))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases hx : lowerTotal env (expandFix xArg) with
        | none => rw [hx] at h; simp at h
        | some t_x =>
          have hr' : lowerTotalExpr env rhs = some t_r := hr
          have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
          have hx' : lowerTotalExpr env xArg = some t_x := hx
          exact ⟨by rw [hr']; rfl, by rw [hb']; rfl, by rw [hx']; rfl⟩
  · rintro ⟨hr, hb, hx⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases hx' : lowerTotalExpr env xArg with
        | none => rw [hx'] at hx; exact absurd hx (by simp)
        | some t_x =>
          rw [lowerTotalExpr_app_let v hr' hb' hx']
          rfl

private theorem lowerTotalExpr_let_app_isSome (env : List VarId) (v : VarId)
    (rhs body xArg : Expr) (hfresh : (freeVars xArg).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalExpr env xArg).isSome := by
  have hfresh_exp : (freeVars (expandFix xArg)).contains v = false :=
    expandFix_freeVars_not_contains xArg v hfresh
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Let [(v, rhs, false)] (.App body xArg)))).isSome := hsome
    simp only [expandFix, expandFixBinds, lowerTotal,
               lowerTotalLet, Option.bind_eq_bind] at h
    cases hr : lowerTotal env (expandFix rhs) with
    | none => rw [hr] at h; simp at h
    | some t_r =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases hb : lowerTotal (v :: env) (expandFix body) with
      | none => rw [hb] at h; simp at h
      | some t_b =>
        rw [hb] at h
        simp only [Option.bind_some] at h
        cases hx_ext : lowerTotal (v :: env) (expandFix xArg) with
        | none => rw [hx_ext] at h; simp at h
        | some t_x_ext =>
          -- Use prepend_unused to go from extended to non-extended (reverse via none case)
          cases hx : lowerTotal env (expandFix xArg) with
          | none =>
            -- If extended succeeds but base fails, that's a contradiction via the none version
            have := lowerTotal_prepend_unused_none env v _ hfresh_exp hx
            rw [hx_ext] at this; exact absurd this (by simp)
          | some t_x =>
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
            have hx' : lowerTotalExpr env xArg = some t_x := hx
            exact ⟨by rw [hr']; rfl, by rw [hb']; rfl, by rw [hx']; rfl⟩
  · rintro ⟨hr, hb, hx⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases hx' : lowerTotalExpr env xArg with
        | none => rw [hx'] at hx; exact absurd hx (by simp)
        | some t_x =>
          rw [lowerTotalExpr_let_app v hfresh hr' hb' hx']
          rfl

/-- Helper: LHS of app-let lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_app_let_eq_none (env : List VarId) (v : VarId)
    (rhs body xArg : Expr)
    (h : lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none ∨
         lowerTotalExpr env xArg = none) :
    lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = none := by
  cases hlhs : lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hr, hb, hx⟩ := (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hs
    rcases h with h | h | h
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)
    · rw [h] at hx; exact absurd hx (by simp)

/-- Helper: RHS of app-let lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_let_app_eq_none (env : List VarId) (v : VarId)
    (rhs body xArg : Expr) (hfresh : (freeVars xArg).contains v = false)
    (h : lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none ∨
         lowerTotalExpr env xArg = none) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = none := by
  cases hlhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hr, hb, hx⟩ := (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hs
    rcases h with h | h | h
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)
    · rw [h] at hx; exact absurd hx (by simp)

theorem mirRefines_let_hoist_app_left_fwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (freeVars xArg).contains v = false) :
    MIRRefines (.App (.Let [(v, rhs, false)] body) xArg)
               (.Let [(v, rhs, false)] (.App body xArg)) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mpr
      ((lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome), ?_⟩
  intro d k env hlen
  cases hr : lowerTotalExpr env rhs with
  | none =>
    rw [lowerTotalExpr_app_let_eq_none env v rhs body xArg (.inl hr)]; trivial
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none =>
      rw [lowerTotalExpr_app_let_eq_none env v rhs body xArg (.inr (.inl hb))]; trivial
    | some t_b =>
      cases hx : lowerTotalExpr env xArg with
      | none =>
        rw [lowerTotalExpr_app_let_eq_none env v rhs body xArg (.inr (.inr hx))]; trivial
        | some t_x =>
          rw [lowerTotalExpr_app_let v hr hb hx, lowerTotalExpr_let_app v hfresh hr hb hx]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          -- LHS state: compute π₁ ρ₁ (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)
          -- 4 admin steps → compute (funV (VLam t_b ρ₁) :: arg t_x ρ₁ :: π₁) ρ₁ t_r
          have h_steps_lhs :
              steps 4 (State.compute π₁ ρ₁ (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)) =
                State.compute (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁) ρ₁ t_r := rfl
          -- RHS state: compute π₂ ρ₂ (.Apply (.Lam 0 (.Apply t_b shifted)) t_r)
          -- 3 admin steps → compute (funV (VLam (.Apply t_b shifted) ρ₂) :: π₂) ρ₂ t_r
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Apply t_b
                (renameTerm (shiftRename 1) t_x))) t_r)) =
                State.compute (.funV (.VLam (.Apply t_b
                  (renameTerm (shiftRename 1) t_x)) ρ₂) :: π₂)
                  ρ₂ t_r := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_x : closedAt env.length t_x :=
            lowerTotal_closedAt env _ t_x hx
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam t_b ρ₁) :: .arg t_x ρ₁ :: π₁)
              (.funV (.VLam (.Apply t_b
                (renameTerm (shiftRename 1) t_x)) ρ₂) :: π₂) :=
            stackRefK_letHoistAppLeft_fwd hclosed_b hclosed_x henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

theorem mirRefines_let_hoist_app_left_bwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (freeVars xArg).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.App body xArg))
               (.App (.Let [(v, rhs, false)] body) xArg) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_app_let_isSome env v rhs body xArg).mpr
      ((lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome), ?_⟩
  intro d k env hlen
  cases hr : lowerTotalExpr env rhs with
  | none =>
    rw [lowerTotalExpr_let_app_eq_none env v rhs body xArg hfresh (.inl hr)]; trivial
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none =>
      rw [lowerTotalExpr_let_app_eq_none env v rhs body xArg hfresh (.inr (.inl hb))]; trivial
    | some t_b =>
      cases hx : lowerTotalExpr env xArg with
      | none =>
        rw [lowerTotalExpr_let_app_eq_none env v rhs body xArg hfresh (.inr (.inr hx))]; trivial
        | some t_x =>
          rw [lowerTotalExpr_let_app v hfresh hr hb hx, lowerTotalExpr_app_let v hr hb hx]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have h_steps_lhs :
              steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Apply t_b
                (renameTerm (shiftRename 1) t_x))) t_r)) =
                State.compute (.funV (.VLam (.Apply t_b
                  (renameTerm (shiftRename 1) t_x)) ρ₁) :: π₁)
                  ρ₁ t_r := rfl
          have h_steps_rhs :
              steps 4 (State.compute π₂ ρ₂ (.Apply (.Apply (.Lam 0 t_b) t_r) t_x)) =
                State.compute (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) ρ₂ t_r := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_x : closedAt env.length t_x :=
            lowerTotal_closedAt env _ t_x hx
          have hd_eq : d = env.length := hlen.symm
          subst hd_eq
          have henv_j : EnvRefinesK j env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv n hn hnd
            exact ⟨w₁, w₂, hl, hr', hw⟩
          have henv_i : EnvRefinesK i env.length ρ₁ ρ₂ := by
            intro n hn hnd
            obtain ⟨w₁, w₂, hl, hr', hw⟩ := henv_j n hn hnd
            exact ⟨w₁, w₂, hl, hr', valueRefinesK_mono hi _ _ hw⟩
          have hπ_aug : StackRefK ValueRefinesK i
              (.funV (.VLam (.Apply t_b
                (renameTerm (shiftRename 1) t_x)) ρ₁) :: π₁)
              (.funV (.VLam t_b ρ₂) :: .arg t_x ρ₂ :: π₂) :=
            stackRefK_letHoistAppLeft_bwd hclosed_b hclosed_x henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

private theorem let_hoist_app_left_close_pres_fwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (freeVars xArg).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg)).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, hx_some⟩ :=
    (lowerTotalExpr_app_let_isSome env v rhs body xArg).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases hx : lowerTotalExpr env xArg with
      | none => rw [hx] at hx_some; exact absurd hx_some (by simp)
      | some t_x =>
        rw [lowerTotalExpr_app_let v hr hb hx] at h₁
        rw [lowerTotalExpr_let_app v hfresh hr hb hx] at h₂
        cases h₁; cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, hr_c⟩, hx_c⟩ := hc
        exact ⟨⟨hb_c, closedAt_renameTerm_shiftRename t_x k 1 (by omega) (by omega) hx_c⟩, hr_c⟩

private theorem let_hoist_app_left_close_pres_bwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (freeVars xArg).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg)) = some t₁ →
      lowerTotalExpr env (.App (.Let [(v, rhs, false)] body) xArg) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.App body xArg))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, hx_some⟩ :=
    (lowerTotalExpr_let_app_isSome env v rhs body xArg hfresh).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases hx : lowerTotalExpr env xArg with
      | none => rw [hx] at hx_some; exact absurd hx_some (by simp)
      | some t_x =>
        rw [lowerTotalExpr_let_app v hfresh hr hb hx] at h₁
        rw [lowerTotalExpr_app_let v hr hb hx] at h₂
        cases h₁; cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, hsh_c⟩, hr_c⟩ := hc
        exact ⟨⟨hb_c, hr_c⟩,
          closedAt_renameTerm_shiftRename_inv t_x k 1 (by omega) (by omega) hsh_c⟩

theorem mirCtxRefines_let_hoist_app_left_fwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (freeVars xArg).contains v = false) :
    MIRCtxRefines (.App (.Let [(v, rhs, false)] body) xArg)
                  (.Let [(v, rhs, false)] (.App body xArg)) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_app_left_fwd v rhs body xArg hfresh)
    (let_hoist_app_left_close_pres_fwd v rhs body xArg hfresh)

theorem mirCtxRefines_let_hoist_app_left_bwd (v : VarId) (rhs body xArg : Expr)
    (hfresh : (freeVars xArg).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.App body xArg))
                  (.App (.Let [(v, rhs, false)] body) xArg) :=
  mirRefines_to_mirCtxRefines (mirRefines_let_hoist_app_left_bwd v rhs body xArg hfresh)
    (let_hoist_app_left_close_pres_bwd v rhs body xArg hfresh)
end Moist.Verified.MIR
