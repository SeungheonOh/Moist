import Moist.Verified.MIR.Primitives.Shared

namespace Moist.Verified.MIR

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR
  (Expr VarId anfNormalizeCore anfNormalizeListCore anfNormalizeBindsCore anfAtom anfAtomList
   wrapLet flattenLetBody freeVars lowerTotalExpr lowerTotal lowerTotalLet expandFix
   expandFixBinds expandFixList expandFixList_freeVars_not_contains freeVarsList lowerTotalList
   lowerTotalList_prepend_unused_gen lowerTotalList_prepend_unused_none_gen VarSet)
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

/-! ## Section 8. Let-hoist-case-scrut primitive

`.Case (.Let [(v, rhs, false)] body) alts ≈ .Let [(v, rhs, false)] (.Case body alts)`
when no alt references `v`.

The lowerings:
* LHS lowers to `.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts`.
* RHS lowers to `.Apply (.Lam 0 (.Case t_body (shift t_alts))) t_rhs`,
  where each alt has been shifted via `shiftRename 1` because the alts
  are now evaluated under an extra let binder.

The forward CEK trace:
* LHS: 4 admin steps produce
  `compute (funV (VLam t_body ρ₁) :: caseScrutinee t_alts ρ₁ :: π₁) ρ₁ t_rhs`.
* RHS: 3 admin steps produce
  `compute (funV (VLam (.Case t_body (shift t_alts)) ρ₂) :: π₂) ρ₂ t_rhs`.

Both sides now evaluate the same `t_rhs`, so `ftlr` bridges via an
augmented-stack helper. After the returned value fires the funV on both
sides, the LHS lands in a `.caseScrutinee` frame with the *unextended*
`ρ₁`, while the RHS evaluates `(.Case t_body (shift t_alts))` which
pushes a `.caseScrutinee` frame with the *extended* `ρ₂.extend v₂`.
`stackRefK_caseScrutinee_shift_aug_fwd` handles this asymmetry. -/

/-- Converts a `∀ alt ∈ alts, ...` freeness hypothesis into the
    list-level `freeVarsList` form. -/
theorem freeVarsList_not_contains_of_forall (v : VarId) (alts : List Expr)
    (hfresh : ∀ alt ∈ alts, (freeVars alt).contains v = false) :
    (freeVarsList alts).contains v = false := by
  induction alts with
  | nil =>
    rw [freeVarsList.eq_1]
    exact VarSet.empty_not_contains v
  | cons a rest ih =>
    rw [freeVarsList.eq_2]
    apply VarSet.union_not_contains_fwd
    · exact hfresh a (List.mem_cons_self)
    · exact ih (fun alt halt => hfresh alt (List.mem_cons_of_mem _ halt))

/-- Stack-frame helper for the forward direction of let-hoist-case-scrut.
    The LHS has a `.caseScrutinee t_alts ρ₁` frame with the original env;
    the RHS has a `.caseScrutinee (shift t_alts) (ρ₂.extend v₂)` frame
    with the extended env. Both fire on a returned value by dispatching
    on its shape; `renameRefinesR (shiftRename 1)` bridges the alt
    evaluation. -/
private theorem stackRefK_caseScrutinee_shift_aug_fwd {i d : Nat}
    {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₂ : CekValue}
    (halts : closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.caseScrutinee t_alts ρ₁ :: π₁)
      (.caseScrutinee (renameTermList (shiftRename 1) t_alts)
          (ρ₂.extend v₂) :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    have halts_j : closedAtList d t_alts = true := halts
    have henv_j : EnvRefinesK (n + 1) d ρ₁ ρ₂ := by
      intro p hp hpd
      obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
      exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono hj _ _ hrel⟩
    match w₁, w₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hw; obtain ⟨rfl, hfields_v⟩ := hw
      simp only [step]
      have hlen_eq : (renameTermList
          (shiftRename 1) t_alts).length = t_alts.length :=
        renameTermList_length _ _
      split
      · rename_i alt_val halt_case
        have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
        have hi₁ : tag₁ < t_alts.length := hsome₁.1
        have hi₂ : tag₁ < (renameTermList
            (shiftRename 1) t_alts).length := by omega
        have halt₂ : (renameTermList (shiftRename 1) t_alts)[tag₁]? =
            some ((renameTermList (shiftRename 1) t_alts)[tag₁]) :=
          List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
        rw [halt₂]; simp only []
        have hidx : (renameTermList (shiftRename 1) t_alts)[tag₁]'hi₂
            = renameTerm (shiftRename 1) (t_alts[tag₁]) :=
          renameTermList_getElem _ _ _ hi₁
        have halt_closed : closedAt d (t_alts[tag₁]) = true :=
          Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
            (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
        have henv_R : RenameEnvRefR (shiftRename 1) (n + 1) d
            ρ₁ (ρ₂.extend v₂) := envRefinesK_to_renameEnvRefR_shift henv_j
        have heq_alt : alt_val = t_alts[tag₁] := hsome₁.2.symm
        subst heq_alt
        rw [hidx]
        exact renameRefinesR_shift1 d (t_alts[tag₁]) halt_closed (n + 1) (n + 1)
          (Nat.le_refl _) ρ₁ (ρ₂.extend v₂) henv_R n (by omega)
          ((fields₁.map Frame.applyArg) ++ π₁)
          ((fields₂.map Frame.applyArg) ++ π₂)
          (applyArgFrames_stackRefK
            (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
            (stackRefK_mono (by omega) hπ))
      · rename_i hnone₁
        have hnone₂ : (renameTermList
            (shiftRename 1) t_alts)[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
        rw [hnone₂]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hw; subst hw
      simp only [step]
      have hlen_eq : (renameTermList
          (shiftRename 1) t_alts).length = t_alts.length :=
        renameTermList_length _ _
      split
      · rename_i tag numCtors fields hconst
        have hif_eq : (decide (numCtors > 0) && decide (t_alts.length > numCtors)) =
            (decide (numCtors > 0) && decide ((renameTermList
              (shiftRename 1) t_alts).length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]
          split
          · rename_i alt_val halt_case
            have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
            have hi₁ : tag < t_alts.length := hsome₁.1
            have hi₂ : tag < (renameTermList
                (shiftRename 1) t_alts).length := by omega
            have halt₂ : (renameTermList
                (shiftRename 1) t_alts)[tag]? =
                some ((renameTermList
                  (shiftRename 1) t_alts)[tag]) :=
              List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
            rw [halt₂]; simp only []
            have hidx : (renameTermList
                (shiftRename 1) t_alts)[tag]'hi₂ =
                renameTerm (shiftRename 1) (t_alts[tag]) :=
              renameTermList_getElem _ _ _ hi₁
            have halt_closed : closedAt d (t_alts[tag]) = true :=
              Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
                (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
            have henv_R : RenameEnvRefR (shiftRename 1) (n + 1) d
                ρ₁ (ρ₂.extend v₂) := envRefinesK_to_renameEnvRefR_shift henv_j
            have heq_alt : alt_val = t_alts[tag] := hsome₁.2.symm
            subst heq_alt
            rw [hidx]
            have hfields_vcon :=
              constToTagAndFields_fields_vcon c₁
            rw [hconst] at hfields_vcon
            exact renameRefinesR_shift1 d (t_alts[tag]) halt_closed (n + 1) (n + 1)
              (Nat.le_refl _) ρ₁ (ρ₂.extend v₂) henv_R n (by omega)
              ((fields.map Frame.applyArg) ++ π₁)
              ((fields.map Frame.applyArg) ++ π₂)
              (applyArgFrames_stackRefK
                (Moist.Verified.Contextual.SoundnessRefines.listRel_refl_vcon_refines n
                  fields hfields_vcon)
                (stackRefK_mono (by omega) hπ))
          · rename_i hnone₁
            have hnone₂ : (renameTermList
                (shiftRename 1) t_alts)[tag]? = none := by
              rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
            rw [hnone₂]; simp only []; exact obsRefinesK_error _
      · exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw

/-- Backward version of `stackRefK_caseScrutinee_shift_aug_fwd`. LHS has the
    `extend`-ed env with shifted alts; RHS has the original env. -/
private theorem stackRefK_caseScrutinee_shift_aug_bwd {i d : Nat}
    {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {v₁ : CekValue}
    (halts : closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.caseScrutinee (renameTermList (shiftRename 1) t_alts)
          (ρ₁.extend v₁) :: π₁)
      (.caseScrutinee t_alts ρ₂ :: π₂) := by
  intro j hj w₁ w₂ hw
  match j with
  | 0 => exact obsRefinesK_zero_ret
  | n + 1 =>
    obsRefinesK_of_step_auto
    have halts_j : closedAtList d t_alts = true := halts
    have henv_j : EnvRefinesK (n + 1) d ρ₁ ρ₂ := by
      intro p hp hpd
      obtain ⟨w₁', w₂', hl, hr, hrel⟩ := henv p hp hpd
      exact ⟨w₁', w₂', hl, hr, valueRefinesK_mono hj _ _ hrel⟩
    match w₁, w₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hw; obtain ⟨rfl, hfields_v⟩ := hw
      simp only [step]
      have hlen_eq : (renameTermList
          (shiftRename 1) t_alts).length = t_alts.length :=
        renameTermList_length _ _
      split
      · rename_i alt_val halt_case
        have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
        have hi₁s : tag₁ < (renameTermList
            (shiftRename 1) t_alts).length := hsome₁.1
        have hi₁ : tag₁ < t_alts.length := by omega
        have halt₂ : t_alts[tag₁]? = some (t_alts[tag₁]) :=
          List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩
        rw [halt₂]; simp only []
        have hidx : (renameTermList (shiftRename 1) t_alts)[tag₁]'hi₁s
            = renameTerm (shiftRename 1) (t_alts[tag₁]) :=
          renameTermList_getElem _ _ _ hi₁
        have halt_closed : closedAt d (t_alts[tag₁]) = true :=
          Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
            (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
        have heq_alt : alt_val = (renameTermList
            (shiftRename 1) t_alts)[tag₁] := hsome₁.2.symm
        subst heq_alt
        rw [hidx]
        have henv_RL : RenameEnvRef
            (shiftRename 1) (n + 1) d (ρ₁.extend v₁) ρ₂ :=
          envRefinesK_to_renameEnvRef_shift henv_j
        exact renameRefines_shift1 d (t_alts[tag₁]) halt_closed
          (n + 1) (n + 1) (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL n (by omega)
          ((fields₁.map Frame.applyArg) ++ π₁)
          ((fields₂.map Frame.applyArg) ++ π₂)
          (applyArgFrames_stackRefK
            (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
            (stackRefK_mono (by omega) hπ))
      · rename_i hnone₁
        have hnone₂ : t_alts[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
        rw [hnone₂]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hw; subst hw
      simp only [step]
      have hlen_eq : (renameTermList
          (shiftRename 1) t_alts).length = t_alts.length :=
        renameTermList_length _ _
      split
      · rename_i tag numCtors fields hconst
        have hif_eq : (decide (numCtors > 0) && decide ((renameTermList
              (shiftRename 1) t_alts).length > numCtors)) =
            (decide (numCtors > 0) && decide (t_alts.length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]
          split
          · rename_i alt_val halt_case
            have hsome₁ := List.getElem?_eq_some_iff.mp halt_case
            have hi₁s : tag < (renameTermList
                (shiftRename 1) t_alts).length := hsome₁.1
            have hi₁ : tag < t_alts.length := by omega
            have halt₂ : t_alts[tag]? = some (t_alts[tag]) :=
              List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩
            rw [halt₂]; simp only []
            have hidx : (renameTermList
                (shiftRename 1) t_alts)[tag]'hi₁s =
                renameTerm (shiftRename 1) (t_alts[tag]) :=
              renameTermList_getElem _ _ _ hi₁
            have halt_closed : closedAt d (t_alts[tag]) = true :=
              Moist.Verified.Contextual.BisimRef.closedAtList_get d t_alts _ _ halts_j
                (List.getElem?_eq_some_iff.mpr ⟨hi₁, rfl⟩)
            have heq_alt : alt_val = (renameTermList
                (shiftRename 1) t_alts)[tag] := hsome₁.2.symm
            subst heq_alt
            rw [hidx]
            have hfields_vcon :=
              constToTagAndFields_fields_vcon c₁
            rw [hconst] at hfields_vcon
            have henv_RL : RenameEnvRef
                (shiftRename 1) (n + 1) d (ρ₁.extend v₁) ρ₂ :=
              envRefinesK_to_renameEnvRef_shift henv_j
            exact renameRefines_shift1 d (t_alts[tag]) halt_closed
              (n + 1) (n + 1) (Nat.le_refl _) (ρ₁.extend v₁) ρ₂ henv_RL n (by omega)
              ((fields.map Frame.applyArg) ++ π₁)
              ((fields.map Frame.applyArg) ++ π₂)
              (applyArgFrames_stackRefK
                (Moist.Verified.Contextual.SoundnessRefines.listRel_refl_vcon_refines n
                  fields hfields_vcon)
                (stackRefK_mono (by omega) hπ))
          · rename_i hnone₁
            have hnone₂ : t_alts[tag]? = none := by
              rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
            rw [hnone₂]; simp only []; exact obsRefinesK_error _
      · exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hw

/-- Forward augmented stack helper for let-hoist-case-scrut, one layer above
    `stackRefK_caseScrutinee_shift_aug_fwd`. LHS has `funV (VLam t_body ρ₁)
    :: caseScrutinee t_alts ρ₁ :: π₁`; RHS has `funV (VLam (.Case t_body
    (shift t_alts)) ρ₂) :: π₂`. -/
private theorem stackRefK_funV_caseScrut_shift_fwd {i d : Nat}
    {t_body : Term} {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_alts : closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam t_body ρ₁) :: .caseScrutinee t_alts ρ₁ :: π₁)
      (.funV (.VLam (.Case t_body
        (renameTermList (shiftRename 1) t_alts)) ρ₂) :: π₂) := by
  intro j hj v₁ v₂ hv
  -- LHS: funV fires → compute (caseScrutinee t_alts ρ₁ :: π₁) (ρ₁.extend v₁) t_body
  have h_lhs :
      steps 1 (State.ret (.funV (.VLam t_body ρ₁) :: .caseScrutinee t_alts ρ₁ :: π₁) v₁) =
        State.compute (.caseScrutinee t_alts ρ₁ :: π₁) (ρ₁.extend v₁) t_body := rfl
  -- RHS: funV fires → compute π₂ (ρ₂.extend v₂) (.Case t_body (shift t_alts))
  --        → compute (caseScrutinee (shift t_alts) (ρ₂.extend v₂) :: π₂) (ρ₂.extend v₂) t_body
  have h_rhs :
      steps 2 (State.ret (.funV (.VLam (.Case t_body
          (renameTermList (shiftRename 1) t_alts)) ρ₂) :: π₂) v₂) =
        State.compute (.caseScrutinee
          (renameTermList (shiftRename 1) t_alts)
          (ρ₂.extend v₂) :: π₂) (ρ₂.extend v₂) t_body := rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := envRefinesK_mono hj henv
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_case : StackRefK ValueRefinesK j
      (.caseScrutinee t_alts ρ₁ :: π₁)
      (.caseScrutinee (renameTermList (shiftRename 1) t_alts)
          (ρ₂.extend v₂) :: π₂) :=
    stackRefK_caseScrutinee_shift_aug_fwd hclosed_alts henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_body hclosed_body j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_case

/-- Backward augmented stack helper for let-hoist-case-scrut. LHS has `funV
    (VLam (.Case t_body (shift t_alts)) ρ₁) :: π₁`; RHS has `funV (VLam
    t_body ρ₂) :: caseScrutinee t_alts ρ₂ :: π₂`. -/
private theorem stackRefK_funV_caseScrut_shift_bwd {i d : Nat}
    {t_body : Term} {t_alts : List Term} {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_alts : closedAtList d t_alts = true)
    (henv : EnvRefinesK i d ρ₁ ρ₂)
    (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    StackRefK ValueRefinesK i
      (.funV (.VLam (.Case t_body
        (renameTermList (shiftRename 1) t_alts)) ρ₁) :: π₁)
      (.funV (.VLam t_body ρ₂) :: .caseScrutinee t_alts ρ₂ :: π₂) := by
  intro j hj v₁ v₂ hv
  have h_lhs :
      steps 2 (State.ret (.funV (.VLam (.Case t_body
          (renameTermList (shiftRename 1) t_alts)) ρ₁) :: π₁) v₁) =
        State.compute (.caseScrutinee
          (renameTermList (shiftRename 1) t_alts)
          (ρ₁.extend v₁) :: π₁) (ρ₁.extend v₁) t_body := rfl
  have h_rhs :
      steps 1 (State.ret (.funV (.VLam t_body ρ₂) :: .caseScrutinee t_alts ρ₂ :: π₂) v₂) =
        State.compute (.caseScrutinee t_alts ρ₂ :: π₂) (ρ₂.extend v₂) t_body := rfl
  apply obsRefinesK_of_steps_left h_lhs
  apply obsRefinesK_of_steps_right h_rhs
  have henv_j : EnvRefinesK j d ρ₁ ρ₂ := envRefinesK_mono hj henv
  have henv_ext : EnvRefinesK j (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
    envRefinesK_extend henv_j hv
  have hπ_case : StackRefK ValueRefinesK j
      (.caseScrutinee (renameTermList (shiftRename 1) t_alts)
          (ρ₁.extend v₁) :: π₁)
      (.caseScrutinee t_alts ρ₂ :: π₂) :=
    stackRefK_caseScrutinee_shift_aug_bwd hclosed_alts henv_j (stackRefK_mono hj hπ)
  exact ftlr (d + 1) t_body hclosed_body j j (Nat.le_refl _) (ρ₁.extend v₁) (ρ₂.extend v₂)
    henv_ext j (Nat.le_refl _) _ _ hπ_case

/-- Lowering shape lemma: `.Case (.Let [(v, rhs, false)] body) alts` lowers
    to `.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts`. -/
private theorem lowerTotalExpr_case_let {env : List VarId} (v : VarId)
    {rhs body : Expr} {alts : List Expr} {t_rhs t_body : Term} {t_alts : List Term}
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_alts : lowerTotalList env (expandFixList alts) = some t_alts) :
    lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) =
      some (.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  show lowerTotal env (expandFix (.Case (.Let [(v, rhs, false)] body) alts)) =
    some (.Case (.Apply (.Lam 0 t_body) t_rhs) t_alts)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_alts]

/-- Lowering shape lemma: `.Let [(v, rhs, false)] (.Case body alts)` lowers
    to `.Apply (.Lam 0 (.Case t_body (shifted t_alts))) t_rhs` when `v` is
    fresh in `alts`. -/
private theorem lowerTotalExpr_let_case_fresh {env : List VarId} (v : VarId)
    {rhs body : Expr} {alts : List Expr} {t_rhs t_body : Term} {t_alts : List Term}
    (hfresh : (freeVarsList alts).contains v = false)
    (h_rhs : lowerTotalExpr env rhs = some t_rhs)
    (h_body : lowerTotalExpr (v :: env) body = some t_body)
    (h_alts : lowerTotalList env (expandFixList alts) = some t_alts) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) =
      some (.Apply (.Lam 0 (.Case t_body
        (renameTermList (shiftRename 1) t_alts))) t_rhs) := by
  have h_rhs' : lowerTotal env (expandFix rhs) = some t_rhs := h_rhs
  have h_body' : lowerTotal (v :: env) (expandFix body) = some t_body := h_body
  have hfresh_exp : (freeVarsList (expandFixList alts)).contains v = false :=
    expandFixList_freeVars_not_contains alts v hfresh
  have h_alts_shift :
      lowerTotalList (v :: env) (expandFixList alts) =
        some (renameTermList (shiftRename 1) t_alts) := by
    have h := lowerTotalList_prepend_unused_gen [] env v
      (expandFixList alts) (.inl hfresh_exp) t_alts h_alts
    simpa using h
  show lowerTotal env (expandFix (.Let [(v, rhs, false)] (.Case body alts))) =
    some (.Apply (.Lam 0 (.Case t_body
      (renameTermList (shiftRename 1) t_alts))) t_rhs)
  simp only [expandFix, expandFixBinds, lowerTotal,
             lowerTotalLet, Option.bind_eq_bind, Option.bind_some,
             h_rhs', h_body', h_alts_shift]

private theorem lowerTotalExpr_case_let_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) (alts : List Expr) :
    (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalList env (expandFixList alts)).isSome := by
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Case (.Let [(v, rhs, false)] body) alts))).isSome := hsome
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
        cases ha : lowerTotalList env (expandFixList alts) with
        | none => rw [ha] at h; simp at h
        | some t_a =>
          have hr' : lowerTotalExpr env rhs = some t_r := hr
          have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
          refine ⟨?_, ?_, ?_⟩
          · rw [hr']; rfl
          · rw [hb']; rfl
          · rfl
  · rintro ⟨hr, hb, ha⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases ha' : lowerTotalList env (expandFixList alts) with
        | none => rw [ha'] at ha; exact absurd ha (by simp)
        | some t_a =>
          rw [lowerTotalExpr_case_let v hr' hb' ha']
          rfl

private theorem lowerTotalExpr_let_case_isSome (env : List VarId) (v : VarId)
    (rhs body : Expr) (alts : List Expr)
    (hfresh : (freeVarsList alts).contains v = false) :
    (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome ↔
      (lowerTotalExpr env rhs).isSome ∧
      (lowerTotalExpr (v :: env) body).isSome ∧
      (lowerTotalList env (expandFixList alts)).isSome := by
  have hfresh_exp : (freeVarsList (expandFixList alts)).contains v = false :=
    expandFixList_freeVars_not_contains alts v hfresh
  constructor
  · intro hsome
    have h : (lowerTotal env (expandFix
        (.Let [(v, rhs, false)] (.Case body alts)))).isSome := hsome
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
        cases ha_ext : lowerTotalList (v :: env) (expandFixList alts) with
        | none => rw [ha_ext] at h; simp at h
        | some t_a_ext =>
          cases ha : lowerTotalList env (expandFixList alts) with
          | none =>
            have := lowerTotalList_prepend_unused_none_gen [] env v
              (expandFixList alts) (.inl hfresh_exp) (by simpa using ha)
            have hext : lowerTotalList (v :: env) (expandFixList alts) = none := by
              simpa using this
            rw [hext] at ha_ext; exact absurd ha_ext (by simp)
          | some t_a =>
            have hr' : lowerTotalExpr env rhs = some t_r := hr
            have hb' : lowerTotalExpr (v :: env) body = some t_b := hb
            refine ⟨?_, ?_, ?_⟩
            · rw [hr']; rfl
            · rw [hb']; rfl
            · rfl
  · rintro ⟨hr, hb, ha⟩
    cases hr' : lowerTotalExpr env rhs with
    | none => rw [hr'] at hr; exact absurd hr (by simp)
    | some t_r =>
      cases hb' : lowerTotalExpr (v :: env) body with
      | none => rw [hb'] at hb; exact absurd hb (by simp)
      | some t_b =>
        cases ha' : lowerTotalList env (expandFixList alts) with
        | none => rw [ha'] at ha; exact absurd ha (by simp)
        | some t_a =>
          rw [lowerTotalExpr_let_case_fresh v hfresh hr' hb' ha']
          rfl

/-- Helper: LHS of case-let lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_case_let_eq_none (env : List VarId) (v : VarId)
    (rhs body : Expr) (alts : List Expr)
    (h : lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none ∨
         lowerTotalList env (expandFixList alts) = none) :
    lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = none := by
  cases hlhs : lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hr, hb, ha⟩ := (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hs
    rcases h with h | h | h
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)
    · rw [h] at ha; exact absurd ha (by simp)

/-- Helper: RHS of let-case lowers to none when any sub-expression fails to lower. -/
private theorem lowerTotalExpr_let_case_eq_none (env : List VarId) (v : VarId)
    (rhs body : Expr) (alts : List Expr)
    (hfresh : (freeVarsList alts).contains v = false)
    (h : lowerTotalExpr env rhs = none ∨
         lowerTotalExpr (v :: env) body = none ∨
         lowerTotalList env (expandFixList alts) = none) :
    lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = none := by
  cases hlhs : lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) with
  | none => rfl
  | some _ =>
    have hs : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome := by
      rw [hlhs]; rfl
    obtain ⟨hr, hb, ha⟩ := (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hs
    rcases h with h | h | h
    · rw [h] at hr; exact absurd hr (by simp)
    · rw [h] at hb; exact absurd hb (by simp)
    · rw [h] at ha; exact absurd ha (by simp)

theorem mirRefines_let_hoist_case_scrut_fwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (freeVarsList alts).contains v = false) :
    MIRRefines (.Case (.Let [(v, rhs, false)] body) alts)
               (.Let [(v, rhs, false)] (.Case body alts)) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mpr
      ((lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome), ?_⟩
  intro d k env hlen
  cases hr : lowerTotalExpr env rhs with
  | none =>
    rw [lowerTotalExpr_case_let_eq_none env v rhs body alts (.inl hr)]; trivial
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none =>
      rw [lowerTotalExpr_case_let_eq_none env v rhs body alts (.inr (.inl hb))]; trivial
    | some t_b =>
      cases ha : lowerTotalList env (expandFixList alts) with
      | none =>
        rw [lowerTotalExpr_case_let_eq_none env v rhs body alts (.inr (.inr ha))]; trivial
      | some t_a =>
          rw [lowerTotalExpr_case_let v hr hb ha, lowerTotalExpr_let_case_fresh v hfresh hr hb ha]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          -- LHS: compute π₁ ρ₁ (.Case (.Apply (.Lam 0 t_b) t_r) t_a)
          -- 1 step: compute (caseScrutinee t_a ρ₁ :: π₁) ρ₁ (.Apply (.Lam 0 t_b) t_r)
          -- then 3 more: compute (funV (VLam t_b ρ₁) :: caseScrutinee t_a ρ₁ :: π₁) ρ₁ t_r
          have h_steps_lhs :
              steps 4 (State.compute π₁ ρ₁ (.Case (.Apply (.Lam 0 t_b) t_r) t_a)) =
                State.compute (.funV (.VLam t_b ρ₁) :: .caseScrutinee t_a ρ₁ :: π₁) ρ₁ t_r := rfl
          -- RHS: compute π₂ ρ₂ (.Apply (.Lam 0 (.Case t_b (shift t_a))) t_r)
          -- 3 steps → compute (funV (VLam (.Case t_b (shift t_a)) ρ₂) :: π₂) ρ₂ t_r
          have h_steps_rhs :
              steps 3 (State.compute π₂ ρ₂ (.Apply (.Lam 0 (.Case t_b
                (renameTermList (shiftRename 1) t_a))) t_r)) =
                State.compute (.funV (.VLam (.Case t_b
                  (renameTermList (shiftRename 1) t_a)) ρ₂) :: π₂)
                  ρ₂ t_r := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_a : closedAtList env.length t_a :=
            lowerTotalList_closedAtList env _ t_a ha
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
              (.funV (.VLam t_b ρ₁) :: .caseScrutinee t_a ρ₁ :: π₁)
              (.funV (.VLam (.Case t_b
                (renameTermList (shiftRename 1) t_a)) ρ₂) :: π₂) :=
            stackRefK_funV_caseScrut_shift_fwd hclosed_b hclosed_a henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

theorem mirRefines_let_hoist_case_scrut_bwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (freeVarsList alts).contains v = false) :
    MIRRefines (.Let [(v, rhs, false)] (.Case body alts))
               (.Case (.Let [(v, rhs, false)] body) alts) := by
  refine ⟨fun env hsome =>
    (lowerTotalExpr_case_let_isSome env v rhs body alts).mpr
      ((lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome), ?_⟩
  intro d k env hlen
  cases hr : lowerTotalExpr env rhs with
  | none =>
    rw [lowerTotalExpr_let_case_eq_none env v rhs body alts hfresh (.inl hr)]; trivial
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none =>
      rw [lowerTotalExpr_let_case_eq_none env v rhs body alts hfresh (.inr (.inl hb))]
      trivial
    | some t_b =>
      cases ha : lowerTotalList env (expandFixList alts) with
      | none =>
        rw [lowerTotalExpr_let_case_eq_none env v rhs body alts hfresh (.inr (.inr ha))]
        trivial
      | some t_a =>
          rw [lowerTotalExpr_let_case_fresh v hfresh hr hb ha, lowerTotalExpr_case_let v hr hb ha]
          simp only
          intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
          have h_steps_lhs :
              steps 3 (State.compute π₁ ρ₁ (.Apply (.Lam 0 (.Case t_b
                (renameTermList (shiftRename 1) t_a))) t_r)) =
                State.compute (.funV (.VLam (.Case t_b
                  (renameTermList (shiftRename 1) t_a)) ρ₁) :: π₁)
                  ρ₁ t_r := rfl
          have h_steps_rhs :
              steps 4 (State.compute π₂ ρ₂ (.Case (.Apply (.Lam 0 t_b) t_r) t_a)) =
                State.compute (.funV (.VLam t_b ρ₂) :: .caseScrutinee t_a ρ₂ :: π₂) ρ₂ t_r := rfl
          apply obsRefinesK_of_steps_left h_steps_lhs
          apply obsRefinesK_of_steps_right h_steps_rhs
          have hclosed_r : closedAt env.length t_r :=
            lowerTotal_closedAt env _ t_r hr
          have hclosed_b : closedAt (env.length + 1) t_b := by
            have := lowerTotal_closedAt (v :: env) _ t_b hb
            simpa [List.length_cons] using this
          have hclosed_a : closedAtList env.length t_a :=
            lowerTotalList_closedAtList env _ t_a ha
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
              (.funV (.VLam (.Case t_b
                (renameTermList (shiftRename 1) t_a)) ρ₁) :: π₁)
              (.funV (.VLam t_b ρ₂) :: .caseScrutinee t_a ρ₂ :: π₂) :=
            stackRefK_funV_caseScrut_shift_bwd hclosed_b hclosed_a henv_i hπ
          exact ftlr env.length t_r hclosed_r j j (Nat.le_refl _) ρ₁ ρ₂ henv_j i hi
            _ _ hπ_aug

private theorem let_hoist_case_scrut_close_pres_fwd (v : VarId) (rhs body : Expr)
    (alts : List Expr) (hfresh : (freeVarsList alts).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = some t₁ →
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts)).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, ha_some⟩ :=
    (lowerTotalExpr_case_let_isSome env v rhs body alts).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases ha : lowerTotalList env (expandFixList alts) with
      | none => rw [ha] at ha_some; exact absurd ha_some (by simp)
      | some t_a =>
        rw [lowerTotalExpr_case_let v hr hb ha] at h₁
        rw [lowerTotalExpr_let_case_fresh v hfresh hr hb ha] at h₂
        cases h₁; cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, hr_c⟩, ha_c⟩ := hc
        exact ⟨⟨hb_c,
          closedAtList_renameTermList_shiftRename t_a k 1 (by omega) (by omega) ha_c⟩, hr_c⟩

private theorem let_hoist_case_scrut_close_pres_bwd (v : VarId) (rhs body : Expr)
    (alts : List Expr) (hfresh : (freeVarsList alts).contains v = false) :
    ∀ env k t₁ t₂,
      lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts)) = some t₁ →
      lowerTotalExpr env (.Case (.Let [(v, rhs, false)] body) alts) = some t₂ →
      closedAt k t₁ = true → closedAt k t₂ = true := by
  intro env k t₁ t₂ h₁ h₂ hc
  have hsome₁ : (lowerTotalExpr env (.Let [(v, rhs, false)] (.Case body alts))).isSome := by
    rw [h₁]; exact rfl
  obtain ⟨hr_some, hb_some, ha_some⟩ :=
    (lowerTotalExpr_let_case_isSome env v rhs body alts hfresh).mp hsome₁
  cases hr : lowerTotalExpr env rhs with
  | none => rw [hr] at hr_some; exact absurd hr_some (by simp)
  | some t_r =>
    cases hb : lowerTotalExpr (v :: env) body with
    | none => rw [hb] at hb_some; exact absurd hb_some (by simp)
    | some t_b =>
      cases ha : lowerTotalList env (expandFixList alts) with
      | none => rw [ha] at ha_some; exact absurd ha_some (by simp)
      | some t_a =>
        rw [lowerTotalExpr_let_case_fresh v hfresh hr hb ha] at h₁
        rw [lowerTotalExpr_case_let v hr hb ha] at h₂
        cases h₁; cases h₂
        simp only [closedAt, Bool.and_eq_true] at hc ⊢
        obtain ⟨⟨hb_c, ha_sh_c⟩, hr_c⟩ := hc
        exact ⟨⟨hb_c, hr_c⟩,
          closedAtList_renameTermList_shiftRename_inv t_a k 1 (by omega) (by omega) ha_sh_c⟩

theorem mirCtxRefines_let_hoist_case_scrut_fwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (freeVarsList alts).contains v = false) :
    MIRCtxRefines (.Case (.Let [(v, rhs, false)] body) alts)
                  (.Let [(v, rhs, false)] (.Case body alts)) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_case_scrut_fwd v rhs body alts hfresh)
    (let_hoist_case_scrut_close_pres_fwd v rhs body alts hfresh)

theorem mirCtxRefines_let_hoist_case_scrut_bwd (v : VarId) (rhs body : Expr) (alts : List Expr)
    (hfresh : (freeVarsList alts).contains v = false) :
    MIRCtxRefines (.Let [(v, rhs, false)] (.Case body alts))
                  (.Case (.Let [(v, rhs, false)] body) alts) :=
  mirRefines_to_mirCtxRefines
    (mirRefines_let_hoist_case_scrut_bwd v rhs body alts hfresh)
    (let_hoist_case_scrut_close_pres_bwd v rhs body alts hfresh)
end Moist.Verified.MIR
