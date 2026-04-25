import Moist.Verified.MIR
import Moist.Verified.MIR.AlphaRenameSoundness
import Moist.Verified.InlineSoundness.Beta
import Moist.Verified.InlineSoundness.StrictOcc
import Moist.Verified.InlineSoundness.SubstRefinesExt
import Moist.Verified.FundamentalRefines
import Moist.Verified.Definitions.BudgetExhaustion
import Moist.Verified.TermObsRefinesWF
import Moist.Verified.FundamentalRefinesWF
import Moist.MIR.Optimize.Inline

/-! # Substitution-lowering commutation and UPLC beta rules

-/

namespace Moist.Verified.InlineSoundness.SubstCommute

open Moist.CEK
open Moist.Plutus.Term (Term)
open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal lowerTotalLet
  expandFix expandFixBinds subst substInBindings substList)
open Moist.Verified (closedAt substTerm renameTerm shiftRename)
open Moist.Verified.Equivalence (ObsRefinesK Reaches steps)
open Moist.Verified.Contextual
  (CtxRefines ctxRefines_refl ctxRefines_trans ObsRefines)
open Moist.Verified.Contextual.SoundnessRefines
  (OpenRefines OpenRefinesK BehRefinesK ValueRefinesK EnvRefinesK
   StackRefK soundness_refines)
open Moist.Verified.InlineSoundness.StrictOcc
  (StrictSingleOcc StrictSingleOccList SingleOcc SingleOccList freeOf freeOfList
   strict_subst_reaches_error same_env_beta_obsRefines same_env_beta_single_obsRefines
   same_env_beta_multi_obsRefines)

/-! ## 3. UPLC-level beta rules at OpenRefines level

Branch C (impure strict): uses `budget_exhaustion` + `StrictSingleOcc`.
For each (ρ₁, π₁), case-split on whether t_rhs halts via `halt_or_error`.

Branches A/B (atoms, values, pure): use `uplc_beta_refines` from Beta.lean
directly — those terms always halt, so `h_rhalts_maker` is satisfiable. -/

section BranchC

open Moist.Verified (halt_or_error)
open Moist.Verified.BetaValueRefines (steps_trans steps_error_fixed
  steps_halt_fixed hasSuffix halt_descends_to_baseπ)

private theorem reaches_halt_not_error {s : State} {v : CekValue}
    (hv : Reaches s (.halt v)) (he : Reaches s .error) : False := by
  obtain ⟨m, hm⟩ := hv; obtain ⟨n, hn⟩ := he
  have h1 : steps (m + n) s = .halt v := by rw [steps_trans, hm, steps_halt_fixed]
  have h2 : steps (n + m) s = .error := by rw [steps_trans, hn, steps_error_fixed]
  rw [show m + n = n + m from Nat.add_comm m n] at h1; rw [h1] at h2
  exact State.noConfusion h2

private theorem error_of_halt_then_error {s : State} {n m : Nat} {v : CekValue}
    (h_halt : steps n s = .halt v) (h_err : steps m s = .error) : False := by
  by_cases hle : n ≤ m
  · have : m = n + (m - n) := by omega
    rw [this, steps_trans, h_halt, steps_halt_fixed] at h_err
    exact State.noConfusion h_err
  · have : n = m + (n - m) := by omega
    rw [this, steps_trans, h_err, steps_error_fixed] at h_halt
    exact State.noConfusion h_halt

private theorem steps_equiv : ∀ (n : Nat) (s : State),
    Moist.Verified.Equivalence.steps n s = Moist.Verified.Semantics.steps n s := by
  intro n; induction n with
  | zero => intro s; rfl
  | succ m ih => intro s; show steps m (step s) = Moist.Verified.Semantics.steps m (step s); exact ih _

private theorem reaches_equiv {s s' : State} :
    Moist.Verified.Equivalence.Reaches s s' ↔ Moist.Verified.Semantics.Reaches s s' := by
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [← steps_equiv]; exact hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, by rw [steps_equiv]; exact hn⟩

theorem uplc_beta_impure_strict_openRefines {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (h_strict : StrictSingleOcc 1 t_body) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) := by
  apply Moist.Verified.TermObsRefinesWF.soundness_refinesWF (d := d)
  · intro k j hj ρ₁ ρ₂ henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
    have h_apply_closed : closedAt d (.Apply (.Lam 0 t_body) t_rhs) = true := by
      simp [closedAt]; exact ⟨hclosed_body, hclosed_rhs⟩
    have h_beta : ObsRefines
        (.compute π₂ ρ₂ (.Apply (.Lam 0 t_body) t_rhs))
        (.compute π₂ ρ₂ (substTerm 1 t_rhs t_body)) :=
      same_env_beta_obsRefines h_strict hclosed_body hclosed_rhs ρ₂ π₂
        henv_wf_r hlen_r hwf_π₂
    have h_self_refine : ObsRefinesK i
        (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) t_rhs))
        (.compute π₂ ρ₂ (.Apply (.Lam 0 t_body) t_rhs)) :=
      Moist.Verified.FundamentalRefinesWF.ftlr_wf d _ h_apply_closed k j hj ρ₁ ρ₂
        henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
    exact Moist.Verified.InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
      h_self_refine h_beta
  · intro C hC1
    have h_apply_closed := (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mp hC1
    simp only [Nat.zero_add] at h_apply_closed
    have hC_outer := h_apply_closed.1
    have h_inner := h_apply_closed.2
    simp only [closedAt, Bool.and_eq_true] at h_inner
    have hbody_closed := h_inner.1
    have hrhs_closed := h_inner.2
    have h_subst_closed : closedAt C.binders (substTerm 1 t_rhs t_body) = true :=
      Moist.Verified.BetaValueRefines.closedAt_substTerm 1 t_rhs t_body C.binders
        (by omega) (by omega) hrhs_closed hbody_closed
    exact (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mpr
      ⟨hC_outer, by simpa [Nat.zero_add] using h_subst_closed⟩

end BranchC

/-! ## 3b. Branch A/B: Beta reduction for atoms (Var/Constant/Builtin)

For atom RHS, `StrictSingleOcc` may not hold (the variable can appear
multiple times). We case-split on the compiled UPLC atom shape:

* **Constant / Builtin** — use `uplc_beta_ctxRefines_halting` with
  `rHaltsRelN_constant` / `rHaltsRelN_builtin`.
* **Var n (n ≥ 1)** — `substTerm 1 (Var n) body` equals
  `renameTerm σ body` for a specific renaming `σ`. We directly
  construct `OpenRefines` via Apply+Lam+Var stepping composed with
  `renameRefinesR`, then lift via `soundness_refines`. -/

section BranchAB

open Moist.Verified (liftRename renameTermList)
open Moist.Verified.BetaValueRefines
  (closedAt_substTerm)
open Moist.Verified.FundamentalRefines
  (RenameEnvRefR Is0Preserving renameRefinesR renameEnvRefR_mono)

private def substVarRename (pos n : Nat) : Nat → Nat
  | k => if k < pos then k else if k = pos then n else k - 1

private theorem substVarRename_is0preserving {pos n : Nat}
    (hpos : pos ≥ 1) (hn : n ≥ 1) :
    Is0Preserving (substVarRename pos n) := by
  refine ⟨?_, ?_⟩
  · show substVarRename pos n 0 = 0
    simp only [substVarRename, if_pos (show 0 < pos by omega)]
  · intro m hm; show substVarRename pos n m ≥ 1
    simp only [substVarRename]
    by_cases h1 : m < pos
    · rw [if_pos h1]; omega
    · rw [if_neg h1]
      by_cases h2 : m = pos
      · rw [if_pos h2]; exact hn
      · rw [if_neg h2]; omega

private theorem liftRename_substVarRename (pos n : Nat) (hpos : pos ≥ 1) :
    liftRename (substVarRename pos n) = substVarRename (pos + 1) (n + 1) := by
  funext k; match k with
  | 0 => simp [liftRename, substVarRename, show (0 : Nat) < pos + 1 by omega]
  | 1 => simp [liftRename, substVarRename, show (1 : Nat) < pos + 1 by omega]
  | k + 2 =>
    show substVarRename pos n (k + 1) + 1 = substVarRename (pos + 1) (n + 1) (k + 2)
    simp only [substVarRename]
    by_cases h1 : k + 1 < pos
    · rw [if_pos h1, if_pos (show k + 2 < pos + 1 by omega)]
    · rw [if_neg h1]
      by_cases h2 : k + 1 = pos
      · rw [if_pos h2, if_neg (show ¬(k + 2 < pos + 1) by omega),
            if_pos (show k + 2 = pos + 1 by omega)]
      · rw [if_neg h2, if_neg (show ¬(k + 2 < pos + 1) by omega),
            if_neg (show ¬(k + 2 = pos + 1) by omega)]
        omega

mutual
private theorem substTerm_var_eq_renameTerm (pos n : Nat) (hpos : pos ≥ 1) (hn : n ≥ 1)
    (t : Term) :
    substTerm pos (.Var n) t = renameTerm (substVarRename pos n) t := by
  match t with
  | .Var k =>
    simp only [substTerm, renameTerm]
    show (if k = pos then Term.Var n else if k > pos then Term.Var (k - 1) else Term.Var k) =
         Term.Var (substVarRename pos n k)
    simp only [substVarRename]
    by_cases h1 : k = pos
    · subst h1; rw [if_pos rfl, if_neg (Nat.lt_irrefl _), if_pos rfl]
    · rw [if_neg h1]
      by_cases h2 : k > pos
      · rw [if_pos h2, if_neg (show ¬(k < pos) by omega), if_neg (show ¬(k = pos) from h1)]
      · rw [if_neg h2, if_pos (show k < pos by omega)]
  | .Constant c => simp [substTerm, renameTerm]
  | .Builtin b => simp [substTerm, renameTerm]
  | .Error => simp [substTerm, renameTerm]
  | .Lam name body =>
    simp only [substTerm, renameTerm]
    congr 1
    have h_shift : shiftRename 1 n = n + 1 := by
      simp only [shiftRename]; rw [if_pos (show n ≥ 1 from hn)]
    rw [h_shift, liftRename_substVarRename pos n hpos]
    exact substTerm_var_eq_renameTerm (pos + 1) (n + 1) (by omega) (by omega) body
  | .Apply f x =>
    simp only [substTerm, renameTerm]
    rw [substTerm_var_eq_renameTerm pos n hpos hn f,
        substTerm_var_eq_renameTerm pos n hpos hn x]
  | .Force e =>
    simp only [substTerm, renameTerm]
    exact congrArg _ (substTerm_var_eq_renameTerm pos n hpos hn e)
  | .Delay e =>
    simp only [substTerm, renameTerm]
    exact congrArg _ (substTerm_var_eq_renameTerm pos n hpos hn e)
  | .Constr tag args =>
    simp only [substTerm, renameTerm]
    exact congrArg _ (substTermList_var_eq_renameTermList pos n hpos hn args)
  | .Case scrut alts =>
    simp only [substTerm, renameTerm]
    rw [substTerm_var_eq_renameTerm pos n hpos hn scrut,
        substTermList_var_eq_renameTermList pos n hpos hn alts]
termination_by sizeOf t

private theorem substTermList_var_eq_renameTermList (pos n : Nat) (hpos : pos ≥ 1) (hn : n ≥ 1)
    (ts : List Term) :
    Moist.Verified.substTermList pos (.Var n) ts =
      renameTermList (substVarRename pos n) ts := by
  match ts with
  | [] => simp [Moist.Verified.substTermList, renameTermList]
  | t :: rest =>
    simp only [Moist.Verified.substTermList, renameTermList]
    rw [substTerm_var_eq_renameTerm pos n hpos hn t,
        substTermList_var_eq_renameTermList pos n hpos hn rest]
termination_by sizeOf ts
end

private theorem renameEnvRefR_substVar_of_envRefinesK {d n j : Nat}
    {ρ₁ ρ₂ : CekEnv} {v₁ : CekValue}
    (hn : n ≥ 1) (hnd : n ≤ d)
    (henv : EnvRefinesK j d ρ₁ ρ₂)
    (hv₁ : ρ₁.lookup n = some v₁) :
    RenameEnvRefR (substVarRename 1 n) j (d + 1) (ρ₁.extend v₁) ρ₂ := by
  intro m hm hmd
  show match (ρ₁.extend v₁).lookup m, ρ₂.lookup (substVarRename 1 n m) with
    | some a, some b => ValueRefinesK j a b
    | none, none => True | _, _ => False
  by_cases hm1 : m = 1
  · subst hm1
    rw [Moist.Verified.BetaValueRefines.extend_lookup_one]
    have h_svr : substVarRename 1 n 1 = n := by simp [substVarRename]
    rw [h_svr]
    obtain ⟨w₁, w₂, hw₁, hw₂, hw_rel⟩ := henv n hn hnd
    rw [hv₁] at hw₁; cases hw₁
    rw [hw₂]; exact hw_rel
  · have hm2 : m ≥ 2 := by omega
    have h_extend : (ρ₁.extend v₁).lookup m = ρ₁.lookup (m - 1) := by
      have := Moist.Verified.BetaValueRefines.extend_lookup_succ ρ₁ v₁ (m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this
    have h_svr : substVarRename 1 n m = m - 1 := by
      simp only [substVarRename]
      rw [if_neg (show ¬(m < 1) by omega), if_neg (show ¬(m = 1) from hm1)]
    rw [h_extend, h_svr]
    obtain ⟨w₁, w₂, hw₁, hw₂, hw_rel⟩ := henv (m - 1) (by omega) (by omega)
    rw [hw₁, hw₂]; exact hw_rel

private theorem var_step_to_body {n : Nat} {π : Stack} {ρ : CekEnv}
    {t_body : Term} {v : CekValue}
    (hv : ρ.lookup n = some v) :
    steps 5 (.compute π ρ (.Apply (.Lam 0 t_body) (.Var n)))
      = .compute π (ρ.extend v) t_body := by
  show steps 4 (step (.compute π ρ (.Apply (.Lam 0 t_body) (.Var n)))) = _
  simp only [step]
  show steps 3 (step (.compute (Frame.arg (.Var n) ρ :: π) ρ (.Lam 0 t_body))) = _
  simp only [step]
  show steps 2 (step (.ret (Frame.arg (.Var n) ρ :: π) (.VLam t_body ρ))) = _
  simp only [step]
  show steps 1 (step (.compute (Frame.funV (.VLam t_body ρ) :: π) ρ (.Var n))) = _
  simp only [step, hv]
  show step (.ret (Frame.funV (.VLam t_body ρ) :: π) v) = _
  simp only [step]

theorem uplc_beta_var_openRefines {d : Nat} {t_body : Term} {n : Nat}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hn : n ≥ 1) (hnd : n ≤ d) :
    CtxRefines (.Apply (.Lam 0 t_body) (.Var n)) (substTerm 1 (.Var n) t_body) := by
  rw [substTerm_var_eq_renameTerm 1 n (by omega) hn t_body]
  apply soundness_refines (d := d)
  · intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
    obtain ⟨v₁, _, hv₁, _, _⟩ := henv n hn hnd
    have h_steps := @var_step_to_body n π₁ ρ₁ t_body v₁ hv₁
    apply Moist.Verified.BetaValueRefines.obsRefinesK_of_steps_left h_steps
    have h_rename_env : RenameEnvRefR (substVarRename 1 n) i (d + 1) (ρ₁.extend v₁) ρ₂ :=
      renameEnvRefR_mono (show i ≤ j from hi)
        (renameEnvRefR_substVar_of_envRefinesK hn hnd henv hv₁)
    exact renameRefinesR (substVarRename 1 n) (substVarRename_is0preserving (by omega) hn)
      (d + 1) t_body hclosed_body k i (Nat.le_trans hi hj)
      (ρ₁.extend v₁) ρ₂ h_rename_env i (Nat.le_refl _) π₁ π₂ hπ
  · intro C hC1
    have h_apply_closed := (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mp hC1
    simp only [Nat.zero_add] at h_apply_closed
    have hC_outer := h_apply_closed.1
    have h_inner := h_apply_closed.2
    simp only [closedAt, Bool.and_eq_true] at h_inner
    have hbody_closed := h_inner.1
    have hrhs_closed := h_inner.2
    have hrhs_closed' : closedAt C.binders (.Var n) = true := by
      simp only [closedAt]; exact hrhs_closed
    have h_subst_closed : closedAt C.binders (renameTerm (substVarRename 1 n) t_body) = true := by
      rw [← substTerm_var_eq_renameTerm 1 n (by omega) hn t_body]
      exact closedAt_substTerm 1 (.Var n) t_body C.binders
        (by omega) (by omega) hrhs_closed' hbody_closed
    exact (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mpr
      ⟨hC_outer, by simpa [Nat.zero_add] using h_subst_closed⟩

end BranchAB

/-! ## 4. Composed beta CtxRefines -/

theorem uplc_beta_ctxRefines_halting {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (h_rhalts_maker : ∀ (k : Nat) (ρ₁ : CekEnv),
       (∀ n, 0 < n → n ≤ d → ∃ v, ρ₁.lookup n = some v) →
       ∀ (π : Stack), ∃ (m : Nat) (v₁ : CekValue),
         steps m (.compute π ρ₁ t_rhs) = .ret π v₁ ∧
         (∀ k' ≤ m, steps k' (.compute π ρ₁ t_rhs) ≠ .error) ∧
         Moist.Verified.BetaValueRefines.ValueWellFormed v₁ ∧
         Moist.Verified.SubstRefines.RHaltsRelN t_rhs v₁ k d) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) := by
  apply soundness_refines
    (fun k => Moist.Verified.InlineSoundness.Beta.uplc_beta_refines
      hclosed_body hclosed_rhs (h_rhalts_maker k))
  intro C hC1
  have h_apply_closed := (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mp hC1
  simp only [Nat.zero_add] at h_apply_closed
  have hC_outer := h_apply_closed.1
  have h_inner := h_apply_closed.2
  simp only [closedAt, Bool.and_eq_true] at h_inner
  have hbody_closed := h_inner.1
  have hrhs_closed := h_inner.2
  have h_subst_closed : closedAt C.binders (substTerm 1 t_rhs t_body) = true :=
    Moist.Verified.BetaValueRefines.closedAt_substTerm 1 t_rhs t_body C.binders
      (by omega) (by omega) hrhs_closed hbody_closed
  exact (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mpr
    ⟨hC_outer, by simpa [Nat.zero_add] using h_subst_closed⟩

theorem uplc_beta_ctxRefines_impure_strict {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (h_strict : StrictSingleOcc 1 t_body) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) :=
  uplc_beta_impure_strict_openRefines hclosed_body hclosed_rhs h_strict

theorem uplc_beta_single_pure_openRefines {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (h_single : SingleOcc 1 t_body)
    (h_rhs_halts : ∀ (ρ : CekEnv),
      (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∀ (π : Stack), ∃ (m : Nat) (v : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v ∧
        ∀ k ≤ m, steps k (.compute π ρ t_rhs) ≠ .error) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) := by
  apply Moist.Verified.TermObsRefinesWF.soundness_refinesWF (d := d)
  · intro k j hj ρ₁ ρ₂ henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
    have h_apply_closed : closedAt d (.Apply (.Lam 0 t_body) t_rhs) = true := by
      simp [closedAt]; exact ⟨hclosed_body, hclosed_rhs⟩
    have hwf_ρ₂ : ∀ n, 0 < n → n ≤ d → ∃ v, ρ₂.lookup n = some v := by
      intro n hn hnd
      obtain ⟨v, hv, _⟩ := Moist.Verified.BetaValueRefines.envWellFormed_lookup d henv_wf_r hn hnd
      exact ⟨v, hv⟩
    have h_beta : ObsRefines
        (.compute π₂ ρ₂ (.Apply (.Lam 0 t_body) t_rhs))
        (.compute π₂ ρ₂ (substTerm 1 t_rhs t_body)) :=
      same_env_beta_single_obsRefines h_single hclosed_body hclosed_rhs ρ₂ π₂
        henv_wf_r hlen_r hwf_π₂ (h_rhs_halts ρ₂ hwf_ρ₂)
    have h_self_refine : ObsRefinesK i
        (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) t_rhs))
        (.compute π₂ ρ₂ (.Apply (.Lam 0 t_body) t_rhs)) :=
      Moist.Verified.FundamentalRefinesWF.ftlr_wf d _ h_apply_closed k j hj ρ₁ ρ₂
        henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
    exact Moist.Verified.InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
      h_self_refine h_beta
  · intro C hC1
    have h_apply_closed := (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mp hC1
    simp only [Nat.zero_add] at h_apply_closed
    have hC_outer := h_apply_closed.1
    have h_inner := h_apply_closed.2
    simp only [closedAt, Bool.and_eq_true] at h_inner
    have hbody_closed := h_inner.1
    have hrhs_closed := h_inner.2
    have h_subst_closed : closedAt C.binders (substTerm 1 t_rhs t_body) = true :=
      Moist.Verified.BetaValueRefines.closedAt_substTerm 1 t_rhs t_body C.binders
        (by omega) (by omega) hrhs_closed hbody_closed
    exact (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mpr
      ⟨hC_outer, by simpa [Nat.zero_add] using h_subst_closed⟩

open Moist.Plutus.Term (Const BuiltinType BuiltinFun) in
theorem uplc_beta_constant_ctxRefines {d : Nat} {t_body : Term}
    {c : Const} {ty : BuiltinType}
    (hclosed_body : closedAt (d + 1) t_body = true) :
    CtxRefines (.Apply (.Lam 0 t_body) (.Constant (c, ty)))
              (substTerm 1 (.Constant (c, ty)) t_body) :=
  uplc_beta_ctxRefines_halting hclosed_body (by simp [closedAt])
    fun k _ρ₁ _ π => ⟨1, .VCon c,
      by show step (.compute π _ρ₁ (.Constant (c, ty))) = .ret π (.VCon c); simp only [step],
      fun k' hk' => by match k' with
        | 0 => simp [steps]
        | 1 => show step (.compute π _ρ₁ (.Constant (c, ty))) ≠ .error
               simp only [step]; exact State.noConfusion,
      Moist.Verified.BetaValueRefines.ValueWellFormed.vcon c,
      Moist.Verified.InlineSoundness.Beta.rHaltsRelN_constant c ty k d⟩

open Moist.Plutus.Term (BuiltinFun) in
theorem uplc_beta_builtin_ctxRefines {d : Nat} {t_body : Term}
    {b : BuiltinFun}
    (hclosed_body : closedAt (d + 1) t_body = true) :
    CtxRefines (.Apply (.Lam 0 t_body) (.Builtin b))
              (substTerm 1 (.Builtin b) t_body) :=
  uplc_beta_ctxRefines_halting hclosed_body (by simp [closedAt])
    fun k _ρ₁ _ π => ⟨1, .VBuiltin b [] (expectedArgs b),
      by show step (.compute π _ρ₁ (.Builtin b)) = .ret π (.VBuiltin b [] (expectedArgs b)); simp only [step],
      fun k' hk' => by match k' with
        | 0 => simp [steps]
        | 1 => show step (.compute π _ρ₁ (.Builtin b)) ≠ .error
               simp only [step]; exact State.noConfusion,
      Moist.Verified.BetaValueRefines.ValueWellFormed.vbuiltin b (expectedArgs b) Moist.Verified.BetaValueRefines.ValueListWellFormed.nil,
      Moist.Verified.InlineSoundness.Beta.rHaltsRelN_builtin b k d⟩

private theorem fixLamWrapUplc_steps16 (body_l : Term) (ρ : CekEnv) (π : Stack) :
    let t_s := Term.Apply (.Lam 0 (.Lam 0 body_l))
      (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)))
    let ρ₂ := (ρ.extend (.VLam t_s ρ)).extend
      (.VLam (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1)) (ρ.extend (.VLam t_s ρ)))
    steps 16 (.compute π ρ (Moist.MIR.fixLamWrapUplc body_l)) =
      .ret π (.VLam body_l ρ₂) := by
  rfl

theorem fixLamWrapUplc_halts (body_l : Term) (ρ : CekEnv) (π : Stack) :
    ∃ (m : Nat) (v : CekValue),
      steps m (.compute π ρ (Moist.MIR.fixLamWrapUplc body_l)) = .ret π v ∧
      ∀ k ≤ m, steps k (.compute π ρ (Moist.MIR.fixLamWrapUplc body_l)) ≠ .error := by
  refine ⟨16, _, fixLamWrapUplc_steps16 body_l ρ π, ?_⟩
  intro k hk h_err
  have h16 := fixLamWrapUplc_steps16 body_l ρ π
  have : 16 = k + (16 - k) := by omega
  rw [this, Moist.Verified.BetaValueRefines.steps_trans, h_err,
      Moist.Verified.BetaValueRefines.steps_error_fixed] at h16
  exact State.noConfusion h16

theorem uplc_beta_multi_pure_openRefines {d : Nat} {t_body t_rhs : Term}
    (hclosed_body : closedAt (d + 1) t_body = true)
    (hclosed_rhs : closedAt d t_rhs = true)
    (h_rhs_halts : ∀ (ρ : CekEnv),
      (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∀ (π : Stack), ∃ (m : Nat) (v : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v ∧
        ∀ k ≤ m, steps k (.compute π ρ t_rhs) ≠ .error) :
    CtxRefines (.Apply (.Lam 0 t_body) t_rhs) (substTerm 1 t_rhs t_body) := by
  apply Moist.Verified.TermObsRefinesWF.soundness_refinesWF (d := d)
  · intro k j hj ρ₁ ρ₂ henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
    have h_apply_closed : closedAt d (.Apply (.Lam 0 t_body) t_rhs) = true := by
      simp [closedAt]; exact ⟨hclosed_body, hclosed_rhs⟩
    have hwf_ρ₂ : ∀ n, 0 < n → n ≤ d → ∃ v, ρ₂.lookup n = some v := by
      intro n hn hnd
      obtain ⟨v, hv, _⟩ := Moist.Verified.BetaValueRefines.envWellFormed_lookup d henv_wf_r hn hnd
      exact ⟨v, hv⟩
    have h_beta : ObsRefines
        (.compute π₂ ρ₂ (.Apply (.Lam 0 t_body) t_rhs))
        (.compute π₂ ρ₂ (substTerm 1 t_rhs t_body)) :=
      same_env_beta_multi_obsRefines hclosed_body hclosed_rhs ρ₂ π₂
        henv_wf_r hlen_r hwf_π₂ (h_rhs_halts ρ₂ hwf_ρ₂)
    have h_self_refine : ObsRefinesK i
        (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) t_rhs))
        (.compute π₂ ρ₂ (.Apply (.Lam 0 t_body) t_rhs)) :=
      Moist.Verified.FundamentalRefinesWF.ftlr_wf d _ h_apply_closed k j hj ρ₁ ρ₂
        henv henv_wf_l hlen_l henv_wf_r hlen_r i hi π₁ π₂ hwf_π₁ hwf_π₂ hπ
    exact Moist.Verified.InlineSoundness.SubstRefinesExt.obsRefinesK_compose_obsRefines_right
      h_self_refine h_beta
  · intro C hC1
    have h_apply_closed := (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mp hC1
    simp only [Nat.zero_add] at h_apply_closed
    have hC_outer := h_apply_closed.1
    have h_inner := h_apply_closed.2
    simp only [closedAt, Bool.and_eq_true] at h_inner
    have hbody_closed := h_inner.1
    have hrhs_closed := h_inner.2
    have h_subst_closed : closedAt C.binders (substTerm 1 t_rhs t_body) = true :=
      Moist.Verified.BetaValueRefines.closedAt_substTerm 1 t_rhs t_body C.binders
        (by omega) (by omega) hrhs_closed hbody_closed
    exact (Moist.Verified.Contextual.fill_closedAt_iff C _ 0).mpr
      ⟨hC_outer, by simpa [Nat.zero_add] using h_subst_closed⟩

/-! ## 5. Phase 2: Substitution / Lowering commutation

MIR-level `subst` followed by `lowerTotal ∘ expandFix` equals lowering under
an extended env and applying UPLC-level `substTerm`. This is the core
correctness property bridging MIR (named variables, fresh-name allocation
for capture-avoidance) and UPLC (de Bruijn indices, explicit shifting).

* Phase 2a (`subst_lowerTotal_comm_gen` / `subst_lowerTotal_comm`) — single
  expression.
* Phase 2b (`substInBindings_lowerTotalLet_comm_gen` /
  `substInBindings_lowerTotalLet_comm`) — let-binding lists; proved by
  induction on `rest` using Phase 2a at each step. -/

section Phase2

open Moist.Verified.SubstRefines (iterShift iterShift_zero iterShift_succ iterShift_shift)
open Moist.MIR (envLookupT distinctBinders)

/-
### Phase 2a + Option B2 scaffolding: alpha-rename prefix into fresh form

Phase 2a states: substituting `v` with `rhs` at MIR level, where `v` lives
at position `prefix_env.length` of the MIR env, corresponds to UPLC
`substTerm` at that position with `t_rhs` shifted by `prefix_env.length`
(to lift its free variables over the prefix binders). The `hv_notin`
hypothesis ensures `v` is not shadowed by any binder in `prefix_env`.

Phase 2a is internally false when `prefix_env` has a binder colliding
with `freeVars rhs` — `subst v rhs body = rhs` would then be captured by
the colliding prefix binder at lowering time, but UPLC `substTerm` assumes
no such capture. We route around this by alpha-renaming `prefix_env` to a
fresh form that is disjoint from `freeVars rhs`, `env`, and `v`, proving
the commutation on the fresh version (Section 5.2), and transferring back
via `alphaRename_lowerTotal_eq` (Section 5.4).

The scaffolding has four parts:
* 5.1 — supporting lemmas: shifted lowering under fresh prefix, env
  lookup decomposition, expandFix / subst interaction helpers.
* 5.2 — `subst_lowerTotal_comm_fresh` + list/let variants; mutual induction
  on `body` with the freshness hypothesis guaranteeing no capture.
* 5.3 — `freshenPrefix`: construct a fresh prefix env from a FreshState
  above a uid bound, plus a rename substitution σ.
* 5.4 — `subst_lowerTotal_comm_gen`: main theorem, invokes 5.2 on the
  freshened form and transfers back via `alphaRename_lowerTotal_eq`.
-/

-- === Section 5.0: `noCaptureFrom` predicate ===

/- `noCaptureFrom fv e` holds when every binder in `e` is absent from the
    variable set `fv`. When `fv = freeVars rhs`, this precondition ensures
    that `subst v rhs body` never takes its capture-avoidance branch (which
    would rename a binder `x ∈ freeVars rhs`). Used to make the
    capture-avoidance branches vacuous in the fresh Phase 2a proof. -/
mutual
  def noCaptureFrom (fv : Moist.MIR.VarSet) : Expr → Bool
    | .Var _ => true
    | .Lit _ => true
    | .Builtin _ => true
    | .Error => true
    | .Lam x body => !fv.contains x && noCaptureFrom fv body
    | .Fix f body => !fv.contains f && noCaptureFrom fv body
    | .App f x => noCaptureFrom fv f && noCaptureFrom fv x
    | .Force e => noCaptureFrom fv e
    | .Delay e => noCaptureFrom fv e
    | .Constr _ args => noCaptureFromList fv args
    | .Case s alts => noCaptureFrom fv s && noCaptureFromList fv alts
    | .Let binds body => noCaptureFromLet fv binds body
  termination_by e => sizeOf e

  def noCaptureFromList (fv : Moist.MIR.VarSet) : List Expr → Bool
    | [] => true
    | e :: rest => noCaptureFrom fv e && noCaptureFromList fv rest
  termination_by es => sizeOf es

  def noCaptureFromLet (fv : Moist.MIR.VarSet)
      : List (VarId × Expr × Bool) → Expr → Bool
    | [], body => noCaptureFrom fv body
    | (x, rhs, _) :: rest, body =>
      !fv.contains x && noCaptureFrom fv rhs && noCaptureFromLet fv rest body
  termination_by binds body => sizeOf binds + sizeOf body
end

theorem noCaptureFrom_lam {fv : Moist.MIR.VarSet} {x : VarId} {body : Expr}
    (h : noCaptureFrom fv (.Lam x body) = true) :
    fv.contains x = false ∧ noCaptureFrom fv body = true := by
  simp only [noCaptureFrom, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h

theorem noCaptureFrom_fix {fv : Moist.MIR.VarSet} {f : VarId} {body : Expr}
    (h : noCaptureFrom fv (.Fix f body) = true) :
    fv.contains f = false ∧ noCaptureFrom fv body = true := by
  simp only [noCaptureFrom, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h

theorem noCaptureFrom_app {fv : Moist.MIR.VarSet} {f x : Expr}
    (h : noCaptureFrom fv (.App f x) = true) :
    noCaptureFrom fv f = true ∧ noCaptureFrom fv x = true := by
  simp only [noCaptureFrom, Bool.and_eq_true] at h; exact h

theorem noCaptureFrom_force {fv : Moist.MIR.VarSet} {e : Expr}
    (h : noCaptureFrom fv (.Force e) = true) :
    noCaptureFrom fv e = true := by
  simp only [noCaptureFrom] at h; exact h

theorem noCaptureFrom_delay {fv : Moist.MIR.VarSet} {e : Expr}
    (h : noCaptureFrom fv (.Delay e) = true) :
    noCaptureFrom fv e = true := by
  simp only [noCaptureFrom] at h; exact h

theorem noCaptureFrom_constr {fv : Moist.MIR.VarSet} {tag : Nat} {args : List Expr}
    (h : noCaptureFrom fv (.Constr tag args) = true) :
    noCaptureFromList fv args = true := by
  simp only [noCaptureFrom] at h; exact h

theorem noCaptureFrom_case {fv : Moist.MIR.VarSet} {s : Expr} {alts : List Expr}
    (h : noCaptureFrom fv (.Case s alts) = true) :
    noCaptureFrom fv s = true ∧ noCaptureFromList fv alts = true := by
  simp only [noCaptureFrom, Bool.and_eq_true] at h; exact h

theorem noCaptureFrom_let {fv : Moist.MIR.VarSet}
    {binds : List (VarId × Expr × Bool)} {body : Expr}
    (h : noCaptureFrom fv (.Let binds body) = true) :
    noCaptureFromLet fv binds body = true := by
  simp only [noCaptureFrom] at h; exact h

theorem noCaptureFromList_cons {fv : Moist.MIR.VarSet} {e : Expr} {rest : List Expr}
    (h : noCaptureFromList fv (e :: rest) = true) :
    noCaptureFrom fv e = true ∧ noCaptureFromList fv rest = true := by
  simp only [noCaptureFromList, Bool.and_eq_true] at h; exact h

theorem noCaptureFromLet_cons {fv : Moist.MIR.VarSet}
    {x : VarId} {rhs_h : Expr} {er : Bool}
    {rest : List (VarId × Expr × Bool)} {body : Expr}
    (h : noCaptureFromLet fv ((x, rhs_h, er) :: rest) body = true) :
    fv.contains x = false ∧ noCaptureFrom fv rhs_h = true ∧
    noCaptureFromLet fv rest body = true := by
  simp only [noCaptureFromLet, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem noCaptureFromLet_nil_body {fv : Moist.MIR.VarSet} {body : Expr}
    (h : noCaptureFromLet fv [] body = true) :
    noCaptureFrom fv body = true := by
  simp only [noCaptureFromLet] at h; exact h

-- === Section 5.1: Supporting lemmas for the fresh-prefix case ===

/-- `envLookupT (prefix_env ++ env) x`: if `x` hits `prefix_env`, return its
    local position; otherwise, the env lookup shifted by `prefix_env.length`. -/
private theorem envLookupT_prefix_env
    (x : VarId) (prefix_env env : List VarId) :
    envLookupT (prefix_env ++ env) x =
      match envLookupT prefix_env x with
      | some j => some j
      | none => (envLookupT env x).map (fun i => prefix_env.length + i) := by
  induction prefix_env with
  | nil =>
    show envLookupT env x = _
    have h_nil : envLookupT ([] : List VarId) x = none := rfl
    rw [h_nil]
    cases h : envLookupT env x <;> simp [Option.map]
  | cons y rest ih =>
    by_cases hyx : (y == x) = true
    · have h1 : envLookupT (y :: rest ++ env) x = some 0 := by
        show envLookupT.go x (y :: rest ++ env) 0 = _
        simp only [List.cons_append, envLookupT.go, hyx, if_true]
      have h2 : envLookupT (y :: rest) x = some 0 := by
        show envLookupT.go x (y :: rest) 0 = _
        simp only [envLookupT.go, hyx, if_true]
      rw [h1, h2]
    · have hne : (y == x) = false := by cases h : (y == x); rfl; exact absurd h hyx
      have h1 : envLookupT (y :: rest ++ env) x = (envLookupT (rest ++ env) x).map (· + 1) := by
        show envLookupT.go x (y :: rest ++ env) 0 = _
        simp only [List.cons_append, envLookupT.go, hne]
        show envLookupT.go x (rest ++ env) (0 + 1) = _
        rw [envLookupT.go_shift x (rest ++ env) 0 1]
        rfl
      have h2 : envLookupT (y :: rest) x = (envLookupT rest x).map (· + 1) := by
        show envLookupT.go x (y :: rest) 0 = _
        simp only [envLookupT.go, hne]
        show envLookupT.go x rest (0 + 1) = _
        rw [envLookupT.go_shift x rest 0 1]
        rfl
      rw [h1, h2, ih]
      cases hlkup : envLookupT rest x with
      | some j => simp [Option.map]
      | none =>
        simp only [Option.map, List.length_cons]
        cases henv : envLookupT env x with
        | none => rfl
        | some i =>
          show some (rest.length + i + 1) = some (rest.length + 1 + i)
          congr 1; omega

/-- Looking up `x` in `prefix_env ++ v :: env` when `x ≠ v`: either hits
    `prefix_env` (returning the prefix position) or env (shifted by
    `prefix_env.length + 1`). -/
private theorem envLookupT_prefix_v_env_neq
    (x v : VarId) (prefix_env env : List VarId) (hne : (x == v) = false) :
    envLookupT (prefix_env ++ v :: env) x =
      match envLookupT prefix_env x with
      | some j => some j
      | none => (envLookupT env x).map (fun i => prefix_env.length + 1 + i) := by
  have hvenv : envLookupT (v :: env) x = (envLookupT env x).map (· + 1) := by
    have : (v == x) = false := by
      rw [Moist.Verified.MIR.VarId_beq_false_iff] at hne ⊢
      rcases hne with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)
    exact Moist.MIR.envLookupT_cons_neq v x env this
  rw [envLookupT_prefix_env x prefix_env (v :: env), hvenv]
  cases hpref : envLookupT prefix_env x with
  | some j => rfl
  | none =>
    cases henv : envLookupT env x with
    | none => rfl
    | some i =>
      simp only [Option.map]
      congr 1; omega

/-- Looking up `v` in `prefix_env ++ v :: env` when `v ∉ prefix_env`:
    lands exactly at position `prefix_env.length`. -/
private theorem envLookupT_prefix_v_env_eq
    (v : VarId) (prefix_env env : List VarId)
    (hv_notin : envLookupT prefix_env v = none) :
    envLookupT (prefix_env ++ v :: env) v = some prefix_env.length := by
  rw [envLookupT_prefix_env v prefix_env (v :: env), hv_notin]
  have hvv : envLookupT (v :: env) v = some 0 := by
    show envLookupT.go v (v :: env) 0 = _
    simp only [envLookupT.go]
    have h_refl : (v == v) = true := by
      rw [Moist.Verified.MIR.VarId_beq_true_iff]; exact ⟨rfl, rfl⟩
    rw [if_pos h_refl]
  rw [hvv]
  show some (prefix_env.length + 0) = some prefix_env.length
  simp

/-- Lowering `rhs` under an extended env `prefix_env ++ env` shifts every
    de Bruijn index in the result by `prefix_env.length`, PROVIDED none of
    `prefix_env`'s binders appear as free variables of `rhs`. Proved by
    iterating `lowerTotal_prepend_unused_gen`. -/
private theorem lowerTotal_expandFix_prepend_fresh
    (prefix_env env : List VarId) (rhs : Expr) (t_rhs : Term)
    (hfresh : ∀ w ∈ prefix_env, (Moist.MIR.freeVars
                (Moist.MIR.expandFix rhs)).contains w = false)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotal (prefix_env ++ env) (Moist.MIR.expandFix rhs) =
      some (iterShift prefix_env.length t_rhs) := by
  induction prefix_env with
  | nil =>
    show Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some (iterShift 0 t_rhs)
    rw [iterShift_zero]; exact h_rhs
  | cons w rest ih =>
    have hfresh_rest : ∀ w' ∈ rest,
        (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w' = false :=
      fun w' hw' => hfresh w' (List.mem_cons_of_mem w hw')
    have hfresh_w : (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w = false :=
      hfresh w List.mem_cons_self
    have h_rest := ih hfresh_rest
    -- Apply lowerTotal_prepend_unused_gen with prefix_env := [], env := rest ++ env, x := w
    have h_step :=
      Moist.MIR.lowerTotal_prepend_unused_gen [] (rest ++ env) w (Moist.MIR.expandFix rhs)
        (Or.inl hfresh_w) (iterShift rest.length t_rhs) h_rest
    -- h_step : lowerTotal ([] ++ w :: (rest ++ env)) (expandFix rhs) =
    --           some (renameTerm (shiftRename ([].length + 1)) (iterShift rest.length t_rhs))
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at h_step
    rw [List.cons_append, List.length_cons, h_step, ← iterShift_succ]
mutual
private theorem substTerm_shift_cancel (pos : Nat) (r t : Term) (hpos : pos ≥ 1) :
    substTerm pos r (renameTerm (Moist.Verified.shiftRename pos) t) = t := by
  match t with
  | .Var n =>
    simp only [renameTerm, Moist.Verified.shiftRename]
    split
    · rename_i hge
      simp only [substTerm]
      have h1 : ¬ (n + 1 = pos) := by omega
      have h2 : n + 1 > pos := by omega
      rw [if_neg h1, if_pos h2]
      show Term.Var (n + 1 - 1) = Term.Var n
      rw [show n + 1 - 1 = n from by omega]
    · rename_i hlt
      simp only [substTerm]
      have h1 : ¬ (n = pos) := by omega
      have h2 : ¬ (n > pos) := by omega
      rw [if_neg h1, if_neg h2]
  | .Constant c => simp [renameTerm, substTerm]
  | .Builtin b => simp [renameTerm, substTerm]
  | .Error => simp [renameTerm, substTerm]
  | .Lam name body =>
    simp only [renameTerm, substTerm]
    rw [Moist.Verified.liftRename_shiftRename hpos]
    exact congrArg (Term.Lam name ·)
      (substTerm_shift_cancel (pos + 1)
        (renameTerm (Moist.Verified.shiftRename 1) r) body (by omega))
  | .Apply f x =>
    simp only [renameTerm, substTerm]
    rw [substTerm_shift_cancel pos r f hpos, substTerm_shift_cancel pos r x hpos]
  | .Force e =>
    simp only [renameTerm, substTerm]
    exact congrArg Term.Force (substTerm_shift_cancel pos r e hpos)
  | .Delay e =>
    simp only [renameTerm, substTerm]
    exact congrArg Term.Delay (substTerm_shift_cancel pos r e hpos)
  | .Constr tag args =>
    simp only [renameTerm, substTerm]
    exact congrArg (Term.Constr tag) (substTermList_shift_cancel pos r args hpos)
  | .Case scrut alts =>
    simp only [renameTerm, substTerm]
    rw [substTerm_shift_cancel pos r scrut hpos, substTermList_shift_cancel pos r alts hpos]
termination_by sizeOf t

private theorem substTermList_shift_cancel (pos : Nat) (r : Term) (ts : List Term) (hpos : pos ≥ 1) :
    Moist.Verified.substTermList pos r
      (Moist.Verified.renameTermList (Moist.Verified.shiftRename pos) ts) = ts := by
  match ts with
  | [] => simp [Moist.Verified.renameTermList, Moist.Verified.substTermList]
  | t :: rest =>
    simp only [Moist.Verified.renameTermList, Moist.Verified.substTermList]
    rw [substTerm_shift_cancel pos r t hpos, substTermList_shift_cancel pos r rest hpos]
termination_by sizeOf ts
end

mutual
  theorem freeVars_subst_not_contains
      (v : VarId) (rhs body : Expr) (w : VarId) (s : Moist.MIR.FreshState)
      (h_nc : noCaptureFrom (Moist.MIR.freeVars rhs) body = true)
      (hw_body : (Moist.MIR.freeVars body).contains w = false)
      (hw_rhs : (Moist.MIR.freeVars rhs).contains w = false) :
      (Moist.MIR.freeVars (Moist.MIR.subst v rhs body s).1).contains w = false := by
    match body with
    | .Var x =>
      simp only [Moist.MIR.subst, pure, StateT.pure]
      by_cases hxv : (x == v) = true
      · simp only [hxv, if_true]; exact hw_rhs
      · simp only [hxv]
        simpa [Moist.MIR.freeVars, Moist.MIR.VarSet.singleton_contains'] using hw_body
    | .Lit _ | .Builtin _ | .Error =>
      simp only [Moist.MIR.subst, pure, StateT.pure, Moist.MIR.freeVars]
      exact Moist.MIR.VarSet.empty_not_contains w
    | .Lam x body' =>
      obtain ⟨h_nc_x, h_nc_b⟩ := noCaptureFrom_lam h_nc
      by_cases hxv : (x == v) = true
      · simp only [Moist.MIR.subst, hxv, if_true, pure, StateT.pure]
        exact hw_body
      · have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
        have h_sub : (Moist.MIR.subst v rhs (.Lam x body') s).1 =
            .Lam x (Moist.MIR.subst v rhs body' s).1 := by
          simp only [Moist.MIR.subst, hne, h_nc_x, bind, pure]; rfl
        rw [h_sub]
        simp only [Moist.MIR.freeVars]
        apply Moist.MIR.VarSet.erase_of_inner_not_contains_or_match
        simp only [Moist.MIR.freeVars] at hw_body
        rcases Moist.MIR.VarSet.erase_not_contains_imp' (Moist.MIR.freeVars body') x w hw_body with h | h
        · exact Or.inl (freeVars_subst_not_contains v rhs body' w s h_nc_b h hw_rhs)
        · exact Or.inr h
    | .Fix f body' =>
      obtain ⟨h_nc_f, h_nc_b⟩ := noCaptureFrom_fix h_nc
      by_cases hfv : (f == v) = true
      · simp only [Moist.MIR.subst, hfv, if_true, pure, StateT.pure]; exact hw_body
      · have hne : (f == v) = false := by cases h : (f == v); rfl; exact absurd h hfv
        have h_sub : (Moist.MIR.subst v rhs (.Fix f body') s).1 =
            .Fix f (Moist.MIR.subst v rhs body' s).1 := by
          simp only [Moist.MIR.subst, hne, h_nc_f, bind, pure]; rfl
        rw [h_sub]
        simp only [Moist.MIR.freeVars]
        apply Moist.MIR.VarSet.erase_of_inner_not_contains_or_match
        simp only [Moist.MIR.freeVars] at hw_body
        rcases Moist.MIR.VarSet.erase_not_contains_imp' (Moist.MIR.freeVars body') f w hw_body with h | h
        · exact Or.inl (freeVars_subst_not_contains v rhs body' w s h_nc_b h hw_rhs)
        · exact Or.inr h
    | .App f a =>
      obtain ⟨h_nc_f, h_nc_a⟩ := noCaptureFrom_app h_nc
      simp only [Moist.MIR.freeVars] at hw_body
      obtain ⟨hw_f, hw_a⟩ := Moist.MIR.VarSet.union_not_contains' _ _ _ hw_body
      have h_sub : (Moist.MIR.subst v rhs (.App f a) s).1 =
          .App (Moist.MIR.subst v rhs f s).1
               (Moist.MIR.subst v rhs a (Moist.MIR.subst v rhs f s).2).1 := by
        simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVars]
      exact Moist.MIR.VarSet.union_not_contains_fwd _ _ _
        (freeVars_subst_not_contains v rhs f w s h_nc_f hw_f hw_rhs)
        (freeVars_subst_not_contains v rhs a w (Moist.MIR.subst v rhs f s).2 h_nc_a hw_a hw_rhs)
    | .Force e =>
      simp only [Moist.MIR.freeVars] at hw_body
      have h_sub : (Moist.MIR.subst v rhs (.Force e) s).1 =
          .Force (Moist.MIR.subst v rhs e s).1 := by
        simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVars]
      exact freeVars_subst_not_contains v rhs e w s (noCaptureFrom_force h_nc) hw_body hw_rhs
    | .Delay e =>
      simp only [Moist.MIR.freeVars] at hw_body
      have h_sub : (Moist.MIR.subst v rhs (.Delay e) s).1 =
          .Delay (Moist.MIR.subst v rhs e s).1 := by
        simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVars]
      exact freeVars_subst_not_contains v rhs e w s (noCaptureFrom_delay h_nc) hw_body hw_rhs
    | .Constr tag args =>
      have h_sub : (Moist.MIR.subst v rhs (.Constr tag args) s).1 =
          .Constr tag (Moist.MIR.substList v rhs args s).1 := by
        simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVars]
      simp only [Moist.MIR.freeVars] at hw_body
      exact freeVarsList_substList_not_contains v rhs args w s (noCaptureFrom_constr h_nc) hw_body hw_rhs
    | .Case scrut alts =>
      obtain ⟨h_nc_s, h_nc_a⟩ := noCaptureFrom_case h_nc
      simp only [Moist.MIR.freeVars] at hw_body
      obtain ⟨hw_s, hw_a⟩ := Moist.MIR.VarSet.union_not_contains' _ _ _ hw_body
      have h_sub : (Moist.MIR.subst v rhs (.Case scrut alts) s).1 =
          .Case (Moist.MIR.subst v rhs scrut s).1
                (Moist.MIR.substList v rhs alts (Moist.MIR.subst v rhs scrut s).2).1 := by
        simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVars]
      exact Moist.MIR.VarSet.union_not_contains_fwd _ _ _
        (freeVars_subst_not_contains v rhs scrut w s h_nc_s hw_s hw_rhs)
        (freeVarsList_substList_not_contains v rhs alts w (Moist.MIR.subst v rhs scrut s).2
          h_nc_a hw_a hw_rhs)
    | .Let binds body' =>
      have h_sub : (Moist.MIR.subst v rhs (.Let binds body') s).1 =
          .Let (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body' s).1.1
               (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body' s).1.2 := by
        simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVars]
      simp only [Moist.MIR.freeVars] at hw_body
      exact freeVarsLet_substLet_not_contains v rhs binds body' w s
              (noCaptureFrom_let h_nc) hw_body hw_rhs
  termination_by sizeOf body

  theorem freeVarsList_substList_not_contains
      (v : VarId) (rhs : Expr) (es : List Expr) (w : VarId) (s : Moist.MIR.FreshState)
      (h_nc : noCaptureFromList (Moist.MIR.freeVars rhs) es = true)
      (hw_es : (Moist.MIR.freeVarsList es).contains w = false)
      (hw_rhs : (Moist.MIR.freeVars rhs).contains w = false) :
      (Moist.MIR.freeVarsList (Moist.MIR.substList v rhs es s).1).contains w = false := by
    match es with
    | [] =>
      simp only [Moist.MIR.substList, pure, StateT.pure, Moist.MIR.freeVarsList]
      exact Moist.MIR.VarSet.empty_not_contains w
    | e :: rest =>
      obtain ⟨h_nc_e, h_nc_rest⟩ := noCaptureFromList_cons h_nc
      simp only [Moist.MIR.freeVarsList] at hw_es
      obtain ⟨hw_e, hw_rest⟩ := Moist.MIR.VarSet.union_not_contains' _ _ _ hw_es
      have h_sub : (Moist.MIR.substList v rhs (e :: rest) s).1 =
          (Moist.MIR.subst v rhs e s).1 ::
          (Moist.MIR.substList v rhs rest (Moist.MIR.subst v rhs e s).2).1 := by
        simp only [Moist.MIR.substList, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [h_sub]; simp only [Moist.MIR.freeVarsList]
      exact Moist.MIR.VarSet.union_not_contains_fwd _ _ _
        (freeVars_subst_not_contains v rhs e w s h_nc_e hw_e hw_rhs)
        (freeVarsList_substList_not_contains v rhs rest w (Moist.MIR.subst v rhs e s).2
          h_nc_rest hw_rest hw_rhs)
  termination_by sizeOf es

  theorem freeVarsLet_substLet_not_contains
      (v : VarId) (rhs : Expr) (binds : List (VarId × Expr × Bool)) (body' : Expr)
      (w : VarId) (s : Moist.MIR.FreshState)
      (h_nc : noCaptureFromLet (Moist.MIR.freeVars rhs) binds body' = true)
      (hw : (Moist.MIR.freeVarsLet binds body').contains w = false)
      (hw_rhs : (Moist.MIR.freeVars rhs).contains w = false) :
      (Moist.MIR.freeVarsLet
          (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body' s).1.1
          (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body' s).1.2).contains w = false := by
    match binds with
    | [] =>
      have h_form : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) [] body' s).1 =
          ([], (Moist.MIR.subst v rhs body' s).1) := by
        simp only [Moist.MIR.substLet, bind, StateT.bind, pure, StateT.pure]; rfl
      rw [show (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) [] body' s).1.1 = []
              from congrArg Prod.fst h_form,
          show (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) [] body' s).1.2 =
               (Moist.MIR.subst v rhs body' s).1
              from congrArg Prod.snd h_form]
      simp only [Moist.MIR.freeVarsLet, Moist.MIR.freeVarsLet] at hw ⊢
      exact freeVars_subst_not_contains v rhs body' w s (noCaptureFromLet_nil_body h_nc) hw hw_rhs
    | (x, rhs_h, er) :: rest =>
      obtain ⟨h_nc_x, h_nc_rhs_h, h_nc_rest⟩ := noCaptureFromLet_cons h_nc
      simp only [Moist.MIR.freeVarsLet] at hw
      obtain ⟨hw_rhs_h, hw_rest_body⟩ := Moist.MIR.VarSet.union_not_contains' _ _ _ hw
      have ih_rhs_h := freeVars_subst_not_contains v rhs rhs_h w s h_nc_rhs_h hw_rhs_h hw_rhs
      by_cases hxv : (x == v) = true
      · have h_form : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                         ((x, rhs_h, er) :: rest) body' s).1 =
            ((x, (Moist.MIR.subst v rhs rhs_h s).1, er) :: rest, body') := by
          simp only [Moist.MIR.substLet, hxv, if_true, bind, StateT.bind, pure, StateT.pure]; rfl
        rw [show (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                    ((x, rhs_h, er) :: rest) body' s).1.1 =
                 (x, (Moist.MIR.subst v rhs rhs_h s).1, er) :: rest
                from congrArg Prod.fst h_form,
            show (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                    ((x, rhs_h, er) :: rest) body' s).1.2 = body'
                from congrArg Prod.snd h_form]
        simp only [Moist.MIR.freeVarsLet]
        exact Moist.MIR.VarSet.union_not_contains_fwd _ _ _ ih_rhs_h hw_rest_body
      · have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
        have h1 : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                    ((x, rhs_h, er) :: rest) body' s).1.1 =
            (x, (Moist.MIR.subst v rhs rhs_h s).1, er) ::
            (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) rest body'
               (Moist.MIR.subst v rhs rhs_h s).2).1.1 := by
          simp only [Moist.MIR.substLet, hne, h_nc_x, bind, StateT.bind, pure, StateT.pure,
                     Bool.false_eq_true, ↓reduceIte]
          rfl
        have h2 : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                    ((x, rhs_h, er) :: rest) body' s).1.2 =
            (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) rest body'
               (Moist.MIR.subst v rhs rhs_h s).2).1.2 := by
          simp only [Moist.MIR.substLet, hne, h_nc_x, bind, StateT.bind, pure, StateT.pure,
                     Bool.false_eq_true, ↓reduceIte]
          rfl
        rw [h1, h2]
        simp only [Moist.MIR.freeVarsLet]
        refine Moist.MIR.VarSet.union_not_contains_fwd _ _ _ ih_rhs_h ?_
        apply Moist.MIR.VarSet.erase_of_inner_not_contains_or_match
        rcases Moist.MIR.VarSet.erase_not_contains_imp' (Moist.MIR.freeVarsLet rest body') x w
                 hw_rest_body with hw_rest | hxw
        · exact Or.inl (freeVarsLet_substLet_not_contains v rhs rest body' w
                          (Moist.MIR.subst v rhs rhs_h s).2 h_nc_rest hw_rest hw_rhs)
        · exact Or.inr hxw
  termination_by sizeOf binds + sizeOf body'
end

/-- `substTerm` distributes through `fixLamWrapUplc`: substituting at
    position `pos` (with `pos ≥ 1`) into the Z-combinator wrapper equals
    wrapping a substitution at position `pos + 3` (with `iterShift 3` on
    the replacement) into the inner body. Used in the `.Fix` case of the
    fresh Phase 2a proof. -/
private theorem substTerm_fixLamWrapUplc (pos : Nat) (r t : Term) (hpos : pos ≥ 1) :
    substTerm pos r (Moist.MIR.fixLamWrapUplc t) =
      Moist.MIR.fixLamWrapUplc (substTerm (pos + 3) (iterShift 3 r) t) := by
  show substTerm pos r
      (.Apply
        (.Lam 0 (.Apply (.Var 1) (.Var 1)))
        (.Lam 0 (.Apply (.Lam 0 (.Lam 0 t))
                        (.Lam 0 (.Apply (.Apply (.Var 2) (.Var 2)) (.Var 1))))))
    = Moist.MIR.fixLamWrapUplc (substTerm (pos + 3) (iterShift 3 r) t)
  simp only [substTerm]
  -- Simplify the .Var references: all of (.Var 1) and (.Var 2) at depth pos+1 or pos+2
  -- stay unchanged since pos ≥ 1.
  have h_one_ne_posp1 : ¬ (1 = pos + 1) := by omega
  have h_one_not_gt_posp1 : ¬ (1 > pos + 1) := by omega
  have h_two_ne_posp2 : ¬ (2 = pos + 2) := by omega
  have h_two_not_gt_posp2 : ¬ (2 > pos + 2) := by omega
  have h_one_ne_posp2 : ¬ (1 = pos + 2) := by omega
  have h_one_not_gt_posp2 : ¬ (1 > pos + 2) := by omega
  rw [if_neg h_one_ne_posp1, if_neg h_one_not_gt_posp1,
      if_neg h_two_ne_posp2, if_neg h_two_not_gt_posp2,
      if_neg h_one_ne_posp2, if_neg h_one_not_gt_posp2]
  -- Unfold fixLamWrapUplc on the RHS and close via rfl after iterShift unfolding
  simp only [Moist.MIR.fixLamWrapUplc, iterShift]

private theorem iterShift_add (m n : Nat) (t : Term) :
    iterShift (m + n) t = iterShift m (iterShift n t) := by
  induction m with
  | zero => simp [iterShift_zero]
  | succ k ih =>
    rw [show k + 1 + n = (k + n) + 1 from by omega, iterShift_succ, ih, iterShift_succ]

-- === Section 5.2: Fresh-prefix Phase 2a (mutual induction on body) ===

mutual

/-- Freshness-strengthened Phase 2a: assumes every binder in `prefix_env`
    is absent from `freeVars (expandFix rhs)`, and every binder in `body`
    is absent from `freeVars rhs`. The second hypothesis (`h_nc`) ensures
    `subst` never takes its capture-avoidance branch when descending into
    `body`. Proved by mutual induction on `body`/`substList`/`substLet`. -/
private theorem subst_lowerTotal_comm_fresh
    (v : VarId) (rhs body : Expr)
    (prefix_env env : List VarId) (s : Moist.MIR.FreshState)
    (t_body t_rhs : Term)
    (hv_notin : envLookupT prefix_env v = none)
    (hfresh : ∀ w ∈ prefix_env, (Moist.MIR.freeVars
                (Moist.MIR.expandFix rhs)).contains w = false)
    (h_nc : noCaptureFrom (Moist.MIR.freeVars rhs) body = true)
    (h_body : Moist.MIR.lowerTotal (prefix_env ++ v :: env)
                (Moist.MIR.expandFix body) = some t_body)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotal (prefix_env ++ env)
        (Moist.MIR.expandFix (Moist.MIR.subst v rhs body s).1) =
      some (substTerm (prefix_env.length + 1)
                      (iterShift prefix_env.length t_rhs) t_body) := by
  match body with
  | .Var x =>
    have h_ef : Moist.MIR.expandFix (Expr.Var x) = Expr.Var x := by
      simp only [Moist.MIR.expandFix]
    rw [h_ef] at h_body
    by_cases hxv : (x == v) = true
    · -- x == v: subst returns rhs
      have heq_beq : ∀ y : VarId, (y == x) = (y == v) := by
        intro y
        have ⟨ho, hu⟩ := (Moist.Verified.MIR.VarId_beq_true_iff x v).mp hxv
        show (y.origin == x.origin && y.uid == x.uid) =
             (y.origin == v.origin && y.uid == v.uid)
        rw [ho, hu]
      have h_env_agree : ∀ env' : List VarId, envLookupT env' x = envLookupT env' v := by
        intro env'
        unfold envLookupT
        generalize (0 : Nat) = n
        induction env' generalizing n with
        | nil => rfl
        | cons y rest ih =>
          simp only [envLookupT.go]
          rw [heq_beq y]
          split
          · rfl
          · exact ih (n + 1)
      have h_lookup : envLookupT (prefix_env ++ v :: env) x = some prefix_env.length := by
        rw [h_env_agree]; exact envLookupT_prefix_v_env_eq v prefix_env env hv_notin
      rw [Moist.MIR.lowerTotal.eq_1] at h_body
      rw [h_lookup] at h_body
      injection h_body with h_tb
      subst h_tb
      have h_sub : (Moist.MIR.subst v rhs (Expr.Var x) s).1 = rhs := by
        simp only [Moist.MIR.subst, pure, StateT.pure]
        simp [hxv]
      rw [h_sub]
      rw [lowerTotal_expandFix_prepend_fresh prefix_env env rhs t_rhs hfresh h_rhs]
      -- Goal: some (iterShift k t_rhs) = some (substTerm (k+1) (iterShift k t_rhs) (.Var (k+1)))
      congr 1
      show iterShift prefix_env.length t_rhs =
           substTerm (prefix_env.length + 1) (iterShift prefix_env.length t_rhs)
             (Term.Var (prefix_env.length + 1))
      simp only [substTerm, if_true]
    · -- x ≠ v: subst returns .Var x
      have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
      have h_sub : (Moist.MIR.subst v rhs (Expr.Var x) s).1 = Expr.Var x := by
        simp only [Moist.MIR.subst, pure, StateT.pure]; simp [hne]
      rw [h_sub, h_ef]
      rw [Moist.MIR.lowerTotal.eq_1] at h_body
      rw [envLookupT_prefix_v_env_neq x v prefix_env env hne] at h_body
      rw [Moist.MIR.lowerTotal.eq_1, envLookupT_prefix_env x prefix_env env]
      cases hpref : envLookupT prefix_env x with
      | some j =>
        rw [hpref] at h_body
        injection h_body with h_tb
        subst h_tb
        have hj : j < prefix_env.length := Moist.MIR.envLookupT_bound prefix_env x j hpref
        simp only [substTerm]
        have hne1 : ¬ (j + 1 = prefix_env.length + 1) := by omega
        have hne2 : ¬ (j + 1 > prefix_env.length + 1) := by omega
        rw [if_neg hne1, if_neg hne2]
      | none =>
        rw [hpref] at h_body
        cases henv : envLookupT env x with
        | none => rw [henv] at h_body; simp at h_body
        | some i =>
          rw [henv] at h_body
          simp only [Option.map] at h_body
          injection h_body with h_tb
          subst h_tb
          simp only [Option.map, substTerm]
          have hne1 : ¬ (prefix_env.length + 1 + i + 1 = prefix_env.length + 1) := by omega
          have hgt : prefix_env.length + 1 + i + 1 > prefix_env.length + 1 := by omega
          rw [if_neg hne1, if_pos hgt]
          congr 2; omega
  | .Lit c =>
    have h_ef : Moist.MIR.expandFix (Expr.Lit c) = Expr.Lit c := by
      simp only [Moist.MIR.expandFix]
    have h_sub : (Moist.MIR.subst v rhs (Expr.Lit c) s).1 = Expr.Lit c := by
      simp only [Moist.MIR.subst, pure, StateT.pure]
    rw [h_ef, Moist.MIR.lowerTotal.eq_2] at h_body
    injection h_body with h_tb
    subst h_tb
    rw [h_sub, h_ef, Moist.MIR.lowerTotal.eq_2]
    simp only [substTerm]
  | .Builtin b =>
    have h_ef : Moist.MIR.expandFix (Expr.Builtin b) = Expr.Builtin b := by
      simp only [Moist.MIR.expandFix]
    have h_sub : (Moist.MIR.subst v rhs (Expr.Builtin b) s).1 = Expr.Builtin b := by
      simp only [Moist.MIR.subst, pure, StateT.pure]
    rw [h_ef, Moist.MIR.lowerTotal.eq_3] at h_body
    injection h_body with h_tb
    subst h_tb
    rw [h_sub, h_ef, Moist.MIR.lowerTotal.eq_3]
    simp only [substTerm]
  | .Error =>
    have h_ef : Moist.MIR.expandFix Expr.Error = Expr.Error := by
      simp only [Moist.MIR.expandFix]
    have h_sub : (Moist.MIR.subst v rhs Expr.Error s).1 = Expr.Error := by
      simp only [Moist.MIR.subst, pure, StateT.pure]
    rw [h_ef, Moist.MIR.lowerTotal.eq_4] at h_body
    injection h_body with h_tb
    subst h_tb
    rw [h_sub, h_ef, Moist.MIR.lowerTotal.eq_4]
    simp only [substTerm]
  | .App f a =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_6,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_body
    obtain ⟨t_f, ht_f, t_a, ht_a, h_body_eq⟩ := h_body
    have ⟨h_nc_f, h_nc_a⟩ := noCaptureFrom_app h_nc
    have ih_f := subst_lowerTotal_comm_fresh v rhs f prefix_env env s t_f t_rhs
                    hv_notin hfresh h_nc_f ht_f h_rhs
    have ih_a := subst_lowerTotal_comm_fresh v rhs a prefix_env env
                    (Moist.MIR.subst v rhs f s).2 t_a t_rhs
                    hv_notin hfresh h_nc_a ht_a h_rhs
    have h_sub : (Moist.MIR.subst v rhs (Expr.App f a) s).1 =
        Expr.App (Moist.MIR.subst v rhs f s).1
          (Moist.MIR.subst v rhs a (Moist.MIR.subst v rhs f s).2).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_6, ih_f, ih_a,
               Option.bind_eq_bind, Option.bind_some]
    injection h_body_eq with h_eq
    rw [← h_eq]
    simp only [substTerm]
  | .Force e =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_7,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_body
    obtain ⟨t_e, ht_e, h_body_eq⟩ := h_body
    have h_nc_e := noCaptureFrom_force h_nc
    have ih_e := subst_lowerTotal_comm_fresh v rhs e prefix_env env s t_e t_rhs
                   hv_notin hfresh h_nc_e ht_e h_rhs
    have h_sub : (Moist.MIR.subst v rhs (Expr.Force e) s).1 =
        Expr.Force (Moist.MIR.subst v rhs e s).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_7, ih_e,
               Option.bind_eq_bind, Option.bind_some]
    injection h_body_eq with h_eq
    rw [← h_eq]
    simp only [substTerm]
  | .Delay e =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_8,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_body
    obtain ⟨t_e, ht_e, h_body_eq⟩ := h_body
    have h_nc_e := noCaptureFrom_delay h_nc
    have ih_e := subst_lowerTotal_comm_fresh v rhs e prefix_env env s t_e t_rhs
                   hv_notin hfresh h_nc_e ht_e h_rhs
    have h_sub : (Moist.MIR.subst v rhs (Expr.Delay e) s).1 =
        Expr.Delay (Moist.MIR.subst v rhs e s).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_8, ih_e,
               Option.bind_eq_bind, Option.bind_some]
    injection h_body_eq with h_eq
    rw [← h_eq]
    simp only [substTerm]
  | .Constr tag args =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_9,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_body
    obtain ⟨t_args, ht_args, h_body_eq⟩ := h_body
    have h_nc_args := noCaptureFrom_constr h_nc
    have ih := substList_lowerTotalList_comm_fresh v rhs args prefix_env env s t_args t_rhs
                 hv_notin hfresh h_nc_args ht_args h_rhs
    have h_sub : (Moist.MIR.subst v rhs (Expr.Constr tag args) s).1 =
        Expr.Constr tag (Moist.MIR.substList v rhs args s).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_9, ih,
               Option.bind_eq_bind, Option.bind_some]
    injection h_body_eq with h_eq
    rw [← h_eq]
    simp only [substTerm]
  | .Case scrut alts =>
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_10,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_body
    obtain ⟨t_scrut, ht_scrut, t_alts, ht_alts, h_body_eq⟩ := h_body
    have ⟨h_nc_scrut, h_nc_alts⟩ := noCaptureFrom_case h_nc
    have ih_scrut := subst_lowerTotal_comm_fresh v rhs scrut prefix_env env s t_scrut t_rhs
                       hv_notin hfresh h_nc_scrut ht_scrut h_rhs
    have ih_alts := substList_lowerTotalList_comm_fresh v rhs alts prefix_env env
                      (Moist.MIR.subst v rhs scrut s).2 t_alts t_rhs
                      hv_notin hfresh h_nc_alts ht_alts h_rhs
    have h_sub : (Moist.MIR.subst v rhs (Expr.Case scrut alts) s).1 =
        Expr.Case (Moist.MIR.subst v rhs scrut s).1
          (Moist.MIR.substList v rhs alts (Moist.MIR.subst v rhs scrut s).2).1 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_10, ih_scrut, ih_alts,
               Option.bind_eq_bind, Option.bind_some]
    injection h_body_eq with h_eq
    rw [← h_eq]
    simp only [substTerm]
  | .Let binds body' =>
    -- expandFix (.Let binds body') = .Let (expandFixBinds binds) (expandFix body')
    -- lowerTotal env (.Let ...) = lowerTotalLet env (expandFixBinds binds) (expandFix body')
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_11] at h_body
    have h_nc_let := noCaptureFrom_let h_nc
    have ih_let := substLet_lowerTotalLet_comm_fresh v rhs binds body' prefix_env env s
                     t_body t_rhs hv_notin hfresh h_nc_let h_body h_rhs
    obtain ⟨t_lb', hlet, ht_lb'_eq⟩ := ih_let
    -- subst v rhs (.Let binds body') s = do (b, bo) ← substLet v rhs (freeVars rhs) binds body'; pure (.Let b bo)
    have h_sub : (Moist.MIR.subst v rhs (Expr.Let binds body') s).1 =
        Expr.Let (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body' s).1.1
                 (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) binds body' s).1.2 := by
      simp only [Moist.MIR.subst, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_11]
    rw [hlet, ht_lb'_eq]
  | .Lam x b' =>
    -- expandFix (.Lam x b') = .Lam x (expandFix b')
    -- lowerTotal env (.Lam x _) = do body_t ← lowerTotal (x :: env) (expandFix b'); some (.Lam 0 body_t)
    simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_5,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_body
    obtain ⟨t_body_inner, ht_body_inner, h_body_eq⟩ := h_body
    -- subst has three cases based on x == v and (freeVars rhs).contains x
    by_cases hxv : (x == v) = true
    · -- Case: x == v (shadow). Subst returns body unchanged.
      have h_sub : (Moist.MIR.subst v rhs (Expr.Lam x b') s).1 = Expr.Lam x b' := by
        simp only [Moist.MIR.subst, pure, StateT.pure, hxv, if_true]
      -- Use lowerTotal_prepend_unused_gen contrapositive to show shorter env also lowers
      have hunused_cond : (Moist.MIR.freeVars (Moist.MIR.expandFix b')).contains v = false ∨
                          (∃ y ∈ (x :: prefix_env), (y == v) = true) :=
        Or.inr ⟨x, List.Mem.head _, hxv⟩
      -- Contrapositive argument: if shorter env gave none, longer would give none
      have h_shorter_some : ∃ T',
          Moist.MIR.lowerTotal (x :: prefix_env ++ env) (Moist.MIR.expandFix b') = some T' := by
        cases h_short : Moist.MIR.lowerTotal (x :: prefix_env ++ env) (Moist.MIR.expandFix b') with
        | some T' => exact ⟨T', rfl⟩
        | none =>
          exfalso
          have h_prepend_none := Moist.MIR.lowerTotal_prepend_unused_none_gen
                                 (x :: prefix_env) env v (Moist.MIR.expandFix b')
                                 hunused_cond h_short
          rw [List.cons_append] at h_prepend_none
          rw [h_prepend_none] at ht_body_inner
          exact Option.noConfusion ht_body_inner
      obtain ⟨T', hT'⟩ := h_shorter_some
      -- By prepend_unused_gen: t_body_inner = renameTerm (shiftRename (k+2)) T'
      have h_prepend_some := Moist.MIR.lowerTotal_prepend_unused_gen
                             (x :: prefix_env) env v (Moist.MIR.expandFix b')
                             hunused_cond T' hT'
      rw [List.cons_append] at h_prepend_some
      rw [ht_body_inner] at h_prepend_some
      injection h_prepend_some with h_shift_eq
      -- h_shift_eq : renameTerm (shiftRename (prefix_env.length + 1 + 1)) T' = t_body_inner
      rw [h_sub]
      simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_5]
      simp only [List.cons_append] at hT'
      rw [hT']
      simp only [Option.bind_eq_bind, Option.bind_some]
      injection h_body_eq with h_eq
      rw [← h_eq]
      simp only [substTerm]
      rw [List.length_cons] at h_shift_eq
      rw [h_shift_eq]
      rw [substTerm_shift_cancel (prefix_env.length + 1 + 1) _ T' (by omega)]
    · -- x ≠ v. h_nc gives `x ∉ freeVars rhs`, so the capture branch is
      -- ruled out and subst descends directly.
      have ⟨hnot_free, h_nc_b'⟩ := noCaptureFrom_lam h_nc
      have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
      have h_sub : (Moist.MIR.subst v rhs (Expr.Lam x b') s).1 =
          Expr.Lam x (Moist.MIR.subst v rhs b' s).1 := by
        simp only [Moist.MIR.subst, hne, hnot_free, bind, pure]
        rfl
      -- Apply IH on b' with prefix_env extended by x
      have hv_notin_ext : envLookupT (x :: prefix_env) v = none := by
        rw [Moist.MIR.envLookupT_cons_neq x v prefix_env hne, hv_notin]; rfl
      have hfresh_ext : ∀ w ∈ (x :: prefix_env),
          (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w = false := by
        intro w hw
        rcases List.mem_cons.mp hw with hhead | htail
        · subst hhead
          exact Moist.MIR.expandFix_freeVars_not_contains rhs w hnot_free
        · exact hfresh w htail
      have hbody_inner' :
          Moist.MIR.lowerTotal ((x :: prefix_env) ++ v :: env) (Moist.MIR.expandFix b') =
            some t_body_inner := by
        rw [List.cons_append]; exact ht_body_inner
      have ih := subst_lowerTotal_comm_fresh v rhs b' (x :: prefix_env) env s
                   t_body_inner t_rhs hv_notin_ext hfresh_ext h_nc_b' hbody_inner' h_rhs
      rw [h_sub]
      simp only [Moist.MIR.expandFix, Moist.MIR.lowerTotal.eq_5]
      rw [List.cons_append] at ih
      rw [ih]
      simp only [Option.bind_eq_bind, Option.bind_some]
      injection h_body_eq with h_eq
      rw [← h_eq]
      simp only [substTerm, List.length_cons]
      rw [← iterShift_succ]
  | .Fix f b =>
    -- h_nc gives: f ∉ freeVars rhs, noCaptureFrom rhs b
    have ⟨h_f_fv, h_nc_b⟩ := noCaptureFrom_fix h_nc
    -- Case split on whether b is .Lam x inner or not
    match b with
    | .Lam x inner =>
      -- body = .Fix f (.Lam x inner). Extract h_nc for inner.
      have ⟨h_x_fv, h_nc_inner⟩ := noCaptureFrom_lam h_nc_b
      -- Decompose h_body through fixLamWrapUplc via the canonical s_c.
      let s_c : VarId := ⟨Moist.MIR.maxUidExpr (Moist.MIR.expandFix inner) + 1, .gen, "s"⟩
      have h_body_decomp :
          (Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ v :: env)
              (Moist.MIR.expandFix inner)).map Moist.MIR.fixLamWrapUplc = some t_body := by
        have h_expr : Moist.MIR.lowerTotalExpr (prefix_env ++ v :: env)
                        (.Fix f (.Lam x inner)) = some t_body := by
          show Moist.MIR.lowerTotal (prefix_env ++ v :: env)
                 (Moist.MIR.expandFix (.Fix f (.Lam x inner))) = some t_body
          exact h_body
        rw [Moist.MIR.lowerTotalExpr_fix_lam_canonical] at h_expr
        exact h_expr
      -- Extract t_inner from h_body_decomp
      cases h_inner_low : Moist.MIR.lowerTotal
          (x :: f :: s_c :: prefix_env ++ v :: env) (Moist.MIR.expandFix inner) with
      | none =>
        exfalso
        rw [h_inner_low] at h_body_decomp
        exact Option.noConfusion h_body_decomp
      | some t_inner =>
        rw [h_inner_low] at h_body_decomp
        simp only [Option.map_some] at h_body_decomp
        -- h_body_decomp : some (fixLamWrapUplc t_inner) = some t_body
        have h_t_body_eq : t_body = Moist.MIR.fixLamWrapUplc t_inner :=
          (Option.some.inj h_body_decomp).symm
        -- Now case-split on subst's behavior
        by_cases hfv : (f == v) = true
        · -- Case A: f == v. subst returns body unchanged.
          have h_sub : (Moist.MIR.subst v rhs (Expr.Fix f (.Lam x inner)) s).1 =
              Expr.Fix f (.Lam x inner) := by
            simp only [Moist.MIR.subst, pure, StateT.pure, hfv, if_true]
          -- Compute RHS lowering using canonical on (prefix_env ++ env)
          have h_rhs_decomp :
              Moist.MIR.lowerTotal (prefix_env ++ env)
                  (Moist.MIR.expandFix (Expr.Fix f (.Lam x inner))) =
                (Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ env)
                    (Moist.MIR.expandFix inner)).map Moist.MIR.fixLamWrapUplc := by
            show Moist.MIR.lowerTotalExpr (prefix_env ++ env)
                   (Expr.Fix f (.Lam x inner)) = _
            exact Moist.MIR.lowerTotalExpr_fix_lam_canonical _ _ _ _
          -- f == v means v is shadowed at position 1 in (x::f::s_c::prefix_env).
          -- By lowerTotal_prepend_unused, shorter-env lowering gives t_some, and
          -- longer-env gives renameTerm (shiftRename ...) t_some.
          have hunused_inner :
              (Moist.MIR.freeVars (Moist.MIR.expandFix inner)).contains v = false ∨
              (∃ y ∈ (x :: f :: s_c :: prefix_env), (y == v) = true) :=
            Or.inr ⟨f, by simp [List.mem_cons], hfv⟩
          -- Contrapositive: longer-env gives some → shorter-env gives some
          have h_shorter_some : ∃ t_some,
              Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ env)
                  (Moist.MIR.expandFix inner) = some t_some := by
            cases h_short : Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ env)
                              (Moist.MIR.expandFix inner) with
            | some t' => exact ⟨t', rfl⟩
            | none =>
              exfalso
              have h_long_none := Moist.MIR.lowerTotal_prepend_unused_none_gen
                  (x :: f :: s_c :: prefix_env) env v (Moist.MIR.expandFix inner)
                  hunused_inner (by
                    rw [show x :: f :: s_c :: prefix_env ++ env =
                          (x :: f :: s_c :: prefix_env) ++ env from rfl] at h_short
                    exact h_short)
              rw [show (x :: f :: s_c :: prefix_env) ++ v :: env =
                    x :: f :: s_c :: prefix_env ++ v :: env from rfl] at h_long_none
              rw [h_long_none] at h_inner_low
              exact Option.noConfusion h_inner_low
          obtain ⟨t_some, ht_some⟩ := h_shorter_some
          -- Apply prepend_unused_gen to derive t_inner = shifted t_some
          have h_shift := Moist.MIR.lowerTotal_prepend_unused_gen
              (x :: f :: s_c :: prefix_env) env v (Moist.MIR.expandFix inner)
              hunused_inner t_some (by
                rw [show x :: f :: s_c :: prefix_env ++ env =
                      (x :: f :: s_c :: prefix_env) ++ env from rfl] at ht_some
                exact ht_some)
          rw [show (x :: f :: s_c :: prefix_env) ++ v :: env =
                x :: f :: s_c :: prefix_env ++ v :: env from rfl] at h_shift
          rw [h_inner_low] at h_shift
          injection h_shift with h_t_inner
          -- h_t_inner : renameTerm (shiftRename (prefix_env.length + 4)) t_some = t_inner
          -- (since (x :: f :: s_c :: prefix_env).length = prefix_env.length + 3, +1 = prefix_env.length + 4)
          -- Assemble the goal
          rw [h_sub, h_rhs_decomp, ht_some, Option.map_some, h_t_body_eq]
          -- Goal: some (fixLamWrapUplc t_some) = some (substTerm (prefix_env.length + 1) _
          --                                              (fixLamWrapUplc t_inner))
          rw [substTerm_fixLamWrapUplc _ _ _ (by omega : prefix_env.length + 1 ≥ 1)]
          -- Now: some (fixLamWrapUplc t_some) = some (fixLamWrapUplc (substTerm _ _ t_inner))
          congr 1
          -- Rewrite t_inner using h_t_inner, then use substTerm_shift_cancel
          rw [h_t_inner]
          simp only [List.length_cons]
          rw [substTerm_shift_cancel (prefix_env.length + 1 + 1 + 1 + 1) _ t_some (by omega)]
        · -- f ≠ v
          have hfv' : (f == v) = false := by cases h : (f == v); rfl; exact absurd h hfv
          -- Subst descends into .Lam x inner. Further case split on x == v.
          by_cases hxv : (x == v) = true
          · -- Case B: f ≠ v, x == v. Subst on .Lam x inner is identity (x shadows v).
            -- Full subst descends through the Fix f and then returns .Lam x inner unchanged.
            have h_sub : (Moist.MIR.subst v rhs (Expr.Fix f (.Lam x inner)) s).1 =
                Expr.Fix f (.Lam x inner) := by
              simp only [Moist.MIR.subst, hfv', h_f_fv, hxv, bind, pure]
              rfl
            -- Proceed as in Case A but with shadow arg at x position (position 0, not 1).
            have h_rhs_decomp :
                Moist.MIR.lowerTotal (prefix_env ++ env)
                    (Moist.MIR.expandFix (Expr.Fix f (.Lam x inner))) =
                  (Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ env)
                      (Moist.MIR.expandFix inner)).map Moist.MIR.fixLamWrapUplc := by
              show Moist.MIR.lowerTotalExpr (prefix_env ++ env)
                     (Expr.Fix f (.Lam x inner)) = _
              exact Moist.MIR.lowerTotalExpr_fix_lam_canonical _ _ _ _
            have hunused_inner :
                (Moist.MIR.freeVars (Moist.MIR.expandFix inner)).contains v = false ∨
                (∃ y ∈ (x :: f :: s_c :: prefix_env), (y == v) = true) :=
              Or.inr ⟨x, List.Mem.head _, hxv⟩
            have h_shorter_some : ∃ t_some,
                Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ env)
                    (Moist.MIR.expandFix inner) = some t_some := by
              cases h_short : Moist.MIR.lowerTotal (x :: f :: s_c :: prefix_env ++ env)
                                (Moist.MIR.expandFix inner) with
              | some t' => exact ⟨t', rfl⟩
              | none =>
                exfalso
                have h_long_none := Moist.MIR.lowerTotal_prepend_unused_none_gen
                    (x :: f :: s_c :: prefix_env) env v (Moist.MIR.expandFix inner)
                    hunused_inner (by
                      rw [show x :: f :: s_c :: prefix_env ++ env =
                            (x :: f :: s_c :: prefix_env) ++ env from rfl] at h_short
                      exact h_short)
                rw [show (x :: f :: s_c :: prefix_env) ++ v :: env =
                      x :: f :: s_c :: prefix_env ++ v :: env from rfl] at h_long_none
                rw [h_long_none] at h_inner_low
                exact Option.noConfusion h_inner_low
            obtain ⟨t_some, ht_some⟩ := h_shorter_some
            have h_shift := Moist.MIR.lowerTotal_prepend_unused_gen
                (x :: f :: s_c :: prefix_env) env v (Moist.MIR.expandFix inner)
                hunused_inner t_some (by
                  rw [show x :: f :: s_c :: prefix_env ++ env =
                        (x :: f :: s_c :: prefix_env) ++ env from rfl] at ht_some
                  exact ht_some)
            rw [show (x :: f :: s_c :: prefix_env) ++ v :: env =
                  x :: f :: s_c :: prefix_env ++ v :: env from rfl] at h_shift
            rw [h_inner_low] at h_shift
            injection h_shift with h_t_inner
            rw [h_sub, h_rhs_decomp, ht_some, Option.map_some, h_t_body_eq]
            rw [substTerm_fixLamWrapUplc _ _ _ (by omega : prefix_env.length + 1 ≥ 1)]
            congr 1
            rw [h_t_inner]
            simp only [List.length_cons]
            rw [substTerm_shift_cancel (prefix_env.length + 1 + 1 + 1 + 1) _ t_some (by omega)]
          · -- Case C: f ≠ v, x ≠ v. Subst descends into inner.
            have hxv' : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
            -- Compute subst: since f ≠ v, f ∉ freeVars rhs, x ≠ v, x ∉ freeVars rhs,
            -- subst descends into inner with Fix and Lam wrappers unchanged.
            have h_sub : (Moist.MIR.subst v rhs (Expr.Fix f (.Lam x inner)) s).1 =
                Expr.Fix f (.Lam x (Moist.MIR.subst v rhs inner s).1) := by
              simp only [Moist.MIR.subst, hfv', h_f_fv, hxv', h_x_fv, bind, StateT.bind,
                         pure, StateT.pure, Bool.false_eq_true, ↓reduceIte]
              rfl
            -- Pick s_pick fresh for inner, rhs, and with uid > v.uid (so s_pick ≠ v)
            let s_pick : VarId :=
              ⟨max (max (Moist.MIR.maxUidExpr inner) (Moist.MIR.maxUidExpr rhs)) v.uid + 1,
               .gen, "s"⟩
            have hs_pick_inner : (Moist.MIR.freeVars inner).contains s_pick = false :=
              Moist.MIR.maxUidExpr_fresh inner s_pick (by
                have h : s_pick.uid = max (max (Moist.MIR.maxUidExpr inner)
                                              (Moist.MIR.maxUidExpr rhs)) v.uid + 1 := rfl
                omega)
            have hs_pick_rhs : (Moist.MIR.freeVars rhs).contains s_pick = false :=
              Moist.MIR.maxUidExpr_fresh rhs s_pick (by
                have h : s_pick.uid = max (max (Moist.MIR.maxUidExpr inner)
                                              (Moist.MIR.maxUidExpr rhs)) v.uid + 1 := rfl
                omega)
            have hs_pick_ef_inner : (Moist.MIR.freeVars (Moist.MIR.expandFix inner)).contains s_pick = false :=
              Moist.MIR.expandFix_freeVars_not_contains inner s_pick hs_pick_inner
            have hs_pick_subst :
                (Moist.MIR.freeVars (Moist.MIR.subst v rhs inner s).1).contains s_pick = false :=
              freeVars_subst_not_contains v rhs inner s_pick s h_nc_inner hs_pick_inner hs_pick_rhs
            have hs_pick_ef_subst :
                (Moist.MIR.freeVars (Moist.MIR.expandFix (Moist.MIR.subst v rhs inner s).1)).contains
                    s_pick = false :=
              Moist.MIR.expandFix_freeVars_not_contains _ s_pick hs_pick_subst
            have h_spick_ne_v : (s_pick == v) = false := by
              rw [Moist.Verified.MIR.VarId_beq_false_iff]
              exact Or.inr (by
                have h : s_pick.uid = max (max (Moist.MIR.maxUidExpr inner)
                                              (Moist.MIR.maxUidExpr rhs)) v.uid + 1 := rfl
                omega)
            -- s_c (the canonical variable for this Fix-Lam) is fresh for expandFix inner
            have hs_c_ef_inner : (Moist.MIR.freeVars (Moist.MIR.expandFix inner)).contains s_c = false :=
              Moist.MIR.maxUidExpr_fresh (Moist.MIR.expandFix inner) s_c (by
                have h : s_c.uid = Moist.MIR.maxUidExpr (Moist.MIR.expandFix inner) + 1 := rfl
                omega)
            -- Swap s_c for s_pick in h_inner_low via env_swap_unused
            have h_inner_low_pick : Moist.MIR.lowerTotal
                (x :: f :: s_pick :: prefix_env ++ v :: env)
                (Moist.MIR.expandFix inner) = some t_inner := by
              rw [show x :: f :: s_pick :: prefix_env ++ v :: env =
                    [x, f] ++ s_pick :: (prefix_env ++ v :: env) from rfl,
                  ← Moist.MIR.lowerTotal_env_swap_unused [x, f] (prefix_env ++ v :: env)
                      s_c s_pick (Moist.MIR.expandFix inner) hs_c_ef_inner hs_pick_ef_inner,
                  show [x, f] ++ s_c :: (prefix_env ++ v :: env) =
                       x :: f :: s_c :: prefix_env ++ v :: env from rfl]
              exact h_inner_low
            -- Build extended hv_notin for prefix x :: f :: s_pick :: prefix_env
            have hv_notin_ext : envLookupT (x :: f :: s_pick :: prefix_env) v = none := by
              rw [Moist.MIR.envLookupT_cons_neq x v (f :: s_pick :: prefix_env) hxv',
                  Moist.MIR.envLookupT_cons_neq f v (s_pick :: prefix_env) hfv',
                  Moist.MIR.envLookupT_cons_neq s_pick v prefix_env h_spick_ne_v,
                  hv_notin]
              rfl
            -- Build extended hfresh: all of x, f, s_pick, prefix_env vars are fresh for expandFix rhs
            have hfresh_ext : ∀ w ∈ (x :: f :: s_pick :: prefix_env),
                (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w = false := by
              intro w hw
              rcases List.mem_cons.mp hw with rfl | hw
              · exact Moist.MIR.expandFix_freeVars_not_contains rhs w h_x_fv
              rcases List.mem_cons.mp hw with rfl | hw
              · exact Moist.MIR.expandFix_freeVars_not_contains rhs w h_f_fv
              rcases List.mem_cons.mp hw with h_ws | hw
              · rw [h_ws]; exact Moist.MIR.expandFix_freeVars_not_contains rhs s_pick hs_pick_rhs
              · exact hfresh w hw
            -- Apply IH to inner with prefix x :: f :: s_pick :: prefix_env
            have ih_inner := subst_lowerTotal_comm_fresh v rhs inner
                (x :: f :: s_pick :: prefix_env) env s t_inner t_rhs
                hv_notin_ext hfresh_ext h_nc_inner
                (by rw [List.cons_append, List.cons_append, List.cons_append]; exact h_inner_low_pick)
                h_rhs
            -- Assemble: decompose LHS lowering, apply IH, match substTerm arguments
            rw [h_sub, h_t_body_eq]
            rw [show Moist.MIR.lowerTotal (prefix_env ++ env)
                    (Moist.MIR.expandFix (.Fix f (.Lam x (Moist.MIR.subst v rhs inner s).1))) =
                  (Moist.MIR.lowerTotal (x :: f :: s_pick :: (prefix_env ++ env))
                      (Moist.MIR.expandFix (Moist.MIR.subst v rhs inner s).1)).map
                    Moist.MIR.fixLamWrapUplc
                from show Moist.MIR.lowerTotalExpr (prefix_env ++ env)
                       (.Fix f (.Lam x (Moist.MIR.subst v rhs inner s).1)) = _
                     from Moist.MIR.lowerTotalExpr_fix_lam_with_fresh
                            (prefix_env ++ env) f x _ s_pick hs_pick_ef_subst]
            rw [show x :: f :: s_pick :: (prefix_env ++ env) =
                  (x :: f :: s_pick :: prefix_env) ++ env from rfl,
                ih_inner, Option.map_some,
                substTerm_fixLamWrapUplc _ _ _ (by omega : prefix_env.length + 1 ≥ 1)]
            have hpos2 : (x :: f :: s_pick :: prefix_env).length + 1 = prefix_env.length + 1 + 3 := by
              simp only [List.length_cons]
            have hshift2 : iterShift (x :: f :: s_pick :: prefix_env).length t_rhs =
                iterShift 3 (iterShift prefix_env.length t_rhs) := by
              simp only [List.length_cons]
              rw [show prefix_env.length + 1 + 1 + 1 = 3 + prefix_env.length from by omega,
                  iterShift_add]
            rw [hpos2, hshift2]
    | .Var _ | .Lit _ | .Builtin _ | .Error | .App _ _
    | .Force _ | .Delay _ | .Constr _ _ | .Case _ _
    | .Let _ _ | .Fix _ _ =>
      -- Non-Lam b: expandFix (.Fix f b) = .Fix f (expandFix b). Lowering fails.
      all_goals (
        simp only [Moist.MIR.expandFix] at h_body
        rw [Moist.MIR.lowerTotal.eq_12] at h_body
        exact absurd h_body (by simp))
termination_by sizeOf body

/-- List variant of the fresh Phase 2a, for `.Constr` / `.Case` alternatives. -/
private theorem substList_lowerTotalList_comm_fresh
    (v : VarId) (rhs : Expr) (es : List Expr)
    (prefix_env env : List VarId) (s : Moist.MIR.FreshState)
    (t_es : List Term) (t_rhs : Term)
    (hv_notin : envLookupT prefix_env v = none)
    (hfresh : ∀ w ∈ prefix_env, (Moist.MIR.freeVars
                (Moist.MIR.expandFix rhs)).contains w = false)
    (h_nc : noCaptureFromList (Moist.MIR.freeVars rhs) es = true)
    (h_es : Moist.MIR.lowerTotalList (prefix_env ++ v :: env)
              (Moist.MIR.expandFixList es) = some t_es)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotalList (prefix_env ++ env)
        (Moist.MIR.expandFixList (Moist.MIR.substList v rhs es s).1) =
      some (Moist.Verified.substTermList (prefix_env.length + 1)
              (iterShift prefix_env.length t_rhs) t_es) := by
  match es with
  | [] =>
    -- substList v rhs [] s = pure []
    -- expandFixList [] = []
    -- lowerTotalList _ [] = some []
    -- substTermList _ _ [] = []
    have h_efl : Moist.MIR.expandFixList ([] : List Expr) = [] := by
      simp only [Moist.MIR.expandFixList]
    rw [h_efl] at h_es
    rw [Moist.MIR.lowerTotalList.eq_1] at h_es
    injection h_es with h_tb
    subst h_tb
    have h_sub : (Moist.MIR.substList v rhs ([] : List Expr) s).1 = [] := by
      simp only [Moist.MIR.substList, pure, StateT.pure]
    rw [h_sub, h_efl]
    show Moist.MIR.lowerTotalList (prefix_env ++ env) ([] : List Expr) = _
    rw [Moist.MIR.lowerTotalList.eq_1]
    simp only [Moist.Verified.substTermList]
  | e :: rest =>
    -- expandFixList (e :: rest) = expandFix e :: expandFixList rest
    -- lowerTotalList env (e :: rest) = do t ← lowerTotal env (expandFix e); ts ← lowerTotalList env (expandFixList rest); some (t :: ts)
    simp only [Moist.MIR.expandFixList, Moist.MIR.lowerTotalList.eq_2,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_es
    obtain ⟨t_e, ht_e, t_rest, ht_rest, h_es_eq⟩ := h_es
    have ⟨h_nc_e, h_nc_rest⟩ := noCaptureFromList_cons h_nc
    have ih_e := subst_lowerTotal_comm_fresh v rhs e prefix_env env s t_e t_rhs
                   hv_notin hfresh h_nc_e ht_e h_rhs
    have ih_rest := substList_lowerTotalList_comm_fresh v rhs rest prefix_env env
                      (Moist.MIR.subst v rhs e s).2 t_rest t_rhs
                      hv_notin hfresh h_nc_rest ht_rest h_rhs
    have h_sub : (Moist.MIR.substList v rhs (e :: rest) s).1 =
        (Moist.MIR.subst v rhs e s).1 ::
         (Moist.MIR.substList v rhs rest (Moist.MIR.subst v rhs e s).2).1 := by
      simp only [Moist.MIR.substList, bind, StateT.bind, pure, StateT.pure]; rfl
    rw [h_sub]
    simp only [Moist.MIR.expandFixList, Moist.MIR.lowerTotalList.eq_2,
               ih_e, ih_rest, Option.bind_eq_bind, Option.bind_some]
    injection h_es_eq with h_eq
    rw [← h_eq]
    simp only [Moist.Verified.substTermList]
termination_by sizeOf es

/-- Let variant of the fresh Phase 2a, for `.Let binds body` bodies. -/
private theorem substLet_lowerTotalLet_comm_fresh
    (v : VarId) (rhs : Expr) (binds : List (VarId × Expr × Bool)) (body : Expr)
    (prefix_env env : List VarId) (s : Moist.MIR.FreshState)
    (t_lb t_rhs : Term)
    (hv_notin : envLookupT prefix_env v = none)
    (hfresh : ∀ w ∈ prefix_env, (Moist.MIR.freeVars
                (Moist.MIR.expandFix rhs)).contains w = false)
    (h_nc : noCaptureFromLet (Moist.MIR.freeVars rhs) binds body = true)
    (h_lb : Moist.MIR.lowerTotalLet (prefix_env ++ v :: env)
              (Moist.MIR.expandFixBinds binds) (Moist.MIR.expandFix body) = some t_lb)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    ∃ t_lb' : Term,
      Moist.MIR.lowerTotalLet (prefix_env ++ env)
          (Moist.MIR.expandFixBinds (Moist.MIR.substLet v rhs
            (Moist.MIR.freeVars rhs) binds body s).1.1)
          (Moist.MIR.expandFix (Moist.MIR.substLet v rhs
            (Moist.MIR.freeVars rhs) binds body s).1.2) = some t_lb' ∧
      t_lb' = substTerm (prefix_env.length + 1)
                (iterShift prefix_env.length t_rhs) t_lb := by
  match binds with
  | [] =>
    -- nil case: substLet does subst on body only
    have h_efb : Moist.MIR.expandFixBinds ([] : List (VarId × Expr × Bool)) = [] := by
      simp only [Moist.MIR.expandFixBinds]
    rw [h_efb, Moist.MIR.lowerTotalLet.eq_1] at h_lb
    have h_nc_body := noCaptureFromLet_nil_body h_nc
    have ih := subst_lowerTotal_comm_fresh v rhs body prefix_env env s t_lb t_rhs
                 hv_notin hfresh h_nc_body h_lb h_rhs
    have h_sl_binds : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) [] body s).1.1 =
                     ([] : List (VarId × Expr × Bool)) := by
      simp only [Moist.MIR.substLet, bind, StateT.bind, pure, StateT.pure]; rfl
    have h_sl_body : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) [] body s).1.2 =
                     (Moist.MIR.subst v rhs body s).1 := by
      simp only [Moist.MIR.substLet, bind, StateT.bind, pure, StateT.pure]; rfl
    refine ⟨substTerm (prefix_env.length + 1) (iterShift prefix_env.length t_rhs) t_lb, ?_, rfl⟩
    rw [h_sl_binds, h_sl_body, h_efb, Moist.MIR.lowerTotalLet.eq_1]
    exact ih
  | (x, rhs_head, er) :: rest =>
    -- Unfold h_lb: cons lowering gives Apply (Lam 0 T) t_rhs_head
    simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet.eq_2,
               Option.bind_eq_bind, Option.bind_eq_some_iff] at h_lb
    obtain ⟨t_rhs_head_orig, h_rhs_head_orig, T, hT, h_lb_eq⟩ := h_lb
    -- Destructure h_nc: (x ∉ freeVars rhs) ∧ noCaptureFrom rhs_head ∧ noCaptureFromLet rest body
    have ⟨h_nc_x, h_nc_rhs_head, h_nc_rest⟩ := noCaptureFromLet_cons h_nc
    -- Apply subst_lowerTotal_comm_fresh to the head's RHS
    have ih_head := subst_lowerTotal_comm_fresh v rhs rhs_head prefix_env env s
                      t_rhs_head_orig t_rhs hv_notin hfresh h_nc_rhs_head h_rhs_head_orig h_rhs
    -- Case split on x == v and freeVars rhs .contains x
    by_cases hxv : (x == v) = true
    · -- Case 1: x == v (shadow). rest/body unchanged.
      have h_sl_binds : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                          ((x, rhs_head, er) :: rest) body s).1.1 =
            (x, (Moist.MIR.subst v rhs rhs_head s).1, er) :: rest := by
        simp only [Moist.MIR.substLet, hxv, if_true, bind, StateT.bind, pure, StateT.pure]
        rfl
      have h_sl_body : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                          ((x, rhs_head, er) :: rest) body s).1.2 = body := by
        simp only [Moist.MIR.substLet, hxv, if_true, bind, StateT.bind, pure, StateT.pure]
        rfl
      -- Show lowerTotalLet succeeds under shorter env via prepend_unused_none contrapositive
      have hunused_cond : (Moist.MIR.freeVarsLet (Moist.MIR.expandFixBinds rest)
                            (Moist.MIR.expandFix body)).contains v = false ∨
                          (∃ y ∈ (x :: prefix_env), (y == v) = true) :=
        Or.inr ⟨x, List.Mem.head _, hxv⟩
      have h_shorter_some : ∃ T',
          Moist.MIR.lowerTotalLet (x :: prefix_env ++ env) (Moist.MIR.expandFixBinds rest)
            (Moist.MIR.expandFix body) = some T' := by
        cases h_short : Moist.MIR.lowerTotalLet (x :: prefix_env ++ env)
                          (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) with
        | some T' => exact ⟨T', rfl⟩
        | none =>
          exfalso
          have h_prepend_none := Moist.MIR.lowerTotalLet_prepend_unused_none_gen
                                 (x :: prefix_env) env v (Moist.MIR.expandFixBinds rest)
                                 (Moist.MIR.expandFix body) hunused_cond h_short
          rw [List.cons_append] at h_prepend_none
          rw [h_prepend_none] at hT
          exact Option.noConfusion hT
      obtain ⟨T', hT'⟩ := h_shorter_some
      have h_prepend_some := Moist.MIR.lowerTotalLet_prepend_unused_gen
                             (x :: prefix_env) env v (Moist.MIR.expandFixBinds rest)
                             (Moist.MIR.expandFix body) hunused_cond T' hT'
      rw [List.cons_append] at h_prepend_some
      rw [hT] at h_prepend_some
      injection h_prepend_some with h_shift_eq
      -- Witness
      refine ⟨substTerm (prefix_env.length + 1)
                (iterShift prefix_env.length t_rhs) t_lb, ?_, rfl⟩
      rw [h_sl_binds, h_sl_body]
      simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet.eq_2,
                 Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨_, ih_head, T', ?_, ?_⟩
      · rw [← List.cons_append]; exact hT'
      · injection h_lb_eq with h_eq
        rw [← h_eq]
        simp only [substTerm, List.length_cons] at h_shift_eq ⊢
        rw [h_shift_eq]
        rw [substTerm_shift_cancel (prefix_env.length + 1 + 1) _ T' (by omega)]
    · -- x ≠ v. h_nc_x gives x ∉ freeVars rhs, so capture branch is vacuous.
      have hne : (x == v) = false := by cases h : (x == v); rfl; exact absurd h hxv
      have hnot_free : (Moist.MIR.freeVars rhs).contains x = false := h_nc_x
      have hnot_free_ef : (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains x = false :=
        Moist.MIR.expandFix_freeVars_not_contains rhs x hnot_free
      -- Compute substLet
      have h_sl_binds : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                          ((x, rhs_head, er) :: rest) body s).1.1 =
            (x, (Moist.MIR.subst v rhs rhs_head s).1, er) ::
              (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) rest body
                (Moist.MIR.subst v rhs rhs_head s).2).1.1 := by
        simp only [Moist.MIR.substLet, hne, hnot_free, bind, StateT.bind, pure]
        rfl
      have h_sl_body : (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs)
                          ((x, rhs_head, er) :: rest) body s).1.2 =
            (Moist.MIR.substLet v rhs (Moist.MIR.freeVars rhs) rest body
              (Moist.MIR.subst v rhs rhs_head s).2).1.2 := by
        simp only [Moist.MIR.substLet, hne, hnot_free, bind, StateT.bind, pure]
        rfl
      -- Extended prefix_env: x :: prefix_env
      have hv_notin_ext : envLookupT (x :: prefix_env) v = none := by
        rw [Moist.MIR.envLookupT_cons_neq x v prefix_env hne, hv_notin]; rfl
      have hfresh_ext : ∀ w ∈ (x :: prefix_env),
          (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w = false := by
        intro w hw
        rcases List.mem_cons.mp hw with hhead | htail
        · subst hhead; exact hnot_free_ef
        · exact hfresh w htail
      -- Apply IH on rest/body
      have hT_ext : Moist.MIR.lowerTotalLet ((x :: prefix_env) ++ v :: env)
                       (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) = some T := by
        rw [List.cons_append]; exact hT
      have ih_rest := substLet_lowerTotalLet_comm_fresh v rhs rest body
                        (x :: prefix_env) env (Moist.MIR.subst v rhs rhs_head s).2
                        T t_rhs hv_notin_ext hfresh_ext h_nc_rest hT_ext h_rhs
      obtain ⟨T', hT', hT'_eq⟩ := ih_rest
      -- Provide witness
      refine ⟨substTerm (prefix_env.length + 1)
                (iterShift prefix_env.length t_rhs) t_lb, ?_, rfl⟩
      rw [h_sl_binds, h_sl_body]
      simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet.eq_2,
                 Option.bind_eq_bind, Option.bind_eq_some_iff]
      refine ⟨_, ih_head, T', ?_, ?_⟩
      · rw [← List.cons_append]; exact hT'
      · injection h_lb_eq with h_eq
        rw [← h_eq]
        simp only [substTerm, List.length_cons] at hT'_eq ⊢
        rw [hT'_eq, ← iterShift_succ]
termination_by sizeOf binds + sizeOf body

end

-- === Section 5.3: Alpha-rename prefix freshening ===

/-- Given `prefix_env` and a FreshState `s` whose `next` bounds all uids in
    `body`, `rhs`, `env`, and `v`, produce a fresh prefix env plus a rename
    substitution σ (as a list of `(old, new)` pairs). Each new binder has
    `.gen` origin and uid ≥ `s.next`, making them disjoint from every uid
    in the ambient context. Matches the `SubstFreshAbove` shape used by
    `alphaRename_lowerTotal_eq` in `AlphaRenameSoundness`. -/
private def freshenPrefix :
    List VarId → Moist.MIR.FreshState →
    (List (VarId × VarId) × List VarId) × Moist.MIR.FreshState
  | [], s => (([], []), s)
  | w :: rest, s =>
    let w' : VarId := { uid := s.next, origin := .gen, hint := w.hint }
    let s' : Moist.MIR.FreshState := ⟨s.next + 1⟩
    let ⟨⟨σ_rest, prefix_fresh_rest⟩, s''⟩ := freshenPrefix rest s'
    (((w, w') :: σ_rest, w' :: prefix_fresh_rest), s'')

/-- `freshenPrefix` preserves list length. -/
private theorem freshenPrefix_length (prefix_env : List VarId)
    (s : Moist.MIR.FreshState) :
    (freshenPrefix prefix_env s).1.2.length = prefix_env.length := by
  induction prefix_env generalizing s with
  | nil => rfl
  | cons w rest ih =>
    show (_ :: (freshenPrefix rest ⟨s.next + 1⟩).1.2).length = (w :: rest).length
    rw [List.length_cons, List.length_cons]
    exact congrArg (· + 1) (ih _)

/-- Every binder produced by `freshenPrefix` has uid ≥ `s.next` and `.gen` origin. -/
private theorem freshenPrefix_fresh_bound (prefix_env : List VarId)
    (s : Moist.MIR.FreshState) :
    ∀ w ∈ (freshenPrefix prefix_env s).1.2, s.next ≤ w.uid ∧ w.origin = .gen := by
  induction prefix_env generalizing s with
  | nil => intro w hw; exact absurd hw List.not_mem_nil
  | cons w rest ih =>
    intro w0 hw0
    have hw0' : w0 ∈ ({ uid := s.next, origin := .gen, hint := w.hint } ::
                     (freshenPrefix rest ⟨s.next + 1⟩).1.2) := hw0
    rcases List.mem_cons.mp hw0' with hhead | htail
    · subst hhead; exact ⟨Nat.le_refl _, rfl⟩
    · have ih' := ih (s := ⟨s.next + 1⟩) w0 htail
      refine ⟨?_, ih'.2⟩
      have hub := ih'.1
      show s.next ≤ w0.uid
      have : (⟨s.next + 1⟩ : Moist.MIR.FreshState).next = s.next + 1 := rfl
      rw [this] at hub
      omega

/-- The rename σ returned by `freshenPrefix` maps exactly the elements of
    `prefix_env` (in order) to their fresh counterparts. -/
private theorem freshenPrefix_sigma_image (prefix_env : List VarId)
    (s : Moist.MIR.FreshState) :
    (freshenPrefix prefix_env s).1.1.map Prod.fst = prefix_env ∧
    (freshenPrefix prefix_env s).1.1.map Prod.snd = (freshenPrefix prefix_env s).1.2 := by
  induction prefix_env generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons w rest ih =>
    have ih' := ih (s := ⟨s.next + 1⟩)
    refine ⟨?_, ?_⟩
    · show ((w, _) :: (freshenPrefix rest _).1.1).map Prod.fst = w :: rest
      simp only [List.map_cons]
      exact congrArg (w :: ·) ih'.1
    · show ((w, _) :: (freshenPrefix rest _).1.1).map Prod.snd =
            _ :: (freshenPrefix rest _).1.2
      simp only [List.map_cons]
      exact congrArg (_ :: ·) ih'.2

-- === Section 5.4: Main theorem via alpha-rename routing ===

/-- Phase 2a main theorem. Takes freshness preconditions to forward to
    the fresh-prefix variant. These must be established at the call site
    (typically via canonicalize prior to inlining). -/
private theorem subst_lowerTotal_comm_gen
    (v : VarId) (rhs body : Expr)
    (prefix_env env : List VarId) (s : Moist.MIR.FreshState)
    (t_body t_rhs : Term)
    (hv_notin : envLookupT prefix_env v = none)
    (hfresh : ∀ w ∈ prefix_env, (Moist.MIR.freeVars
                (Moist.MIR.expandFix rhs)).contains w = false)
    (h_nc : noCaptureFrom (Moist.MIR.freeVars rhs) body = true)
    (h_body : Moist.MIR.lowerTotal (prefix_env ++ v :: env)
                (Moist.MIR.expandFix body) = some t_body)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotal (prefix_env ++ env)
        (Moist.MIR.expandFix (Moist.MIR.subst v rhs body s).1) =
      some (substTerm (prefix_env.length + 1)
                      (iterShift prefix_env.length t_rhs) t_body) :=
  subst_lowerTotal_comm_fresh v rhs body prefix_env env s t_body t_rhs
    hv_notin hfresh h_nc h_body h_rhs

/-- Phase 2a (direct form: empty prefix env). -/
private theorem subst_lowerTotal_comm
    (v : VarId) (rhs body : Expr)
    (env : List VarId) (s : Moist.MIR.FreshState)
    (t_body t_rhs : Term)
    (h_nc : noCaptureFrom (Moist.MIR.freeVars rhs) body = true)
    (h_body : Moist.MIR.lowerTotal (v :: env) (Moist.MIR.expandFix body) = some t_body)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotal env (Moist.MIR.expandFix (Moist.MIR.subst v rhs body s).1) =
      some (substTerm 1 t_rhs t_body) := by
  have h := subst_lowerTotal_comm_gen v rhs body [] env s t_body t_rhs rfl
              (by intro w hw; exact absurd hw List.not_mem_nil) h_nc h_body h_rhs
  simpa [iterShift_zero] using h

/-- Phase 2b (generalized with prefix env).

By induction on `rest`; each head binding uses Phase 2a on its RHS and the
IH on the tail (with `prefix_env` extended by the head binder `w`). The
position / shift parameters track correctly via `iterShift_succ`.

* `hv_notin` ensures `v` is not shadowed in `prefix_env` (propagates to Phase 2a).
* `hbinders` ensures no binder in `rest` equals `v`; combined with `hv_notin`
  this keeps the extended prefix `w :: prefix_env` v-free across the IH. -/
private theorem substInBindings_lowerTotalLet_comm_gen
    (v : VarId) (rhs body : Expr)
    (rest : List (VarId × Expr × Bool))
    (prefix_env env : List VarId) (sb sr : Moist.MIR.FreshState)
    (t_rest t_rhs : Term)
    (hv_notin : envLookupT prefix_env v = none)
    (hbinders : rest.all (fun b => !(b.1 == v)) = true)
    (hfresh : ∀ w ∈ prefix_env, (Moist.MIR.freeVars
                (Moist.MIR.expandFix rhs)).contains w = false)
    (h_nc_body : noCaptureFrom (Moist.MIR.freeVars rhs) body = true)
    (h_nc_rest : rest.all
        (fun b => noCaptureFrom (Moist.MIR.freeVars rhs) b.2.1) = true)
    (h_binders_fresh : rest.all
        (fun b => !(Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains b.1) = true)
    (h_rest : Moist.MIR.lowerTotalLet (prefix_env ++ v :: env)
                (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) = some t_rest)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotalLet (prefix_env ++ env)
        (Moist.MIR.expandFixBinds (Moist.MIR.substInBindings v rhs rest sr).1.val)
        (Moist.MIR.expandFix (Moist.MIR.subst v rhs body sb).1) =
      some (substTerm (prefix_env.length + 1)
                      (iterShift prefix_env.length t_rhs) t_rest) := by
  induction rest generalizing prefix_env sb sr t_rest with
  | nil =>
    -- substInBindings v rhs [] sr has .1.val = []
    -- expandFixBinds [] = []
    -- lowerTotalLet env [] t = lowerTotal env t
    have hsib : (Moist.MIR.substInBindings v rhs [] sr).1.val = [] := rfl
    -- Simplify h_rest: expandFixBinds [] = [] and lowerTotalLet _ [] t = lowerTotal _ t
    simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet] at h_rest
    have h_subst :
        Moist.MIR.lowerTotal (prefix_env ++ env) (Moist.MIR.expandFix (Moist.MIR.subst v rhs body sb).1)
          = some (substTerm (prefix_env.length + 1) (iterShift prefix_env.length t_rhs) t_rest) :=
      subst_lowerTotal_comm_gen v rhs body prefix_env env sb t_rest t_rhs hv_notin
        hfresh h_nc_body h_rest h_rhs
    -- Simplify goal similarly
    show Moist.MIR.lowerTotalLet (prefix_env ++ env)
          (Moist.MIR.expandFixBinds (Moist.MIR.substInBindings v rhs [] sr).1.val)
          (Moist.MIR.expandFix (Moist.MIR.subst v rhs body sb).1) = _
    rw [hsib]
    simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet]
    exact h_subst
  | cons head tail ih =>
    obtain ⟨w, e, er⟩ := head
    -- Extract binder-distinctness for head (w ≠ v) and tail from hbinders
    have hbinders_head : (w == v) = false := by
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                 Bool.not_true] at hbinders
      exact hbinders.1
    have hbinders_tail : tail.all (fun b => !(b.1 == v)) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at hbinders
      exact hbinders.2
    -- Extract head and tail h_nc from h_nc_rest
    have h_nc_e : noCaptureFrom (Moist.MIR.freeVars rhs) e = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h_nc_rest
      exact h_nc_rest.1
    have h_nc_tail : tail.all
        (fun b => noCaptureFrom (Moist.MIR.freeVars rhs) b.2.1) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h_nc_rest
      exact h_nc_rest.2
    -- Extract head freshness and tail freshness from h_binders_fresh
    have h_w_fresh : (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w = false := by
      simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                 Bool.not_true] at h_binders_fresh
      exact h_binders_fresh.1
    have h_binders_fresh_tail : tail.all
        (fun b => !(Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains b.1) = true := by
      simp only [List.all_cons, Bool.and_eq_true] at h_binders_fresh
      exact h_binders_fresh.2
    -- Extend hv_notin to (w :: prefix_env)
    have hv_notin_ext : envLookupT (w :: prefix_env) v = none := by
      rw [Moist.MIR.envLookupT_cons_neq w v prefix_env hbinders_head, hv_notin]
      rfl
    -- Extend hfresh to (w :: prefix_env)
    have hfresh_ext : ∀ w' ∈ (w :: prefix_env),
        (Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains w' = false := by
      intro w' hw'
      rcases List.mem_cons.mp hw' with hh | ht
      · subst hh; exact h_w_fresh
      · exact hfresh w' ht
    -- Unfold expandFixBinds on (w, e, er) :: tail  AND  lowerTotalLet for cons in h_rest
    simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet] at h_rest
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h_rest
    obtain ⟨t_e, ht_e, T, hT, heq⟩ := h_rest
    -- Apply Phase 2a on e
    have h_e_subst :
        Moist.MIR.lowerTotal (prefix_env ++ env) (Moist.MIR.expandFix (Moist.MIR.subst v rhs e sr).1)
          = some (substTerm (prefix_env.length + 1) (iterShift prefix_env.length t_rhs) t_e) :=
      subst_lowerTotal_comm_gen v rhs e prefix_env env sr t_e t_rhs hv_notin
        hfresh h_nc_e ht_e h_rhs
    -- Apply IH with extended prefix_env
    have hT' : Moist.MIR.lowerTotalLet ((w :: prefix_env) ++ v :: env)
                 (Moist.MIR.expandFixBinds tail) (Moist.MIR.expandFix body) = some T := by
      rw [List.cons_append]; exact hT
    have h_ih := ih (prefix_env := w :: prefix_env) (sb := sb)
                    (sr := (Moist.MIR.subst v rhs e sr).2) (t_rest := T)
                    hv_notin_ext hbinders_tail hfresh_ext h_nc_tail
                    h_binders_fresh_tail hT'
    rw [List.cons_append, List.length_cons] at h_ih
    -- Now unfold the goal's LHS: substInBindings on cons, then expandFixBinds, then lowerTotalLet
    have h_sib_cons :
        (Moist.MIR.substInBindings v rhs ((w, e, er) :: tail) sr).1.val
          = (w, (Moist.MIR.subst v rhs e sr).1, er) ::
             (Moist.MIR.substInBindings v rhs tail (Moist.MIR.subst v rhs e sr).2).1.val := rfl
    show Moist.MIR.lowerTotalLet (prefix_env ++ env)
          (Moist.MIR.expandFixBinds
            (Moist.MIR.substInBindings v rhs ((w, e, er) :: tail) sr).1.val)
          (Moist.MIR.expandFix (Moist.MIR.subst v rhs body sb).1) = _
    rw [h_sib_cons]
    simp only [Moist.MIR.expandFixBinds, Moist.MIR.lowerTotalLet]
    have h_ih_adj : Moist.MIR.lowerTotalLet (w :: (prefix_env ++ env))
        (Moist.MIR.expandFixBinds
          (Moist.MIR.substInBindings v rhs tail (Moist.MIR.subst v rhs e sr).2).1.val)
        (Moist.MIR.expandFix (Moist.MIR.subst v rhs body sb).1) =
      some (substTerm (prefix_env.length + 1 + 1)
                      (iterShift (prefix_env.length + 1) t_rhs) T) := by
      rw [← List.cons_append]; exact h_ih
    rw [h_e_subst, h_ih_adj]
    simp only [Option.bind_eq_bind, Option.bind_some]
    -- Goal: some (Apply (Lam 0 (substTerm (k+1+1) (iterShift (k+1) t_rhs) T))
    --               (substTerm (k+1) (iterShift k t_rhs) t_e))
    --     = some (substTerm (k+1) (iterShift k t_rhs) t_rest)
    -- where t_rest = Apply (Lam 0 T) t_e (from heq after injection)
    have h_rest_eq : t_rest = .Apply (.Lam 0 T) t_e := by
      have := Option.some.inj heq.symm
      exact this
    rw [h_rest_eq]
    -- Unfold substTerm on Apply and Lam
    simp only [substTerm, iterShift_succ]

end Phase2

/-- Phase 2b (direct form: used by `InlineSoundness.lean`).

Lowering the inlined form of a let — body and rest-RHSes both substituted
with `rhs` for `v` — equals UPLC `substTerm` at position 1 applied to the
original Let lowering. Requires `distinct_binders` on the full binding list
to ensure `v` doesn't collide with any inner binder. -/
theorem substInBindings_lowerTotalLet_comm
    (v : VarId) (rhs : Expr)
    (rest : List (VarId × Expr × Bool)) (body : Expr) (er : Bool)
    (env : List VarId) (s : Moist.MIR.FreshState) (t_rest t_rhs : Term)
    (distinct_binders : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true)
    (h_nc_body : noCaptureFrom
                   (Moist.MIR.freeVars rhs) body = true)
    (h_nc_rest : rest.all (fun b => noCaptureFrom
                                      (Moist.MIR.freeVars rhs) b.2.1) = true)
    (h_binders_fresh : rest.all
        (fun b => !(Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains b.1) = true)
    (h_rest : Moist.MIR.lowerTotalLet (v :: env)
                (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) = some t_rest)
    (h_rhs : Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs) :
    Moist.MIR.lowerTotalLet env
        (Moist.MIR.expandFixBinds
          (Moist.MIR.substInBindings v rhs rest (Moist.MIR.subst v rhs body s).2).1.val)
        (Moist.MIR.expandFix (Moist.MIR.subst v rhs body s).1) =
      some (substTerm 1 t_rhs t_rest) := by
  -- Extract the `rest.all (!= v)` constraint from distinct_binders
  have hbinders : rest.all (fun b => !(b.1 == v)) = true := by
    simp only [Moist.MIR.distinctBinders, Bool.and_eq_true] at distinct_binders
    exact distinct_binders.1
  have h := Moist.Verified.InlineSoundness.SubstCommute.substInBindings_lowerTotalLet_comm_gen
              v rhs body rest [] env s
              (Moist.MIR.subst v rhs body s).2 t_rest t_rhs
              rfl hbinders (by intro w hw; exact absurd hw List.not_mem_nil)
              h_nc_body h_nc_rest h_binders_fresh h_rest h_rhs
  simpa [Moist.Verified.SubstRefines.iterShift_zero] using h

/-- Compile preservation for the Let-inline transformation.

If the original `let ((v, rhs, er) :: rest) body` form compiles to UPLC, then
after substituting `rhs` for `v` in `body` and in each `rest` binding's RHS,
the resulting `Let` form also compiles. This is the `isSome → isSome`
component required by `MIRCtxRefines`. Follows as a corollary of Phase 2b
(which gives an exact UPLC equality, hence `isSome`). -/
theorem subst_compile_preservation
    (v : VarId) (rhs body : Expr) (er : Bool)
    (rest : List (VarId × Expr × Bool))
    (s : Moist.MIR.FreshState) (env : List VarId)
    (distinct_binders : Moist.MIR.distinctBinders ((v, rhs, er) :: rest) = true)
    (h_nc_body : Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                   (Moist.MIR.freeVars rhs) body = true)
    (h_nc_rest : rest.all (fun b => Moist.Verified.InlineSoundness.SubstCommute.noCaptureFrom
                                      (Moist.MIR.freeVars rhs) b.2.1) = true)
    (h_binders_fresh : rest.all
        (fun b => !(Moist.MIR.freeVars (Moist.MIR.expandFix rhs)).contains b.1) = true) :
    (Moist.MIR.lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body)).isSome →
    (Moist.MIR.lowerTotalExpr env
        (.Let (Moist.MIR.substInBindings v rhs rest
                  (Moist.MIR.subst v rhs body s).2).1.val
              (Moist.MIR.subst v rhs body s).1)).isSome := by
  intro h_some
  -- Unfold lowerTotalExpr on the original Let to extract t_rhs and t_rest
  have h_lhs_unfold : Moist.MIR.lowerTotalExpr env (.Let ((v, rhs, er) :: rest) body) =
      (do let rhs' ← Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs)
          let rest' ← Moist.MIR.lowerTotalLet (v :: env)
                        (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body)
          some (.Apply (.Lam 0 rest') rhs')) := by
    simp only [Moist.MIR.lowerTotalExpr, Moist.MIR.expandFix,
               Moist.MIR.expandFixBinds, Moist.MIR.lowerTotal, Moist.MIR.lowerTotalLet]
  rw [h_lhs_unfold] at h_some
  -- Extract the two component successes
  have h_rhs_some : ∃ t_rhs, Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) = some t_rhs := by
    revert h_some; cases Moist.MIR.lowerTotal env (Moist.MIR.expandFix rhs) <;> simp
  obtain ⟨t_rhs, ht_rhs⟩ := h_rhs_some
  rw [ht_rhs] at h_some; simp at h_some
  have h_rest_some : ∃ t_rest, Moist.MIR.lowerTotalLet (v :: env)
      (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) = some t_rest := by
    revert h_some
    cases Moist.MIR.lowerTotalLet (v :: env)
      (Moist.MIR.expandFixBinds rest) (Moist.MIR.expandFix body) <;> simp
  obtain ⟨t_rest, ht_rest⟩ := h_rest_some
  -- Now apply Phase 2b to get the concrete lowered form
  have h_subst := substInBindings_lowerTotalLet_comm v rhs rest body er env s t_rest t_rhs
                    distinct_binders h_nc_body h_nc_rest h_binders_fresh ht_rest ht_rhs
  -- Unfold lowerTotalExpr on the substituted Let
  have h_rhs_unfold : Moist.MIR.lowerTotalExpr env
      (.Let (Moist.MIR.substInBindings v rhs rest
              (Moist.MIR.subst v rhs body s).2).1.val
            (Moist.MIR.subst v rhs body s).1) =
      Moist.MIR.lowerTotalLet env
        (Moist.MIR.expandFixBinds
          (Moist.MIR.substInBindings v rhs rest (Moist.MIR.subst v rhs body s).2).1.val)
        (Moist.MIR.expandFix (Moist.MIR.subst v rhs body s).1) := by
    simp only [Moist.MIR.lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.lowerTotal]
  rw [h_rhs_unfold, h_subst]
  rfl

end Moist.Verified.InlineSoundness.SubstCommute
