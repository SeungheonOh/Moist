import Moist.Verified.MIR
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Purity
import Moist.Verified.StepLift
import Moist.Verified.FundamentalRefines

/-! # Dead-let refinement

`Apply (Lam 0 (shift body)) rhs ⊑ body` whenever `rhs` returns to its
caller's stack. The left side takes `3 + m + 1` steps to reach
`compute π (ρ.extend v) (shift body)`, which refines `compute π ρ body` by
`renameRefines_shift1`.
-/

namespace Moist.Verified.DeadLet

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines

/-- A pure expression lowered in a well-sized environment returns to any
    stack without passing through `.error`. -/
theorem dead_let_pure_stack_poly
    (env : List Moist.MIR.VarId) (e : Moist.MIR.Expr) {t : Moist.Plutus.Term.Term}
    {ρ : CekEnv}
    (hpure : Moist.MIR.isPure e = true)
    (hlower : Moist.MIR.lowerTotal env e = some t)
    (hwf : Moist.Verified.Semantics.WellSizedEnv env.length ρ) :
    ∀ (π : Stack), ∃ (m : Nat) (v : CekValue),
      steps m (.compute π ρ t) = .ret π v ∧
      ∀ k ≤ m, steps k (.compute π ρ t) ≠ .error := by
  intro π
  obtain ⟨v, hhalt⟩ := Moist.Verified.Purity.isPure_halts e t env ρ hpure hlower hwf
  obtain ⟨m, hm⟩ := Moist.Verified.Purity.compute_to_ret_from_halt ρ t v π hhalt
  refine ⟨m, v, hm, fun k hk herr => ?_⟩
  rw [show m = k + (m - k) by omega, Equivalence.steps_trans, herr, steps_error] at hm
  cases hm

/-- Unidirectional dead-let refinement at the UPLC level: the dropped `t_rhs`
    must return to the caller's stack in every environment well-sized at `d`. -/
theorem uplc_dead_let_refines {d : Nat} {t_body : Term} (t_rhs : Term)
    (hclosed : closedAt d t_body = true)
    (h_rhs_returns : ∀ (ρ : CekEnv),
      (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
      ∀ (π : Stack), ∃ (m : Nat) (v_rhs : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v_rhs) :
    ∀ (k : Nat) (j : Nat), j ≤ k → ∀ (ρ₁ ρ₂ : CekEnv), EnvRefinesK j d ρ₁ ρ₂ →
      ∀ (i : Nat), i ≤ j → ∀ (π₁ π₂ : Stack), StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁
             (.Apply (.Lam 0 (renameTerm (shiftRename 1) t_body)) t_rhs))
          (.compute π₂ ρ₂ t_body) := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have hwf : ∀ n, 0 < n → n ≤ d → ∃ v, ρ₁.lookup n = some v := fun n hn hnd =>
    let ⟨v, _, hl, _⟩ := henv n hn hnd; ⟨v, hl⟩
  obtain ⟨m, v, hm⟩ :=
    h_rhs_returns ρ₁ hwf (.funV (.VLam (renameTerm (shiftRename 1) t_body) ρ₁) :: π₁)
  refine Equivalence.obsRefinesK_of_steps_left
    (n := 3 + m + 1) (s₁' := .compute π₁ (ρ₁.extend v) (renameTerm (shiftRename 1) t_body))
    (by
      rw [Equivalence.steps_trans, Equivalence.steps_trans]
      show steps 1 (steps m (.compute (.funV (.VLam _ ρ₁) :: π₁) ρ₁ t_rhs)) = _
      rw [hm]; rfl) ?_
  exact FundamentalRefines.renameRefines_shift1 d t_body hclosed i i (Nat.le_refl _) _ ρ₂
    (FundamentalRefines.renameEnvRef_mono hi
      (FundamentalRefines.envRefinesK_to_renameEnvRef_shift henv))
    i (Nat.le_refl _) π₁ π₂ hπ

open Moist.Verified.MIR (lowerTotal_closedAt)
open Moist.Verified.MIR
open Moist.MIR (Expr VarId lowerTotalExpr lowerTotal
  lowerTotal_prepend_unused lowerTotal_prepend_unused_none
  freeVars)

/-- MIR-level dead-let refinement: an unused pure binding can be dropped. -/
theorem dead_let_mirRefines {x : VarId} {e body : Expr}
    (hunused : (Moist.MIR.freeVars body).contains x = false)
    (hsafe : Moist.MIR.isPure e = true) :
    MIRRefines (.Let [(x, e, false)] body) body := by
  -- Derive preservation of freshness and purity under expandFix
  have hunused' : (Moist.MIR.freeVars (Moist.MIR.expandFix body)).contains x = false :=
    Moist.MIR.expandFix_freeVars_not_contains body x hunused
  have hsafe' : Moist.MIR.isPure (Moist.MIR.expandFix e) = true :=
    Moist.Verified.Purity.isPure_expandFix e hsafe
  refine ⟨?_, ?_⟩
  · -- Compile preservation: if Let lowers, body lowers
    intro env h_let
    -- Unfold lowerTotalExpr to reveal lowerTotal on expandFix'd expression
    have hlet_eq : lowerTotalExpr env (.Let [(x, e, false)] body) =
        lowerTotal env (.Let [(x, Moist.MIR.expandFix e, false)] (Moist.MIR.expandFix body)) := by
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds]
    have hbody_eq : lowerTotalExpr env body = lowerTotal env (Moist.MIR.expandFix body) := by
      simp only [lowerTotalExpr]
    rw [hlet_eq] at h_let
    rw [hbody_eq]
    cases hb_env : lowerTotal env (Moist.MIR.expandFix body) with
    | some _ => rfl
    | none =>
      exfalso
      have h_xe : lowerTotal (x :: env) (Moist.MIR.expandFix body) = none :=
        lowerTotal_prepend_unused_none env x _ hunused' hb_env
      simp only [Moist.MIR.lowerTotal.eq_11, Moist.MIR.lowerTotalLet.eq_2,
        Moist.MIR.lowerTotalLet.eq_1, h_xe, Option.bind_eq_bind] at h_let
      cases he : lowerTotal env (Moist.MIR.expandFix e) with
      | none => rw [he] at h_let; simp at h_let
      | some e_t => rw [he] at h_let; simp at h_let
  · -- Semantic part: MIROpenRef at every depth d
    intro d k env hlen
    have hlet_eq : lowerTotalExpr env (.Let [(x, e, false)] body) =
        lowerTotal env (.Let [(x, Moist.MIR.expandFix e, false)] (Moist.MIR.expandFix body)) := by
      simp only [lowerTotalExpr, Moist.MIR.expandFix, Moist.MIR.expandFixBinds]
    have hbody_eq : lowerTotalExpr env body = lowerTotal env (Moist.MIR.expandFix body) := by
      simp only [lowerTotalExpr]
    rw [hlet_eq, hbody_eq]
    simp only [Moist.MIR.lowerTotal.eq_11, Moist.MIR.lowerTotalLet.eq_2,
      Moist.MIR.lowerTotalLet.eq_1, Option.bind_eq_bind]
    cases he : lowerTotal env (Moist.MIR.expandFix e) with
    | none => simp
    | some e_t =>
      simp only [Option.bind_some]
      cases hb_env : lowerTotal env (Moist.MIR.expandFix body) with
      | none =>
        have := lowerTotal_prepend_unused_none env x _ hunused' hb_env
        rw [this]
        simp
      | some body_t =>
        have hshift := lowerTotal_prepend_unused env x _ hunused' body_t hb_env
        rw [hshift]
        simp only [Option.bind_some]
        intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
        have hclosed : closedAt d body_t = true := by
          have := lowerTotal_closedAt env _ body_t hb_env
          rw [hlen] at this; exact this
        refine uplc_dead_let_refines e_t hclosed (fun ρ hwf_ρ π => ?_) k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
        obtain ⟨m, v, hm, -⟩ := dead_let_pure_stack_poly env (Moist.MIR.expandFix e) hsafe' he
          (hlen ▸ hwf_ρ) π
        exact ⟨m, v, hm⟩

end Moist.Verified.DeadLet
