import Moist.Verified.EtaReduce.Relation
import Moist.Verified.BuiltinStateSoundness

/-! # The local eta rule

`λ. (shift F) 1 ⊑ F` whenever `F` returns a callable value (a closure, or a
builtin state whose next argument is a value) on every stack in every
well-sized environment. The source closure re-evaluates `F` each time it is
applied; the target applies the value `F` returned up front. Because `F`
returns on every stack, the target's early evaluation cannot fail or diverge,
and since `F` is deterministic each application of the closure behaves like an
application of that value.
-/

namespace Moist.Verified.EtaReduce

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList renameTerm shiftRename)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Semantics (WellSizedEnv)
open Moist.Verified.BuiltinState (Callable)
open Moist.Verified.FundamentalRefines (RenameEnvRef2 is0preserving_shiftRename
  is0preserving_id)

/-- The closure built by the source relates to a callable target value when
    applying the closure to related arguments refines applying the value. -/
theorem etaRel_closure {k : Nat} {body : Term} {ρ : CekEnv} {value : CekValue}
    (callable : Callable value)
    (apply : ∀ j < k, ∀ a₁ a₂, EtaRel j a₁ a₂ → ∀ i ≤ j, ∀ π₁ π₂, StackRel i π₁ π₂ →
      ObsRefinesK i (.compute π₁ (ρ.extend a₁) body) (.ret (.funV value :: π₂) a₂)) :
    EtaRel k (.VLam body ρ) value := by
  cases value with
  | VCon _ | VDelay _ _ | VConstr _ _ => exact absurd callable id
  | VLam body' ρ' =>
    cases k with
    | zero => simp only [EtaRel]
    | succ k =>
      simp only [EtaRel]
      intro j hj a₁ a₂ ha i hi π₁ π₂ hπ
      exact obsRefinesK_right_steps (n := 1) (apply j (by omega) a₁ a₂ ha i hi π₁ π₂ hπ)
  | VBuiltin b args remaining =>
    have head : remaining.head = .argV := callable
    cases k with
    | zero => simp only [EtaRel]; exact head
    | succ k =>
      simp only [EtaRel]
      exact ⟨head, fun j hj a₁ a₂ ha i hi π₁ π₂ hπ =>
        apply j (by omega) a₁ a₂ ha i hi π₁ π₂ hπ⟩

private theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat) (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  match m, hm with
  | k + 1, _ => rfl

theorem envRel_shift {k d : Nat} {ρ₁ ρ₂ : CekEnv} (w : CekValue) (h : EnvRel k d ρ₁ ρ₂) :
    RenameEnvRef2 EtaRel (shiftRename 1) id k d (ρ₁.extend w) ρ₂ := by
  intro n hn hnd
  have hsr : shiftRename 1 n = n + 1 := by simp [shiftRename]; omega
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match (ρ₁.extend w).lookup (shiftRename 1 n), ρ₂.lookup n with
       | some v₁, some v₂ => EtaRel k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hsr, extend_lookup_succ ρ₁ w n hn, hl, hr]
  exact hrel

theorem envRel_wellSized {k d : Nat} {ρ₁ ρ₂ : CekEnv} (h : EnvRel k d ρ₁ ρ₂) :
    WellSizedEnv d ρ₂ := by
  intro n hn hnd
  obtain ⟨_, v₂, _, h₂, _⟩ := h n hn hnd
  exact ⟨v₂, h₂⟩

/-- Every term `F` that returns a callable value is refined into by its eta
    expansion, for the eta relation. -/
theorem eta_openRel (d : Nat) (F : Term) (closed : closedAt d F = true)
    (returns : ∀ ρ, WellSizedEnv d ρ → ∃ value, Callable value ∧
      ∀ π, ∃ fuel, steps fuel (.compute π ρ F) = .ret π value) :
    OpenRel d (.Lam 0 (.Apply (renameTerm (shiftRename 1) F) (.Var 1))) F := by
  intro k ρ₁ ρ₂ henv j hj π₁ π₂ hπ
  obtain ⟨value, callable, returns⟩ := returns ρ₂ (envRel_wellSized henv)
  obtain ⟨fuel, returned⟩ := returns π₂
  apply obsRefinesK_right_unsteps (n := fuel)
  rw [returned]
  refine obsRefinesK_left_budget (n := 1) rfl (fun _ h => by cases h) (fun h => by cases h) ?_
  refine ret_obs (etaRel_closure callable ?_) (stackRel_mono (by omega) hπ)
  intro j' hj' a₁ a₂ ha i hi σ₁ σ₂ hσ
  obtain ⟨fuel', returned'⟩ := returns (.arg (.Var 1) (ρ₂.extend a₂) :: σ₂)
  have target : steps (fuel' + 2) (.compute (.arg (.Var 1) (ρ₂.extend a₂) :: σ₂) ρ₂ F) =
      .ret (.funV value :: σ₂) a₂ := by
    rw [steps_trans, returned']
    rfl
  rw [← target]
  apply obsRefinesK_right_steps
  match i with
  | 0 => exact obsRefinesK_zero_compute
  | i + 1 =>
    refine obsRefinesK_left_budget (n := 1) rfl (fun _ h => by cases h) (fun h => by cases h) ?_
    simp only [Nat.add_sub_cancel]
    have shifted := rename_eval (shiftRename 1) id (is0preserving_shiftRename (by omega))
      is0preserving_id d F closed i
      (envRel_shift a₁ (envRel_mono (show i ≤ k by omega) henv))
    rw [Moist.Verified.renameTerm_id] at shifted
    have argument : Eval i (ρ₁.extend a₁) (ρ₂.extend a₂) (.Var 1) (.Var 1) :=
      fundamental 1 (.Var 1) (by simp [closedAt]) i _ _
        (fun n hn hnd => by
          have : n = 1 := by omega
          subst this
          exact ⟨a₁, a₂, rfl, rfl, etaRel_mono (by omega) ha⟩)
    exact shifted i (Nat.le_refl _) _ _ (arg_stackRel argument (stackRel_mono (by omega) hσ))

/-- The local eta rule as a contextual refinement. -/
theorem eta_ctxRefines (d : Nat) (F : Term) (closed : closedAt d F = true)
    (returns : ∀ ρ, WellSizedEnv d ρ → ∃ value, Callable value ∧
      ∀ π, ∃ fuel, steps fuel (.compute π ρ F) = .ret π value) :
    CtxRefines (.Lam 0 (.Apply (renameTerm (shiftRename 1) F) (.Var 1))) F := by
  apply ctxRefines_of_openRel (eta_openRel d F closed returns)
  intro C sourceClosed
  obtain ⟨contextClosed, termClosed⟩ := (fill_closedAt_iff C _ 0).mp sourceClosed
  refine (fill_closedAt_iff C F 0).mpr ⟨contextClosed, ?_⟩
  simp only [closedAt, Bool.and_eq_true] at termClosed
  exact Moist.Verified.closedAt_renameTerm_shiftRename_inv F _ 1 (by omega) (by omega)
    termClosed.1

end Moist.Verified.EtaReduce
