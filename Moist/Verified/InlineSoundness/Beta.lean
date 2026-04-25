import Moist.Verified.SubstRefines
import Moist.Verified.StepWellFormed

/-! # Beta reduction refinement

Core UPLC-level theorem: `Apply (Lam 0 body) rhs` refines
`substTerm 1 rhs body` under conditions that guarantee rhs
evaluates safely and produces well-formed, self-related values.

This module provides:
1. `uplc_beta_refines` — the core stepping + substRefinesR_body composition
2. Helper constructors for `RHaltsRelN` for specific term shapes
-/

namespace Moist.Verified.InlineSoundness.Beta

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun BuiltinType)
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.BetaValueRefines
open Moist.Verified.FundamentalRefines
open Moist.Verified.SubstRefines
open Moist.Verified.StepWellFormed

section Helpers

private theorem envRefinesK_sized_left {j d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvRefinesK j d ρ₁ ρ₂) :
    ∀ n, 0 < n → n ≤ d → ∃ v, ρ₁.lookup n = some v := by
  intro n hn hnd
  obtain ⟨v₁, _, hl₁, _, _⟩ := h n hn hnd
  exact ⟨v₁, hl₁⟩

private theorem envRefinesK_sized_right {j d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvRefinesK j d ρ₁ ρ₂) :
    ∀ n, 0 < n → n ≤ d → ∃ v, ρ₂.lookup n = some v := by
  intro n hn hnd
  obtain ⟨_, v₂, _, hl₂, _⟩ := h n hn hnd
  exact ⟨v₂, hl₂⟩

theorem substEnvRef_of_envRefinesK_extend
    {j d : Nat} {v₁ : CekValue} {ρ₁ ρ₂ : CekEnv}
    (henv : EnvRefinesK j d ρ₁ ρ₂)
    (hvrefl : ValueRefinesK j v₁ v₁) :
    SubstEnvRef 1 v₁ j (d + 1) (ρ₁.extend v₁) ρ₂ := by
  intro n hn hnd
  by_cases h1 : n < 1
  · omega
  · simp only [h1, ite_false]
    by_cases h2 : n = 1
    · simp only [h2, ite_true]
      show match (ρ₁.extend v₁).lookup 1 with
        | some v₁' => ValueRefinesK j v₁' v₁
        | none => False
      rw [extend_lookup_one]
      exact hvrefl
    · simp only [h2, ite_false]
      have hn_gt : n > 1 := by omega
      have hn_ge2 : n ≥ 2 := by omega
      match n, hn_ge2 with
      | m + 2, _ =>
        have hm1 : m + 1 ≥ 1 := by omega
        have hmd : m + 1 ≤ d := by omega
        obtain ⟨u₁, u₂, hl₁, hl₂, hrel⟩ := henv (m + 1) (by omega) hmd
        show match (ρ₁.extend v₁).lookup (m + 2), ρ₂.lookup (m + 2 - 1) with
          | some v₁', some v₂' => ValueRefinesK j v₁' v₂'
          | _, _ => False
        have hlext : (ρ₁.extend v₁).lookup (m + 2) = ρ₁.lookup (m + 1) :=
          extend_lookup_succ ρ₁ v₁ (m + 1) hm1
        rw [hlext, hl₁]
        show match some u₁, ρ₂.lookup (m + 1) with
          | some v₁', some v₂' => ValueRefinesK j v₁' v₂'
          | _, _ => False
        rw [hl₂]
        exact hrel

end Helpers

section BetaStepping

private theorem steps_apply_lam_rhs
    {π : Stack} {ρ : CekEnv} {t_body t_rhs : Term}
    {m : Nat} {v₁ : CekValue}
    (h_rhs : steps m (.compute (Frame.funV (.VLam t_body ρ) :: π) ρ t_rhs)
      = .ret (Frame.funV (.VLam t_body ρ) :: π) v₁) :
    steps (m + 4) (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
      = .compute π (ρ.extend v₁) t_body := by
  have h1 : step (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
    = .compute (.arg t_rhs ρ :: π) ρ (.Lam 0 t_body) := by
    simp [step]
  have h2 : step (.compute (.arg t_rhs ρ :: π) ρ (.Lam 0 t_body))
    = .ret (.arg t_rhs ρ :: π) (.VLam t_body ρ) := by
    simp [step]
  have h3 : step (.ret (.arg t_rhs ρ :: π) (.VLam t_body ρ))
    = .compute (.funV (.VLam t_body ρ) :: π) ρ t_rhs := by
    simp [step]
  have h4 : steps m (.compute (.funV (.VLam t_body ρ) :: π) ρ t_rhs)
    = .ret (.funV (.VLam t_body ρ) :: π) v₁ := h_rhs
  have h5 : step (.ret (.funV (.VLam t_body ρ) :: π) v₁)
    = .compute π (ρ.extend v₁) t_body := by
    simp [step]
  show steps (m + 4) (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
    = .compute π (ρ.extend v₁) t_body
  rw [show m + 4 = 3 + (m + 1) from by omega, steps_trans 3 (m + 1)]
  have h3 : steps 3 (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))
      = .compute (Frame.funV (.VLam t_body ρ) :: π) ρ t_rhs := by
    show steps 2 (step (.compute π ρ (.Apply (.Lam 0 t_body) t_rhs))) = _
    simp only [step]
    show steps 1 (step (.compute (.arg t_rhs ρ :: π) ρ (.Lam 0 t_body))) = _
    simp only [step]
    show step (.ret (.arg t_rhs ρ :: π) (.VLam t_body ρ)) = _
    simp only [step]
  rw [h3, steps_trans m 1, h4]
  show step (.ret (.funV (.VLam t_body ρ) :: π) v₁) = _
  exact h5

/-- Core beta-reduction refinement.

Given:
- `t_body` closed at `d+1`, `t_rhs` closed at `d`
- For each env `ρ₁`, evaluating `t_rhs` produces a value `v₁` that is
  well-formed and serves as the canonical value for `RHaltsRelN`

Conclude: `Apply (Lam 0 t_body) t_rhs` ObsRefines `substTerm 1 t_rhs t_body`
at the open-term level. -/
theorem uplc_beta_refines {d : Nat} {t_body t_rhs : Term} {k : Nat}
    (hclosed : closedAt (d + 1) t_body = true)
    (hrhs_closed : closedAt d t_rhs = true)
    (h_rhalts_maker : ∀ (ρ₁ : CekEnv),
       (∀ n, 0 < n → n ≤ d → ∃ v, ρ₁.lookup n = some v) →
       ∀ (π : Stack), ∃ (m : Nat) (v₁ : CekValue),
         steps m (.compute π ρ₁ t_rhs) = .ret π v₁ ∧
         (∀ k' ≤ m, steps k' (.compute π ρ₁ t_rhs) ≠ .error) ∧
         ValueWellFormed v₁ ∧
         RHaltsRelN t_rhs v₁ k d) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) t_rhs))
          (.compute π₂ ρ₂ (substTerm 1 t_rhs t_body)) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have hρ₁_sized := envRefinesK_sized_left henv
  obtain ⟨m₁, v₁, hsteps_rhs, hnoerr, hvwf, hrhalts⟩ :=
    h_rhalts_maker ρ₁ hρ₁_sized (Frame.funV (.VLam t_body ρ₁) :: π₁)
  have hlhs_steps : steps (m₁ + 4) (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) t_rhs))
      = .compute π₁ (ρ₁.extend v₁) t_body :=
    steps_apply_lam_rhs hsteps_rhs
  apply obsRefinesK_of_steps_left hlhs_steps
  have hvrefl : ValueRefinesK j v₁ v₁ :=
    valueRefinesK_mono hj v₁ v₁ (valueRefinesK_refl k v₁ hvwf)
  have hsubst_env : SubstEnvRef 1 v₁ j (d + 1) (ρ₁.extend v₁) ρ₂ :=
    substEnvRef_of_envRefinesK_extend henv hvrefl
  have hexact : (ρ₁.extend v₁).lookup 1 = some v₁ :=
    extend_lookup_one ρ₁ v₁
  exact substRefinesR_body 1 t_rhs v₁ k d t_body hclosed hrhs_closed
    (by omega) (by omega) hrhalts j hj (ρ₁.extend v₁) ρ₂
    hsubst_env hexact i hi π₁ π₂ hπ

end BetaStepping

section RHaltsConstructors

/-- `RHaltsRelN` for constant terms: evaluation always produces
    the same `VCon c` regardless of env. -/
theorem rHaltsRelN_constant (c : Const) (ty : BuiltinType) (k d : Nat) :
    RHaltsRelN (.Constant (c, ty)) (.VCon c) k d := by
  intro n
  have hiter : iterShift n (.Constant (c, ty)) = .Constant (c, ty) := by
    induction n with
    | zero => rfl
    | succ m ih => simp only [iterShift]; rw [ih]; rfl
  show RHaltsRel (iterShift n (.Constant (c, ty))) (.VCon c) k (d + n)
  rw [hiter]
  intro ρ π hρ_sized
  refine ⟨1, .VCon c, ?_, ?_, ?_⟩
  · show step (.compute π ρ (.Constant (c, ty))) = .ret π (.VCon c)
    simp only [step]
  · intro k' hk'
    match k' with
    | 0 => simp [steps]
    | 1 =>
      show step (.compute π ρ (.Constant (c, ty))) ≠ .error
      simp only [step]; exact State.noConfusion
  · cases k with
    | zero => simp [ValueRefinesK]
    | succ => simp [ValueRefinesK]

/-- `RHaltsRelN` for builtin terms: evaluation always produces
    the same `VBuiltin b [] (expectedArgs b)` regardless of env. -/
theorem rHaltsRelN_builtin (b : BuiltinFun) (k d : Nat) :
    RHaltsRelN (.Builtin b) (.VBuiltin b [] (expectedArgs b)) k d := by
  intro n
  have hiter : iterShift n (.Builtin b) = .Builtin b := by
    induction n with
    | zero => rfl
    | succ m ih => simp only [iterShift]; rw [ih]; rfl
  show RHaltsRel (iterShift n (.Builtin b)) (.VBuiltin b [] (expectedArgs b)) k (d + n)
  rw [hiter]
  intro ρ π hρ_sized
  refine ⟨1, .VBuiltin b [] (expectedArgs b), ?_, ?_, ?_⟩
  · show step (.compute π ρ (.Builtin b)) = .ret π (.VBuiltin b [] (expectedArgs b))
    simp only [step]
  · intro k' hk'
    match k' with
    | 0 => simp [steps]
    | 1 =>
      show step (.compute π ρ (.Builtin b)) ≠ .error
      simp only [step]; exact State.noConfusion
  · cases k with
    | zero => simp [ValueRefinesK]
    | succ k' => simp [ValueRefinesK, ListRel]

end RHaltsConstructors

section ConcreteInstances

/-- Beta refinement for constant rhs: `Apply (Lam 0 body) (Constant c)`
    refines `substTerm 1 (Constant c) body`. -/
theorem uplc_beta_constant {d : Nat} {t_body : Term} {c : Const} {ty : BuiltinType}
    (hclosed : closedAt (d + 1) t_body = true) :
    ∀ k j, j ≤ k → ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) (.Constant (c, ty))))
          (.compute π₂ ρ₂ (substTerm 1 (.Constant (c, ty)) t_body)) := by
  intro k
  apply uplc_beta_refines hclosed (by simp [closedAt])
  intro ρ₁ _ π
  refine ⟨1, .VCon c, ?_, ?_, ?_, ?_⟩
  · show step (.compute π ρ₁ (.Constant (c, ty))) = .ret π (.VCon c)
    simp only [step]
  · intro k' hk'
    match k' with
    | 0 => simp [steps]
    | 1 =>
      show step (.compute π ρ₁ (.Constant (c, ty))) ≠ .error
      simp only [step]; exact State.noConfusion
  · exact ValueWellFormed.vcon c
  · exact rHaltsRelN_constant c ty k d

/-- Beta refinement for builtin rhs. -/
theorem uplc_beta_builtin {d : Nat} {t_body : Term} {b : BuiltinFun}
    (hclosed : closedAt (d + 1) t_body = true) :
    ∀ k j, j ≤ k → ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (.Apply (.Lam 0 t_body) (.Builtin b)))
          (.compute π₂ ρ₂ (substTerm 1 (.Builtin b) t_body)) := by
  intro k
  apply uplc_beta_refines hclosed (by simp [closedAt])
  intro ρ₁ _ π
  refine ⟨1, .VBuiltin b [] (expectedArgs b), ?_, ?_, ?_, ?_⟩
  · show step (.compute π ρ₁ (.Builtin b)) = .ret π (.VBuiltin b [] (expectedArgs b))
    simp only [step]
  · intro k' hk'
    match k' with
    | 0 => simp [steps]
    | 1 =>
      show step (.compute π ρ₁ (.Builtin b)) ≠ .error
      simp only [step]; exact State.noConfusion
  · exact ValueWellFormed.vbuiltin b (expectedArgs b) ValueListWellFormed.nil
  · exact rHaltsRelN_builtin b k d

end ConcreteInstances

end Moist.Verified.InlineSoundness.Beta
