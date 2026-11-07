import Moist.Verified.FundamentalRefines
import Moist.Verified.AdvancedRefinement

/-! # A logical relation for eta reduction

`EtaRel` is the step-indexed value refinement of `Contextual.Guarded.ValueRel`
(without guards) extended by one clause: a closure may be refined by a builtin
state that still expects a value argument, provided that applying the two to
related arguments gives related observations. Forcing, case analysis and
builtin evaluation treat the two shapes alike (forcing and case analysis fail
on both; builtins never inspect non-constant arguments), so every frame lemma
of the original relation still holds.

The file mirrors the original development: frame lemmas, the fundamental
property for renamed terms (`rename_eval`) and for `TermSubstL`-related terms
(`termSubst_eval`), and soundness (`ctxRefines_of_openRel`).
-/

namespace Moist.Verified.EtaReduce

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines (TermSubstL TermListSubstL fill_termSubstL)
open Moist.Verified.FundamentalRefines (Is0Preserving is0preserving_lift RenameEnvRef2
  renameEnvRef2_map renameEnvRef2_extend)

/-! ## The value relation -/

def EtaRel : Nat → CekValue → CekValue → Prop
  | 0, .VCon c₁, .VCon c₂ => c₁ = c₂
  | 0, .VLam _ _, .VLam _ _ => True
  | 0, .VLam _ _, .VBuiltin _ _ exp => exp.head = .argV
  | 0, .VDelay _ _, .VDelay _ _ => True
  | 0, .VConstr tag₁ _, .VConstr tag₂ _ => tag₁ = tag₂
  | 0, .VBuiltin b₁ _ exp₁, .VBuiltin b₂ _ exp₂ => b₁ = b₂ ∧ exp₁ = exp₂
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      ∀ j ≤ k, ∀ arg₁ arg₂, EtaRel j arg₁ arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, EtaRel i' w₁ w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ (ρ₁.extend arg₁) b₁)
                        (.compute π₂ (ρ₂.extend arg₂) b₂)
  | k + 1, .VLam b₁ ρ₁, .VBuiltin b args exp =>
      exp.head = .argV ∧
      ∀ j ≤ k, ∀ arg₁ arg₂, EtaRel j arg₁ arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, EtaRel i' w₁ w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ (ρ₁.extend arg₁) b₁)
                        (.ret (.funV (.VBuiltin b args exp) :: π₂) arg₂)
  | k + 1, .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      ∀ j ≤ k,
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, EtaRel i' w₁ w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ ρ₁ b₁) (.compute π₂ ρ₂ b₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      tag₁ = tag₂ ∧ ListRel (EtaRel k) fields₁ fields₂
  | k + 1, .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      b₁ = b₂ ∧ exp₁ = exp₂ ∧ ListRel (EtaRel k) args₁ args₂
  | _, _, _ => False

private theorem etaRel_mono_le (k : Nat) :
    ∀ j, j ≤ k → ∀ v₁ v₂, EtaRel k v₁ v₂ → EtaRel j v₁ v₂ := by
  induction k with
  | zero => intro j hj v₁ v₂ h; cases Nat.le_zero.mp hj; exact h
  | succ k ih =>
    intro j hj v₁ v₂ h
    cases j with
    | zero =>
      cases v₁ <;> cases v₂ <;> simp only [EtaRel] at h ⊢
      all_goals first | exact h | exact h.1 | exact ⟨h.1, h.2.1⟩
    | succ j =>
      cases v₁ <;> cases v₂ <;> simp only [EtaRel] at h ⊢
      all_goals first
        | exact h
        | exact fun j₀ hj₀ => h j₀ (by omega)
        | exact ⟨h.1, fun j₀ hj₀ => h.2 j₀ (by omega)⟩
        | exact ⟨h.1, listRel_mono (fun a b hab => ih j (by omega) a b hab) h.2⟩
        | exact ⟨h.1, h.2.1, listRel_mono (fun a b hab => ih j (by omega) a b hab) h.2.2⟩

theorem etaRel_mono {j k : Nat} (hjk : j ≤ k) {v₁ v₂ : CekValue}
    (h : EtaRel k v₁ v₂) : EtaRel j v₁ v₂ :=
  etaRel_mono_le k j hjk v₁ v₂ h

theorem listRel_etaRel_mono {j k : Nat} (hjk : j ≤ k) {l₁ l₂ : List CekValue}
    (h : ListRel (EtaRel k) l₁ l₂) : ListRel (EtaRel j) l₁ l₂ :=
  listRel_mono (fun _ _ h => etaRel_mono hjk h) h

theorem etaRel_vcon_left {k : Nat} {c : Const} {v : CekValue}
    (h : EtaRel k (.VCon c) v) : v = .VCon c := by
  cases k <;> cases v <;> simp only [EtaRel] at h <;> rw [h]

theorem etaRel_vcon_right {k : Nat} {c : Const} {v : CekValue}
    (h : EtaRel k v (.VCon c)) : v = .VCon c := by
  cases k <;> cases v <;> simp only [EtaRel] at h <;> rw [h]

theorem etaRel_vcon (k : Nat) (c : Const) : EtaRel k (.VCon c) (.VCon c) := by
  cases k <;> simp only [EtaRel]

theorem listRel_vcon_refl (k : Nat) :
    ∀ (l : List CekValue), (∀ v ∈ l, ∃ c, v = .VCon c) → ListRel (EtaRel k) l l
  | [], _ => trivial
  | v :: vs, h => by
    obtain ⟨c, rfl⟩ := h v (.head _)
    exact ⟨etaRel_vcon k c, listRel_vcon_refl k vs fun w hw => h w (.tail _ hw)⟩

theorem etaRel_constr {k tag : Nat} {fs₁ fs₂ : List CekValue}
    (h : ListRel (EtaRel k) fs₁ fs₂) :
    EtaRel k (.VConstr tag fs₁) (.VConstr tag fs₂) := by
  cases k with
  | zero => simp only [EtaRel]
  | succ k => simp only [EtaRel]; exact ⟨trivial, listRel_etaRel_mono (by omega) h⟩

theorem etaRel_builtin {k : Nat} {b : BuiltinFun} {ea : ExpectedArgs}
    {args₁ args₂ : List CekValue} (h : ListRel (EtaRel k) args₁ args₂) :
    EtaRel k (.VBuiltin b args₁ ea) (.VBuiltin b args₂ ea) := by
  cases k with
  | zero => simp only [EtaRel]; exact ⟨trivial, trivial⟩
  | succ k => simp only [EtaRel]; exact ⟨trivial, trivial, listRel_etaRel_mono (by omega) h⟩

/-! ## Stacks and evaluation -/

/-- Related values returned to the two stacks give related observations. -/
def StackRel (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, EtaRel j v₁ v₂ → ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂)

/-- Two terms evaluated in two environments are related on related stacks. -/
def Eval (k : Nat) (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂, StackRel j π₁ π₂ →
    ObsRefinesK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

theorem stackRel_mono {i k : Nat} (hik : i ≤ k) {π₁ π₂ : Stack}
    (h : StackRel k π₁ π₂) : StackRel i π₁ π₂ :=
  fun j hj => h j (Nat.le_trans hj hik)

theorem eval_mono {j k : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv} {t₁ t₂ : Term}
    (h : Eval k ρ₁ ρ₂ t₁ t₂) : Eval j ρ₁ ρ₂ t₁ t₂ :=
  fun i hi => h i (Nat.le_trans hi hjk)

theorem stackRel_nil (k : Nat) : StackRel k [] [] := by
  intro j _ v₁ v₂ _
  cases j with
  | zero => obsRefinesK_zero_nonhalt_auto
  | succ j => obsRefinesK_of_step_auto; exact obsRefinesK_halt_halt j v₁ v₂

theorem ret_obs {j : Nat} {π₁ π₂ : Stack} {v₁ v₂ : CekValue} (hv : EtaRel j v₁ v₂)
    (hπ : StackRel j π₁ π₂) : ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂) :=
  hπ j (Nat.le_refl _) v₁ v₂ hv

theorem etaRel_lam {k : Nat} {b₁ b₂ : Term} {ρ₁ ρ₂ : CekEnv}
    (hbody : ∀ j < k, ∀ a₁ a₂, EtaRel j a₁ a₂ → Eval j (ρ₁.extend a₁) (ρ₂.extend a₂) b₁ b₂) :
    EtaRel k (.VLam b₁ ρ₁) (.VLam b₂ ρ₂) := by
  cases k with
  | zero => simp only [EtaRel]
  | succ k =>
    simp only [EtaRel]
    intro j hj a₁ a₂ ha i hi π₁ π₂ hπ
    exact hbody j (by omega) a₁ a₂ ha i hi π₁ π₂ hπ

theorem etaRel_delay {k : Nat} {b₁ b₂ : Term} {ρ₁ ρ₂ : CekEnv}
    (hbody : ∀ j < k, Eval j ρ₁ ρ₂ b₁ b₂) :
    EtaRel k (.VDelay b₁ ρ₁) (.VDelay b₂ ρ₂) := by
  cases k with
  | zero => simp only [EtaRel]
  | succ k =>
    simp only [EtaRel]
    intro j hj i hi π₁ π₂ hπ
    exact hbody j (by omega) i hi π₁ π₂ hπ

theorem eval_of_step {k : Nat} {ρ₁ ρ₂ : CekEnv} {t₁ t₂ : Term}
    (h : ∀ j < k, ∀ π₁ π₂, StackRel j π₁ π₂ →
      ObsRefinesK j (step (.compute π₁ ρ₁ t₁)) (step (.compute π₂ ρ₂ t₂))) :
    Eval k ρ₁ ρ₂ t₁ t₂ := by
  intro j hj π₁ π₂ hπ
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    exact obsRefinesK_of_step_compute (h j (by omega) π₁ π₂ (stackRel_mono (by omega) hπ))

/-! ## Observation helpers -/

/-- Running the right state forward or backward does not change what it reaches. -/
theorem obsRefinesK_right_steps {k n : Nat} {s₁ s₂ : State}
    (h : ObsRefinesK k s₁ s₂) : ObsRefinesK k s₁ (steps n s₂) := by
  refine ⟨fun v hv => ?_, fun m hm herr => ?_⟩
  · obtain ⟨v', reaches⟩ := h.1 v hv
    exact ⟨v', (AdvancedRefinement.reaches_after_prefix n rfl).mp reaches⟩
  · exact (AdvancedRefinement.reaches_after_prefix n rfl).mp (h.2 m hm herr)

theorem obsRefinesK_right_unsteps {k n : Nat} {s₁ s₂ : State}
    (h : ObsRefinesK k s₁ (steps n s₂)) : ObsRefinesK k s₁ s₂ :=
  obsRefinesK_of_steps_right rfl h

/-- Left steps to a non-terminal state are paid from the budget. -/
theorem obsRefinesK_left_budget {k n : Nat} {s₁ s₁' s₂ : State}
    (hsteps : steps n s₁ = s₁') (hhalt : ∀ v, s₁' ≠ .halt v) (herror : s₁' ≠ .error)
    (h : ObsRefinesK (k - n) s₁' s₂) : ObsRefinesK k s₁ s₂ := by
  have late : ∀ m, steps m s₁ = s₁' → ∀ final : State, step final = final →
      steps m s₁ = final → n ≤ m ∨ s₁' = final := by
    intro m _ final fixed reach
    by_cases hmn : n ≤ m
    · exact .inl hmn
    · right
      rw [← hsteps, show n = m + (n - m) by omega, steps_trans, reach]
      clear reach hmn
      induction n - m with
      | zero => rfl
      | succ r ih => simp only [steps, fixed]; exact ih
  refine ⟨fun v ⟨m, hm, hs⟩ => ?_, fun m hm hs => ?_⟩
  · by_cases hmn : n ≤ m
    · exact h.1 v ⟨m - n, by omega, by rw [← hsteps, ← steps_trans,
        show n + (m - n) = m by omega]; exact hs⟩
    · exfalso
      have equal : s₁' = .halt v := by
        rw [← hsteps, show n = m + (n - m) by omega, steps_trans, hs, steps_halt]
      exact hhalt v equal
  · by_cases hmn : n ≤ m
    · exact h.2 (m - n) (by omega) (by rw [← hsteps, ← steps_trans,
        show n + (m - n) = m by omega]; exact hs)
    · exfalso
      have equal : s₁' = .error := by
        rw [← hsteps, show n = m + (n - m) by omega, steps_trans, hs, steps_error]
      exact herror equal

/-! ## Environments -/

def EnvRel (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ EtaRel k v₁ v₂

def AtLeastEnvRel (k : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ρ₁.length = ρ₂.length ∧
  ∀ n, 0 < n → n ≤ ρ₁.length →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ EtaRel k v₁ v₂

/-- Open refinement at depth `d` for the eta relation. -/
def OpenRel (d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ k ρ₁ ρ₂, EnvRel k d ρ₁ ρ₂ → Eval k ρ₁ ρ₂ t₁ t₂

theorem envRel_mono {j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : EnvRel k d ρ₁ ρ₂) : EnvRel j d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h n hn hnd
  exact ⟨v₁, v₂, h₁, h₂, etaRel_mono hjk hv⟩

theorem atLeastEnvRel_mono {j k : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : AtLeastEnvRel k ρ₁ ρ₂) : AtLeastEnvRel j ρ₁ ρ₂ := by
  refine ⟨h.1, fun n hn hlen => ?_⟩
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.2 n hn hlen
  exact ⟨v₁, v₂, h₁, h₂, etaRel_mono hjk hv⟩

theorem atLeastEnvRel_envRel {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : AtLeastEnvRel k ρ₁ ρ₂) (hd : d ≤ ρ₁.length) : EnvRel k d ρ₁ ρ₂ :=
  fun n hn hnd => h.2 n hn (Nat.le_trans hnd hd)

theorem atLeastEnvRel_extend {k : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hρ : AtLeastEnvRel k ρ₁ ρ₂) (hv : EtaRel k v₁ v₂) :
    AtLeastEnvRel k (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  refine ⟨by simp [CekEnv.extend, CekEnv.length, hρ.1], fun n hn hlen => ?_⟩
  match n with
  | 1 => exact ⟨v₁, v₂, rfl, rfl, hv⟩
  | n + 2 =>
    simp only [CekEnv.extend, CekEnv.length] at hlen
    obtain ⟨w₁, w₂, h₁, h₂, hw⟩ := hρ.2 (n + 1) (by omega) (by omega)
    exact ⟨w₁, w₂, h₁, h₂, hw⟩

theorem atLeastEnvRel_lookup {k : Nat} {ρ₁ ρ₂ : CekEnv} (h : AtLeastEnvRel k ρ₁ ρ₂)
    (n : Nat) : (ρ₁.lookup n = none ∧ ρ₂.lookup n = none) ∨
      ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ EtaRel k v₁ v₂ := by
  by_cases hn : n = 0
  · subst hn; left; exact ⟨by cases ρ₁ <;> rfl, by cases ρ₂ <;> rfl⟩
  · by_cases hlen : n ≤ ρ₁.length
    · exact .inr (h.2 n (by omega) hlen)
    · exact .inl ⟨CekEnv.lookup_none_of_gt_length ρ₁ n (by omega),
        CekEnv.lookup_none_of_gt_length ρ₂ n (by rw [← h.1]; omega)⟩

/-! ## Builtins -/

theorem evalBuiltin_obs {k : Nat} {b : BuiltinFun} {args₁ args₂ : List CekValue}
    {π₁ π₂ : Stack} (hargs : ListRel (EtaRel k) args₁ args₂) (hπ : StackRel k π₁ π₂) :
    ObsRefinesK k
      (match evalBuiltin b args₁ with | some v => .ret π₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => .ret π₂ v | none => .error) := by
  have h_rel := evalBuiltin_rel (b := b) etaRel_vcon_left etaRel_vcon_right
    (etaRel_vcon k) hargs
  revert h_rel
  cases evalBuiltin b args₁ <;> cases evalBuiltin b args₂ <;> intro h_rel
  · exact obsRefinesK_error_error _
  · exact absurd h_rel id
  · exact absurd h_rel id
  · exact ret_obs h_rel hπ

/-! ## Frame lemmas -/

theorem app_obs {k : Nat} {f₁ f₂ a₁ a₂ : CekValue} {π₁ π₂ : Stack}
    (hf : EtaRel (k + 1) f₁ f₂) (ha : EtaRel k a₁ a₂) (hπ : StackRel k π₁ π₂) :
    ObsRefinesK k (step (.ret (.funV f₁ :: π₁) a₁)) (step (.ret (.funV f₂ :: π₂) a₂)) := by
  cases f₁ <;> cases f₂ <;> simp only [EtaRel] at hf
  all_goals first | exact obsRefinesK_error_error k | skip
  · exact hf k (Nat.le_refl _) a₁ a₂ ha k (Nat.le_refl _) π₁ π₂ hπ
  · exact obsRefinesK_right_steps (n := 1)
      (hf.2 k (Nat.le_refl _) a₁ a₂ ha k (Nat.le_refl _) π₁ π₂ hπ)
  · obtain ⟨rfl, rfl, hargs⟩ := hf
    simp only [step]
    split
    · split
      · exact ret_obs (etaRel_builtin ⟨ha, hargs⟩) hπ
      · exact evalBuiltin_obs ⟨ha, hargs⟩ hπ
    · exact obsRefinesK_error_error k

theorem force_obs {k : Nat} {v₁ v₂ : CekValue} {π₁ π₂ : Stack}
    (hv : EtaRel (k + 1) v₁ v₂) (hπ : StackRel k π₁ π₂) :
    ObsRefinesK k (step (.ret (.force :: π₁) v₁)) (step (.ret (.force :: π₂) v₂)) := by
  cases v₁ <;> cases v₂ <;> simp only [EtaRel] at hv
  all_goals first | exact obsRefinesK_error_error k | skip
  · exact hv k (Nat.le_refl _) k (Nat.le_refl _) π₁ π₂ hπ
  · simp only [step, hv.1]; exact obsRefinesK_error_error k
  · obtain ⟨rfl, rfl, hargs⟩ := hv
    simp only [step]
    split
    · split
      · exact ret_obs (etaRel_builtin hargs) hπ
      · exact evalBuiltin_obs hargs hπ
    · exact obsRefinesK_error_error k

theorem funV_stackRel {k : Nat} {f₁ f₂ : CekValue} {π₁ π₂ : Stack}
    (hf : EtaRel k f₁ f₂) (hπ : StackRel k π₁ π₂) :
    StackRel k (.funV f₁ :: π₁) (.funV f₂ :: π₂) := by
  intro j hj a₁ a₂ ha
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact app_obs (etaRel_mono hj hf) (etaRel_mono (by omega) ha) (stackRel_mono (by omega) hπ)

theorem force_stackRel {k : Nat} {π₁ π₂ : Stack} (hπ : StackRel k π₁ π₂) :
    StackRel k (.force :: π₁) (.force :: π₂) := by
  intro j hj v₁ v₂ hv
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact force_obs hv (stackRel_mono (by omega) hπ)

theorem arg_stackRel {k : Nat} {a₁ a₂ : Term} {ρ₁ ρ₂ : CekEnv} {π₁ π₂ : Stack}
    (ha : Eval k ρ₁ ρ₂ a₁ a₂) (hπ : StackRel k π₁ π₂) :
    StackRel k (.arg a₁ ρ₁ :: π₁) (.arg a₂ ρ₂ :: π₂) := by
  intro j hj f₁ f₂ hf
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact ha j (by omega) _ _
      (funV_stackRel (etaRel_mono (by omega) hf) (stackRel_mono (by omega) hπ))

private theorem step_applyArg (v w : CekValue) (π : Stack) :
    step (.ret (.applyArg v :: π) w) = step (.ret (.funV w :: π) v) := by
  cases w <;> rfl

theorem applyArgs_stackRel {k : Nat} : ∀ {fs₁ fs₂ : List CekValue} {π₁ π₂ : Stack},
    ListRel (EtaRel k) fs₁ fs₂ → StackRel k π₁ π₂ →
    StackRel k (fs₁.map Frame.applyArg ++ π₁) (fs₂.map Frame.applyArg ++ π₂)
  | [], [], _, _, _, hπ => hπ
  | [], _ :: _, _, _, h, _ => absurd h id
  | _ :: _, [], _, _, h, _ => absurd h id
  | v₁ :: fs₁, v₂ :: fs₂, π₁, π₂, hfs, hπ => by
    simp only [List.map_cons, List.cons_append]
    have hrest := applyArgs_stackRel hfs.2 hπ
    intro j hj w₁ w₂ hw
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
      refine obsRefinesK_of_step_ret ?_
      rw [step_applyArg, step_applyArg]
      exact app_obs hw (etaRel_mono (by omega) hfs.1) (stackRel_mono (by omega) hrest)

def AltsRel (k : Nat) (ρ₁ ρ₂ : CekEnv) (as₁ as₂ : List Term) : Prop :=
  as₁.length = as₂.length ∧
  ∀ n : Nat, (as₁[n]? = none ∧ as₂[n]? = none) ∨
    ∃ a₁ a₂, as₁[n]? = some a₁ ∧ as₂[n]? = some a₂ ∧ Eval k ρ₁ ρ₂ a₁ a₂

theorem altsRel_of_listRel {k : Nat} {ρ₁ ρ₂ : CekEnv} :
    ∀ {as₁ as₂ : List Term}, ListRel (Eval k ρ₁ ρ₂) as₁ as₂ → AltsRel k ρ₁ ρ₂ as₁ as₂
  | [], [], _ => ⟨rfl, fun _ => .inl ⟨rfl, rfl⟩⟩
  | [], _ :: _, h | _ :: _, [], h => absurd h id
  | a₁ :: as₁, a₂ :: as₂, h => by
    have ih := altsRel_of_listRel h.2
    refine ⟨by simp [ih.1], fun n => ?_⟩
    cases n with
    | zero => exact .inr ⟨a₁, a₂, rfl, rfl, h.1⟩
    | succ n => simpa using ih.2 n

theorem case_stackRel {k : Nat} {as₁ as₂ : List Term} {ρ₁ ρ₂ : CekEnv} {π₁ π₂ : Stack}
    (halts : AltsRel k ρ₁ ρ₂ as₁ as₂) (hπ : StackRel k π₁ π₂) :
    StackRel k (.caseScrutinee as₁ ρ₁ :: π₁) (.caseScrutinee as₂ ρ₂ :: π₂) := by
  intro j hj v₁ v₂ hv
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
  refine obsRefinesK_of_step_ret ?_
  have dispatch : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue}, ListRel (EtaRel j) fs₁ fs₂ →
      ObsRefinesK j
        (match as₁[tag]? with
          | some alt => .compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt | none => .error)
        (match as₂[tag]? with
          | some alt => .compute (fs₂.map Frame.applyArg ++ π₂) ρ₂ alt | none => .error) := by
    intro tag fs₁ fs₂ hfs
    rcases halts.2 tag with ⟨e₁, e₂⟩ | ⟨a₁, a₂, e₁, e₂, hev⟩
    · rw [e₁, e₂]; exact obsRefinesK_error_error j
    · rw [e₁, e₂]
      exact hev j (by omega) _ _ (applyArgs_stackRel hfs (stackRel_mono (by omega) hπ))
  cases v₁ <;> cases v₂ <;> simp only [EtaRel] at hv
  all_goals first | exact obsRefinesK_error_error j | skip
  · subst hv
    simp only [step]
    rw [← halts.1]
    rename_i c
    cases hc : constToTagAndFields c with
    | none => exact obsRefinesK_error_error j
    | some r =>
      obtain ⟨tag, numCtors, fs⟩ := r
      simp only
      split
      · exact obsRefinesK_error_error j
      · have hvcon := constToTagAndFields_fields_vcon c
        rw [hc] at hvcon
        exact dispatch tag (listRel_vcon_refl j fs hvcon)
  · obtain ⟨rfl, hfs⟩ := hv
    simp only [step]
    exact dispatch _ hfs

theorem constrField_stackRel {tag : Nat} {ρ₁ ρ₂ : CekEnv} :
    ∀ {k : Nat} {ms₁ ms₂ : List Term} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack},
    ListRel (Eval k ρ₁ ρ₂) ms₁ ms₂ → ListRel (EtaRel k) done₁ done₂ →
    StackRel k π₁ π₂ →
    StackRel k (.constrField tag done₁ ms₁ ρ₁ :: π₁) (.constrField tag done₂ ms₂ ρ₂ :: π₂)
  | _, [], [], done₁, done₂, π₁, π₂, _, hdone, hπ => by
    intro j hj v₁ v₂ hv
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    have hrev : ListRel (EtaRel j) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append (listRel_reverse (listRel_etaRel_mono (by omega) hdone))
        ⟨etaRel_mono (by omega) hv, trivial⟩
    exact ret_obs (etaRel_constr hrev) (stackRel_mono (by omega) hπ)
  | _, [], _ :: _, _, _, _, _, h, _, _ => absurd h id
  | _, _ :: _, [], _, _, _, _, h, _, _ => absurd h id
  | _, m₁ :: ms₁, m₂ :: ms₂, done₁, done₂, π₁, π₂, hms, hdone, hπ => by
    intro j hj v₁ v₂ hv
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact hms.1 j (by omega) _ _
      (constrField_stackRel (listRel_mono (fun _ _ h => eval_mono (by omega) h) hms.2)
        ⟨etaRel_mono (by omega) hv, listRel_etaRel_mono (by omega) hdone⟩
        (stackRel_mono (by omega) hπ))

/-! ## Fundamental property for renamed terms -/

private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

mutual

theorem rename_eval (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) (d : Nat) (t : Term) (ht : closedAt d t = true) (k : Nat)
    {ρ₁ ρ₂ : CekEnv} (henv : RenameEnvRef2 EtaRel r₁ r₂ k d ρ₁ ρ₂) :
    Eval k ρ₁ ρ₂ (Moist.Verified.renameTerm r₁ t) (Moist.Verified.renameTerm r₂ t) := by
  have mono : ∀ {j}, j ≤ k → RenameEnvRef2 EtaRel r₁ r₂ j d ρ₁ ρ₂ :=
    fun hj => renameEnvRef2_map (fun _ _ h => etaRel_mono hj h) henv
  match t with
  | .Var n =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht
    by_cases hn : n = 0
    · subst hn
      rw [h₁.1, h₂.1, lookup_zero, lookup_zero]
      exact obsRefinesK_error_error j
    · have h_n := henv n (by omega) ht
      revert h_n
      cases ρ₁.lookup (r₁ n) <;> cases ρ₂.lookup (r₂ n) <;> intro h_n
      · exact obsRefinesK_error_error j
      · exact absurd h_n id
      · exact absurd h_n id
      · exact ret_obs (etaRel_mono (by omega) h_n) hπ
  | .Constant _ =>
    exact eval_of_step fun j _ _ _ hπ => ret_obs (etaRel_vcon j _) hπ
  | .Builtin _ =>
    exact eval_of_step fun j _ _ _ hπ => ret_obs (etaRel_builtin (k := j) trivial) hπ
  | .Error => exact eval_of_step fun j _ _ _ _ => obsRefinesK_error_error j
  | .Lam _ body =>
    simp only [closedAt] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    refine ret_obs (etaRel_lam fun j' hj' a₁ a₂ ha => ?_) hπ
    exact rename_eval _ _ (is0preserving_lift r₁) (is0preserving_lift r₂) (d + 1) body ht j'
      (renameEnvRef2_extend h₁ h₂ (mono (by omega)) ha)
  | .Delay body =>
    simp only [closedAt] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact ret_obs (etaRel_delay
      fun j' hj' => rename_eval r₁ r₂ h₁ h₂ d body ht j' (mono (by omega))) hπ
  | .Apply f x =>
    simp only [closedAt, Bool.and_eq_true] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact rename_eval r₁ r₂ h₁ h₂ d f ht.1 j (mono (by omega)) j (Nat.le_refl _) _ _
      (arg_stackRel (rename_eval r₁ r₂ h₁ h₂ d x ht.2 j (mono (by omega))) hπ)
  | .Force e =>
    simp only [closedAt] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact rename_eval r₁ r₂ h₁ h₂ d e ht j (mono (by omega)) j (Nat.le_refl _) _ _
      (force_stackRel hπ)
  | .Constr tag [] =>
    exact eval_of_step fun j _ _ _ hπ => ret_obs (etaRel_constr (k := j) trivial) hπ
  | .Constr tag (m :: ms) =>
    simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact rename_eval r₁ r₂ h₁ h₂ d m ht.1 j (mono (by omega)) j (Nat.le_refl _) _ _
      (constrField_stackRel (rename_evalList r₁ r₂ h₁ h₂ d ms ht.2 j (mono (by omega)))
        trivial hπ)
  | .Case scrut alts =>
    simp only [closedAt, Bool.and_eq_true] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact rename_eval r₁ r₂ h₁ h₂ d scrut ht.1 j (mono (by omega)) j (Nat.le_refl _) _ _
      (case_stackRel (altsRel_of_listRel
          (rename_evalList r₁ r₂ h₁ h₂ d alts ht.2 j (mono (by omega)))) hπ)
  termination_by sizeOf t

theorem rename_evalList (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) (d : Nat) (ts : List Term) (hts : closedAtList d ts = true)
    (k : Nat) {ρ₁ ρ₂ : CekEnv} (henv : RenameEnvRef2 EtaRel r₁ r₂ k d ρ₁ ρ₂) :
    ListRel (Eval k ρ₁ ρ₂)
      (Moist.Verified.renameTermList r₁ ts) (Moist.Verified.renameTermList r₂ ts) := by
  match ts, hts with
  | [], _ => exact trivial
  | t :: rest, hts =>
    simp only [closedAtList, Bool.and_eq_true] at hts
    exact ⟨rename_eval r₁ r₂ h₁ h₂ d t hts.1 k henv,
      rename_evalList r₁ r₂ h₁ h₂ d rest hts.2 k henv⟩
  termination_by sizeOf ts

end

/-- A closed term refines itself under the eta relation. -/
theorem fundamental (d : Nat) (t : Term) (ht : closedAt d t = true) : OpenRel d t t := by
  intro k ρ₁ ρ₂ henv
  have h := rename_eval id id FundamentalRefines.is0preserving_id
    FundamentalRefines.is0preserving_id d t ht k
    (FundamentalRefines.renameEnvRef2_id henv)
  rwa [Moist.Verified.renameTerm_id] at h

/-! ## Fundamental property for `TermSubstL` and soundness -/

private theorem termListSubstL_listRel {t₁ t₂ : Term} {R : Term → Term → Prop}
    (h : ∀ {a₁ a₂}, TermSubstL t₁ t₂ a₁ a₂ → R a₁ a₂) :
    ∀ {l₁ l₂ : List Term}, TermListSubstL t₁ t₂ l₁ l₂ → ListRel R l₁ l₂
  | _, _, .nil => trivial
  | _, _, .cons hh ht => ⟨h hh, termListSubstL_listRel h ht⟩

theorem termSubst_eval {d : Nat} {t₁ t₂ : Term} (h_open : OpenRel d t₁ t₂) :
    ∀ (k : Nat) {ρ₁ ρ₂ : CekEnv}, AtLeastEnvRel k ρ₁ ρ₂ → d ≤ ρ₁.length →
      ∀ {tm₁ tm₂ : Term}, TermSubstL t₁ t₂ tm₁ tm₂ → Eval k ρ₁ ρ₂ tm₁ tm₂ := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro ρ₁ ρ₂ hρ hd tm₁ tm₂ htm
  have sub : ∀ j < k, ∀ {a₁ a₂}, TermSubstL t₁ t₂ a₁ a₂ → Eval j ρ₁ ρ₂ a₁ a₂ :=
    fun j hj _ _ h => ih j hj (atLeastEnvRel_mono (by omega) hρ) hd h
  cases htm with
  | swap =>
    intro j hj π₁ π₂ hπ
    exact h_open j ρ₁ ρ₂ (atLeastEnvRel_envRel (atLeastEnvRel_mono hj hρ) hd) j
      (Nat.le_refl _) π₁ π₂ hπ
  | varRefl n =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    simp only [step]
    rcases atLeastEnvRel_lookup hρ n with ⟨e₁, e₂⟩ | ⟨v₁, v₂, e₁, e₂, hv⟩
    · rw [e₁, e₂]; exact obsRefinesK_error_error j
    · rw [e₁, e₂]
      exact ret_obs (etaRel_mono (by omega) hv) hπ
  | constRefl c =>
    exact eval_of_step fun j hj π₁ π₂ hπ => ret_obs (etaRel_vcon j c.1) hπ
  | builtinRefl b =>
    exact eval_of_step fun j hj π₁ π₂ hπ => ret_obs (etaRel_builtin (k := j) trivial) hπ
  | errorRefl =>
    exact eval_of_step fun j _ _ _ _ => obsRefinesK_error_error j
  | lam hb =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    refine ret_obs (etaRel_lam ?_) hπ
    intro j' hj' a₁ a₂ ha
    exact ih j' (by omega) (atLeastEnvRel_extend (atLeastEnvRel_mono (by omega) hρ) ha)
      (by simp [CekEnv.extend, CekEnv.length]; omega) hb
  | delay hb =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact ret_obs (etaRel_delay fun j' hj' => sub j' (by omega) hb) hπ
  | apply hf ha =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact sub j hj hf j (Nat.le_refl _) _ _ (arg_stackRel (sub j hj ha) hπ)
  | force he =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact sub j hj he j (Nat.le_refl _) _ _ (force_stackRel hπ)
  | constr hms =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    cases hms with
    | nil => exact ret_obs (etaRel_constr (k := j) trivial) hπ
    | cons hm hms =>
      exact sub j hj hm j (Nat.le_refl _) _ _
        (constrField_stackRel (termListSubstL_listRel (sub j hj) hms) trivial hπ)
  | case hs has =>
    refine eval_of_step fun j hj π₁ π₂ hπ => ?_
    exact sub j hj hs j (Nat.le_refl _) _ _
      (case_stackRel (altsRel_of_listRel (termListSubstL_listRel (sub j hj) has)) hπ)

open Moist.Verified.Contextual.Soundness (dummyEnv dummyEnv_length locality_obsRefinesK)
open Moist.Verified.Contextual.BisimRef (LocalState LocalEnv LocalStack)

theorem atLeastEnvRel_dummyEnv (k : Nat) : ∀ n, AtLeastEnvRel k (dummyEnv n) (dummyEnv n)
  | 0 => ⟨rfl, fun m _ hm => by simp [dummyEnv, CekEnv.length] at hm; omega⟩
  | n + 1 => atLeastEnvRel_extend (atLeastEnvRel_dummyEnv k n) (etaRel_vcon k .Unit)

/-- Open refinement under the eta relation implies contextual refinement. -/
theorem ctxRefines_of_openRel {d : Nat} {t₁ t₂ : Term} (h_open : OpenRel d t₁ t₂)
    (h_close_pres : ∀ (C : Context),
      closedAt 0 (fill C t₁) = true → closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ := by
  intro C h_c1
  have h_c2 := h_close_pres C h_c1
  refine ⟨h_c2, ?_⟩
  have hls₁ : LocalState (.compute [] .nil (fill C t₁)) (.compute [] (dummyEnv d) (fill C t₁)) :=
    LocalState.compute LocalEnv.zero h_c1 LocalStack.nil
  have hls₂ : LocalState (.compute [] .nil (fill C t₂)) (.compute [] (dummyEnv d) (fill C t₂)) :=
    LocalState.compute LocalEnv.zero h_c2 LocalStack.nil
  have h_obs : ∀ n, ObsRefinesK n (.compute [] (dummyEnv d) (fill C t₁))
      (.compute [] (dummyEnv d) (fill C t₂)) := fun n =>
    termSubst_eval h_open n (atLeastEnvRel_dummyEnv n d)
      (by rw [dummyEnv_length]; exact Nat.le_refl _)
      (fill_termSubstL C t₁ t₂) n (Nat.le_refl _) [] [] (stackRel_nil n)
  refine ⟨fun ⟨v, n, hs⟩ => ?_, fun ⟨n, hs⟩ => ?_⟩
  · exact (locality_obsRefinesK n hls₁ hls₂ (h_obs n)).1 v ⟨n, Nat.le_refl _, hs⟩
  · exact (locality_obsRefinesK n hls₁ hls₂ (h_obs n)).2 n (Nat.le_refl _) hs

end Moist.Verified.EtaReduce
