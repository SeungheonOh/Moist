import Moist.Verified.Equivalence
import Moist.Verified.Definitions.StepIndexed

variable [sv : Moist.CEK.SemVariant]

/-! # Guarded step-indexed logical relation

One step-indexed value relation, parameterized by well-formedness predicates
(`Guard`), serves both the plain refinement proofs (`Guard.trivial`, where
every predicate is `True`) and the proofs that track CEK well-formedness
(`TermObsRefinesWF`, `FundamentalRefinesWF`).

Besides the relation itself, this file proves one lemma per CEK stack frame:
each turns a single return step into a relation on stacks (`StackRel`). The
fundamental-property proofs (`term_obsRefinesG`, `renameRefinesG`) are then
one CEK step per term constructor followed by the matching frame lemma.
-/

namespace Moist.Verified.Contextual.Guarded

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified.Equivalence

/-- Well-formedness predicates on values, stacks, environments and states,
    with the closure facts the fundamental proofs use. -/
structure Guard where
  V : CekValue → Prop
  S : Stack → Prop
  E : Nat → CekEnv → Prop
  St : State → Prop
  step : ∀ {s}, St s → St (Moist.CEK.step s)
  ret : ∀ {π v}, St (.ret π v) ↔ S π ∧ V v
  compute : ∀ {π ρ t}, St (.compute π ρ t) → S π
  tail : ∀ {f π}, S (f :: π) → S π
  funV : ∀ {v π}, V v → S π → S (.funV v :: π)
  force : ∀ {π}, S π → S (.force :: π)
  applyArg : ∀ {v π}, S (.applyArg v :: π) → V v
  extend : ∀ {d ρ v}, E d ρ → d ≤ ρ.length → V v → E d (ρ.extend v)

/-- No well-formedness tracking. -/
def Guard.trivial : Guard where
  V _ := True
  S _ := True
  E _ _ := True
  St _ := True
  step _ := True.intro
  ret := ⟨fun _ => ⟨True.intro, True.intro⟩, fun _ => True.intro⟩
  compute _ := True.intro
  tail _ := True.intro
  funV _ _ := True.intro
  force _ := True.intro
  applyArg _ := True.intro
  extend _ _ _ := True.intro

/-! ## The value relation -/

/-- Step-indexed value refinement guarded by `W`. With `W = Guard.trivial` it
    is equivalent to `ValueRefinesK` (`SoundnessRefines.valueRel_trivial`). -/
def ValueRel (W : Guard) : Nat → CekValue → CekValue → Prop
  | 0, .VCon c₁, .VCon c₂ => c₁ = c₂
  | 0, .VLam _ _, .VLam _ _ => True
  | 0, .VDelay _ _, .VDelay _ _ => True
  | 0, .VConstr tag₁ _, .VConstr tag₂ _ => tag₁ = tag₂
  | 0, .VBuiltin b₁ _ exp₁, .VBuiltin b₂ _ exp₂ => b₁ = b₂ ∧ exp₁ = exp₂
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      W.V (.VLam b₁ ρ₁) ∧ W.V (.VLam b₂ ρ₂) ∧
      ∀ j ≤ k, ∀ arg₁ arg₂, ValueRel W j arg₁ arg₂ → W.V arg₁ → W.V arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂, W.S π₁ → W.S π₂ →
          (∀ i' ≤ i, ∀ w₁ w₂, ValueRel W i' w₁ w₂ → W.V w₁ → W.V w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ (ρ₁.extend arg₁) b₁)
                        (.compute π₂ (ρ₂.extend arg₂) b₂)
  | k + 1, .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      ∀ j ≤ k,
        ∀ i ≤ j, ∀ π₁ π₂, W.S π₁ → W.S π₂ →
          (∀ i' ≤ i, ∀ w₁ w₂, ValueRel W i' w₁ w₂ → W.V w₁ → W.V w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ ρ₁ b₁) (.compute π₂ ρ₂ b₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      tag₁ = tag₂ ∧ ListRel (ValueRel W k) fields₁ fields₂
  | k + 1, .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      b₁ = b₂ ∧ exp₁ = exp₂ ∧ ListRel (ValueRel W k) args₁ args₂
  | _, _, _ => False

variable {W : Guard}

private theorem valueRel_mono_le (k : Nat) :
    ∀ j, j ≤ k → ∀ v₁ v₂, ValueRel W k v₁ v₂ → ValueRel W j v₁ v₂ := by
  induction k with
  | zero => intro j hj v₁ v₂ h; cases Nat.le_zero.mp hj; exact h
  | succ k ih =>
    intro j hj v₁ v₂ h
    match j, v₁, v₂ with
    | 0, .VCon _, .VCon _ => simp only [ValueRel] at h ⊢; exact h
    | 0, .VLam _ _, .VLam _ _ | 0, .VDelay _ _, .VDelay _ _ => simp only [ValueRel]
    | 0, .VConstr _ _, .VConstr _ _ => simp only [ValueRel] at h ⊢; exact h.1
    | 0, .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [ValueRel] at h ⊢; exact ⟨h.1, h.2.1⟩
    | j' + 1, .VCon _, .VCon _ => simp only [ValueRel] at h ⊢; exact h
    | j' + 1, .VLam _ _, .VLam _ _ =>
      simp only [ValueRel] at h ⊢
      exact ⟨h.1, h.2.1, fun j₀ hj₀ => h.2.2 j₀ (by omega)⟩
    | j' + 1, .VDelay _ _, .VDelay _ _ =>
      simp only [ValueRel] at h ⊢
      exact fun j₀ hj₀ => h j₀ (by omega)
    | j' + 1, .VConstr _ _, .VConstr _ _ =>
      simp only [ValueRel] at h ⊢
      exact ⟨h.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2⟩
    | j' + 1, .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueRel] at h ⊢
      exact ⟨h.1, h.2.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2.2⟩
    | _, .VCon _, .VLam _ _ | _, .VCon _, .VDelay _ _ | _, .VCon _, .VConstr _ _
    | _, .VCon _, .VBuiltin _ _ _ | _, .VLam _ _, .VCon _ | _, .VLam _ _, .VDelay _ _
    | _, .VLam _ _, .VConstr _ _ | _, .VLam _ _, .VBuiltin _ _ _
    | _, .VDelay _ _, .VCon _ | _, .VDelay _ _, .VLam _ _ | _, .VDelay _ _, .VConstr _ _
    | _, .VDelay _ _, .VBuiltin _ _ _ | _, .VConstr _ _, .VCon _
    | _, .VConstr _ _, .VLam _ _ | _, .VConstr _ _, .VDelay _ _
    | _, .VConstr _ _, .VBuiltin _ _ _ | _, .VBuiltin _ _ _, .VCon _
    | _, .VBuiltin _ _ _, .VLam _ _ | _, .VBuiltin _ _ _, .VDelay _ _
    | _, .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRel] at h

theorem valueRel_mono {j k : Nat} (hjk : j ≤ k) {v₁ v₂ : CekValue}
    (h : ValueRel W k v₁ v₂) : ValueRel W j v₁ v₂ :=
  valueRel_mono_le k j hjk v₁ v₂ h

theorem listRel_valueRel_mono {j k : Nat} (hjk : j ≤ k) {l₁ l₂ : List CekValue}
    (h : ListRel (ValueRel W k) l₁ l₂) : ListRel (ValueRel W j) l₁ l₂ :=
  listRel_mono (fun _ _ h => valueRel_mono hjk h) h

theorem valueRel_vcon_left {k : Nat} {c : Const} {v : CekValue}
    (h : ValueRel W k (.VCon c) v) : v = .VCon c := by
  cases k <;> cases v <;> simp only [ValueRel] at h <;> rw [h]

theorem valueRel_vcon_right {k : Nat} {c : Const} {v : CekValue}
    (h : ValueRel W k v (.VCon c)) : v = .VCon c := by
  cases k <;> cases v <;> simp only [ValueRel] at h <;> rw [h]

theorem valueRel_vcon (k : Nat) (c : Const) : ValueRel W k (.VCon c) (.VCon c) := by
  cases k <;> simp only [ValueRel]

theorem listRel_vcon_refl (k : Nat) :
    ∀ (l : List CekValue), (∀ v ∈ l, ∃ c, v = .VCon c) → ListRel (ValueRel W k) l l
  | [], _ => trivial
  | v :: vs, h => by
    obtain ⟨c, rfl⟩ := h v (.head _)
    exact ⟨valueRel_vcon k c, listRel_vcon_refl k vs fun w hw => h w (.tail _ hw)⟩

theorem valueRel_constr {k tag : Nat} {fs₁ fs₂ : List CekValue}
    (h : ListRel (ValueRel W k) fs₁ fs₂) :
    ValueRel W k (.VConstr tag fs₁) (.VConstr tag fs₂) := by
  cases k with
  | zero => simp only [ValueRel]
  | succ k => simp only [ValueRel]; exact ⟨trivial, listRel_valueRel_mono (by omega) h⟩

theorem valueRel_builtin {k : Nat} {b : BuiltinFun} {ea : ExpectedArgs}
    {args₁ args₂ : List CekValue} (h : ListRel (ValueRel W k) args₁ args₂) :
    ValueRel W k (.VBuiltin b args₁ ea) (.VBuiltin b args₂ ea) := by
  cases k with
  | zero => simp only [ValueRel]; exact ⟨trivial, trivial⟩
  | succ k => simp only [ValueRel]; exact ⟨trivial, trivial, listRel_valueRel_mono (by omega) h⟩

/-! ## Stacks and evaluation -/

/-- Related values returned to the two stacks give related observations. -/
def Fn (W : Guard) (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, ValueRel W j v₁ v₂ → W.V v₁ → W.V v₂ →
    ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂)

def StackRel (W : Guard) (k : Nat) (π₁ π₂ : Stack) : Prop :=
  W.S π₁ ∧ W.S π₂ ∧ Fn W k π₁ π₂

/-- Two terms evaluated in two environments are related on related stacks. -/
def Eval (W : Guard) (k : Nat) (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂, StackRel W j π₁ π₂ →
    W.St (.compute π₁ ρ₁ t₁) → W.St (.compute π₂ ρ₂ t₂) →
    ObsRefinesK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

theorem stackRel_mono {i k : Nat} (hik : i ≤ k) {π₁ π₂ : Stack}
    (h : StackRel W k π₁ π₂) : StackRel W i π₁ π₂ :=
  ⟨h.1, h.2.1, fun j hj => h.2.2 j (Nat.le_trans hj hik)⟩

theorem eval_mono {j k : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv} {t₁ t₂ : Term}
    (h : Eval W k ρ₁ ρ₂ t₁ t₂) : Eval W j ρ₁ ρ₂ t₁ t₂ :=
  fun i hi => h i (Nat.le_trans hi hjk)

theorem stackRel_nil (hnil : W.S []) (k : Nat) : StackRel W k [] [] := by
  refine ⟨hnil, hnil, fun j _ v₁ v₂ _ _ _ => ?_⟩
  cases j with
  | zero => obsRefinesK_zero_nonhalt_auto
  | succ j => obsRefinesK_of_step_auto; exact obsRefinesK_halt_halt j v₁ v₂

/-- Returning related values to related stacks. -/
theorem ret_obs {j : Nat} {π₁ π₂ : Stack} {v₁ v₂ : CekValue} (hv : ValueRel W j v₁ v₂)
    (hst₁ : W.St (.ret π₁ v₁)) (hst₂ : W.St (.ret π₂ v₂)) (hπ : StackRel W j π₁ π₂) :
    ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂) :=
  hπ.2.2 j (Nat.le_refl _) v₁ v₂ hv (W.ret.mp hst₁).2 (W.ret.mp hst₂).2

/-- A closure built from related bodies. -/
theorem valueRel_lam {k : Nat} {b₁ b₂ : Term} {ρ₁ ρ₂ : CekEnv}
    (hv₁ : W.V (.VLam b₁ ρ₁)) (hv₂ : W.V (.VLam b₂ ρ₂))
    (hbody : ∀ j < k, ∀ a₁ a₂, ValueRel W j a₁ a₂ → W.V a₁ → W.V a₂ →
      Eval W j (ρ₁.extend a₁) (ρ₂.extend a₂) b₁ b₂) :
    ValueRel W k (.VLam b₁ ρ₁) (.VLam b₂ ρ₂) := by
  cases k with
  | zero => simp only [ValueRel]
  | succ k =>
    simp only [ValueRel]
    refine ⟨hv₁, hv₂, fun j hj a₁ a₂ ha ha₁ ha₂ i hi π₁ π₂ hs₁ hs₂ hfn => ?_⟩
    exact hbody j (by omega) a₁ a₂ ha ha₁ ha₂ i hi π₁ π₂ ⟨hs₁, hs₂, hfn⟩
      (W.step (W.ret.mpr ⟨W.funV hv₁ hs₁, ha₁⟩)) (W.step (W.ret.mpr ⟨W.funV hv₂ hs₂, ha₂⟩))

/-- A delayed computation built from related bodies. -/
theorem valueRel_delay {k : Nat} {b₁ b₂ : Term} {ρ₁ ρ₂ : CekEnv}
    (hv₁ : W.V (.VDelay b₁ ρ₁)) (hv₂ : W.V (.VDelay b₂ ρ₂))
    (hbody : ∀ j < k, Eval W j ρ₁ ρ₂ b₁ b₂) :
    ValueRel W k (.VDelay b₁ ρ₁) (.VDelay b₂ ρ₂) := by
  cases k with
  | zero => simp only [ValueRel]
  | succ k =>
    simp only [ValueRel]
    intro j hj i hi π₁ π₂ hs₁ hs₂ hfn
    exact hbody j (by omega) i hi π₁ π₂ ⟨hs₁, hs₂, hfn⟩
      (W.step (W.ret.mpr ⟨W.force hs₁, hv₁⟩)) (W.step (W.ret.mpr ⟨W.force hs₂, hv₂⟩))

/-- Evaluate after one CEK step on both sides. -/
theorem eval_of_step {k : Nat} {ρ₁ ρ₂ : CekEnv} {t₁ t₂ : Term}
    (h : ∀ j < k, ∀ π₁ π₂, StackRel W j π₁ π₂ →
      W.St (step (.compute π₁ ρ₁ t₁)) → W.St (step (.compute π₂ ρ₂ t₂)) →
      ObsRefinesK j (step (.compute π₁ ρ₁ t₁)) (step (.compute π₂ ρ₂ t₂))) :
    Eval W k ρ₁ ρ₂ t₁ t₂ := by
  intro j hj π₁ π₂ hπ hst₁ hst₂
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    exact obsRefinesK_of_step_compute
      (h j (by omega) π₁ π₂ (stackRel_mono (by omega) hπ) (W.step hst₁) (W.step hst₂))

/-! ## Environments -/

/-- Related environments on positions `1..d`. -/
def EnvRel (W : Guard) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ ValueRel W k v₁ v₂

/-- Related environments of equal length, related at every position. -/
def AtLeastEnvRel (W : Guard) (k : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ρ₁.length = ρ₂.length ∧
  ∀ n, 0 < n → n ≤ ρ₁.length →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ ValueRel W k v₁ v₂

/-- Open refinement at depth `d`: related environments and stacks give
    related observations. -/
def OpenRel (W : Guard) (d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ k, ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRel W j d ρ₁ ρ₂ →
    W.E d ρ₁ → d ≤ ρ₁.length → W.E d ρ₂ → d ≤ ρ₂.length →
    ∀ i ≤ j, ∀ π₁ π₂, W.S π₁ → W.S π₂ → Fn W i π₁ π₂ →
      ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

theorem atLeastEnvRel_mono {j k : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : AtLeastEnvRel W k ρ₁ ρ₂) : AtLeastEnvRel W j ρ₁ ρ₂ := by
  refine ⟨h.1, fun n hn hlen => ?_⟩
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h.2 n hn hlen
  exact ⟨v₁, v₂, h₁, h₂, valueRel_mono hjk hv⟩

theorem atLeastEnvRel_envRel {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : AtLeastEnvRel W k ρ₁ ρ₂) (hd : d ≤ ρ₁.length) : EnvRel W k d ρ₁ ρ₂ :=
  fun n hn hnd => h.2 n hn (Nat.le_trans hnd hd)

theorem atLeastEnvRel_extend {k : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hρ : AtLeastEnvRel W k ρ₁ ρ₂) (hv : ValueRel W k v₁ v₂) :
    AtLeastEnvRel W k (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  refine ⟨by simp [CekEnv.extend, CekEnv.length, hρ.1], fun n hn hlen => ?_⟩
  match n with
  | 1 => exact ⟨v₁, v₂, rfl, rfl, hv⟩
  | n + 2 =>
    simp only [CekEnv.extend, CekEnv.length] at hlen
    obtain ⟨w₁, w₂, h₁, h₂, hw⟩ := hρ.2 (n + 1) (by omega) (by omega)
    exact ⟨w₁, w₂, h₁, h₂, hw⟩

theorem atLeastEnvRel_lookup {k : Nat} {ρ₁ ρ₂ : CekEnv} (h : AtLeastEnvRel W k ρ₁ ρ₂)
    (n : Nat) : (ρ₁.lookup n = none ∧ ρ₂.lookup n = none) ∨
      ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ ValueRel W k v₁ v₂ := by
  by_cases hn : n = 0
  · subst hn; left; exact ⟨by cases ρ₁ <;> rfl, by cases ρ₂ <;> rfl⟩
  · by_cases hlen : n ≤ ρ₁.length
    · exact .inr (h.2 n (by omega) hlen)
    · exact .inl ⟨CekEnv.lookup_none_of_gt_length ρ₁ n (by omega),
        CekEnv.lookup_none_of_gt_length ρ₂ n (by rw [← h.1]; omega)⟩

/-! ## Builtins -/

theorem evalBuiltin_obs {k : Nat} {b : BuiltinFun} {args₁ args₂ : List CekValue}
    {π₁ π₂ : Stack} (hargs : ListRel (ValueRel W k) args₁ args₂)
    (hst₁ : W.St (match evalBuiltin b args₁ with | some v => .ret π₁ v | none => .error))
    (hst₂ : W.St (match evalBuiltin b args₂ with | some v => .ret π₂ v | none => .error))
    (hπ : StackRel W k π₁ π₂) :
    ObsRefinesK k
      (match evalBuiltin b args₁ with | some v => .ret π₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => .ret π₂ v | none => .error) := by
  have h_rel := evalBuiltin_rel (b := b) valueRel_vcon_left valueRel_vcon_right
    (valueRel_vcon k) hargs
  revert h_rel hst₁ hst₂
  cases evalBuiltin b args₁ <;> cases evalBuiltin b args₂ <;> intro hst₁ hst₂ h_rel
  · exact obsRefinesK_error_error _
  · exact absurd h_rel id
  · exact absurd h_rel id
  · exact ret_obs h_rel hst₁ hst₂ hπ

/-! ## Frame lemmas -/

/-- Applying related functions to related arguments (one `funV` return step). -/
theorem app_obs {k : Nat} {f₁ f₂ a₁ a₂ : CekValue} {π₁ π₂ : Stack}
    (hf : ValueRel W (k + 1) f₁ f₂) (ha : ValueRel W k a₁ a₂)
    (hst₁ : W.St (.ret (.funV f₁ :: π₁) a₁)) (hst₂ : W.St (.ret (.funV f₂ :: π₂) a₂))
    (hπ : StackRel W k π₁ π₂) :
    ObsRefinesK k (step (.ret (.funV f₁ :: π₁) a₁)) (step (.ret (.funV f₂ :: π₂) a₂)) := by
  have hs₁ := W.step hst₁
  have hs₂ := W.step hst₂
  have ha₁ := (W.ret.mp hst₁).2
  have ha₂ := (W.ret.mp hst₂).2
  cases f₁ <;> cases f₂ <;> simp only [ValueRel] at hf
  all_goals first | exact obsRefinesK_error_error k | skip
  · exact hf.2.2 k (Nat.le_refl _) a₁ a₂ ha ha₁ ha₂ k (Nat.le_refl _) π₁ π₂ hπ.1 hπ.2.1 hπ.2.2
  · obtain ⟨rfl, rfl, hargs⟩ := hf
    simp only [step] at hs₁ hs₂ ⊢
    split
    · split
      · rename_i rest _
        simp only [*] at hs₁ hs₂
        exact ret_obs (valueRel_builtin ⟨ha, hargs⟩) hs₁ hs₂ hπ
      · simp only [*] at hs₁ hs₂
        exact evalBuiltin_obs ⟨ha, hargs⟩ hs₁ hs₂ hπ
    · exact obsRefinesK_error_error k

/-- Forcing related values (one `force` return step). -/
theorem force_obs {k : Nat} {v₁ v₂ : CekValue} {π₁ π₂ : Stack}
    (hv : ValueRel W (k + 1) v₁ v₂)
    (hst₁ : W.St (.ret (.force :: π₁) v₁)) (hst₂ : W.St (.ret (.force :: π₂) v₂))
    (hπ : StackRel W k π₁ π₂) :
    ObsRefinesK k (step (.ret (.force :: π₁) v₁)) (step (.ret (.force :: π₂) v₂)) := by
  have hs₁ := W.step hst₁
  have hs₂ := W.step hst₂
  cases v₁ <;> cases v₂ <;> simp only [ValueRel] at hv
  all_goals first | exact obsRefinesK_error_error k | skip
  · exact hv k (Nat.le_refl _) k (Nat.le_refl _) π₁ π₂ hπ.1 hπ.2.1 hπ.2.2
  · obtain ⟨rfl, rfl, hargs⟩ := hv
    simp only [step] at hs₁ hs₂ ⊢
    split
    · split
      · simp only [*] at hs₁ hs₂
        exact ret_obs (valueRel_builtin hargs) hs₁ hs₂ hπ
      · simp only [*] at hs₁ hs₂
        exact evalBuiltin_obs hargs hs₁ hs₂ hπ
    · exact obsRefinesK_error_error k

theorem funV_stackRel {k : Nat} {f₁ f₂ : CekValue} {π₁ π₂ : Stack}
    (hf : ValueRel W k f₁ f₂) (hv₁ : W.V f₁) (hv₂ : W.V f₂) (hπ : StackRel W k π₁ π₂) :
    StackRel W k (.funV f₁ :: π₁) (.funV f₂ :: π₂) := by
  refine ⟨W.funV hv₁ hπ.1, W.funV hv₂ hπ.2.1, fun j hj a₁ a₂ ha ha₁ ha₂ => ?_⟩
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact app_obs (valueRel_mono hj hf) (valueRel_mono (by omega) ha)
      (W.ret.mpr ⟨W.funV hv₁ hπ.1, ha₁⟩) (W.ret.mpr ⟨W.funV hv₂ hπ.2.1, ha₂⟩)
      (stackRel_mono (by omega) hπ)

theorem force_stackRel {k : Nat} {π₁ π₂ : Stack} (hπ : StackRel W k π₁ π₂) :
    StackRel W k (.force :: π₁) (.force :: π₂) := by
  refine ⟨W.force hπ.1, W.force hπ.2.1, fun j hj v₁ v₂ hv hv₁ hv₂ => ?_⟩
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact force_obs hv (W.ret.mpr ⟨W.force hπ.1, hv₁⟩) (W.ret.mpr ⟨W.force hπ.2.1, hv₂⟩)
      (stackRel_mono (by omega) hπ)

/-- The `arg` frame: the argument is evaluated next, then applied. -/
theorem arg_stackRel {k : Nat} {a₁ a₂ : Term} {ρ₁ ρ₂ : CekEnv} {π₁ π₂ : Stack}
    (ha : Eval W k ρ₁ ρ₂ a₁ a₂)
    (hs₁ : W.S (.arg a₁ ρ₁ :: π₁)) (hs₂ : W.S (.arg a₂ ρ₂ :: π₂)) (hπ : StackRel W k π₁ π₂) :
    StackRel W k (.arg a₁ ρ₁ :: π₁) (.arg a₂ ρ₂ :: π₂) := by
  refine ⟨hs₁, hs₂, fun j hj f₁ f₂ hf hf₁ hf₂ => ?_⟩
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    exact ha j (by omega) _ _
      (funV_stackRel (valueRel_mono (by omega) hf) hf₁ hf₂ (stackRel_mono (by omega) hπ))
      (W.step (W.ret.mpr ⟨hs₁, hf₁⟩)) (W.step (W.ret.mpr ⟨hs₂, hf₂⟩))

private theorem step_applyArg (v w : CekValue) (π : Stack) :
    step (.ret (.applyArg v :: π) w) = step (.ret (.funV w :: π) v) := by
  cases w <;> rfl

/-- Pending field arguments of a `Case` alternative. -/
theorem applyArgs_stackRel {k : Nat} : ∀ {fs₁ fs₂ : List CekValue} {π₁ π₂ : Stack},
    ListRel (ValueRel W k) fs₁ fs₂ →
    W.S (fs₁.map Frame.applyArg ++ π₁) → W.S (fs₂.map Frame.applyArg ++ π₂) →
    StackRel W k π₁ π₂ →
    StackRel W k (fs₁.map Frame.applyArg ++ π₁) (fs₂.map Frame.applyArg ++ π₂)
  | [], [], _, _, _, _, _, hπ => hπ
  | [], _ :: _, _, _, h, _, _, _ => absurd h id
  | _ :: _, [], _, _, h, _, _, _ => absurd h id
  | v₁ :: fs₁, v₂ :: fs₂, π₁, π₂, hfs, hs₁, hs₂, hπ => by
    simp only [List.map_cons, List.cons_append] at hs₁ hs₂ ⊢
    have hrest := applyArgs_stackRel hfs.2 (W.tail hs₁) (W.tail hs₂) hπ
    refine ⟨hs₁, hs₂, fun j hj w₁ w₂ hw hw₁ hw₂ => ?_⟩
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
      refine obsRefinesK_of_step_ret ?_
      rw [step_applyArg, step_applyArg]
      exact app_obs hw (valueRel_mono (by omega) hfs.1)
        (W.ret.mpr ⟨W.funV hw₁ (W.tail hs₁), W.applyArg hs₁⟩)
        (W.ret.mpr ⟨W.funV hw₂ (W.tail hs₂), W.applyArg hs₂⟩)
        (stackRel_mono (by omega) hrest)

/-- Alternatives that are related position by position. -/
def AltsRel (W : Guard) (k : Nat) (ρ₁ ρ₂ : CekEnv) (as₁ as₂ : List Term) : Prop :=
  as₁.length = as₂.length ∧
  ∀ n : Nat, (as₁[n]? = none ∧ as₂[n]? = none) ∨
    ∃ a₁ a₂, as₁[n]? = some a₁ ∧ as₂[n]? = some a₂ ∧ Eval W k ρ₁ ρ₂ a₁ a₂

theorem altsRel_of_listRel {k : Nat} {ρ₁ ρ₂ : CekEnv} :
    ∀ {as₁ as₂ : List Term}, ListRel (Eval W k ρ₁ ρ₂) as₁ as₂ → AltsRel W k ρ₁ ρ₂ as₁ as₂
  | [], [], _ => ⟨rfl, fun _ => .inl ⟨rfl, rfl⟩⟩
  | [], _ :: _, h | _ :: _, [], h => absurd h id
  | a₁ :: as₁, a₂ :: as₂, h => by
    have ih := altsRel_of_listRel h.2
    refine ⟨by simp [ih.1], fun n => ?_⟩
    cases n with
    | zero => exact .inr ⟨a₁, a₂, rfl, rfl, h.1⟩
    | succ n => simpa using ih.2 n

/-- The `caseScrutinee` frame: dispatch to related alternatives. -/
theorem case_stackRel {k : Nat} {as₁ as₂ : List Term} {ρ₁ ρ₂ : CekEnv} {π₁ π₂ : Stack}
    (halts : AltsRel W k ρ₁ ρ₂ as₁ as₂)
    (hs₁ : W.S (.caseScrutinee as₁ ρ₁ :: π₁)) (hs₂ : W.S (.caseScrutinee as₂ ρ₂ :: π₂))
    (hπ : StackRel W k π₁ π₂) :
    StackRel W k (.caseScrutinee as₁ ρ₁ :: π₁) (.caseScrutinee as₂ ρ₂ :: π₂) := by
  refine ⟨hs₁, hs₂, fun j hj v₁ v₂ hv hv₁ hv₂ => ?_⟩
  match j with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | j + 1 =>
  refine obsRefinesK_of_step_ret ?_
  have hst₁ := W.step (W.ret.mpr ⟨hs₁, hv₁⟩)
  have hst₂ := W.step (W.ret.mpr ⟨hs₂, hv₂⟩)
  -- Dispatch on the tag with related field lists.
  have dispatch : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue}, ListRel (ValueRel W j) fs₁ fs₂ →
      W.St (match as₁[tag]? with
        | some alt => .compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt | none => .error) →
      W.St (match as₂[tag]? with
        | some alt => .compute (fs₂.map Frame.applyArg ++ π₂) ρ₂ alt | none => .error) →
      ObsRefinesK j
        (match as₁[tag]? with
          | some alt => .compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt | none => .error)
        (match as₂[tag]? with
          | some alt => .compute (fs₂.map Frame.applyArg ++ π₂) ρ₂ alt | none => .error) := by
    intro tag fs₁ fs₂ hfs h₁ h₂
    rcases halts.2 tag with ⟨e₁, e₂⟩ | ⟨a₁, a₂, e₁, e₂, hev⟩
    · rw [e₁, e₂]; exact obsRefinesK_error_error j
    · rw [e₁] at h₁ ⊢; rw [e₂] at h₂ ⊢
      exact hev j (by omega) _ _
        (applyArgs_stackRel hfs (W.compute h₁) (W.compute h₂) (stackRel_mono (by omega) hπ)) h₁ h₂
  cases v₁ <;> cases v₂ <;> simp only [ValueRel] at hv
  all_goals first | exact obsRefinesK_error_error j | skip
  · subst hv
    simp only [step] at hst₁ hst₂ ⊢
    rw [← halts.1] at hst₂ ⊢
    rename_i c
    cases hc : constToTagAndFields c with
    | none => exact obsRefinesK_error_error j
    | some r =>
      obtain ⟨tag, numCtors, fs⟩ := r
      simp only [hc] at hst₁ hst₂ ⊢
      split
      · exact obsRefinesK_error_error j
      · rename_i hcond
        simp only [hcond] at hst₁ hst₂
        have hvcon := constToTagAndFields_fields_vcon c
        rw [hc] at hvcon
        exact dispatch tag (listRel_vcon_refl j fs hvcon) hst₁ hst₂
  · obtain ⟨rfl, hfs⟩ := hv
    simp only [step] at hst₁ hst₂ ⊢
    exact dispatch _ hfs hst₁ hst₂

/-- The `constrField` frame: remaining fields are evaluated in turn. -/
theorem constrField_stackRel {tag : Nat} {ρ₁ ρ₂ : CekEnv} :
    ∀ {k : Nat} {ms₁ ms₂ : List Term} {done₁ done₂ : List CekValue} {π₁ π₂ : Stack},
    ListRel (Eval W k ρ₁ ρ₂) ms₁ ms₂ → ListRel (ValueRel W k) done₁ done₂ →
    W.S (.constrField tag done₁ ms₁ ρ₁ :: π₁) → W.S (.constrField tag done₂ ms₂ ρ₂ :: π₂) →
    StackRel W k π₁ π₂ →
    StackRel W k (.constrField tag done₁ ms₁ ρ₁ :: π₁) (.constrField tag done₂ ms₂ ρ₂ :: π₂)
  | _, [], [], done₁, done₂, π₁, π₂, _, hdone, hs₁, hs₂, hπ => by
    refine ⟨hs₁, hs₂, fun j hj v₁ v₂ hv hv₁ hv₂ => ?_⟩
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    have hst₁ := W.step (W.ret.mpr ⟨hs₁, hv₁⟩)
    have hst₂ := W.step (W.ret.mpr ⟨hs₂, hv₂⟩)
    have hrev : ListRel (ValueRel W j) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append (listRel_reverse (listRel_valueRel_mono (by omega) hdone))
        ⟨valueRel_mono (by omega) hv, trivial⟩
    exact ret_obs (valueRel_constr hrev) hst₁ hst₂ (stackRel_mono (by omega) hπ)
  | _, [], _ :: _, _, _, _, _, h, _, _, _, _ => absurd h id
  | _, _ :: _, [], _, _, _, _, h, _, _, _, _ => absurd h id
  | _, m₁ :: ms₁, m₂ :: ms₂, done₁, done₂, π₁, π₂, hms, hdone, hs₁, hs₂, hπ => by
    refine ⟨hs₁, hs₂, fun j hj v₁ v₂ hv hv₁ hv₂ => ?_⟩
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | j + 1 =>
    refine obsRefinesK_of_step_ret ?_
    have hst₁ := W.step (W.ret.mpr ⟨hs₁, hv₁⟩)
    have hst₂ := W.step (W.ret.mpr ⟨hs₂, hv₂⟩)
    exact hms.1 j (by omega) _ _
      (constrField_stackRel (listRel_mono (fun _ _ h => eval_mono (by omega) h) hms.2)
        ⟨valueRel_mono (by omega) hv, listRel_valueRel_mono (by omega) hdone⟩
        (W.compute hst₁) (W.compute hst₂) (stackRel_mono (by omega) hπ))
      hst₁ hst₂

end Moist.Verified.Contextual.Guarded
