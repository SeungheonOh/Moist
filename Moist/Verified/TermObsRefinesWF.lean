import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.StepWellFormed

/-! # WF-propagating variant of `term_obsRefines`

Defines `ValueRefinesKWF` — a WF-enriched value relation where
VLam/VDelay body clauses explicitly receive `StackWellFormed`.
`term_obsRefinesWF` takes **only** `OpenRefinesWF d t₁ t₂`.
`soundness_refinesWF` derives `CtxRefines` from `OpenRefinesWF` alone.
-/

namespace Moist.Verified.TermObsRefinesWF

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.BetaValueRefines
open Moist.Verified.StepWellFormed (StateWellFormed step_preserves_wf evalBuiltin_preserves_wf)

section ValueRelation

def ValueRefinesKWF : Nat → CekValue → CekValue → Prop
  | 0, .VCon c₁, .VCon c₂ => c₁ = c₂
  | 0, .VLam _ _, .VLam _ _ => True
  | 0, .VDelay _ _, .VDelay _ _ => True
  | 0, .VConstr tag₁ _, .VConstr tag₂ _ => tag₁ = tag₂
  | 0, .VBuiltin b₁ _ exp₁, .VBuiltin b₂ _ exp₂ => b₁ = b₂ ∧ exp₁ = exp₂
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      ValueWellFormed (.VLam b₁ ρ₁) ∧ ValueWellFormed (.VLam b₂ ρ₂) ∧
      ∀ j ≤ k, ∀ arg₁ arg₂, ValueRefinesKWF j arg₁ arg₂ →
        ValueWellFormed arg₁ → ValueWellFormed arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂,
          StackWellFormed π₁ → StackWellFormed π₂ →
          (∀ i' ≤ i, ∀ w₁ w₂, ValueRefinesKWF i' w₁ w₂ →
            ValueWellFormed w₁ → ValueWellFormed w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ (ρ₁.extend arg₁) b₁)
                        (.compute π₂ (ρ₂.extend arg₂) b₂)
  | k + 1, .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      ∀ j ≤ k,
        ∀ i ≤ j, ∀ π₁ π₂,
          StackWellFormed π₁ → StackWellFormed π₂ →
          (∀ i' ≤ i, ∀ w₁ w₂, ValueRefinesKWF i' w₁ w₂ →
            ValueWellFormed w₁ → ValueWellFormed w₂ →
            ObsRefinesK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsRefinesK i (.compute π₁ ρ₁ b₁) (.compute π₂ ρ₂ b₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      tag₁ = tag₂ ∧ ListRel (ValueRefinesKWF k) fields₁ fields₂
  | k + 1, .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      b₁ = b₂ ∧ exp₁ = exp₂ ∧ ListRel (ValueRefinesKWF k) args₁ args₂
  | _, _, _ => False

private theorem valueRefinesKWF_mono_le (k : Nat) :
    ∀ j, j ≤ k → ∀ v₁ v₂, ValueRefinesKWF k v₁ v₂ → ValueRefinesKWF j v₁ v₂ := by
  induction k with
  | zero =>
    intro j hj v₁ v₂ h; cases Nat.le_zero.mp hj; exact h
  | succ k ih =>
    intro j hj v₁ v₂ h
    match j, v₁, v₂ with
    | 0, .VCon _, .VCon _ => simp only [ValueRefinesKWF] at h ⊢; exact h
    | 0, .VLam _ _, .VLam _ _ => simp only [ValueRefinesKWF]
    | 0, .VDelay _ _, .VDelay _ _ => simp only [ValueRefinesKWF]
    | 0, .VConstr _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at h ⊢; exact h.1
    | 0, .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [ValueRefinesKWF] at h ⊢; exact ⟨h.1, h.2.1⟩
    | j' + 1, .VCon _, .VCon _ => simp only [ValueRefinesKWF] at h ⊢; exact h
    | j' + 1, .VLam _ _, .VLam _ _ =>
      simp only [ValueRefinesKWF] at h ⊢
      exact ⟨h.1, h.2.1, fun j₀ hj₀ a₁ a₂ ha ha_wf₁ ha_wf₂ i hi π₁ π₂ hw₁ hw₂ hπ =>
        h.2.2 j₀ (by omega) a₁ a₂ ha ha_wf₁ ha_wf₂ i hi π₁ π₂ hw₁ hw₂ hπ⟩
    | j' + 1, .VDelay _ _, .VDelay _ _ =>
      simp only [ValueRefinesKWF] at h ⊢
      exact fun j₀ hj₀ i hi π₁ π₂ hw₁ hw₂ hπ =>
        h j₀ (by omega) i hi π₁ π₂ hw₁ hw₂ hπ
    | j' + 1, .VConstr _ _, .VConstr _ _ =>
      simp only [ValueRefinesKWF] at h ⊢
      exact ⟨h.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2⟩
    | j' + 1, .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueRefinesKWF] at h ⊢
      exact ⟨h.1, h.2.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2.2⟩
    | _, .VCon _, .VLam _ _ | _, .VCon _, .VDelay _ _ | _, .VCon _, .VConstr _ _
    | _, .VCon _, .VBuiltin _ _ _ | _, .VLam _ _, .VCon _ | _, .VLam _ _, .VDelay _ _
    | _, .VLam _ _, .VConstr _ _ | _, .VLam _ _, .VBuiltin _ _ _
    | _, .VDelay _ _, .VCon _ | _, .VDelay _ _, .VLam _ _ | _, .VDelay _ _, .VConstr _ _
    | _, .VDelay _ _, .VBuiltin _ _ _ | _, .VConstr _ _, .VCon _
    | _, .VConstr _ _, .VLam _ _ | _, .VConstr _ _, .VDelay _ _
    | _, .VConstr _ _, .VBuiltin _ _ _ | _, .VBuiltin _ _ _, .VCon _
    | _, .VBuiltin _ _ _, .VLam _ _ | _, .VBuiltin _ _ _, .VDelay _ _
    | _, .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at h

theorem valueRefinesKWF_mono {j k : Nat} (hjk : j ≤ k)
    (v₁ v₂ : CekValue) (h : ValueRefinesKWF k v₁ v₂) : ValueRefinesKWF j v₁ v₂ :=
  valueRefinesKWF_mono_le k j hjk v₁ v₂ h

private theorem listRel_valueRefinesKWF_mono {j k : Nat} (hjk : j ≤ k)
    {l₁ l₂ : List CekValue} (h : ListRel (ValueRefinesKWF k) l₁ l₂) :
    ListRel (ValueRefinesKWF j) l₁ l₂ :=
  listRel_mono (fun a b h => valueRefinesKWF_mono hjk a b h) h

private theorem valueRefinesKWF_vcon_inv {k : Nat} {c : Const} {v : CekValue}
    (h : ValueRefinesKWF k (.VCon c) v) : v = .VCon c := by
  match k, v with
  | 0, .VCon c' | _ + 1, .VCon c' => simp only [ValueRefinesKWF] at h; cases h; rfl
  | 0, .VLam _ _ | 0, .VDelay _ _ | 0, .VConstr _ _ | 0, .VBuiltin _ _ _
  | _ + 1, .VLam _ _ | _ + 1, .VDelay _ _ | _ + 1, .VConstr _ _ | _ + 1, .VBuiltin _ _ _ =>
    simp only [ValueRefinesKWF] at h

end ValueRelation

section Definitions

def StackFnKWF (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, ValueRefinesKWF j v₁ v₂ →
    ValueWellFormed v₁ → ValueWellFormed v₂ →
    ObsRefinesK j (.ret π₁ v₁) (.ret π₂ v₂)

def StackRefKWF (k : Nat) (π₁ π₂ : Stack) : Prop :=
  StackWellFormed π₁ ∧ StackWellFormed π₂ ∧ StackFnKWF k π₁ π₂

def AtLeastEnvRefinesKWF (k : Nat) (ρ_l ρ_r : CekEnv) : Prop :=
  ρ_l.length = ρ_r.length ∧
  ∀ n, 0 < n → n ≤ ρ_l.length →
    ∃ v_l v_r, ρ_l.lookup n = some v_l ∧ ρ_r.lookup n = some v_r ∧
      ValueRefinesKWF k v_l v_r

def EnvRefinesKWF (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧
      ValueRefinesKWF k v₁ v₂

def BehRefinesKWF (k : Nat) (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂,
    StackWellFormed π₁ → StackWellFormed π₂ → StackFnKWF j π₁ π₂ →
    ObsRefinesK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

def OpenRefinesKWF (k d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesKWF j d ρ₁ ρ₂ →
    EnvWellFormed d ρ₁ → d ≤ ρ₁.length →
    EnvWellFormed d ρ₂ → d ≤ ρ₂.length →
    BehRefinesKWF j ρ₁ ρ₂ t₁ t₂

def OpenRefinesWF (d : Nat) (t₁ t₂ : Term) : Prop := ∀ k, OpenRefinesKWF k d t₁ t₂

theorem atLeastEnvRefinesKWF_mono {j k : Nat} (hjk : j ≤ k) {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvRefinesKWF k ρ_l ρ_r) : AtLeastEnvRefinesKWF j ρ_l ρ_r := by
  refine ⟨h.1, ?_⟩
  intro n hn hnlen
  obtain ⟨v_l, v_r, hl, hr, hrel⟩ := h.2 n hn hnlen
  exact ⟨v_l, v_r, hl, hr, valueRefinesKWF_mono hjk _ _ hrel⟩

theorem atLeastEnvRefinesKWF_to_envRefinesKWF {k d : Nat} {ρ_l ρ_r : CekEnv}
    (h : AtLeastEnvRefinesKWF k ρ_l ρ_r) (hd : d ≤ ρ_l.length) :
    EnvRefinesKWF k d ρ_l ρ_r := by
  intro n hn hnd
  exact h.2 n hn (Nat.le_trans hnd hd)

theorem atLeastEnvRefinesKWF_extend {k : Nat} {ρ_l ρ_r : CekEnv} {v_l v_r : CekValue}
    (hρ : AtLeastEnvRefinesKWF k ρ_l ρ_r) (hv : ValueRefinesKWF k v_l v_r) :
    AtLeastEnvRefinesKWF k (ρ_l.extend v_l) (ρ_r.extend v_r) := by
  refine ⟨?_, ?_⟩
  · simp [CekEnv.extend, CekEnv.length, hρ.1]
  · intro n hn hnlen
    by_cases h1 : n = 1
    · subst h1
      refine ⟨v_l, v_r, ?_, ?_, hv⟩
      · simp [CekEnv.extend, CekEnv.lookup]
      · simp [CekEnv.extend, CekEnv.lookup]
    · have hn2 : n ≥ 2 := by omega
      have hlen_ext : (ρ_l.extend v_l).length = ρ_l.length + 1 := by
        simp [CekEnv.extend, CekEnv.length]
      rw [hlen_ext] at hnlen
      match n, hn2 with
      | n' + 2, _ =>
        obtain ⟨w_l, w_r, hl, hr, hrel⟩ := hρ.2 (n' + 1) (by omega) (by omega)
        refine ⟨w_l, w_r, ?_, ?_, hrel⟩
        · simp [CekEnv.extend, CekEnv.lookup]; exact hl
        · simp [CekEnv.extend, CekEnv.lookup]; exact hr

end Definitions

section Helpers

theorem stackRefKWF_nil (k : Nat) : StackRefKWF k [] [] := by
  refine ⟨StackWellFormed.nil, StackWellFormed.nil, ?_⟩
  intro j _ v_l v_r _ _ _
  cases j with
  | zero => obsRefinesK_zero_nonhalt_auto
  | succ j' =>
    obsRefinesK_of_step_auto; simp only [step]
    exact obsRefinesK_halt j' v_l v_r

theorem stackRefKWF_mono {i k : Nat} (hik : i ≤ k) {π₁ π₂ : Stack}
    (h : StackRefKWF k π₁ π₂) : StackRefKWF i π₁ π₂ :=
  ⟨h.1, h.2.1, fun j hj v₁ v₂ hv hv_wf₁ hv_wf₂ =>
    h.2.2 j (Nat.le_trans hj hik) v₁ v₂ hv hv_wf₁ hv_wf₂⟩

private theorem listRel_refl_vcon_refinesWF (j : Nat) (l : List CekValue)
    (h : ∀ v ∈ l, ∃ c, v = .VCon c) : ListRel (ValueRefinesKWF j) l l := by
  induction l with
  | nil => trivial
  | cons v vs ih =>
    obtain ⟨c, rfl⟩ := h _ (.head _)
    refine ⟨?_, ih (fun w hw => h w (.tail _ hw))⟩
    cases j with | zero => simp only [ValueRefinesKWF] | succ => simp [ValueRefinesKWF]

end Helpers

section EvalBuiltinCompat

private theorem extractConsts_eq_refinesWF {k : Nat} {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueRefinesKWF k) args₁ args₂) :
    extractConsts args₁ = extractConsts args₂ := by
  induction args₁ generalizing args₂ with
  | nil => cases args₂ <;> simp_all [ListRel, extractConsts]
  | cons a₁ as₁ ih =>
    cases args₂ with
    | nil => exact absurd hargs id
    | cons a₂ as₂ =>
      obtain ⟨ha, has⟩ := hargs
      match a₁, a₂ with
      | .VCon c₁, .VCon c₂ =>
        have : c₁ = c₂ := by cases k <;> (simp only [ValueRefinesKWF] at ha; exact ha)
        subst this; simp only [extractConsts]; rw [ih has]
      | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
      | .VConstr _ _, .VConstr _ _ | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
        simp [extractConsts]
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at ha

private theorem listRel_cons_inv_wf {R : α → α → Prop} {a : α} {as : List α} {l₂ : List α}
    (h : ListRel R (a :: as) l₂) : ∃ b bs, l₂ = b :: bs ∧ R a b ∧ ListRel R as bs := by
  cases l₂ with
  | nil => exact absurd h id
  | cons b bs => exact ⟨b, bs, rfl, h.1, h.2⟩

private theorem listRel_nil_inv_wf {R : α → α → Prop} {l₂ : List α}
    (h : ListRel R ([] : List α) l₂) : l₂ = [] := by
  cases l₂ with | nil => rfl | cons => exact absurd h id

private theorem valueRefinesKWF_vcon_eq {k : Nat} {c₁ c₂ : Const}
    (h : ValueRefinesKWF k (.VCon c₁) (.VCon c₂)) : c₁ = c₂ := by
  cases k <;> (simp only [ValueRefinesKWF] at h; exact h)

set_option maxHeartbeats 6400000 in
private theorem evalBuiltinPassThrough_compat_refinesWF {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueRefinesKWF k) args₁ args₂) :
    match evalBuiltinPassThrough b args₁, evalBuiltinPassThrough b args₂ with
    | some v₁, some v₂ => ValueRefinesKWF k v₁ v₂
    | none, none => True
    | _, _ => False := by
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                 b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · -- IfThenElse
      cases args₁ with
      | nil => rw [listRel_nil_inv_wf hargs]; simp [evalBuiltinPassThrough]
      | cons e₁ r₁ =>
      obtain ⟨e₂, r₂, rfl, he, hr⟩ := listRel_cons_inv_wf hargs; cases r₁ with
      | nil => rw [listRel_nil_inv_wf hr]; simp [evalBuiltinPassThrough]
      | cons t₁ s₁ =>
      obtain ⟨t₂, s₂, rfl, ht, hs⟩ := listRel_cons_inv_wf hr; cases s₁ with
      | nil => rw [listRel_nil_inv_wf hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv_wf hs
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesKWF_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv_wf hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 rename_i bv; cases bv <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesKWF] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv_wf hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hu; simp [evalBuiltinPassThrough]
    · -- ChooseUnit
      cases args₁ with
      | nil => rw [listRel_nil_inv_wf hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv_wf hargs; cases s₁ with
      | nil => rw [listRel_nil_inv_wf hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv_wf hs
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesKWF_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv_wf hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesKWF] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv_wf hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hu; simp [evalBuiltinPassThrough]
    · -- Trace
      cases args₁ with
      | nil => rw [listRel_nil_inv_wf hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv_wf hargs; cases s₁ with
      | nil => rw [listRel_nil_inv_wf hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv_wf hs
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesKWF_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv_wf hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesKWF] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv_wf hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hu; simp [evalBuiltinPassThrough]
    · -- ChooseData
      cases args₁ with
      | nil => rw [listRel_nil_inv_wf hargs]; simp [evalBuiltinPassThrough]
      | cons a₁ r₁ =>
      obtain ⟨a₂, r₂, rfl, ha, hr⟩ := listRel_cons_inv_wf hargs; cases r₁ with
      | nil => rw [listRel_nil_inv_wf hr]; simp [evalBuiltinPassThrough]
      | cons b₁ s₁ =>
      obtain ⟨b₂, s₂, rfl, hb, hs⟩ := listRel_cons_inv_wf hr; cases s₁ with
      | nil => rw [listRel_nil_inv_wf hs]; simp [evalBuiltinPassThrough]
      | cons c₁ t₁ =>
      obtain ⟨c₂, t₂, rfl, hc_val, ht⟩ := listRel_cons_inv_wf hs; cases t₁ with
      | nil => rw [listRel_nil_inv_wf ht]; simp [evalBuiltinPassThrough]
      | cons d₁ u₁ =>
      obtain ⟨d₂, u₂, rfl, hd, hu⟩ := listRel_cons_inv_wf ht; cases u₁ with
      | nil => rw [listRel_nil_inv_wf hu]; simp [evalBuiltinPassThrough]
      | cons e₁ w₁ =>
      obtain ⟨e₂, w₂, rfl, he_val, hw⟩ := listRel_cons_inv_wf hu
      cases w₁ with
      | nil => rw [listRel_nil_inv_wf hw]; simp [evalBuiltinPassThrough]
      | cons f₁ x₁ =>
      obtain ⟨f₂, x₂, rfl, hf, hx⟩ := listRel_cons_inv_wf hw
      match f₁ with
      | .VCon c_const =>
        rw [valueRefinesKWF_vcon_inv hf]
        cases x₁ with
        | nil => rw [listRel_nil_inv_wf hx]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 rename_i dat; cases dat <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hx
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match f₂ with
        | .VCon _ => simp only [ValueRefinesKWF] at hf
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases x₁ with
          | nil => rw [listRel_nil_inv_wf hx]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hx; simp [evalBuiltinPassThrough]
    · -- ChooseList
      cases args₁ with
      | nil => rw [listRel_nil_inv_wf hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv_wf hargs; cases s₁ with
      | nil => rw [listRel_nil_inv_wf hs]; simp [evalBuiltinPassThrough]
      | cons t₁ u₁ =>
      obtain ⟨t₂, u₂, rfl, ht, hu⟩ := listRel_cons_inv_wf hs; cases u₁ with
      | nil => rw [listRel_nil_inv_wf hu]; simp [evalBuiltinPassThrough]
      | cons c₁ w₁ =>
      obtain ⟨c₂, w₂, rfl, hc, hw⟩ := listRel_cons_inv_wf hu
      match c₁ with
      | .VCon c_const =>
        rw [valueRefinesKWF_vcon_inv hc]
        cases w₁ with
        | nil => rw [listRel_nil_inv_wf hw]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 all_goals (split <;> assumption)
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hw
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueRefinesKWF] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases w₁ with
          | nil => rw [listRel_nil_inv_wf hw]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hw; simp [evalBuiltinPassThrough]
    · -- MkCons
      cases args₁ with
      | nil => rw [listRel_nil_inv_wf hargs]; simp [evalBuiltinPassThrough]
      | cons a₁ r₁ =>
      obtain ⟨a₂, r₂, rfl, ha, hr⟩ := listRel_cons_inv_wf hargs; cases r₁ with
      | nil => rw [listRel_nil_inv_wf hr]; simp [evalBuiltinPassThrough]
      | cons b₁ s₁ =>
      obtain ⟨b₂, s₂, rfl, hb, hs⟩ := listRel_cons_inv_wf hr
      cases s₁ with
      | cons _ _ =>
        obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv_wf hs; simp [evalBuiltinPassThrough]
      | nil =>
      rw [listRel_nil_inv_wf hs]
      match a₁ with
      | .VCon c_const =>
        rw [valueRefinesKWF_vcon_inv ha]
        cases c_const <;> simp [evalBuiltinPassThrough]
        rename_i tail₁
        match b₁, b₂ with
        | .VCon c₁, .VCon c₂ =>
          have hbeq := valueRefinesKWF_vcon_eq hb; subst hbeq
          cases k <;> simp [ValueRefinesKWF]
        | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
        | .VConstr _ _, .VConstr _ _ | .VBuiltin _ _ _, .VBuiltin _ _ _ => trivial
        | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _
        | .VCon _, .VConstr _ _ | .VCon _, .VBuiltin _ _ _
        | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
        | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
        | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _
        | .VDelay _ _, .VConstr _ _ | .VDelay _ _, .VBuiltin _ _ _
        | .VConstr _ _, .VCon _ | .VConstr _ _, .VLam _ _
        | .VConstr _ _, .VDelay _ _ | .VConstr _ _, .VBuiltin _ _ _
        | .VBuiltin _ _ _, .VCon _ | .VBuiltin _ _ _, .VLam _ _
        | .VBuiltin _ _ _, .VDelay _ _ | .VBuiltin _ _ _, .VConstr _ _ =>
          simp only [ValueRefinesKWF] at hb
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match a₂ with
        | .VCon _ => simp only [ValueRefinesKWF] at ha
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          simp [evalBuiltinPassThrough]
  · have hb_not : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                   b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons :=
      ⟨fun h => hb (h ▸ .inl rfl), fun h => hb (h ▸ .inr (.inl rfl)),
       fun h => hb (h ▸ .inr (.inr (.inl rfl))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inl rfl)))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inl rfl))))),
       fun h => hb (h ▸ .inr (.inr (.inr (.inr (.inr rfl)))))⟩
    rw [evalBuiltinPassThrough_none_of_not_passthrough b args₁ hb_not,
        evalBuiltinPassThrough_none_of_not_passthrough b args₂ hb_not]; trivial

private theorem evalBuiltin_rel_WF {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueRefinesKWF k) args₁ args₂) :
    match evalBuiltin b args₁, evalBuiltin b args₂ with
    | some v₁, some v₂ => ValueRefinesKWF k v₁ v₂
    | none, none => True
    | _, _ => False := by
  have h_ext := extractConsts_eq_refinesWF hargs
  have h_pt := evalBuiltinPassThrough_compat_refinesWF (b := b) hargs
  simp only [evalBuiltin]
  revert h_pt
  cases evalBuiltinPassThrough b args₁ <;> cases evalBuiltinPassThrough b args₂ <;> intro h_pt
  · rw [h_ext]; simp only []
    cases extractConsts args₂ with
    | none => simp
    | some consts =>
      simp only []
      cases evalBuiltinConst b consts with
      | none => simp
      | some c => cases k <;> simp [ValueRefinesKWF]
  · exact absurd h_pt id
  · exact absurd h_pt id
  · exact h_pt

theorem evalBuiltin_compat_refinesWF {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue} {π₁ π₂ : Stack}
    (hargs : ListRel (ValueRefinesKWF k) args₁ args₂)
    (hπ : StackRefKWF k π₁ π₂)
    (hwf_args₁ : ValueListWellFormed args₁)
    (hwf_args₂ : ValueListWellFormed args₂) :
    ObsRefinesK k
      (match evalBuiltin b args₁ with | some v => State.ret π₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => State.ret π₂ v | none => .error) := by
  have h_rel := evalBuiltin_rel_WF (b := b) hargs
  revert h_rel
  cases heb₁ : evalBuiltin b args₁ <;> cases heb₂ : evalBuiltin b args₂ <;> intro h_rel
  · exact obsRefinesK_error _
  · exact absurd h_rel id
  · exact absurd h_rel id
  · match k with
    | 0 => exact obsRefinesK_zero_ret
    | m + 1 =>
      exact hπ.2.2 (m+1) (Nat.le_refl _) _ _ h_rel
        (evalBuiltin_preserves_wf heb₁ hwf_args₁)
        (evalBuiltin_preserves_wf heb₂ hwf_args₂)

end EvalBuiltinCompat

section MainTheorem

private theorem stackWellFormed_applyArgFrames_wf {fields : List CekValue} {π : Stack}
    (hfs : ValueListWellFormed fields) (hπ : StackWellFormed π) :
    StackWellFormed (fields.map Frame.applyArg ++ π) := by
  induction fields with
  | nil => simp; exact hπ
  | cons v rest ih =>
    cases hfs with
    | cons hv hrest =>
      simp [List.map, List.cons_append]
      exact StackWellFormed.cons (FrameWellFormed.applyArg hv) (ih hrest)

private theorem constrField_helper_refinesWF {d : Nat} {t₁ t₂ : Term}
    (_h_open_wf : OpenRefinesWF d t₁ t₂)
    {tag : Nat} {k : Nat}
    (ih_te : ∀ i ≤ k, ∀ {ρ_l ρ_r : CekEnv} {π_l π_r : Stack} {tm_l tm_r : Term},
      AtLeastEnvRefinesKWF i ρ_l ρ_r → d ≤ ρ_l.length →
      EnvWellFormed d ρ_l → EnvWellFormed d ρ_r →
      StackRefKWF i π_l π_r →
      StateWellFormed (.compute π_l ρ_l tm_l) →
      StateWellFormed (.compute π_r ρ_r tm_r) →
      TermSubstL t₁ t₂ tm_l tm_r →
      ObsRefinesK i (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r)) :
    ∀ {ms_l ms_r : List Term}, TermListSubstL t₁ t₂ ms_l ms_r →
    ∀ {j : Nat}, j ≤ k →
      ∀ {done_l done_r : List CekValue} {ρ_l ρ_r : CekEnv} {π_l π_r : Stack},
        AtLeastEnvRefinesKWF j ρ_l ρ_r →
        d ≤ ρ_l.length →
        EnvWellFormed d ρ_l → EnvWellFormed d ρ_r →
        ListRel (ValueRefinesKWF j) done_l done_r →
        StackRefKWF j π_l π_r →
        StackWellFormed (.constrField tag done_l ms_l ρ_l :: π_l) →
        StackWellFormed (.constrField tag done_r ms_r ρ_r :: π_r) →
        StackRefKWF j (.constrField tag done_l ms_l ρ_l :: π_l)
                       (.constrField tag done_r ms_r ρ_r :: π_r) := by
  intro ms_l ms_r hms
  induction ms_l generalizing ms_r with
  | nil =>
    cases hms with
    | nil =>
      intro j _ done_l done_r ρ_l ρ_r π_l π_r _ _ henv_wf_l henv_wf_r h_done hπ hwf_stack_l hwf_stack_r
      refine ⟨hwf_stack_l, hwf_stack_r, ?_⟩
      intro j' hj'_j v_l v_r hv hv_wf_l hv_wf_r
      match j' with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | n + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        have hrev : ListRel (ValueRefinesKWF n) ((v_l :: done_l).reverse) ((v_r :: done_r).reverse) := by
          simp only [List.reverse_cons]
          exact listRel_append
            (listRel_reverse
              (listRel_mono (fun a b h => valueRefinesKWF_mono (by omega) a b h) h_done))
            ⟨valueRefinesKWF_mono (by omega) v_l v_r hv, trivial⟩
        have hval : ValueRefinesKWF (n + 1)
            (.VConstr tag ((v_l :: done_l).reverse))
            (.VConstr tag ((v_r :: done_r).reverse)) := by
          cases n with
          | zero => simp only [ValueRefinesKWF]; exact ⟨trivial, hrev⟩
          | succ _ => simp only [ValueRefinesKWF]; exact ⟨trivial, hrev⟩
        have hval_wf_l : ValueWellFormed (.VConstr tag ((v_l :: done_l).reverse)) := by
          have hswf := step_preserves_wf (.ret (.constrField tag done_l [] ρ_l :: π_l) v_l)
            (StateWellFormed.ret hwf_stack_l hv_wf_l)
          simp only [step] at hswf
          cases hswf with | ret _ hv => exact hv
        have hval_wf_r : ValueWellFormed (.VConstr tag ((v_r :: done_r).reverse)) := by
          have hswf := step_preserves_wf (.ret (.constrField tag done_r [] ρ_r :: π_r) v_r)
            (StateWellFormed.ret hwf_stack_r hv_wf_r)
          simp only [step] at hswf
          cases hswf with | ret _ hv => exact hv
        exact obsRefinesK_mono (by omega) (hπ.2.2 (n + 1) (by omega) _ _ hval hval_wf_l hval_wf_r)
  | cons m ms_l_rest ih_ms =>
    cases hms with
    | cons hm hms_rest =>
      rename_i m_r ms_r_rest
      intro j hj_k done_l done_r ρ_l ρ_r π_l π_r hρ hd henv_wf_l henv_wf_r h_done hπ hwf_stack_l hwf_stack_r
      refine ⟨hwf_stack_l, hwf_stack_r, ?_⟩
      intro j' hj'_j v_l v_r hv hv_wf_l hv_wf_r
      match j' with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | n + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        have hswf_step_l := step_preserves_wf (.ret (.constrField tag done_l (m :: ms_l_rest) ρ_l :: π_l) v_l)
          (StateWellFormed.ret hwf_stack_l hv_wf_l)
        simp only [step] at hswf_step_l
        have hswf_step_r := step_preserves_wf (.ret (.constrField tag done_r (m_r :: ms_r_rest) ρ_r :: π_r) v_r)
          (StateWellFormed.ret hwf_stack_r hv_wf_r)
        simp only [step] at hswf_step_r
        have hwf_new_stack_l : StackWellFormed (.constrField tag (v_l :: done_l) ms_l_rest ρ_l :: π_l) := by
          cases hswf_step_l with | compute h _ _ _ => exact h
        have hwf_new_stack_r : StackWellFormed (.constrField tag (v_r :: done_r) ms_r_rest ρ_r :: π_r) := by
          cases hswf_step_r with | compute h _ _ _ => exact h
        apply ih_te n (by omega) (atLeastEnvRefinesKWF_mono (by omega) hρ) hd henv_wf_l henv_wf_r ?_ hswf_step_l hswf_step_r hm
        exact ih_ms hms_rest (by omega : n ≤ k) (atLeastEnvRefinesKWF_mono (by omega) hρ) hd henv_wf_l henv_wf_r
          (show ListRel (ValueRefinesKWF n) (v_l :: done_l) (v_r :: done_r) from
            ⟨valueRefinesKWF_mono (by omega) v_l v_r hv,
             listRel_mono (fun a b h => valueRefinesKWF_mono (by omega) a b h) h_done⟩)
          (stackRefKWF_mono (by omega) hπ)
          hwf_new_stack_l hwf_new_stack_r

theorem applyArgFrames_stackRefKWF {j : Nat}
    {fields₁ fields₂ : List CekValue} {π₁ π₂ : Stack}
    (hfields : ListRel (ValueRefinesKWF j) fields₁ fields₂)
    (hπ : StackRefKWF j π₁ π₂)
    (hwf₁ : ValueListWellFormed fields₁)
    (hwf₂ : ValueListWellFormed fields₂) :
    StackRefKWF j (fields₁.map Frame.applyArg ++ π₁)
                   (fields₂.map Frame.applyArg ++ π₂) := by
  induction fields₁ generalizing fields₂ π₁ π₂ with
  | nil =>
    cases fields₂ with
    | nil => simp; exact hπ
    | cons => exact absurd hfields id
  | cons v₁ vs₁ ih =>
    cases fields₂ with
    | nil => exact absurd hfields id
    | cons v₂ vs₂ =>
    have hv := hfields.1; have hvs := hfields.2
    cases hwf₁ with | cons hv_wf₁ hvs_wf₁ =>
    cases hwf₂ with | cons hv_wf₂ hvs_wf₂ =>
    simp [List.map, List.cons_append]
    have hπ_rest := ih (listRel_valueRefinesKWF_mono (by omega) hvs) (stackRefKWF_mono (by omega) hπ)
      hvs_wf₁ hvs_wf₂
    refine ⟨StackWellFormed.cons (FrameWellFormed.applyArg hv_wf₁) hπ_rest.1,
            StackWellFormed.cons (FrameWellFormed.applyArg hv_wf₂) hπ_rest.2.1, ?_⟩
    intro j' hj' w₁ w₂ hw hw_wf₁ hw_wf₂
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    match w₁, w₂ with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
      simp only [step, ValueRefinesKWF] at hw ⊢
      obtain ⟨_, _, hw_fn⟩ := hw
      exact hw_fn n (by omega) v₁ v₂
        (valueRefinesKWF_mono (by omega) v₁ v₂ hv) hv_wf₁ hv_wf₂
        n (Nat.le_refl _) _ _ hπ_rest.1 hπ_rest.2.1
        (fun i' hi' w₁ w₂ hw' hw'_wf₁ hw'_wf₂ =>
          hπ_rest.2.2 i' (by omega) w₁ w₂ hw' hw'_wf₁ hw'_wf₂)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
      simp only [ValueRefinesKWF] at hw; obtain ⟨rfl, rfl, hargs⟩ := hw; simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesKWF (n + 1)
              (.VBuiltin b₁ (v₁ :: args₁) rest)
              (.VBuiltin b₁ (v₂ :: args₂) rest) := by
            simp only [ValueRefinesKWF]; refine ⟨trivial, trivial, ?_⟩
            exact ⟨valueRefinesKWF_mono (by omega) v₁ v₂ hv,
                   listRel_valueRefinesKWF_mono (by omega) hargs⟩
          have hval_wf₁ : ValueWellFormed (.VBuiltin b₁ (v₁ :: args₁) rest) := by
            cases hw_wf₁ with | vbuiltin _ _ haw => exact .vbuiltin _ _ (.cons hv_wf₁ haw)
          have hval_wf₂ : ValueWellFormed (.VBuiltin b₁ (v₂ :: args₂) rest) := by
            cases hw_wf₂ with | vbuiltin _ _ haw => exact .vbuiltin _ _ (.cons hv_wf₂ haw)
          exact obsRefinesK_mono (by omega)
            (hπ_rest.2.2 (n+1) (by omega) _ _ hval hval_wf₁ hval_wf₂)
        · have hwf_args₁ : ValueListWellFormed (v₁ :: args₁) := by
            cases hw_wf₁ with | vbuiltin _ _ haw => exact .cons hv_wf₁ haw
          have hwf_args₂ : ValueListWellFormed (v₂ :: args₂) := by
            cases hw_wf₂ with | vbuiltin _ _ haw => exact .cons hv_wf₂ haw
          exact evalBuiltin_compat_refinesWF
            ⟨valueRefinesKWF_mono (by omega) v₁ v₂ hv,
             listRel_valueRefinesKWF_mono (by omega) hargs⟩
            (stackRefKWF_mono (by omega) hπ_rest) hwf_args₁ hwf_args₂
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _
    | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at hw

private theorem constToTagAndFields_fields_wf_local (c : Const) :
    match constToTagAndFields c with
    | some (_, _, fields) => ValueListWellFormed fields
    | none => True := by
  have h := constToTagAndFields_fields_vcon c
  cases hc : constToTagAndFields c with
  | none => trivial
  | some val =>
    obtain ⟨tag, numCtors, fields⟩ := val; simp [hc] at h
    exact go fields h
where
  go : (fields : List CekValue) → (∀ v ∈ fields, ∃ c, v = .VCon c) → ValueListWellFormed fields
    | [], _ => .nil
    | v :: rest, h =>
      have ⟨cv, hcv⟩ := h v (.head rest)
      hcv ▸ .cons (.vcon cv) (go rest (fun x hx => h x (.tail v hx)))

set_option maxHeartbeats 800000 in
theorem term_obsRefinesWF {d : Nat} {t₁ t₂ : Term}
    (h_open_wf : OpenRefinesWF d t₁ t₂) :
    ∀ (k : Nat) (i : Nat), i ≤ k →
      ∀ {ρ_l ρ_r : CekEnv} {π_l π_r : Stack} {tm_l tm_r : Term},
        AtLeastEnvRefinesKWF i ρ_l ρ_r →
        d ≤ ρ_l.length →
        EnvWellFormed d ρ_l → EnvWellFormed d ρ_r →
        StackRefKWF i π_l π_r →
        StateWellFormed (.compute π_l ρ_l tm_l) →
        StateWellFormed (.compute π_r ρ_r tm_r) →
        TermSubstL t₁ t₂ tm_l tm_r →
        ObsRefinesK i (.compute π_l ρ_l tm_l) (.compute π_r ρ_r tm_r) := by
  intro k
  induction k with
  | zero =>
    intro i hi; cases Nat.le_zero.mp hi
    intros; obsRefinesK_zero_nonhalt_auto
  | succ m ih =>
    intro i hi
    by_cases hi_m : i ≤ m
    · exact ih i hi_m
    · have hi_eq : i = m + 1 := by omega
      subst hi_eq
      intro hρ hd henv_wf_l henv_wf_r hπ_wf hswf_l hswf_r htm
      rename_i ρ_l ρ_r π_l π_r tm_l tm_r
      have hπ := hπ_wf.2.2
      cases htm with
      | swap =>
        have hlen_r : d ≤ ρ_r.length := by rw [← hρ.1]; exact hd
        exact h_open_wf (m+1) (m+1) (Nat.le_refl _) ρ_l ρ_r
          (atLeastEnvRefinesKWF_to_envRefinesKWF hρ hd)
          henv_wf_l hd henv_wf_r hlen_r
          (m+1) (Nat.le_refl _) π_l π_r
          hπ_wf.1 hπ_wf.2.1 hπ
      | varRefl n =>
        obsRefinesK_of_step_auto
        simp only [step]
        by_cases hn : n = 0
        · subst hn
          have hl : ρ_l.lookup 0 = none := by cases ρ_l <;> rfl
          have hr : ρ_r.lookup 0 = none := by cases ρ_r <;> rfl
          rw [hl, hr]; exact obsRefinesK_error _
        · have hpos : n > 0 := Nat.pos_of_ne_zero hn
          by_cases hnlen : n ≤ ρ_l.length
          · obtain ⟨v_l, v_r, hl, hr, hrel⟩ := hρ.2 n hpos hnlen
            rw [hl, hr]
            have hstep_l : step (.compute π_l ρ_l (.Var n)) = .ret π_l v_l := by simp [step, hl]
            have hvwf_l : ValueWellFormed v_l := by
              have := step_preserves_wf _ hswf_l; rw [hstep_l] at this
              cases this with | ret _ hv => exact hv
            have hstep_r : step (.compute π_r ρ_r (.Var n)) = .ret π_r v_r := by simp [step, hr]
            have hvwf_r : ValueWellFormed v_r := by
              have := step_preserves_wf _ hswf_r; rw [hstep_r] at this
              cases this with | ret _ hv => exact hv
            exact hπ m (Nat.le_succ m) v_l v_r
              (valueRefinesKWF_mono (Nat.le_succ m) v_l v_r hrel) hvwf_l hvwf_r
          · have hl : ρ_l.lookup n = none :=
              CekEnv.lookup_none_of_gt_length ρ_l n (by omega)
            have hnr : n > ρ_r.length := by rw [← hρ.1]; omega
            have hr : ρ_r.lookup n = none :=
              CekEnv.lookup_none_of_gt_length ρ_r n hnr
            rw [hl, hr]; exact obsRefinesK_error _
      | constRefl c =>
        obsRefinesK_of_step_auto
        simp only [step]
        obtain ⟨kc, _⟩ := c
        exact hπ m (Nat.le_succ m) (.VCon kc) (.VCon kc)
          (by cases m <;> simp only [ValueRefinesKWF])
          (.vcon kc) (.vcon kc)
      | builtinRefl b =>
        obsRefinesK_of_step_auto
        simp only [step]
        exact hπ m (Nat.le_succ m) (.VBuiltin b [] (expectedArgs b)) (.VBuiltin b [] (expectedArgs b))
          (by cases m with
              | zero => simp only [ValueRefinesKWF]; exact ⟨trivial, trivial⟩
              | succ _ => simp only [ValueRefinesKWF, ListRel]; exact ⟨trivial, trivial, trivial⟩)
          (.vbuiltin b (expectedArgs b) .nil) (.vbuiltin b (expectedArgs b) .nil)
      | errorRefl =>
        obsRefinesK_of_step_auto; simp only [step]; exact obsRefinesK_error _
      | lam hb =>
        obsRefinesK_of_step_auto
        simp only [step]
        have hstep_wf_l := step_preserves_wf _ hswf_l; simp only [step] at hstep_wf_l
        have hvlam_wf_l := by cases hstep_wf_l with | ret _ hv => exact hv
        have hstep_wf_r := step_preserves_wf _ hswf_r; simp only [step] at hstep_wf_r
        have hvlam_wf_r := by cases hstep_wf_r with | ret _ hv => exact hv
        apply hπ m (Nat.le_succ m) _ _ _ hvlam_wf_l hvlam_wf_r
        match m with
        | 0 => simp only [ValueRefinesKWF]
        | m' + 1 =>
          simp only [ValueRefinesKWF]
          refine ⟨hvlam_wf_l, hvlam_wf_r, ?_⟩
          intro j hj_m' arg_l arg_r harg harg_wf_l harg_wf_r i hi π_l_app π_r_app hwf_l hwf_r hπ_app
          have hswf_body_l := by
            cases hvlam_wf_l with
            | vlam henv_l hlen_l hclosed_l =>
              exact StateWellFormed.compute hwf_l (envWellFormed_extend _ henv_l hlen_l harg_wf_l)
                (by simp [CekEnv.extend, CekEnv.length]; omega) hclosed_l
          have hswf_body_r := by
            cases hvlam_wf_r with
            | vlam henv_r hlen_r hclosed_r =>
              exact StateWellFormed.compute hwf_r (envWellFormed_extend _ henv_r hlen_r harg_wf_r)
                (by simp [CekEnv.extend, CekEnv.length]; omega) hclosed_r
          apply ih i (by omega)
          · apply atLeastEnvRefinesKWF_extend
            · exact atLeastEnvRefinesKWF_mono (by omega) hρ
            · exact valueRefinesKWF_mono hi _ _ harg
          · show d ≤ (ρ_l.extend arg_l).length
            simp [CekEnv.extend, CekEnv.length]; omega
          · exact envWellFormed_narrow _ (envWellFormed_extend _ henv_wf_l hd harg_wf_l) (by omega)
          · have hlen_r : d ≤ ρ_r.length := by rw [← hρ.1]; exact hd
            exact envWellFormed_narrow _ (envWellFormed_extend _ henv_wf_r hlen_r harg_wf_r) (by omega)
          · exact ⟨hwf_l, hwf_r, hπ_app⟩
          · exact hswf_body_l
          · exact hswf_body_r
          · exact hb
      | delay hb =>
        obsRefinesK_of_step_auto
        simp only [step]
        have hvdelay_wf_l := by
          have := step_preserves_wf _ hswf_l; simp only [step] at this
          cases this with | ret _ hv => exact hv
        have hvdelay_wf_r := by
          have := step_preserves_wf _ hswf_r; simp only [step] at this
          cases this with | ret _ hv => exact hv
        apply hπ m (Nat.le_succ m) _ _ _ hvdelay_wf_l hvdelay_wf_r
        match m with
        | 0 => simp only [ValueRefinesKWF]
        | m' + 1 =>
          simp only [ValueRefinesKWF]
          intro j hj_m' i hi π_l_app π_r_app hwf_l hwf_r hπ_app
          have hswf_body_l := by
            cases hvdelay_wf_l with
            | vdelay henv_l hlen_l hclosed_l =>
              exact StateWellFormed.compute hwf_l henv_l hlen_l hclosed_l
          have hswf_body_r := by
            cases hvdelay_wf_r with
            | vdelay henv_r hlen_r hclosed_r =>
              exact StateWellFormed.compute hwf_r henv_r hlen_r hclosed_r
          apply ih i (by omega)
          · exact atLeastEnvRefinesKWF_mono (by omega) hρ
          · exact hd
          · exact henv_wf_l
          · exact henv_wf_r
          · exact ⟨hwf_l, hwf_r, hπ_app⟩
          · exact hswf_body_l
          · exact hswf_body_r
          · exact hb
      | apply hf ha =>
        rename_i f_l f_r a_l a_r
        obsRefinesK_of_step_auto
        simp only [step]
        have hswf_l' := step_preserves_wf _ hswf_l; simp only [step] at hswf_l'
        have hswf_r' := step_preserves_wf _ hswf_r; simp only [step] at hswf_r'
        have hπ_arg : StackRefKWF m
            (Frame.arg a_l ρ_l :: π_l) (Frame.arg a_r ρ_r :: π_r) := by
          have hwf_l' : StackWellFormed (Frame.arg a_l ρ_l :: π_l) := by
            cases hswf_l' with | compute h _ _ _ => exact h
          have hwf_r' : StackWellFormed (Frame.arg a_r ρ_r :: π_r) := by
            cases hswf_r' with | compute h _ _ _ => exact h
          refine ⟨hwf_l', hwf_r', ?_⟩
          intro j hj_m vf_l vf_r hvf hvf_wf_l hvf_wf_r
          match j with
          | 0 => obsRefinesK_zero_nonhalt_auto
          | j' + 1 =>
            obsRefinesK_of_step_auto; simp only [step]
            have hswf_arg_l := step_preserves_wf (.ret (Frame.arg a_l ρ_l :: π_l) vf_l)
              (StateWellFormed.ret hwf_l' hvf_wf_l)
            simp only [step] at hswf_arg_l
            have hswf_arg_r := step_preserves_wf (.ret (Frame.arg a_r ρ_r :: π_r) vf_r)
              (StateWellFormed.ret hwf_r' hvf_wf_r)
            simp only [step] at hswf_arg_r
            have hπ_funv : StackRefKWF j'
                (Frame.funV vf_l :: π_l) (Frame.funV vf_r :: π_r) := by
              refine ⟨StackWellFormed.cons (FrameWellFormed.funV hvf_wf_l) hπ_wf.1,
                      StackWellFormed.cons (FrameWellFormed.funV hvf_wf_r) hπ_wf.2.1, ?_⟩
              intro j'' hj''_j' w_l w_r hw hw_wf_l hw_wf_r
              match j'' with
              | 0 => obsRefinesK_zero_nonhalt_auto
              | j''' + 1 =>
                obsRefinesK_of_step_auto
                match vf_l, vf_r with
                | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
                | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsRefinesK_error _
                | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
                | .VLam b_lv ρ_lv, .VLam b_rv ρ_rv =>
                  simp only [step, ValueRefinesKWF] at hvf ⊢
                  obtain ⟨_, _, hvf_fn⟩ := hvf
                  exact hvf_fn j''' (by omega) w_l w_r
                    (valueRefinesKWF_mono (Nat.le_succ _) _ _ hw) hw_wf_l hw_wf_r
                    j''' (Nat.le_refl _) π_l π_r hπ_wf.1 hπ_wf.2.1
                    (fun i' hi' x_l x_r hx hx_wf_l hx_wf_r =>
                      hπ i' (by omega) x_l x_r hx hx_wf_l hx_wf_r)
                | .VBuiltin b args_l ea, .VBuiltin _ args_r _ =>
                  simp only [ValueRefinesKWF] at hvf
                  obtain ⟨rfl, rfl, hargs_rel⟩ := hvf
                  simp only [step]; split
                  · split
                    · rename_i rest _
                      have hval : ValueRefinesKWF (j''' + 1)
                          (.VBuiltin b (w_l :: args_l) rest)
                          (.VBuiltin b (w_r :: args_r) rest) := by
                        simp only [ValueRefinesKWF]; refine ⟨trivial, trivial, ?_⟩
                        exact ⟨valueRefinesKWF_mono (by omega) w_l w_r hw,
                               listRel_valueRefinesKWF_mono (by omega) hargs_rel⟩
                      have hval_wf_l : ValueWellFormed (.VBuiltin b (w_l :: args_l) rest) := by
                        cases hvf_wf_l with | vbuiltin _ _ ha => exact .vbuiltin _ _ (.cons hw_wf_l ha)
                      have hval_wf_r : ValueWellFormed (.VBuiltin b (w_r :: args_r) rest) := by
                        cases hvf_wf_r with | vbuiltin _ _ ha => exact .vbuiltin _ _ (.cons hw_wf_r ha)
                      exact obsRefinesK_mono (by omega : j''' ≤ j''' + 1)
                        (hπ (j''' + 1) (by omega) _ _ hval hval_wf_l hval_wf_r)
                    · have hwf_args_l : ValueListWellFormed (w_l :: args_l) := by
                        cases hvf_wf_l with | vbuiltin _ _ ha => exact .cons hw_wf_l ha
                      have hwf_args_r : ValueListWellFormed (w_r :: args_r) := by
                        cases hvf_wf_r with | vbuiltin _ _ ha => exact .cons hw_wf_r ha
                      exact evalBuiltin_compat_refinesWF
                        ⟨valueRefinesKWF_mono (by omega) w_l w_r hw,
                         listRel_valueRefinesKWF_mono (by omega) hargs_rel⟩
                        (stackRefKWF_mono (by omega) hπ_wf) hwf_args_l hwf_args_r
                  · exact obsRefinesK_error _
                | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
                | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
                | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
                | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
                | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
                | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
                | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
                | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
                | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at hvf
            apply ih j' (by omega) (atLeastEnvRefinesKWF_mono (by omega) hρ) hd
              henv_wf_l henv_wf_r hπ_funv hswf_arg_l hswf_arg_r ha
        apply ih m (Nat.le_refl m) (atLeastEnvRefinesKWF_mono (Nat.le_succ m) hρ) hd
          henv_wf_l henv_wf_r hπ_arg hswf_l' hswf_r' hf
      | force he =>
        obsRefinesK_of_step_auto
        simp only [step]
        have hswf_l' := step_preserves_wf _ hswf_l; simp only [step] at hswf_l'
        have hswf_r' := step_preserves_wf _ hswf_r; simp only [step] at hswf_r'
        have hπ_force : StackRefKWF m
            (Frame.force :: π_l) (Frame.force :: π_r) := by
          refine ⟨StackWellFormed.cons FrameWellFormed.force hπ_wf.1,
                  StackWellFormed.cons FrameWellFormed.force hπ_wf.2.1, ?_⟩
          intro j hj_m vf_l vf_r hvf hvf_wf_l hvf_wf_r
          match j with
          | 0 => obsRefinesK_zero_nonhalt_auto
          | j' + 1 =>
            obsRefinesK_of_step_auto
            match vf_l, vf_r with
            | .VDelay b_lv ρ_lv, .VDelay b_rv ρ_rv =>
              simp only [step, ValueRefinesKWF] at hvf ⊢
              have hswf_del_l : StateWellFormed (.compute π_l ρ_lv b_lv) := by
                cases hvf_wf_l with
                | vdelay he hl hc => exact StateWellFormed.compute hπ_wf.1 he hl hc
              have hswf_del_r : StateWellFormed (.compute π_r ρ_rv b_rv) := by
                cases hvf_wf_r with
                | vdelay he hl hc => exact StateWellFormed.compute hπ_wf.2.1 he hl hc
              exact hvf j' (Nat.le_refl _) j' (Nat.le_refl _) π_l π_r hπ_wf.1 hπ_wf.2.1
                (fun i' hi' w_l w_r hw' hw'_wf_l hw'_wf_r =>
                  hπ i' (by omega) w_l w_r hw' hw'_wf_l hw'_wf_r)
            | .VBuiltin b args_l ea, .VBuiltin _ args_r _ =>
              simp only [ValueRefinesKWF] at hvf
              obtain ⟨rfl, rfl, hargs_rel⟩ := hvf
              simp only [step]; split
              · split
                · rename_i rest _
                  have hval : ValueRefinesKWF (j' + 1)
                      (.VBuiltin b args_l rest) (.VBuiltin b args_r rest) := by
                    simp only [ValueRefinesKWF]; exact ⟨trivial, trivial, hargs_rel⟩
                  have hval_wf_l : ValueWellFormed (.VBuiltin b args_l rest) := by
                    cases hvf_wf_l with | vbuiltin _ _ ha => exact .vbuiltin _ _ ha
                  have hval_wf_r : ValueWellFormed (.VBuiltin b args_r rest) := by
                    cases hvf_wf_r with | vbuiltin _ _ ha => exact .vbuiltin _ _ ha
                  exact obsRefinesK_mono (by omega : j' ≤ j' + 1)
                    (hπ (j' + 1) (by omega) _ _ hval hval_wf_l hval_wf_r)
                · have hwf_args_l : ValueListWellFormed args_l := by
                    cases hvf_wf_l with | vbuiltin _ _ ha => exact ha
                  have hwf_args_r : ValueListWellFormed args_r := by
                    cases hvf_wf_r with | vbuiltin _ _ ha => exact ha
                  exact evalBuiltin_compat_refinesWF hargs_rel
                    (stackRefKWF_mono (by omega) hπ_wf) hwf_args_l hwf_args_r
              · exact obsRefinesK_error _
            | .VCon _, .VCon _ | .VLam _ _, .VLam _ _ | .VConstr _ _, .VConstr _ _ =>
              simp only [step]; exact obsRefinesK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at hvf
        apply ih m (Nat.le_refl m) (atLeastEnvRefinesKWF_mono (Nat.le_succ m) hρ) hd
          henv_wf_l henv_wf_r hπ_force hswf_l' hswf_r' he
      | constr hms =>
        cases hms with
        | nil =>
          obsRefinesK_of_step_auto
          simp only [step]
          exact hπ m (Nat.le_succ m) (.VConstr _ []) (.VConstr _ [])
            (by cases m with
                | zero => simp only [ValueRefinesKWF]
                | succ _ => simp only [ValueRefinesKWF, ListRel]; exact ⟨trivial, trivial⟩)
            (.vconstr _ .nil) (.vconstr _ .nil)
        | cons hm hms_rest =>
          obsRefinesK_of_step_auto
          simp only [step]
          have hswf_l' := step_preserves_wf _ hswf_l; simp only [step] at hswf_l'
          have hswf_r' := step_preserves_wf _ hswf_r; simp only [step] at hswf_r'
          have hwf_stack_l := by
            cases hswf_l' with | compute h _ _ _ => exact h
          have hwf_stack_r := by
            cases hswf_r' with | compute h _ _ _ => exact h
          apply ih m (Nat.le_refl m) (atLeastEnvRefinesKWF_mono (Nat.le_succ m) hρ) hd
            henv_wf_l henv_wf_r ?_ hswf_l' hswf_r' hm
          exact constrField_helper_refinesWF h_open_wf ih hms_rest (Nat.le_refl m)
            (atLeastEnvRefinesKWF_mono (Nat.le_succ m) hρ) hd henv_wf_l henv_wf_r
            (show ListRel (ValueRefinesKWF m) [] [] from trivial)
            (stackRefKWF_mono (Nat.le_succ m) hπ_wf)
            hwf_stack_l hwf_stack_r
      | case hs has =>
        rename_i as_l as_r
        obsRefinesK_of_step_auto
        simp only [step]
        have hswf_l' := step_preserves_wf _ hswf_l; simp only [step] at hswf_l'
        have hswf_r' := step_preserves_wf _ hswf_r; simp only [step] at hswf_r'
        have hwf_l' : StackWellFormed (Frame.caseScrutinee as_l ρ_l :: π_l) := by
          cases hswf_l' with | compute h _ _ _ => exact h
        have hwf_r' : StackWellFormed (Frame.caseScrutinee as_r ρ_r :: π_r) := by
          cases hswf_r' with | compute h _ _ _ => exact h
        have hπ_case : StackRefKWF m
            (Frame.caseScrutinee as_l ρ_l :: π_l) (Frame.caseScrutinee as_r ρ_r :: π_r) := by
          refine ⟨hwf_l', hwf_r', ?_⟩
          intro j hj_m vf_l vf_r hvf hvf_wf_l hvf_wf_r
          match j with
          | 0 => obsRefinesK_zero_nonhalt_auto
          | j' + 1 =>
            obsRefinesK_of_step_auto
            match vf_l, vf_r with
            | .VConstr tag_l fields_l, .VConstr tag_r fields_r =>
              simp only [step]
              simp only [ValueRefinesKWF] at hvf
              obtain ⟨h_tag, h_fields⟩ := hvf; subst h_tag
              have h_lk := termListSubstL_getElem? has tag_l
              have hwf_fields_l : ValueListWellFormed fields_l := by
                cases hvf_wf_l with | vconstr _ h => exact h
              have hwf_fields_r : ValueListWellFormed fields_r := by
                cases hvf_wf_r with | vconstr _ h => exact h
              cases h_lk with
              | inl h =>
                obtain ⟨hl, hr⟩ := h; rw [hl, hr]; exact obsRefinesK_error _
              | inr h =>
                obtain ⟨alt_l, alt_r, hl, hr, halt⟩ := h; rw [hl, hr]
                have hswf_case_step_l := step_preserves_wf (.ret (Frame.caseScrutinee as_l ρ_l :: π_l) (.VConstr tag_l fields_l))
                  (StateWellFormed.ret hwf_l' hvf_wf_l)
                simp [step, hl] at hswf_case_step_l
                have hswf_case_step_r := step_preserves_wf (.ret (Frame.caseScrutinee as_r ρ_r :: π_r) (.VConstr tag_l fields_r))
                  (StateWellFormed.ret hwf_r' hvf_wf_r)
                simp [step, hr] at hswf_case_step_r
                apply ih j' (by omega) (atLeastEnvRefinesKWF_mono (by omega) hρ) hd
                  henv_wf_l henv_wf_r ?_ hswf_case_step_l hswf_case_step_r halt
                exact applyArgFrames_stackRefKWF h_fields (stackRefKWF_mono (by omega) hπ_wf)
                  hwf_fields_l hwf_fields_r
            | .VCon c_l, .VCon c_r =>
              simp only [ValueRefinesKWF] at hvf; subst hvf; simp only [step]
              have hlen := termListSubstL_length_eq has
              rw [show as_r.length = as_l.length from hlen.symm]
              cases h_const : constToTagAndFields c_l with
              | none => exact obsRefinesK_error _
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple; dsimp only []
                by_cases hcond : (decide (numCtors > 0) && decide (as_l.length > numCtors)) = true
                · rw [if_pos hcond, if_pos hcond]; exact obsRefinesK_error _
                · rw [if_neg hcond, if_neg hcond]
                  have h_lk := termListSubstL_getElem? has tag
                  have hfields_vcon := constToTagAndFields_fields_vcon c_l
                  rw [h_const] at hfields_vcon
                  have hfields_wf : ValueListWellFormed fields := by
                    have := constToTagAndFields_fields_wf_local c_l; rw [h_const] at this; exact this
                  cases h_lk with
                  | inl h =>
                    obtain ⟨hl, hr⟩ := h; rw [hl, hr]; exact obsRefinesK_error _
                  | inr h =>
                    obtain ⟨alt_l, alt_r, hl, hr, halt⟩ := h; rw [hl, hr]
                    have hswf_vcon_step_l := step_preserves_wf (.ret (Frame.caseScrutinee as_l ρ_l :: π_l) (.VCon c_l))
                      (StateWellFormed.ret hwf_l' hvf_wf_l)
                    simp only [step, h_const] at hswf_vcon_step_l
                    rw [if_neg hcond, hl] at hswf_vcon_step_l
                    have hswf_vcon_step_r := step_preserves_wf (.ret (Frame.caseScrutinee as_r ρ_r :: π_r) (.VCon c_l))
                      (StateWellFormed.ret hwf_r' hvf_wf_r)
                    simp only [step, h_const, hlen.symm] at hswf_vcon_step_r
                    rw [if_neg hcond, hr] at hswf_vcon_step_r
                    apply ih j' (by omega) (atLeastEnvRefinesKWF_mono (by omega) hρ) hd
                      henv_wf_l henv_wf_r ?_ hswf_vcon_step_l hswf_vcon_step_r halt
                    exact applyArgFrames_stackRefKWF
                      (listRel_refl_vcon_refinesWF j' fields hfields_vcon)
                      (stackRefKWF_mono (by omega) hπ_wf)
                      hfields_wf hfields_wf
            | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
              simp only [step]; exact obsRefinesK_error _
            | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
            | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
            | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
            | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
            | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
            | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
            | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
            | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
            | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesKWF] at hvf
        apply ih m (Nat.le_refl m) (atLeastEnvRefinesKWF_mono (Nat.le_succ m) hρ) hd
          henv_wf_l henv_wf_r hπ_case hswf_l' hswf_r' hs

end MainTheorem

section Soundness

open Moist.Verified.Contextual.Soundness
  (dummyEnv dummyEnv_length locality_obsRefinesK)
open Moist.Verified.Contextual.BisimRef (LocalState LocalEnv LocalStack)

private theorem dummyEnv_wellFormed : ∀ (n : Nat),
    EnvWellFormed n (dummyEnv n) := by
  intro n
  induction n with
  | zero => exact EnvWellFormed.zero
  | succ k ih =>
    have hlen : k ≤ (dummyEnv k).length := by rw [dummyEnv_length]; exact Nat.le_refl _
    exact envWellFormed_extend k ih hlen (ValueWellFormed.vcon .Unit)

theorem atLeastEnvRefinesKWF_dummyEnv (k n : Nat) :
    AtLeastEnvRefinesKWF k (dummyEnv n) (dummyEnv n) := by
  induction n with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro m _ hmlen
    simp [dummyEnv, CekEnv.length] at hmlen; omega
  | succ m ih =>
    refine ⟨rfl, ?_⟩
    intro j hj hjlen
    by_cases h1 : j = 1
    · subst h1
      refine ⟨.VCon .Unit, .VCon .Unit, ?_, ?_, ?_⟩
      · show (CekEnv.cons _ (dummyEnv m)).lookup 1 = some _; rfl
      · show (CekEnv.cons _ (dummyEnv m)).lookup 1 = some _; rfl
      · cases k <;> simp only [ValueRefinesKWF]
    · have hj2 : j ≥ 2 := by omega
      have hlen : (dummyEnv (m + 1)).length = m + 1 := dummyEnv_length (m + 1)
      rw [hlen] at hjlen
      match j, hj2 with
      | j' + 2, _ =>
        have hjlen' : j' + 1 ≤ (dummyEnv m).length := by rw [dummyEnv_length m]; omega
        obtain ⟨v_l, v_r, hl, hr, hrel⟩ := ih.2 (j' + 1) (by omega) hjlen'
        refine ⟨v_l, v_r, ?_, ?_, hrel⟩
        · show (CekEnv.cons _ (dummyEnv m)).lookup (j' + 2) = some v_l; exact hl
        · show (CekEnv.cons _ (dummyEnv m)).lookup (j' + 2) = some v_r; exact hr

private theorem closedAt_mono' {d d' : Nat} {t : Term}
    (hle : d ≤ d') (h : closedAt d t = true) :
    closedAt d' t = true :=
  Moist.Verified.Contextual.closedAt_mono h hle

theorem soundness_refinesWF {d : Nat} {t₁ t₂ : Term}
    (h_open_wf : OpenRefinesWF d t₁ t₂)
    (h_close_pres : ∀ (C : Context),
      Moist.Verified.closedAt 0 (fill C t₁) = true →
      Moist.Verified.closedAt 0 (fill C t₂) = true) :
    CtxRefines t₁ t₂ := by
  intro C h_c1
  have h_c2 := h_close_pres C h_c1
  refine ⟨h_c2, ?_⟩
  have hls₁ : LocalState (.compute [] .nil (fill C t₁))
                         (.compute [] (dummyEnv d) (fill C t₁)) :=
    LocalState.compute LocalEnv.zero h_c1 LocalStack.nil
  have hls₂ : LocalState (.compute [] .nil (fill C t₂))
                         (.compute [] (dummyEnv d) (fill C t₂)) :=
    LocalState.compute LocalEnv.zero h_c2 LocalStack.nil
  have h_swf_l : StateWellFormed (.compute [] (dummyEnv d) (fill C t₁)) :=
    StateWellFormed.compute StackWellFormed.nil (dummyEnv_wellFormed d)
      (by rw [dummyEnv_length]; exact Nat.le_refl _) (closedAt_mono' (Nat.zero_le d) h_c1)
  have h_swf_r : StateWellFormed (.compute [] (dummyEnv d) (fill C t₂)) :=
    StateWellFormed.compute StackWellFormed.nil (dummyEnv_wellFormed d)
      (by rw [dummyEnv_length]; exact Nat.le_refl _) (closedAt_mono' (Nat.zero_le d) h_c2)
  refine ⟨?_, ?_⟩
  · rintro ⟨v, n, hs⟩
    have h_obs : ObsRefinesK n
        (.compute [] (dummyEnv d) (fill C t₁))
        (.compute [] (dummyEnv d) (fill C t₂)) :=
      term_obsRefinesWF h_open_wf n n (Nat.le_refl _)
        (atLeastEnvRefinesKWF_dummyEnv n d)
        (by rw [dummyEnv_length]; exact Nat.le_refl _)
        (dummyEnv_wellFormed d) (dummyEnv_wellFormed d)
        (stackRefKWF_nil n) h_swf_l h_swf_r (fill_termSubstL C t₁ t₂)
    exact (locality_obsRefinesK n hls₁ hls₂ h_obs).1 v ⟨n, Nat.le_refl _, hs⟩
  · rintro ⟨n, hs⟩
    have h_obs : ObsRefinesK n
        (.compute [] (dummyEnv d) (fill C t₁))
        (.compute [] (dummyEnv d) (fill C t₂)) :=
      term_obsRefinesWF h_open_wf n n (Nat.le_refl _)
        (atLeastEnvRefinesKWF_dummyEnv n d)
        (by rw [dummyEnv_length]; exact Nat.le_refl _)
        (dummyEnv_wellFormed d) (dummyEnv_wellFormed d)
        (stackRefKWF_nil n) h_swf_l h_swf_r (fill_termSubstL C t₁ t₂)
    exact (locality_obsRefinesK n hls₁ hls₂ h_obs).2 n (Nat.le_refl _) hs

end Soundness

end Moist.Verified.TermObsRefinesWF
