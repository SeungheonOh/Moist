import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Verified.ClosedAt
import Moist.Verified.Definitions
import Moist.Verified.Definitions.Contextual
import Moist.Verified.Definitions.StepIndexed
import Moist.CEK.DecidableEq

namespace Moist.Verified.Equivalence

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified (closedAt closedAtList)

--------------------------------------------------------------------------------
-- Theorems.
--
-- The definitions (`steps`, `Reaches`, `ListRel`, `ObsRefinesK`, ...) live in
-- `Moist.Verified.Definitions` and `Moist.Verified.Definitions.StepIndexed`.
--------------------------------------------------------------------------------

/-- `ObsRefinesK` is monotone in the step index. -/
theorem obsRefinesK_mono {j k : Nat} (hjk : j ≤ k) {s₁ s₂ : State}
    (h : ObsRefinesK k s₁ s₂) : ObsRefinesK j s₁ s₂ :=
  ⟨fun v ⟨n, hn, hs⟩ => h.1 v ⟨n, Nat.le_trans hn hjk, hs⟩,
   fun n hnj hs => h.2 n (Nat.le_trans hnj hjk) hs⟩

/-- `ObsRefinesK k .error .error` is trivially true. -/
theorem obsRefinesK_error_error (k : Nat) : ObsRefinesK k (.error : State) .error := by
  refine ⟨?_, ?_⟩
  · intro v ⟨n, _, hs⟩
    rw [steps_error n] at hs
    exact absurd hs State.noConfusion
  · intro _ _ _
    exact ⟨0, rfl⟩

/-- Halt states refine each other trivially. -/
theorem obsRefinesK_halt_halt (k : Nat) (v_l v_r : CekValue) :
    ObsRefinesK k (.halt v_l) (.halt v_r) := by
  refine ⟨?_, ?_⟩
  · intro v ⟨n, _, hs⟩
    rw [steps_halt n v_l] at hs
    cases hs
    exact ⟨v_r, 0, rfl⟩
  · intro n _ hs
    rw [steps_halt n v_l] at hs
    exact absurd hs State.noConfusion

/-- Zero-step refinement for `ObsRefinesK 0` when LHS is neither halt nor error. -/
theorem obsRefinesK_zero_nonhalt {s₁ s₂ : State}
    (h₁ : ∀ v, s₁ ≠ .halt v) (h_err : s₁ ≠ .error) : ObsRefinesK 0 s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v ⟨n, hn, hs⟩
    have : n = 0 := Nat.le_zero.mp hn
    subst this; simp only [steps] at hs
    exact absurd hs (h₁ v)
  · intro n hnk hs
    have : n = 0 := Nat.le_zero.mp hnk
    subst this; simp only [steps] at hs
    exact absurd hs h_err

/-- Peel one deterministic step from both sides (one-way).

    The `h_err` hypothesis is needed for the `n = 0` sub-case of the error
    clause: at `n = 0` we would have `s₁ = .error`, and `ObsRefinesK k (step s₁)
    (step s₂)` gives us no information about `s₂`'s error behavior in that
    case. In practice call sites peel steps from compute/ret states, so
    `h_err` is immediate via `State.noConfusion`. -/
theorem obsRefinesK_of_step {s₁ s₂ : State} {k : Nat}
    (h₁ : ∀ v, s₁ ≠ .halt v) (_h₂ : ∀ v, s₂ ≠ .halt v)
    (h_err : s₁ ≠ .error)
    (h : ObsRefinesK k (step s₁) (step s₂)) :
    ObsRefinesK (k + 1) s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v ⟨n, hn, hs⟩
    match n with
    | 0 => exact absurd hs (h₁ v)
    | n + 1 =>
      have hstep : steps n (step s₁) = .halt v := by simp only [steps] at hs; exact hs
      obtain ⟨v', m, hm⟩ := h.1 v ⟨n, Nat.le_of_succ_le_succ hn, hstep⟩
      exact ⟨v', m + 1, by simp only [steps]; exact hm⟩
  · intro n hnk hs
    match n with
    | 0 => simp only [steps] at hs; exact absurd hs h_err
    | n' + 1 =>
      have hstep : steps n' (step s₁) = .error := by simp only [steps] at hs; exact hs
      obtain ⟨m, hm⟩ := h.2 n' (by omega) hstep
      exact ⟨m + 1, by simp only [steps]; exact hm⟩

/-- Run the left state forward `n` steps. No side conditions: if the left
    state halts or errors before step `n`, it stays there (both are absorbing).
    Protected because several proof files still carry a same-named local copy. -/
protected theorem obsRefinesK_of_steps_left {k n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁') (h : ObsRefinesK k s₁' s₂) : ObsRefinesK k s₁ s₂ := by
  subst h_steps
  have reach : ∀ {m t}, steps m s₁ = t → (t = .error ∨ ∃ v, t = .halt v) →
      ∃ m' ≤ m, steps m' (steps n s₁) = t := by
    intro m t hm ht
    by_cases hle : m ≤ n
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [show n = m + (n - m) by omega, Equivalence.steps_trans, hm]
      rcases ht with rfl | ⟨v, rfl⟩
      · exact steps_error _
      · exact steps_halt _ v
    · refine ⟨m - n, by omega, ?_⟩
      rw [← Equivalence.steps_trans, show n + (m - n) = m by omega, hm]
  refine ⟨fun v ⟨m, hm, hs⟩ => ?_, fun m hm hs => ?_⟩
  · obtain ⟨m', hm', hs'⟩ := reach hs (.inr ⟨v, rfl⟩)
    exact h.1 v ⟨m', by omega, hs'⟩
  · obtain ⟨m', hm', hs'⟩ := reach hs (.inl rfl)
    exact h.2 m' (by omega) hs'

/-- Run the right state forward `n` steps. -/
protected theorem obsRefinesK_of_steps_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefinesK k s₁ s₂') : ObsRefinesK k s₁ s₂ := by
  subst h_steps
  refine ⟨fun v hv => ?_, fun m hm hs => ?_⟩
  · obtain ⟨v', m, hm⟩ := h.1 v hv
    exact ⟨v', n + m, by rw [Equivalence.steps_trans]; exact hm⟩
  · obtain ⟨m', hm'⟩ := h.2 m hm hs
    exact ⟨n + m', by rw [Equivalence.steps_trans]; exact hm'⟩

/-- ObsRefinesK 0 at compute-compute states. -/
theorem obsRefinesK_zero_compute {π₁ : Stack} {ρ₁ : CekEnv} {t₁ : Term}
    {π₂ : Stack} {ρ₂ : CekEnv} {t₂ : Term} :
    ObsRefinesK 0 (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂) :=
  obsRefinesK_zero_nonhalt (fun _ h => by cases h) (fun h => by cases h)

/-- ObsRefinesK 0 at ret-ret states. -/
theorem obsRefinesK_zero_ret {π₁ : Stack} {v₁ : CekValue}
    {π₂ : Stack} {v₂ : CekValue} :
    ObsRefinesK 0 (.ret π₁ v₁) (.ret π₂ v₂) :=
  obsRefinesK_zero_nonhalt (fun _ h => by cases h) (fun h => by cases h)

/-- Peel a step on ObsRefinesK at compute-compute states. -/
theorem obsRefinesK_of_step_compute {k : Nat}
    {π₁ : Stack} {ρ₁ : CekEnv} {t₁ : Term}
    {π₂ : Stack} {ρ₂ : CekEnv} {t₂ : Term}
    (h : ObsRefinesK k (step (.compute π₁ ρ₁ t₁)) (step (.compute π₂ ρ₂ t₂))) :
    ObsRefinesK (k+1) (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂) :=
  obsRefinesK_of_step (fun _ h => by cases h) (fun _ h => by cases h)
                      (fun h => by cases h) h

/-- Peel a step on ObsRefinesK at ret-ret states. -/
theorem obsRefinesK_of_step_ret {k : Nat}
    {π₁ : Stack} {v₁ : CekValue}
    {π₂ : Stack} {v₂ : CekValue}
    (h : ObsRefinesK k (step (.ret π₁ v₁)) (step (.ret π₂ v₂))) :
    ObsRefinesK (k+1) (.ret π₁ v₁) (.ret π₂ v₂) :=
  obsRefinesK_of_step (fun _ h => by cases h) (fun _ h => by cases h)
                      (fun h => by cases h) h

/-- Dispatch wrapper: use in compat_* lemmas where the state could be compute
    or ret. Relies on `first` to select the appropriate specialized lemma. -/
macro "obsRefinesK_zero_nonhalt_auto" : tactic =>
  `(tactic| first | exact obsRefinesK_zero_compute | exact obsRefinesK_zero_ret)

macro "obsRefinesK_of_step_auto" : tactic =>
  `(tactic| first | refine obsRefinesK_of_step_compute ?_
                  | refine obsRefinesK_of_step_ret ?_)

theorem listRel_mono {R S : α → α → Prop} (hRS : ∀ a b, R a b → S a b)
    {l₁ l₂ : List α} (h : ListRel R l₁ l₂) : ListRel S l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at h
    | cons b bs => simp only [ListRel] at h ⊢; exact ⟨hRS _ _ h.1, ih h.2⟩

theorem listRel_append {R : α → α → Prop} {l₁ l₂ m₁ m₂ : List α}
    (hl : ListRel R l₁ l₂) (hm : ListRel R m₁ m₂) : ListRel R (l₁ ++ m₁) (l₂ ++ m₂) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at hl
    | cons b bs => simp only [List.cons_append, ListRel]; exact ⟨hl.1, ih hl.2⟩

theorem listRel_reverse {R : α → α → Prop} {l₁ l₂ : List α}
    (h : ListRel R l₁ l₂) : ListRel R l₁.reverse l₂.reverse := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at h
    | cons b bs =>
      simp only [List.reverse_cons, ListRel] at h ⊢
      exact listRel_append (ih h.2) ⟨h.1, trivial⟩

private theorem listRel_length {R : α → α → Prop} :
    {l₁ l₂ : List α} → ListRel R l₁ l₂ → l₁.length = l₂.length
  | [], [], _ => rfl
  | _ :: _, [], h => absurd h id
  | [], _ :: _, h => absurd h id
  | _ :: _, _ :: _, h => by simp; exact listRel_length h.2

theorem listRel_getElem {R : α → α → Prop} {l₁ l₂ : List α}
    (h : ListRel R l₁ l₂) {i : Nat} (hi : i < l₁.length) :
    R (l₁[i]'hi) (l₂[i]'(by have := listRel_length h; omega)) := by
  induction l₁ generalizing l₂ i with
  | nil => simp at hi
  | cons a as ih =>
    cases l₂ with
    | nil => exact absurd h id
    | cons b bs =>
      cases i with
      | zero => exact h.1
      | succ i' => exact ih h.2 (by simp at hi ⊢; omega)

theorem constToTagAndFields_fields_vcon (c : Const) :
    match constToTagAndFields c with
    | some (_, _, fields) => ∀ v ∈ fields, ∃ c, v = .VCon c
    | none => True := by
  cases c with
  | Bool b => cases b <;> simp [constToTagAndFields]
  | Unit => simp [constToTagAndFields]
  | Integer n =>
    simp only [constToTagAndFields]
    split <;> simp_all
  | ConstList l =>
    cases l with
    | nil => simp [constToTagAndFields]
    | cons h t =>
      simp only [constToTagAndFields]
      intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | ConstDataList l =>
    cases l with
    | nil => simp [constToTagAndFields]
    | cons h t =>
      simp only [constToTagAndFields]
      intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields]
    intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields]
    intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | _ => trivial

/-! ## Builtins under a constant-respecting value relation

`R` relates a constant exactly to itself (in both directions). All value
relations used in the proofs (`ValueRefinesK`, `ValueRefinesKWF`,
`LocalValue`) have this shape. -/

theorem listRel_cons_inv {R : α → α → Prop} {a : α} {as : List α} {l₂ : List α}
    (h : ListRel R (a :: as) l₂) : ∃ b bs, l₂ = b :: bs ∧ R a b ∧ ListRel R as bs := by
  cases l₂ with
  | nil => exact absurd h id
  | cons b bs => exact ⟨b, bs, rfl, h.1, h.2⟩

theorem listRel_nil_inv {R : α → α → Prop} {l₂ : List α}
    (h : ListRel R ([] : List α) l₂) : l₂ = [] := by
  cases l₂ with | nil => rfl | cons => exact absurd h id

theorem extractConsts_rel {R : CekValue → CekValue → Prop}
    (vconL : ∀ {c v}, R (.VCon c) v → v = .VCon c)
    (vconR : ∀ {c v}, R v (.VCon c) → v = .VCon c)
    {args₁ args₂ : List CekValue} (hargs : ListRel R args₁ args₂) :
    extractConsts args₁ = extractConsts args₂ := by
  induction args₁ generalizing args₂ with
  | nil => rw [listRel_nil_inv hargs]
  | cons a₁ as₁ ih =>
    obtain ⟨a₂, as₂, rfl, ha, has⟩ := listRel_cons_inv hargs
    match a₁ with
    | .VCon c => rw [vconL ha]; simp only [extractConsts]; rw [ih has]
    | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
      match a₂ with
      | .VCon _ => cases vconR ha
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ => rfl

/-- Pass-through builtins on related arguments give related results, for any
    value relation that relates a constant exactly to itself. -/
theorem evalBuiltinPassThrough_rel {R : CekValue → CekValue → Prop}
    (vconL : ∀ {c v}, R (.VCon c) v → v = .VCon c)
    (vconR : ∀ {c v}, R v (.VCon c) → v = .VCon c)
    (vconRefl : ∀ c, R (.VCon c) (.VCon c))
    {b : BuiltinFun} {args₁ args₂ : List CekValue} (hargs : ListRel R args₁ args₂) :
    match evalBuiltinPassThrough b args₁, evalBuiltinPassThrough b args₂ with
    | some v₁, some v₂ => R v₁ v₂
    | none, none => True
    | _, _ => False := by
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                 b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · -- IfThenElse
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons e₁ r₁ =>
      obtain ⟨e₂, r₂, rfl, he, hr⟩ := listRel_cons_inv hargs; cases r₁ with
      | nil => rw [listRel_nil_inv hr]; simp [evalBuiltinPassThrough]
      | cons t₁ s₁ =>
      obtain ⟨t₂, s₂, rfl, ht, hs⟩ := listRel_cons_inv hr; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [vconL hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 rename_i bv; cases bv <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => cases vconR hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- ChooseUnit
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [vconL hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => cases vconR hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- Trace
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [vconL hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => cases vconR hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- ChooseData
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons a₁ r₁ =>
      obtain ⟨a₂, r₂, rfl, ha, hr⟩ := listRel_cons_inv hargs; cases r₁ with
      | nil => rw [listRel_nil_inv hr]; simp [evalBuiltinPassThrough]
      | cons b₁ s₁ =>
      obtain ⟨b₂, s₂, rfl, hb, hs⟩ := listRel_cons_inv hr; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ t₁ =>
      obtain ⟨c₂, t₂, rfl, hc_val, ht⟩ := listRel_cons_inv hs; cases t₁ with
      | nil => rw [listRel_nil_inv ht]; simp [evalBuiltinPassThrough]
      | cons d₁ u₁ =>
      obtain ⟨d₂, u₂, rfl, hd, hu⟩ := listRel_cons_inv ht; cases u₁ with
      | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
      | cons e₁ w₁ =>
      obtain ⟨e₂, w₂, rfl, he_val, hw⟩ := listRel_cons_inv hu
      cases w₁ with
      | nil => rw [listRel_nil_inv hw]; simp [evalBuiltinPassThrough]
      | cons f₁ x₁ =>
      obtain ⟨f₂, x₂, rfl, hf, hx⟩ := listRel_cons_inv hw
      match f₁ with
      | .VCon c_const =>
        rw [vconL hf]
        cases x₁ with
        | nil => rw [listRel_nil_inv hx]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 rename_i dat; cases dat <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hx
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match f₂ with
        | .VCon _ => cases vconR hf
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases x₁ with
          | nil => rw [listRel_nil_inv hx]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hx; simp [evalBuiltinPassThrough]
    · -- ChooseList
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons t₁ u₁ =>
      obtain ⟨t₂, u₂, rfl, ht, hu⟩ := listRel_cons_inv hs; cases u₁ with
      | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
      | cons c₁ w₁ =>
      obtain ⟨c₂, w₂, rfl, hc, hw⟩ := listRel_cons_inv hu
      match c₁ with
      | .VCon c_const =>
        rw [vconL hc]
        cases w₁ with
        | nil => rw [listRel_nil_inv hw]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 all_goals (split <;> assumption)
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hw
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => cases vconR hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases w₁ with
          | nil => rw [listRel_nil_inv hw]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hw; simp [evalBuiltinPassThrough]
    · -- MkCons
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons a₁ r₁ =>
      obtain ⟨a₂, r₂, rfl, ha, hr⟩ := listRel_cons_inv hargs; cases r₁ with
      | nil => rw [listRel_nil_inv hr]; simp [evalBuiltinPassThrough]
      | cons b₁ s₁ =>
      obtain ⟨b₂, s₂, rfl, hb, hs⟩ := listRel_cons_inv hr
      cases s₁ with
      | cons _ _ =>
        obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hs; simp [evalBuiltinPassThrough]
      | nil =>
      rw [listRel_nil_inv hs]
      match a₁ with
      | .VCon c_const =>
        rw [vconL ha]
        cases c_const <;> simp [evalBuiltinPassThrough]
        rename_i tail₁
        match b₁ with
        | .VCon c₁ => rw [vconL hb]; exact vconRefl _
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          match b₂ with
          | .VCon _ => cases vconR hb
          | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ => trivial
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match a₂ with
        | .VCon _ => cases vconR ha
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

/-- `evalBuiltin` on related arguments gives related results. -/
theorem evalBuiltin_rel {R : CekValue → CekValue → Prop}
    (vconL : ∀ {c v}, R (.VCon c) v → v = .VCon c)
    (vconR : ∀ {c v}, R v (.VCon c) → v = .VCon c)
    (vconRefl : ∀ c, R (.VCon c) (.VCon c))
    {b : BuiltinFun} {args₁ args₂ : List CekValue} (hargs : ListRel R args₁ args₂) :
    match evalBuiltin b args₁, evalBuiltin b args₂ with
    | some v₁, some v₂ => R v₁ v₂
    | none, none => True
    | _, _ => False := by
  have h_pt := evalBuiltinPassThrough_rel vconL vconR vconRefl (b := b) hargs
  simp only [evalBuiltin]
  revert h_pt
  cases evalBuiltinPassThrough b args₁ <;> cases evalBuiltinPassThrough b args₂ <;> intro h_pt
  · rw [extractConsts_rel vconL vconR hargs]
    cases extractConsts args₂ with
    | none => trivial
    | some consts =>
      simp only []
      cases evalBuiltinConst b consts with
      | none => trivial
      | some c => exact vconRefl c
  · exact absurd h_pt id
  · exact absurd h_pt id
  · exact h_pt

end Moist.Verified.Equivalence
