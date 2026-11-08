import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.Verified.ClosedAt
import Moist.Verified.Definitions
import Moist.Verified.Definitions.Contextual
import Moist.Verified.Definitions.StepIndexed
import Moist.CEK.DecidableEq

variable [sv : Moist.CEK.SemVariant]

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

private theorem steps_fixed {t : State} (ht : step t = t) : ∀ n, steps n t = t
  | 0 => rfl
  | n + 1 => by simp only [steps, ht]; exact steps_fixed ht n

/-- A fixed point reached after `m` steps is still reached `m - n` steps after step `n`. -/
private theorem steps_after {n m : Nat} {s t : State} (ht : step t = t) (h : steps m s = t) :
    steps (m - n) (steps n s) = t := by
  by_cases hmn : m ≤ n
  · rw [Nat.sub_eq_zero_of_le hmn, show n = m + (n - m) by omega, steps_trans, h, steps_fixed ht]
    rfl
  · rw [← steps_trans, show n + (m - n) = m by omega, h]

/-- Running the left state forward preserves refinement (halt and error are
    absorbing, so no side condition is needed). -/
theorem obsRefinesK_of_steps_left {k n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁') (h : ObsRefinesK k s₁' s₂) : ObsRefinesK k s₁ s₂ := by
  subst h_steps
  exact ⟨fun v ⟨m, hm, hs⟩ => h.1 v ⟨m - n, by omega, steps_after rfl hs⟩,
    fun m hm hs => h.2 (m - n) (by omega) (steps_after rfl hs)⟩

/-- Running the right state forward preserves refinement. -/
theorem obsRefinesK_of_steps_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefinesK k s₁ s₂') : ObsRefinesK k s₁ s₂ := by
  refine ⟨fun v hv => ?_, fun m hm herr => ?_⟩
  · obtain ⟨v', m, hm⟩ := h.1 v hv
    exact ⟨v', n + m, by rw [steps_trans, h_steps]; exact hm⟩
  · obtain ⟨m', hm'⟩ := h.2 m hm herr
    exact ⟨n + m', by rw [steps_trans, h_steps]; exact hm'⟩

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

omit sv in
theorem listRel_mono {R S : α → α → Prop} (hRS : ∀ a b, R a b → S a b)
    {l₁ l₂ : List α} (h : ListRel R l₁ l₂) : ListRel S l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at h
    | cons b bs => simp only [ListRel] at h ⊢; exact ⟨hRS _ _ h.1, ih h.2⟩

omit sv in
theorem listRel_append {R : α → α → Prop} {l₁ l₂ m₁ m₂ : List α}
    (hl : ListRel R l₁ l₂) (hm : ListRel R m₁ m₂) : ListRel R (l₁ ++ m₁) (l₂ ++ m₂) := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at hl
    | cons b bs => simp only [List.cons_append, ListRel]; exact ⟨hl.1, ih hl.2⟩

omit sv in
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

omit sv in
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
  | ConstList ty l =>
    cases l with
    | nil => simp [constToTagAndFields]
    | cons h t =>
      simp only [constToTagAndFields]
      intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields]
    intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  | _ => trivial

/-! ## Builtins under a constant-respecting value relation

`R` relates a constant exactly to itself (in both directions). All value
relations used in the proofs (`ValueRefinesK`, `ValueRefinesKWF`,
`LocalValue`) have this shape. -/

omit sv in
theorem listRel_cons_inv {R : α → α → Prop} {a : α} {as : List α} {l₂ : List α}
    (h : ListRel R (a :: as) l₂) : ∃ b bs, l₂ = b :: bs ∧ R a b ∧ ListRel R as bs := by
  cases l₂ with
  | nil => exact absurd h id
  | cons b bs => exact ⟨b, bs, rfl, h.1, h.2⟩

omit sv in
theorem listRel_nil_inv {R : α → α → Prop} {l₂ : List α}
    (h : ListRel R ([] : List α) l₂) : l₂ = [] := by
  cases l₂ with | nil => rfl | cons => exact absurd h id

omit sv in
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

omit sv in
private theorem listRel_cons_vcon {R : CekValue → CekValue → Prop}
    (vconL : ∀ {c v}, R (.VCon c) v → v = .VCon c)
    {c : Const} {as bs : List CekValue}
    (h : ListRel R (.VCon c :: as) bs) : ∃ bs', bs = .VCon c :: bs' ∧ ListRel R as bs' := by
  obtain ⟨b, bs', rfl, hb, h⟩ := listRel_cons_inv h
  exact ⟨bs', by rw [vconL hb], h⟩

omit sv in
theorem listRel_flip {R : α → α → Prop} : ∀ {as bs : List α},
    ListRel R as bs → ListRel (fun x y => R y x) bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨h, listRel_flip hs⟩

omit sv in
/-- Pass-through builtins only inspect constant arguments, so a successful call
    on the left has a related successful call on the right. -/
private theorem evalBuiltinPassThrough_some_rel {R : CekValue → CekValue → Prop}
    (vconL : ∀ {c v}, R (.VCon c) v → v = .VCon c)
    (vconRefl : ∀ c, R (.VCon c) (.VCon c))
    {b : BuiltinFun} {args₁ args₂ : List CekValue} (hargs : ListRel R args₁ args₂)
    {v₁ : CekValue} (heval : evalBuiltinPassThrough b args₁ = some v₁) :
    ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ R v₁ v₂ := by
  simp only [evalBuiltinPassThrough] at heval
  split at heval <;> (repeat' split at heval) <;> cases heval
  all_goals
    repeat (first
      | (replace hargs := listRel_cons_vcon vconL hargs; obtain ⟨_, rfl, hargs⟩ := hargs)
      | (replace hargs := listRel_cons_inv hargs; obtain ⟨_, _, rfl, _, hargs⟩ := hargs))
    try obtain rfl := listRel_nil_inv hargs
    first
      | refine ⟨_, ?_, ‹_›⟩; simp [evalBuiltinPassThrough, *]
      | exact ⟨_, rfl, vconRefl _⟩

omit sv in
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
  cases h₁ : evalBuiltinPassThrough b args₁ with
  | some v₁ =>
    obtain ⟨v₂, h₂, r⟩ := evalBuiltinPassThrough_some_rel vconL vconRefl hargs h₁
    rw [h₂]; exact r
  | none =>
    cases h₂ : evalBuiltinPassThrough b args₂ with
    | some v₂ =>
      obtain ⟨_, h, _⟩ := evalBuiltinPassThrough_some_rel (R := fun x y => R y x)
        vconR vconRefl (listRel_flip hargs) h₂
      rw [h₁] at h; cases h
    | none => trivial

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

/-- `Option.Rel` form of `evalBuiltin_rel`. -/
theorem evalBuiltin_optionRel {R : CekValue → CekValue → Prop}
    (vconL : ∀ {c v}, R (.VCon c) v → v = .VCon c)
    (vconR : ∀ {c v}, R v (.VCon c) → v = .VCon c)
    (vconRefl : ∀ c, R (.VCon c) (.VCon c))
    {b : BuiltinFun} {args₁ args₂ : List CekValue} (hargs : ListRel R args₁ args₂) :
    Option.Rel R (evalBuiltin b args₁) (evalBuiltin b args₂) := by
  have h := evalBuiltin_rel vconL vconR vconRefl (b := b) hargs
  revert h
  cases evalBuiltin b args₁ <;> cases evalBuiltin b args₂ <;> intro h
  · exact .none
  · exact h.elim
  · exact h.elim
  · exact .some h

end Moist.Verified.Equivalence
