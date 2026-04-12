import Moist.CEK.Machine
import Moist.CEK.Readback
import Moist.VerifiedNewNew.Rename
import Moist.CEK.DecidableEq

namespace Moist.VerifiedNewNew.Equivalence

open Moist.CEK
open Moist.Plutus.Term
open Moist.VerifiedNewNew (closedAt closedAtList)

--------------------------------------------------------------------------------
-- 1. OBSERVATIONS
--------------------------------------------------------------------------------

def steps : Nat → State → State
  | 0, s => s
  | n + 1, s => steps n (step s)

def Reaches (s s' : State) : Prop := ∃ n : Nat, steps n s = s'

/-- Full observational equivalence: both halt AND error behavior preserved. -/
def ObsEq (c₁ c₂ : State) : Prop :=
  ((∃ v₁, Reaches c₁ (.halt v₁)) ↔ (∃ v₂, Reaches c₂ (.halt v₂))) ∧
  (Reaches c₁ .error ↔ Reaches c₂ .error)

/-- One-way step-indexed observation: halt preservation within k steps and
    error preservation within k steps (including n = 0, i.e. `s₁ = .error`).
    Building block for ObsEqK (two-way) and
    Contextual.SoundnessRefines.ObsRefinesK. -/
def ObsRefinesK (k : Nat) (s₁ s₂ : State) : Prop :=
  (∀ v, (∃ n ≤ k, steps n s₁ = .halt v) → ∃ v', Reaches s₂ (.halt v')) ∧
  (∀ n ≤ k, steps n s₁ = .error → Reaches s₂ .error)

/-- Bounded observation: both halt (within k steps) and error (within k
    positive steps) behavior preserved in both directions. -/
def ObsEqK (k : Nat) (s₁ s₂ : State) : Prop :=
  ObsRefinesK k s₁ s₂ ∧ ObsRefinesK k s₂ s₁

--------------------------------------------------------------------------------
-- 2. LIFTING OPERATORS (Kripke-Monotone with bounded ObsEqK)
--------------------------------------------------------------------------------

def StackRelK (V : Nat → CekValue → CekValue → Prop) (k : Nat) (π₁ π₂ : Stack) : Prop :=
  ∀ j ≤ k, ∀ v₁ v₂, V j v₁ v₂ → ObsEqK j (.ret π₁ v₁) (.ret π₂ v₂)

def BehEqK (V : Nat → CekValue → CekValue → Prop) (k : Nat)
    (ρ₁ ρ₂ : CekEnv) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ π₁ π₂, StackRelK V j π₁ π₂ →
    ObsEqK j (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)

--------------------------------------------------------------------------------
-- 3. THE KNOT
--------------------------------------------------------------------------------

def ListRel (R : α → α → Prop) : List α → List α → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ ListRel R as bs
  | _, _ => False

/-- Step-indexed value relation. At level 0 we enforce shape matching and
    VCon content equality — otherwise `evalBuiltin_compat` at k=0 would not
    hold, because level-0 args carrying no information would fail to force
    matching `extractConsts`/`evalBuiltinConst` outputs on both sides. -/
def ValueEqK : Nat → CekValue → CekValue → Prop
  | 0, .VCon c₁, .VCon c₂ => c₁ = c₂
  | 0, .VLam _ _, .VLam _ _ => True
  | 0, .VDelay _ _, .VDelay _ _ => True
  | 0, .VConstr tag₁ _, .VConstr tag₂ _ => tag₁ = tag₂
  | 0, .VBuiltin b₁ _ exp₁, .VBuiltin b₂ _ exp₂ => b₁ = b₂ ∧ exp₁ = exp₂
  | _ + 1, .VCon c₁, .VCon c₂ => c₁ = c₂
  | k + 1, .VLam b₁ ρ₁, .VLam b₂ ρ₂ =>
      ∀ j ≤ k, ∀ arg₁ arg₂, ValueEqK j arg₁ arg₂ →
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, ValueEqK i' w₁ w₂ → ObsEqK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsEqK i (.compute π₁ (ρ₁.extend arg₁) b₁) (.compute π₂ (ρ₂.extend arg₂) b₂)
  | k + 1, .VDelay b₁ ρ₁, .VDelay b₂ ρ₂ =>
      ∀ j ≤ k,
        ∀ i ≤ j, ∀ π₁ π₂,
          (∀ i' ≤ i, ∀ w₁ w₂, ValueEqK i' w₁ w₂ → ObsEqK i' (.ret π₁ w₁) (.ret π₂ w₂)) →
          ObsEqK i (.compute π₁ ρ₁ b₁) (.compute π₂ ρ₂ b₂)
  | k + 1, .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      tag₁ = tag₂ ∧ ListRel (ValueEqK k) fields₁ fields₂
  | k + 1, .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      b₁ = b₂ ∧ exp₁ = exp₂ ∧ ListRel (ValueEqK k) args₁ args₂
  | _, _, _ => False

--------------------------------------------------------------------------------
-- 4. OPEN EQUIVALENCE
--------------------------------------------------------------------------------

def EnvEqK (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup n with
    | some v₁, some v₂ => ValueEqK k v₁ v₂
    | none, none => True
    | _, _ => False

def OpenEqK (k d : Nat) (t₁ t₂ : Term) : Prop :=
  ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvEqK j d ρ₁ ρ₂ → BehEqK ValueEqK j ρ₁ ρ₂ t₁ t₂

def OpenEq (d : Nat) (t₁ t₂ : Term) : Prop := ∀ k, OpenEqK k d t₁ t₂

--------------------------------------------------------------------------------
-- 5. INFRASTRUCTURE
--------------------------------------------------------------------------------

theorem steps_error : ∀ n, steps n .error = .error := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => simp [steps, step, ih]

theorem steps_halt : ∀ n (v : CekValue), steps n (.halt v) = .halt v := by
  intro n v; induction n with
  | zero => rfl
  | succ n ih => simp [steps, step, ih]

/-- Helper: compute states are not halt. -/
theorem compute_ne_halt {π : Stack} {ρ : CekEnv} {t : Term} :
    ∀ v, (State.compute π ρ t : State) ≠ .halt v :=
  fun _ h => by cases h

/-- Helper: compute states are not error. -/
theorem compute_ne_error {π : Stack} {ρ : CekEnv} {t : Term} :
    (State.compute π ρ t : State) ≠ .error :=
  fun h => by cases h

/-- Helper: ret states are not halt. -/
theorem ret_ne_halt {π : Stack} {v : CekValue} :
    ∀ v', (State.ret π v : State) ≠ .halt v' :=
  fun _ h => by cases h

/-- Helper: ret states are not error. -/
theorem ret_ne_error {π : Stack} {v : CekValue} :
    (State.ret π v : State) ≠ .error :=
  fun h => by cases h

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

/-- ObsEqK is monotone: fewer steps to check ⇒ easier to satisfy. -/
theorem obsEqK_mono {j k : Nat} (hjk : j ≤ k) {s₁ s₂ : State}
    (h : ObsEqK k s₁ s₂) : ObsEqK j s₁ s₂ :=
  ⟨obsRefinesK_mono hjk h.1, obsRefinesK_mono hjk h.2⟩

/-- Stepping consumes one fuel unit (two-way). -/
theorem obsEqK_of_step {s₁ s₂ : State}
    (h₁ : ∀ v, s₁ ≠ .halt v) (h₂ : ∀ v, s₂ ≠ .halt v)
    (he₁ : s₁ ≠ .error) (he₂ : s₂ ≠ .error)
    (h : ObsEqK k (step s₁) (step s₂)) : ObsEqK (k+1) s₁ s₂ :=
  ⟨obsRefinesK_of_step h₁ h₂ he₁ h.1,
   obsRefinesK_of_step h₂ h₁ he₂ h.2⟩

theorem obsEqK_error (k : Nat) : ObsEqK k .error .error :=
  ⟨obsRefinesK_error_error k, obsRefinesK_error_error k⟩

/-- ObsEqK 0 is vacuously true for states that are neither halt nor error
    (i.e. compute or ret). -/
theorem obsEqK_zero_nonhalt {s₁ s₂ : State}
    (h₁ : ∀ v, s₁ ≠ .halt v) (h₂ : ∀ v, s₂ ≠ .halt v)
    (he₁ : s₁ ≠ .error) (he₂ : s₂ ≠ .error) : ObsEqK 0 s₁ s₂ :=
  ⟨obsRefinesK_zero_nonhalt h₁ he₁, obsRefinesK_zero_nonhalt h₂ he₂⟩

-- ── Concretized wrappers to avoid state-metavariable elaboration issues ──

/-- ObsEqK 0 at compute-compute states. -/
theorem obsEqK_zero_compute {π₁ : Stack} {ρ₁ : CekEnv} {t₁ : Term}
    {π₂ : Stack} {ρ₂ : CekEnv} {t₂ : Term} :
    ObsEqK 0 (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂) :=
  obsEqK_zero_nonhalt (fun _ h => by cases h) (fun _ h => by cases h)
                      (fun h => by cases h) (fun h => by cases h)

/-- ObsEqK 0 at ret-ret states. -/
theorem obsEqK_zero_ret {π₁ : Stack} {v₁ : CekValue}
    {π₂ : Stack} {v₂ : CekValue} :
    ObsEqK 0 (.ret π₁ v₁) (.ret π₂ v₂) :=
  obsEqK_zero_nonhalt (fun _ h => by cases h) (fun _ h => by cases h)
                      (fun h => by cases h) (fun h => by cases h)

/-- Peel a step at compute-compute states. -/
theorem obsEqK_of_step_compute {k : Nat}
    {π₁ : Stack} {ρ₁ : CekEnv} {t₁ : Term}
    {π₂ : Stack} {ρ₂ : CekEnv} {t₂ : Term}
    (h : ObsEqK k (step (.compute π₁ ρ₁ t₁)) (step (.compute π₂ ρ₂ t₂))) :
    ObsEqK (k+1) (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂) :=
  obsEqK_of_step (fun _ h => by cases h) (fun _ h => by cases h)
                 (fun h => by cases h) (fun h => by cases h) h

/-- Peel a step at ret-ret states. -/
theorem obsEqK_of_step_ret {k : Nat}
    {π₁ : Stack} {v₁ : CekValue}
    {π₂ : Stack} {v₂ : CekValue}
    (h : ObsEqK k (step (.ret π₁ v₁)) (step (.ret π₂ v₂))) :
    ObsEqK (k+1) (.ret π₁ v₁) (.ret π₂ v₂) :=
  obsEqK_of_step (fun _ h => by cases h) (fun _ h => by cases h)
                 (fun h => by cases h) (fun h => by cases h) h

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
macro "obsEqK_zero_nonhalt_auto" : tactic =>
  `(tactic| first | exact obsEqK_zero_compute | exact obsEqK_zero_ret)

macro "obsEqK_of_step_auto" : tactic =>
  `(tactic| first | refine obsEqK_of_step_compute ?_
                  | refine obsEqK_of_step_ret ?_)

macro "obsRefinesK_zero_nonhalt_auto" : tactic =>
  `(tactic| first | exact obsRefinesK_zero_compute | exact obsRefinesK_zero_ret)

macro "obsRefinesK_of_step_auto" : tactic =>
  `(tactic| first | refine obsRefinesK_of_step_compute ?_
                  | refine obsRefinesK_of_step_ret ?_)

theorem stackRelK_mono {V : Nat → CekValue → CekValue → Prop} {i k : Nat}
    (hik : i ≤ k) {π₁ π₂ : Stack} (h : StackRelK V k π₁ π₂) : StackRelK V i π₁ π₂ :=
  fun j hj v₁ v₂ hv => h j (Nat.le_trans hj hik) v₁ v₂ hv

theorem listRel_mono {R S : α → α → Prop} (hRS : ∀ a b, R a b → S a b)
    {l₁ l₂ : List α} (h : ListRel R l₁ l₂) : ListRel S l₁ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at h
    | cons b bs => simp only [ListRel] at h ⊢; exact ⟨hRS _ _ h.1, ih h.2⟩

private theorem valueEqK_mono_le (k : Nat) :
    ∀ j, j ≤ k → ∀ v₁ v₂, ValueEqK k v₁ v₂ → ValueEqK j v₁ v₂ := by
  induction k with
  | zero =>
    intro j hj v₁ v₂ h
    have hj0 : j = 0 := by omega
    subst hj0; exact h
  | succ k ih =>
    intro j hj v₁ v₂ h
    match j, v₁, v₂ with
    | 0, .VCon _, .VCon _ => simp only [ValueEqK] at h ⊢; exact h
    | 0, .VLam _ _, .VLam _ _ => simp only [ValueEqK]
    | 0, .VDelay _ _, .VDelay _ _ => simp only [ValueEqK]
    | 0, .VConstr _ _, .VConstr _ _ =>
      simp only [ValueEqK] at h ⊢; exact h.1
    | 0, .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueEqK] at h ⊢; exact ⟨h.1, h.2.1⟩
    | j' + 1, .VCon _, .VCon _ => simp only [ValueEqK] at h ⊢; exact h
    | j' + 1, .VLam _ _, .VLam _ _ =>
      simp only [ValueEqK] at h ⊢
      intro i' hi' a₁ a₂ ha ib hib π₁ π₂ hπ
      exact h i' (by omega) a₁ a₂ ha ib hib π₁ π₂ hπ
    | j' + 1, .VDelay _ _, .VDelay _ _ =>
      simp only [ValueEqK] at h ⊢
      intro i' hi' ib hib π₁ π₂ hπ
      exact h i' (by omega) ib hib π₁ π₂ hπ
    | j' + 1, .VConstr _ _, .VConstr _ _ =>
      simp only [ValueEqK] at h ⊢
      exact ⟨h.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2⟩
    | j' + 1, .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueEqK] at h ⊢
      exact ⟨h.1, h.2.1, listRel_mono (fun a b hab => ih j' (by omega) a b hab) h.2.2⟩
    | _, .VCon _, .VLam _ _ | _, .VCon _, .VDelay _ _ | _, .VCon _, .VConstr _ _
    | _, .VCon _, .VBuiltin _ _ _ | _, .VLam _ _, .VCon _ | _, .VLam _ _, .VDelay _ _
    | _, .VLam _ _, .VConstr _ _ | _, .VLam _ _, .VBuiltin _ _ _
    | _, .VDelay _ _, .VCon _ | _, .VDelay _ _, .VLam _ _ | _, .VDelay _ _, .VConstr _ _
    | _, .VDelay _ _, .VBuiltin _ _ _ | _, .VConstr _ _, .VCon _
    | _, .VConstr _ _, .VLam _ _ | _, .VConstr _ _, .VDelay _ _
    | _, .VConstr _ _, .VBuiltin _ _ _ | _, .VBuiltin _ _ _, .VCon _
    | _, .VBuiltin _ _ _, .VLam _ _ | _, .VBuiltin _ _ _, .VDelay _ _
    | _, .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at h

theorem valueEqK_mono {j k : Nat} (hjk : j ≤ k) (v₁ v₂ : CekValue)
    (h : ValueEqK k v₁ v₂) : ValueEqK j v₁ v₂ :=
  valueEqK_mono_le k j hjk v₁ v₂ h

theorem envEqK_mono {j k d : Nat} (hjk : j ≤ k) {ρ₁ ρ₂ : CekEnv}
    (h : EnvEqK k d ρ₁ ρ₂) : EnvEqK j d ρ₁ ρ₂ := by
  intro n hn hnd; have h_n := h n hn hnd
  cases h₁ : ρ₁.lookup n <;> cases h₂ : ρ₂.lookup n <;> simp_all
  · exact valueEqK_mono hjk _ _ h_n

theorem envEqK_extend {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : EnvEqK k d ρ₁ ρ₂) (hv : ValueEqK k v₁ v₂) :
    EnvEqK k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1; simp [CekEnv.extend, CekEnv.lookup]; exact hv
  · -- n ≥ 2: extended lookup shifts to original at n-1
    have hn2 : n ≥ 2 := by omega
    simp only [CekEnv.extend]
    match n, hn2 with
    | n' + 2, _ =>
      simp only [CekEnv.lookup]
      -- Goal: match ρ₁.lookup (n'+1), ρ₂.lookup (n'+1) with ...
      exact henv (n'+1) (by omega) (by omega)

/-- VCon values in ListRel have equal constants, so extractConsts gives the same list. -/
private theorem extractConsts_eq {k : Nat} {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueEqK k) args₁ args₂) :
    extractConsts args₁ = extractConsts args₂ := by
  induction args₁ generalizing args₂ with
  | nil => cases args₂ <;> simp_all [ListRel, extractConsts]
  | cons a₁ as₁ ih =>
    cases args₂ with
    | nil => simp [ListRel] at hargs
    | cons a₂ as₂ =>
      simp only [ListRel] at hargs
      obtain ⟨ha, has⟩ := hargs
      match a₁, a₂ with
      | .VCon c₁, .VCon c₂ =>
        have heq : c₁ = c₂ := by
          cases k with
          | zero => simp only [ValueEqK] at ha; exact ha
          | succ => simp only [ValueEqK] at ha; exact ha
        subst heq
        simp only [extractConsts]; rw [ih has]
      | .VLam _ _, .VLam _ _ => simp [extractConsts]
      | .VDelay _ _, .VDelay _ _ => simp [extractConsts]
      | .VConstr _ _, .VConstr _ _ => simp [extractConsts]
      | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp [extractConsts]
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at ha

-- ── ListRel / ValueEqK inversion helpers ──

private theorem listRel_cons_inv {R : α → α → Prop} {a : α} {as : List α} {l₂ : List α}
    (h : ListRel R (a :: as) l₂) : ∃ b bs, l₂ = b :: bs ∧ R a b ∧ ListRel R as bs := by
  cases l₂ with
  | nil => exact absurd h id
  | cons b bs => exact ⟨b, bs, rfl, h.1, h.2⟩

private theorem listRel_nil_inv {R : α → α → Prop} {l₂ : List α}
    (h : ListRel R ([] : List α) l₂) : l₂ = [] := by
  cases l₂ with | nil => rfl | cons => exact absurd h id

private theorem valueEqK_vcon_inv {k : Nat} {c : Const} {v : CekValue}
    (h : ValueEqK k (.VCon c) v) : v = .VCon c := by
  match k, v with
  | 0, .VCon c' => simp only [ValueEqK] at h; cases h; rfl
  | 0, .VLam _ _ | 0, .VDelay _ _ | 0, .VConstr _ _ | 0, .VBuiltin _ _ _ =>
    simp only [ValueEqK] at h
  | _ + 1, .VCon c' => simp only [ValueEqK] at h; cases h; rfl
  | _ + 1, .VLam _ _ | _ + 1, .VDelay _ _ | _ + 1, .VConstr _ _ | _ + 1, .VBuiltin _ _ _ =>
    simp only [ValueEqK] at h

set_option maxHeartbeats 6400000 in
private theorem evalBuiltinPassThrough_compat {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueEqK k) args₁ args₂) :
    match evalBuiltinPassThrough b args₁, evalBuiltinPassThrough b args₂ with
    | some v₁, some v₂ => ValueEqK k v₁ v₂
    | none, none => True
    | _, _ => False := by
  -- Non-pass-through builtins: both sides return none.
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                 b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    -- For each pass-through builtin: peel list via ListRel, case-split on
    -- condition value constructors, then simp [evalBuiltinPassThrough].
    -- VCon conditions: rw [valueEqK_vcon_inv]; cases Const; simp
    -- Non-VCon conditions: match c₂ same-ctor → simp; cross → ValueEqK contradiction
    · -- IfThenElse [elseV, thenV, VCon (Bool cond)]
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
      -- Dispatch on the condition value c₁
      match c₁ with
      | .VCon c_const =>
        rw [valueEqK_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 -- Only Bool survives: split on the boolean
                 rename_i bv; cases bv <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueEqK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- ChooseUnit [result, VCon Unit]
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [valueEqK_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr  -- Unit case: returns result
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueEqK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- Trace [result, VCon (String _)]
      cases args₁ with
      | nil => rw [listRel_nil_inv hargs]; simp [evalBuiltinPassThrough]
      | cons r₁ s₁ =>
      obtain ⟨r₂, s₂, rfl, hr, hs⟩ := listRel_cons_inv hargs; cases s₁ with
      | nil => rw [listRel_nil_inv hs]; simp [evalBuiltinPassThrough]
      | cons c₁ u₁ =>
      obtain ⟨c₂, u₂, rfl, hc, hu⟩ := listRel_cons_inv hs
      match c₁ with
      | .VCon c_const =>
        rw [valueEqK_vcon_inv hc]
        cases u₁ with
        | nil => rw [listRel_nil_inv hu]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 exact hr  -- String case: returns result
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueEqK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases u₁ with
          | nil => rw [listRel_nil_inv hu]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hu; simp [evalBuiltinPassThrough]
    · -- ChooseData [bCase, iCase, listCase, mapCase, constrCase, VCon (Data d)]
      -- Need 6 levels of peeling (condition is at position 5)
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
      -- e₁ is position 4 (constrCase). Condition (pos 5) is in w₁.
      cases w₁ with
      | nil => rw [listRel_nil_inv hw]; simp [evalBuiltinPassThrough]
      | cons f₁ x₁ =>
      obtain ⟨f₂, x₂, rfl, hf, hx⟩ := listRel_cons_inv hw
      -- f₁ at position 5 is the condition (VCon (Data d))
      match f₁ with
      | .VCon c_const =>
        rw [valueEqK_vcon_inv hf]
        cases x₁ with
        | nil => rw [listRel_nil_inv hx]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 -- Data case: split on Data constructors
                 rename_i dat; cases dat <;> simp <;> assumption
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hx
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match f₂ with
        | .VCon _ => simp only [ValueEqK] at hf
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases x₁ with
          | nil => rw [listRel_nil_inv hx]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hx; simp [evalBuiltinPassThrough]
    · -- ChooseList [consCase, nilCase, VCon (ConstList/ConstDataList l)]
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
        rw [valueEqK_vcon_inv hc]
        cases w₁ with
        | nil => rw [listRel_nil_inv hw]
                 cases c_const <;> simp [evalBuiltinPassThrough]
                 -- ConstList/ConstDataList: split on the if-then-else
                 all_goals (split <;> assumption)
        | cons _ _ =>
          obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hw
          cases c_const <;> simp [evalBuiltinPassThrough]
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match c₂ with
        | .VCon _ => simp only [ValueEqK] at hc
        | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
          cases w₁ with
          | nil => rw [listRel_nil_inv hw]; simp [evalBuiltinPassThrough]
          | cons _ _ =>
            obtain ⟨_, _, rfl, _, _⟩ := listRel_cons_inv hw; simp [evalBuiltinPassThrough]
    · -- MkCons [VCon (ConstList tail), elem]
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
      -- args = [a₁, b₁]. MkCons: first arg is condition (VCon ConstList)
      match a₁ with
      | .VCon c_const =>
        rw [valueEqK_vcon_inv ha]
        -- Split on Const: only ConstList matches MkCons; rest → none
        cases c_const <;> simp [evalBuiltinPassThrough]
        -- Only ConstList case survives: elem b₁ determines result
        rename_i tail₁
        match b₁, b₂ with
        | .VCon c₁, .VCon c₂ =>
          have hbeq : c₁ = c₂ := by cases k <;> (simp only [ValueEqK] at hb; exact hb)
          subst hbeq
          cases k <;> simp [ValueEqK]
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
          simp only [ValueEqK] at hb
      | .VLam _ _ | .VDelay _ _ | .VConstr _ _ | .VBuiltin _ _ _ =>
        match a₂ with
        | .VCon _ => simp only [ValueEqK] at ha
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

/-- evalBuiltin with related args gives related outputs. -/
private theorem evalBuiltin_rel {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue}
    (hargs : ListRel (ValueEqK k) args₁ args₂) :
    match evalBuiltin b args₁, evalBuiltin b args₂ with
    | some v₁, some v₂ => ValueEqK k v₁ v₂
    | none, none => True
    | _, _ => False := by
  have h_ext := extractConsts_eq hargs
  have h_pt := evalBuiltinPassThrough_compat (b := b) hargs
  simp only [evalBuiltin]
  revert h_pt
  cases evalBuiltinPassThrough b args₁ <;> cases evalBuiltinPassThrough b args₂ <;> intro h_pt
  · -- none, none → extractConsts path. Reduce trivial matches.
    rw [h_ext]; simp only []
    cases extractConsts args₂ with
    | none => simp
    | some consts =>
      simp only []
      cases evalBuiltinConst b consts with
      | none => simp
      | some c => cases k <;> simp [ValueEqK]
  · exact absurd h_pt id
  · exact absurd h_pt id
  · exact h_pt

theorem evalBuiltin_compat {k : Nat} {b : BuiltinFun}
    {args₁ args₂ : List CekValue} {π₁ π₂ : Stack}
    (hargs : ListRel (ValueEqK k) args₁ args₂)
    (hπ : StackRelK ValueEqK k π₁ π₂) :
    ObsEqK k
      (match evalBuiltin b args₁ with | some v => State.ret π₁ v | none => .error)
      (match evalBuiltin b args₂ with | some v => State.ret π₂ v | none => .error) := by
  have h_rel := evalBuiltin_rel (b := b) hargs
  revert h_rel
  cases evalBuiltin b args₁ <;> cases evalBuiltin b args₂ <;> intro h_rel
  · exact obsEqK_error _
  · exact absurd h_rel id
  · exact absurd h_rel id
  · exact hπ k (Nat.le_refl _) _ _ h_rel

--------------------------------------------------------------------------------
-- 6. CONGRUENCE: compat_app_k (FULLY PROVED modulo evalBuiltin_compat)
--------------------------------------------------------------------------------

theorem compat_app_k {k d : Nat} {f₁ f₂ a₁ a₂ : Term} :
    OpenEqK (k+1) d f₁ f₂ → OpenEqK (k+1) d a₁ a₂ →
    OpenEqK k d (.Apply f₁ a₁) (.Apply f₂ a₂) := by
  intro hf ha j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  -- ── Level 0: Apply step (consumes 1 fuel) ──
  match i with
  | 0 => obsEqK_zero_nonhalt_auto
  | i' + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  apply hf (i'+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) i' (by omega)
  -- ── Level 1: arg frame StackRelK (ret consumes 1 fuel) ──
  intro i₁ hi₁ v₁ v₂ hv
  match i₁ with
  | 0 => obsEqK_zero_nonhalt_auto
  | m₁ + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  apply ha (m₁+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) m₁ (by omega)
  -- ── Level 2: funV frame StackRelK (ret consumes 1 fuel) ──
  intro i₂ hi₂ w₁ w₂ hw
  match i₂ with
  | 0 => obsEqK_zero_nonhalt_auto
  | m₂ + 1 =>
  obsEqK_of_step_auto
  -- ── Constructor dispatch on v₁, v₂ ──
  match v₁, v₂ with
  | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
    simp only [step, ValueEqK] at hv ⊢
    -- Goal: ObsEqK m₂. Closure gives BehEqK at j' ≤ m₁. Use j' = m₂ (m₂ ≤ m₁ from hi₂).
    exact hv m₂ (by omega) w₁ w₂ (valueEqK_mono (by omega) w₁ w₂ hw)
      m₂ (Nat.le_refl _) π₁ π₂ (stackRelK_mono (by omega) hπ)
  | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
    simp only [ValueEqK] at hv
    obtain ⟨rfl, rfl, hargs_rel⟩ := hv
    simp only [step]
    split -- ea.head
    · split -- ea.tail
      · -- some rest: return new VBuiltin to stack
        rename_i rest _
        have hval : ValueEqK (m₂ + 1)
            (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
          simp only [ValueEqK]; refine ⟨trivial, trivial, ?_⟩; simp only [ListRel]
          exact ⟨valueEqK_mono (by omega) w₁ w₂ hw,
                 listRel_mono (fun a b h => valueEqK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
        exact obsEqK_mono (by omega)
          (hπ (m₂ + 1) (by omega) _ _ hval)
      · -- none: fully saturated
        exact evalBuiltin_compat
          (by simp only [ListRel]
              exact ⟨valueEqK_mono (by omega) w₁ w₂ hw,
                listRel_mono (fun a b h => valueEqK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩)
          (stackRelK_mono (by omega) hπ)
    · exact obsEqK_error _
  | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
  | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsEqK_error _
  | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
  | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
  | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
  | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
  | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv

theorem compat_lam_k {k d : Nat} {name : Nat} {body₁ body₂ : Term} :
    OpenEqK (k+1) (d+1) body₁ body₂ →
    OpenEqK k d (.Lam name body₁) (.Lam name body₂) := by
  intro hbody j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match i with
  | 0 => obsEqK_zero_nonhalt_auto
  | i' + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  -- Goal: ObsEqK i' (.ret π₁ (.VLam body₁ ρ₁)) (.ret π₂ (.VLam body₂ ρ₂))
  -- Build ValueEqK for the closures, then use hπ + obsEqK_mono
  have hval : ValueEqK i' (.VLam body₁ ρ₁) (.VLam body₂ ρ₂) := by
    cases i' with
    | zero => simp only [ValueEqK]
    | succ m =>
      simp only [ValueEqK]
      intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
      exact hbody j' (by omega) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
        (envEqK_extend (envEqK_mono (by omega) henv) hargs) ib hib π₁' π₂' hπ'
  exact hπ i' (by omega) _ _ hval

theorem compat_delay_k {k d : Nat} {body₁ body₂ : Term} :
    OpenEqK (k+1) d body₁ body₂ →
    OpenEqK k d (.Delay body₁) (.Delay body₂) := by
  intro hbody j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match i with
  | 0 => obsEqK_zero_nonhalt_auto
  | i' + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  have hval : ValueEqK i' (.VDelay body₁ ρ₁) (.VDelay body₂ ρ₂) := by
    cases i' with
    | zero => simp only [ValueEqK]
    | succ m =>
      simp only [ValueEqK]
      intro j' hj' ib hib π₁' π₂' hπ'
      exact hbody j' (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) ib hib π₁' π₂' hπ'
  exact hπ i' (by omega) _ _ hval

theorem compat_force_k {k d : Nat} {t₁ t₂ : Term} :
    OpenEqK (k+1) d t₁ t₂ → OpenEqK k d (.Force t₁) (.Force t₂) := by
  intro ht j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  -- ── Level 0: Force step (consumes 1 fuel) ──
  match i with
  | 0 => obsEqK_zero_nonhalt_auto
  | i' + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  -- Goal: ObsEqK i' (.compute (.force :: π₁) ρ₁ t₁) (.compute (.force :: π₂) ρ₂ t₂)
  apply ht (i'+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) i' (by omega)
  -- ── Build StackRelK for the force frame ──
  intro j' hj' v₁ v₂ hv
  match j' with
  | 0 => obsEqK_zero_nonhalt_auto
  | m + 1 =>
  obsEqK_of_step_auto
  -- ── Dispatch on the forced value ──
  match v₁, v₂ with
  | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
    simp only [step, ValueEqK] at hv ⊢
    -- hv : ∀ j ≤ m, ∀ i ≤ j, ∀ π₁ π₂, StackRelK → ObsEqK i (compute π₁ ρ₁' body₁) ...
    exact hv m (by omega) m (by omega) π₁ π₂ (stackRelK_mono (by omega) hπ)
  | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
    simp only [ValueEqK] at hv
    obtain ⟨rfl, rfl, hargs_rel⟩ := hv
    simp only [step]
    split -- ea.head
    · split -- ea.tail
      · -- some rest: consume type arg, return VBuiltin
        rename_i rest _
        have hval : ValueEqK (m + 1)
            (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
          simp only [ValueEqK]; exact ⟨trivial, trivial, hargs_rel⟩
        exact obsEqK_mono (by omega) (hπ (m + 1) (by omega) _ _ hval)
      · -- none: fully saturated builtin
        exact evalBuiltin_compat hargs_rel (stackRelK_mono (by omega) hπ)
    · -- argV under force: error
      exact obsEqK_error _
  | .VCon _, .VCon _ => simp only [step]; exact obsEqK_error _
  | .VLam _ _, .VLam _ _ => simp only [step]; exact obsEqK_error _
  | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
  | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
  | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
  | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
  | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv

-- ── ListRel helpers for reverse and append ──

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

-- ── constrField StackRelK by induction on the remaining field list ──

private theorem constrField_stackRelK {d tag k : Nat}
    {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ => OpenEqK (k+1) d t₁ t₂) ms₁ ms₂) :
    ∀ {j : Nat}, j ≤ k →
      ∀ {done₁ done₂ : List CekValue} {π₁ π₂ : Stack},
        EnvEqK j d ρ₁ ρ₂ →
        ListRel (ValueEqK j) done₁ done₂ →
        StackRelK ValueEqK j π₁ π₂ →
        StackRelK ValueEqK j (.constrField tag done₁ ms₁ ρ₁ :: π₁)
                              (.constrField tag done₂ ms₂ ρ₂ :: π₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
    cases ms₂ with
    | cons => exact absurd hfields id
    | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsEqK_zero_nonhalt_auto
    | n + 1 =>
    obsEqK_of_step_auto
    simp only [step]
    have hrev : ListRel (ValueEqK n) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hdone))
        ⟨valueEqK_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueEqK (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse)) (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueEqK]; exact ⟨trivial, hrev⟩
    exact obsEqK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m₁ ms₁' ih =>
    cases ms₂ with
    | nil => exact absurd hfields id
    | cons m₂ ms₂' =>
    have hm : OpenEqK (k+1) d m₁ m₂ := hfields.1
    have hfs : ListRel (fun t₁ t₂ => OpenEqK (k+1) d t₁ t₂) ms₁' ms₂' := hfields.2
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsEqK_zero_nonhalt_auto
    | n + 1 =>
    obsEqK_of_step_auto
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (envEqK_mono (by omega) henv)
      (show ListRel (ValueEqK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueEqK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hdone⟩)
      (stackRelK_mono (by omega) hπ)

theorem compat_constr_k {k d : Nat} {tag : Nat} {m₁ m₂ : Term} {ms₁ ms₂ : List Term} :
    OpenEqK (k+1) d m₁ m₂ →
    ListRel (fun t₁ t₂ => OpenEqK (k+1) d t₁ t₂) ms₁ ms₂ →
    OpenEqK k d (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  intro hm hfields j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match i with
  | 0 => obsEqK_zero_nonhalt_auto
  | i' + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  apply hm (i'+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) i' (by omega)
  exact constrField_stackRelK hfields (by omega : i' ≤ k)
    (envEqK_mono (by omega) henv) trivial (stackRelK_mono (by omega) hπ)

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

theorem listRel_refl_vcon (j : Nat) (l : List CekValue)
    (h : ∀ v ∈ l, ∃ c, v = .VCon c) : ListRel (ValueEqK j) l l := by
  induction l with
  | nil => trivial
  | cons v vs ih =>
    obtain ⟨c, rfl⟩ := h _ (.head _)
    refine ⟨?_, ih (fun w hw => h w (.tail _ hw))⟩
    cases j with
    | zero => simp only [ValueEqK.eq_1]
    | succ => simp [ValueEqK]

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

/-- applyArg frames for related field values give StackRelK when composed with a StackRelK tail. -/
theorem applyArgFrames_stackRelK {j : Nat}
    {fields₁ fields₂ : List CekValue} {π₁ π₂ : Stack}
    (hfields : ListRel (ValueEqK j) fields₁ fields₂)
    (hπ : StackRelK ValueEqK j π₁ π₂) :
    StackRelK ValueEqK j (fields₁.map Frame.applyArg ++ π₁)
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
    simp [List.map, List.cons_append]
    -- StackRelK for (.applyArg v₁ :: rest₁) (.applyArg v₂ :: rest₂)
    intro j' hj' w₁ w₂ hw
    match j' with
    | 0 => obsEqK_zero_nonhalt_auto
    | n + 1 =>
    obsEqK_of_step_auto
    -- Dispatch on the returned function w₁, w₂
    match w₁, w₂ with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
      simp only [step, ValueEqK] at hw ⊢
      exact hw n (by omega) v₁ v₂ (valueEqK_mono (by omega) v₁ v₂ hv)
        n (Nat.le_refl _) _ _
        (stackRelK_mono (by omega)
          (ih (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hvs)
              (stackRelK_mono (by omega) hπ)))
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
      simp only [ValueEqK] at hw; obtain ⟨rfl, rfl, hargs⟩ := hw; simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueEqK (n + 1)
              (.VBuiltin b₁ (v₁ :: args₁) rest) (.VBuiltin b₁ (v₂ :: args₂) rest) := by
            simp only [ValueEqK]; refine ⟨trivial, trivial, ?_⟩
            exact ⟨valueEqK_mono (by omega) v₁ v₂ hv,
                   listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hargs⟩
          exact obsEqK_mono (by omega)
            ((stackRelK_mono (by omega)
              (ih (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hvs)
                   (stackRelK_mono (by omega) hπ))) (n+1) (by omega) _ _ hval)
        · exact evalBuiltin_compat
            ⟨valueEqK_mono (by omega) v₁ v₂ hv,
             listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hargs⟩
            (stackRelK_mono (by omega)
              (ih (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hvs)
                  (stackRelK_mono (by omega) hπ)))
      · exact obsEqK_error _
    | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _
    | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsEqK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hw

theorem compat_case_k {k d : Nat} {scrut₁ scrut₂ : Term} {alts₁ alts₂ : List Term}
    (halts : ListRel (fun a₁ a₂ => OpenEqK (k+1) d a₁ a₂) alts₁ alts₂) :
    OpenEqK (k+1) d scrut₁ scrut₂ →
    OpenEqK k d (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  intro hscrut j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match i with
  | 0 => obsEqK_zero_nonhalt_auto
  | i' + 1 =>
  obsEqK_of_step_auto
  simp only [step]
  apply hscrut (i'+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) i' (by omega)
  -- StackRelK for caseScrutinee alts₁ ρ₁ :: π₁ vs caseScrutinee alts₂ ρ₂ :: π₂
  intro j' hj' v₁ v₂ hv
  match j' with
  | 0 => obsEqK_zero_nonhalt_auto
  | n + 1 =>
  obsEqK_of_step_auto
  have hlen : alts₁.length = alts₂.length := listRel_length halts
  match v₁, v₂ with
  | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
    simp only [ValueEqK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
    simp only [step]
    -- Dispatch on alts₁[tag₁]? and alts₂[tag₁]? jointly via length equality
    cases halt₁ : alts₁[tag₁]? with
    | some alt₁ =>
      have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
      have hi₁ : tag₁ < alts₁.length := hsome₁.1
      have hi₂ : tag₁ < alts₂.length := by rw [← hlen]; exact hi₁
      have halt₂_eq : alts₂[tag₁]? = some (alts₂[tag₁]'hi₂) := by
        rw [List.getElem?_eq_getElem hi₂]
      rw [halt₂_eq]
      have halt_eq : OpenEqK (k+1) d alt₁ (alts₂[tag₁]'hi₂) := by
        have heq₁ : alts₁[tag₁] = alt₁ := hsome₁.2
        rw [← heq₁]; exact listRel_getElem halts hi₁
      apply halt_eq (n+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) n (by omega)
      exact applyArgFrames_stackRelK
        (listRel_mono (fun a b h => valueEqK_mono (by omega) a b h) hfields_v)
        (stackRelK_mono (by omega) hπ)
    | none =>
      have hge₁ : alts₁.length ≤ tag₁ := List.getElem?_eq_none_iff.mp halt₁
      have hge₂ : alts₂.length ≤ tag₁ := by rw [← hlen]; exact hge₁
      have halt₂ : alts₂[tag₁]? = none := List.getElem?_eq_none hge₂
      rw [halt₂]
      exact obsEqK_error _
  | .VCon c₁, .VCon c₂ =>
    simp only [ValueEqK] at hv; subst hv
    simp only [step]
    -- Align RHS's alts₂.length with alts₁.length so the IF condition matches
    rw [show alts₂.length = alts₁.length from hlen.symm]
    cases h_const : constToTagAndFields c₁ with
    | none => exact obsEqK_error _
    | some triple =>
      obtain ⟨tag, numCtors, fields⟩ := triple
      dsimp only []
      -- Dispatch on the IF condition (same on both sides now)
      by_cases h_check : (decide (numCtors > 0) && decide (alts₁.length > numCtors)) = true
      · rw [if_pos h_check, if_pos h_check]
        exact obsEqK_error _
      · rw [if_neg h_check, if_neg h_check]
        cases halt₁ : alts₁[tag]? with
        | some alt₁ =>
          have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
          have hi₁ : tag < alts₁.length := hsome₁.1
          have hi₂ : tag < alts₂.length := by rw [← hlen]; exact hi₁
          have halt₂_eq : alts₂[tag]? = some (alts₂[tag]'hi₂) :=
            List.getElem?_eq_getElem hi₂
          rw [halt₂_eq]
          have halt_eq : OpenEqK (k+1) d alt₁ (alts₂[tag]'hi₂) := by
            have heq₁ : alts₁[tag] = alt₁ := hsome₁.2
            rw [← heq₁]; exact listRel_getElem halts hi₁
          apply halt_eq (n+1) (by omega) ρ₁ ρ₂ (envEqK_mono (by omega) henv) n (by omega)
          have hfields_vcon := constToTagAndFields_fields_vcon c₁
          rw [h_const] at hfields_vcon
          exact applyArgFrames_stackRelK
            (listRel_refl_vcon n fields hfields_vcon)
            (stackRelK_mono (by omega) hπ)
        | none =>
          have hge₁ : alts₁.length ≤ tag := List.getElem?_eq_none_iff.mp halt₁
          have hge₂ : alts₂.length ≤ tag := by rw [← hlen]; exact hge₁
          have halt₂ : alts₂[tag]? = none := List.getElem?_eq_none hge₂
          rw [halt₂]
          exact obsEqK_error _
  | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsEqK_error _
  | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
  | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
  | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
  | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
  | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
  | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
  | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
  | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
  | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at hv

--------------------------------------------------------------------------------
-- 6b. UNBOUNDED CONGRUENCE COROLLARIES (OpenEq versions of compat_*_k)
--
-- Each compat_*_k step lemma drops the step index by one. Quantifying over
-- all k turns them into proper OpenEq congruences, giving the building blocks
-- for the contextual closure proof in `Contextual.lean`.
--------------------------------------------------------------------------------

theorem compat_app {d : Nat} {f₁ f₂ a₁ a₂ : Term}
    (hf : OpenEq d f₁ f₂) (ha : OpenEq d a₁ a₂) :
    OpenEq d (.Apply f₁ a₁) (.Apply f₂ a₂) :=
  fun k => compat_app_k (hf (k+1)) (ha (k+1))

theorem compat_lam {d : Nat} {name : Nat} {body₁ body₂ : Term}
    (hbody : OpenEq (d+1) body₁ body₂) :
    OpenEq d (.Lam name body₁) (.Lam name body₂) :=
  fun k => compat_lam_k (hbody (k+1))

theorem compat_delay {d : Nat} {body₁ body₂ : Term}
    (hbody : OpenEq d body₁ body₂) :
    OpenEq d (.Delay body₁) (.Delay body₂) :=
  fun k => compat_delay_k (hbody (k+1))

theorem compat_force {d : Nat} {t₁ t₂ : Term}
    (ht : OpenEq d t₁ t₂) :
    OpenEq d (.Force t₁) (.Force t₂) :=
  fun k => compat_force_k (ht (k+1))

theorem compat_constr {d tag : Nat} {m₁ m₂ : Term} {ms₁ ms₂ : List Term}
    (hm : OpenEq d m₁ m₂)
    (hms : ListRel (fun t₁ t₂ => OpenEq d t₁ t₂) ms₁ ms₂) :
    OpenEq d (.Constr tag (m₁ :: ms₁)) (.Constr tag (m₂ :: ms₂)) := by
  intro k
  exact compat_constr_k (hm (k+1)) (listRel_mono (fun _ _ h => h (k+1)) hms)

theorem compat_case {d : Nat} {scrut₁ scrut₂ : Term} {alts₁ alts₂ : List Term}
    (halts : ListRel (fun a₁ a₂ => OpenEq d a₁ a₂) alts₁ alts₂)
    (hscrut : OpenEq d scrut₁ scrut₂) :
    OpenEq d (.Case scrut₁ alts₁) (.Case scrut₂ alts₂) := by
  intro k
  exact compat_case_k (listRel_mono (fun _ _ h => h (k+1)) halts) (hscrut (k+1))

--------------------------------------------------------------------------------
-- 7. MAIN THEOREMS
--------------------------------------------------------------------------------

-- ── Symmetry helpers ──

theorem obsEqK_symm {k : Nat} {s₁ s₂ : State}
    (h : ObsEqK k s₁ s₂) : ObsEqK k s₂ s₁ := ⟨h.2, h.1⟩

private theorem listRel_symm {R : α → α → Prop} (hR : ∀ a b, R a b → R b a)
    {l₁ l₂ : List α} (h : ListRel R l₁ l₂) : ListRel R l₂ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all [ListRel]
  | cons a as ih =>
    cases l₂ with
    | nil => simp [ListRel] at h
    | cons b bs => simp only [ListRel] at h ⊢; exact ⟨hR _ _ h.1, ih h.2⟩

theorem stackRelK_symm_of {V : Nat → CekValue → CekValue → Prop}
    (hV : ∀ k v₁ v₂, V k v₁ v₂ → V k v₂ v₁) {i : Nat} {π₁ π₂ : Stack}
    (h : StackRelK V i π₁ π₂) : StackRelK V i π₂ π₁ :=
  fun j hj v₁ v₂ hv => obsEqK_symm (h j hj v₂ v₁ (hV j v₁ v₂ hv))

private theorem valueEqK_symm_le (k : Nat) :
    ∀ j, j ≤ k → ∀ v₁ v₂, ValueEqK j v₁ v₂ → ValueEqK j v₂ v₁ := by
  induction k with
  | zero =>
    intro j hj v₁ v₂ h
    have hj0 : j = 0 := by omega
    subst hj0
    match v₁, v₂ with
    | .VCon _, .VCon _ => simp only [ValueEqK] at h ⊢; exact h.symm
    | .VLam _ _, .VLam _ _ => simp only [ValueEqK]
    | .VDelay _ _, .VDelay _ _ => simp only [ValueEqK]
    | .VConstr _ _, .VConstr _ _ => simp only [ValueEqK] at h ⊢; exact h.symm
    | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
      simp only [ValueEqK] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at h
  | succ k ih =>
    intro j hj v₁ v₂ h
    by_cases hjk : j ≤ k
    · exact ih j hjk v₁ v₂ h
    · have hjeq : j = k + 1 := by omega
      subst hjeq
      match v₁, v₂ with
      | .VCon _, .VCon _ =>
        simp only [ValueEqK] at h ⊢; exact h.symm
      | .VLam _ _, .VLam _ _ =>
        simp only [ValueEqK] at h ⊢
        intro j' hj' a₁ a₂ ha ib hib π₁ π₂ hπ
        exact obsEqK_symm (h j' hj' a₂ a₁ (ih j' hj' a₁ a₂ ha)
          ib hib π₂ π₁
          (fun i' hi' v₁ v₂ hv => obsEqK_symm (hπ i' hi' v₂ v₁ (ih i' (by omega) v₁ v₂ hv))))
      | .VDelay _ _, .VDelay _ _ =>
        simp only [ValueEqK] at h ⊢
        intro j' hj' ib hib π₁ π₂ hπ
        exact obsEqK_symm (h j' hj'
          ib hib π₂ π₁
          (fun i' hi' v₁ v₂ hv => obsEqK_symm (hπ i' hi' v₂ v₁ (ih i' (by omega) v₁ v₂ hv))))
      | .VConstr _ _, .VConstr _ _ =>
        simp only [ValueEqK] at h ⊢
        exact ⟨h.1.symm, listRel_symm (ih k (by omega)) h.2⟩
      | .VBuiltin _ _ _, .VBuiltin _ _ _ =>
        simp only [ValueEqK] at h ⊢
        exact ⟨h.1.symm, h.2.1.symm, listRel_symm (ih k (by omega)) h.2.2⟩
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueEqK] at h

theorem valueEqK_symm (k : Nat) (v₁ v₂ : CekValue)
    (h : ValueEqK k v₁ v₂) : ValueEqK k v₂ v₁ :=
  valueEqK_symm_le k k (Nat.le_refl k) v₁ v₂ h

theorem envEqK_symm {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvEqK k d ρ₁ ρ₂) : EnvEqK k d ρ₂ ρ₁ := by
  intro n hn hnd; have h_n := h n hn hnd
  cases h₁ : ρ₁.lookup n <;> cases h₂ : ρ₂.lookup n <;> simp_all
  · exact valueEqK_symm k _ _ h_n

-- ── Reflexivity ──

mutual
private def openEq_fields (d : Nat) (ms : List Term) (hms : closedAtList d ms = true) (k : Nat) :
    ListRel (fun t₁ t₂ => OpenEqK k d t₁ t₂) ms ms :=
  match ms, hms with
  | [], _ => trivial
  | m :: ms', hms => by
    simp [closedAtList] at hms
    exact ⟨openEq_refl d m hms.1 k, openEq_fields d ms' hms.2 k⟩
  termination_by sizeOf ms

def openEq_refl (d : Nat) (t : Term) (ht : closedAt d t = true) : OpenEq d t t := by
  intro k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match t with
  | .Apply f x =>
    simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
    exact (compat_app_k (openEq_refl d f hf (j+1)) (openEq_refl d x hx (j+1)))
      j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  | .Force e =>
    simp [closedAt] at ht
    exact (compat_force_k (openEq_refl d e ht (j+1)))
      j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  | .Constr tag fields =>
    match fields with
    | [] =>
      match i with
      | 0 => obsEqK_zero_nonhalt_auto
      | i' + 1 =>
        obsEqK_of_step_auto
        simp only [step]
        have : ValueEqK i' (.VConstr tag []) (.VConstr tag []) := by
          cases i' with
          | zero => simp only [ValueEqK]
          | succ => simp [ValueEqK, ListRel]
        exact hπ i' (by omega) _ _ this
    | m :: ms =>
      simp [closedAt] at ht
      have hm : closedAt d m = true := by
        have := ht; simp [closedAtList] at this; exact this.1
      have hms : closedAtList d ms = true := by
        have := ht; simp [closedAtList] at this; exact this.2
      exact (compat_constr_k (openEq_refl d m hm (j+1))
        (openEq_fields d ms hms (j+1)))
        j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  | .Case scrut alts =>
    simp [closedAt] at ht
    exact (compat_case_k (openEq_fields d alts ht.2 (j+1)) (openEq_refl d scrut ht.1 (j+1)))
      j (Nat.le_refl _) ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  | .Error =>
    match i with
    | 0 => obsEqK_zero_nonhalt_auto
    | i' + 1 =>
      obsEqK_of_step_auto
      simp [step]; exact obsEqK_error _
  | .Constant c =>
    match i with
    | 0 => obsEqK_zero_nonhalt_auto
    | i' + 1 =>
      obsEqK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK]
        | succ => simp only [ValueEqK])
  | .Builtin b =>
    match i with
    | 0 => obsEqK_zero_nonhalt_auto
    | i' + 1 =>
      obsEqK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK]; exact ⟨trivial, trivial⟩
        | succ => simp [ValueEqK, ListRel])
  | .Var n =>
    match i with
    | 0 => obsEqK_zero_nonhalt_auto
    | i' + 1 =>
      simp [closedAt] at ht
      obsEqK_of_step_auto
      simp only [step]
      by_cases hn : n = 0
      · subst hn
        have h1 : ρ₁.lookup 0 = none := by cases ρ₁ <;> rfl
        have h2 : ρ₂.lookup 0 = none := by cases ρ₂ <;> rfl
        simp [h1, h2]; exact obsEqK_error _
      · have h_n := henv n (by omega) ht
        revert h_n
        cases ρ₁.lookup n <;> cases ρ₂.lookup n <;> intro h_n
        · exact obsEqK_error _
        · exact absurd h_n id
        · exact absurd h_n id
        · exact hπ i' (by omega) _ _ (valueEqK_mono (by omega : i' ≤ j) _ _ h_n)
  | .Lam _ body =>
    match i with
    | 0 => obsEqK_zero_nonhalt_auto
    | i' + 1 =>
      simp [closedAt] at ht
      obsEqK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK]
        | succ m =>
          simp only [ValueEqK]
          intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
          exact openEq_refl (d + 1) body ht j' j' (Nat.le_refl _)
            (ρ₁.extend arg₁) (ρ₂.extend arg₂) (envEqK_extend (envEqK_mono (by omega) henv) hargs)
            ib hib π₁' π₂' hπ')
  | .Delay body =>
    match i with
    | 0 => obsEqK_zero_nonhalt_auto
    | i' + 1 =>
      simp [closedAt] at ht
      obsEqK_of_step_auto
      simp only [step]
      exact hπ i' (by omega) _ _ (by cases i' with
        | zero => simp only [ValueEqK]
        | succ m =>
          simp only [ValueEqK]
          intro j' hj' ib hib π₁' π₂' hπ'
          exact openEq_refl d body ht j' j' (Nat.le_refl _) ρ₁ ρ₂ (envEqK_mono (by omega) henv)
            ib hib π₁' π₂' hπ')
  termination_by sizeOf t
  decreasing_by all_goals simp_wf <;> omega
end

-- ── Symmetry ──

theorem openEq_symm {d : Nat} {t₁ t₂ : Term} (h : OpenEq d t₁ t₂) : OpenEq d t₂ t₁ :=
  fun k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ =>
    obsEqK_symm (h k j hj ρ₂ ρ₁ (envEqK_symm henv) i hi π₂ π₁
      (stackRelK_symm_of (fun k' => valueEqK_symm k') hπ))

-- Transitivity is not true on openEq
-- /-- Transitivity requires chaining through an intermediate computation `compute π₂ ρ₂ t₂`.
--     The biorthogonal BehEqK locks ρ₁↔π₁ (left) and ρ₂↔π₂ (right), so the right side of h₁₂
--     is `(π₃, ρ₃, t₂)` while the left side of h₂₃ is `(π₁, ρ₁, t₂)` — they don't match.
--     Fixing this requires StackRelK/EnvEqK reflexivity, which in turn needs ValueEqK reflexivity
--     for arbitrary runtime values (closures with unknown bodies). This is provable from
--     `openEq_refl` if we add `closedAt` hypotheses on t₂. -/
-- theorem openEq_trans (d : Nat) (t₁ t₂ t₃ : Term) :
--     OpenEq d t₁ t₂ → OpenEq d t₂ t₃ → OpenEq d t₁ t₃ := sorry

end Moist.VerifiedNewNew.Equivalence
