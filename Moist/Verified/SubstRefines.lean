import Moist.Verified.BetaValueRefines
import Moist.Verified.FundamentalRefines
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.ClosedAt

namespace Moist.Verified.SubstRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.BetaValueRefines
open Moist.Verified.FundamentalRefines

section Infrastructure

theorem reaches_trans {s₁ s₂ s₃ : State}
    (h₁ : Reaches s₁ s₂) (h₂ : Reaches s₂ s₃) :
    Reaches s₁ s₃ := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by rw [steps_trans]; rw [hm]; exact hn⟩

theorem obsRefinesK_prepend_rhs {i : Nat} {s₁ s₂_mid s₂ : State}
    (hreach : Reaches s₂ s₂_mid)
    (hobs : ObsRefinesK i s₁ s₂_mid) :
    ObsRefinesK i s₁ s₂ := by
  constructor
  · intro v ⟨n, hn, hs⟩
    obtain ⟨v', hv'⟩ := hobs.1 v ⟨n, hn, hs⟩
    exact ⟨v', reaches_trans hreach hv'⟩
  · intro n hn hs
    exact reaches_trans hreach (hobs.2 n hn hs)

theorem obsRefinesK_of_lhs_var_lookup {i : Nat}
    {π₁ : Stack} {ρ₁ : CekEnv} {n : Nat} {v₁ : CekValue}
    {s₂ : State}
    (hlookup : ρ₁.lookup n = some v₁)
    (h : ObsRefinesK i (.ret π₁ v₁) s₂) :
    ObsRefinesK (i + 1) (.compute π₁ ρ₁ (.Var n)) s₂ := by
  constructor
  · intro v ⟨m, hm, hs⟩
    match m with
    | 0 => exact absurd hs (by intro h; cases h)
    | m + 1 =>
      have hstep : steps m (step (.compute π₁ ρ₁ (.Var n))) = .halt v := by
        simp only [steps] at hs; exact hs
      simp only [step, hlookup] at hstep
      exact h.1 v ⟨m, by omega, hstep⟩
  · intro m hm hs
    match m with
    | 0 => exact absurd hs (by intro h; cases h)
    | m + 1 =>
      have hstep : steps m (step (.compute π₁ ρ₁ (.Var n))) = .error := by
        simp only [steps] at hs; exact hs
      simp only [step, hlookup] at hstep
      exact h.2 m (by omega) hstep

theorem sized_rhs_of_substEnvRef {pos k d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂)
    (hpos : 1 ≤ pos) (hposd : pos ≤ d) :
    ∀ n, 0 < n → n ≤ d - 1 → ∃ v, ρ₂.lookup n = some v := by
  intro n hn hnd
  by_cases h1 : n < pos
  · obtain ⟨_, v₂, _, hl₂, _⟩ := substEnvRef_below_pos h hn (by omega) h1
    exact ⟨v₂, hl₂⟩
  · have h_gt : n + 1 > pos := by omega
    obtain ⟨_, v₂, _, hl₂, _⟩ := substEnvRef_above_pos h (by omega) (by omega) h_gt
    have : (n + 1) - 1 = n := by omega
    rw [this] at hl₂
    exact ⟨v₂, hl₂⟩

def iterShift : Nat → Term → Term
  | 0, t => t
  | n + 1, t => renameTerm (shiftRename 1) (iterShift n t)

theorem iterShift_zero (t : Term) : iterShift 0 t = t := rfl

theorem iterShift_succ (n : Nat) (t : Term) :
    iterShift (n + 1) t = renameTerm (shiftRename 1) (iterShift n t) := rfl

theorem iterShift_shift (n : Nat) (t : Term) :
    iterShift n (renameTerm (shiftRename 1) t) = iterShift (n + 1) t := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show renameTerm (shiftRename 1) (iterShift m (renameTerm (shiftRename 1) t)) =
         renameTerm (shiftRename 1) (iterShift (m + 1) t)
    rw [ih]

theorem closedAt_iterShift {d : Nat} {t : Term} (h : closedAt d t = true) :
    ∀ n, closedAt (d + n) (iterShift n t) = true := by
  intro n
  induction n with
  | zero => simp [iterShift]; exact h
  | succ m ih =>
    simp only [iterShift]
    have heq : d + m + 1 = d + (m + 1) := by omega
    rw [← heq]
    exact closedAt_shift ih

def RHaltsRelN (r : Term) (v_rhs : CekValue) (k d : Nat) : Prop :=
  ∀ (n : Nat), RHaltsRel (iterShift n r) v_rhs k (d + n)

theorem rHaltsRelN_zero {r : Term} {v_rhs : CekValue} {k d : Nat}
    (h : RHaltsRelN r v_rhs k d) : RHaltsRel r v_rhs k d := by
  have := h 0; simp [iterShift] at this; exact this

theorem rHaltsRelN_mono {r : Term} {v_rhs : CekValue} {j k d : Nat}
    (hjk : j ≤ k) (h : RHaltsRelN r v_rhs k d) :
    RHaltsRelN r v_rhs j d := by
  intro n; exact rHaltsRel_mono hjk (h n)

theorem rHaltsRelN_shift {r : Term} {v_rhs : CekValue} {k d : Nat}
    (h : RHaltsRelN r v_rhs k d) :
    RHaltsRelN (renameTerm (shiftRename 1) r) v_rhs k (d + 1) := by
  intro n
  have h1 : iterShift n (renameTerm (shiftRename 1) r) = iterShift (n + 1) r :=
    iterShift_shift n r
  have h2 : d + 1 + n = d + (n + 1) := by omega
  rw [show RHaltsRel (iterShift n (renameTerm (shiftRename 1) r)) v_rhs k (d + 1 + n)
      = RHaltsRel (iterShift (n + 1) r) v_rhs k (d + (n + 1)) from by rw [h1, h2]]
  exact h (n + 1)

end Infrastructure

section ConstrHelper

private theorem substRefinesConstrField
    {pos : Nat} {v_rhs : CekValue} {k d : Nat}
    {tag : Nat} {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂,
        SubstEnvRef pos v_rhs j (d + 1) ρ₁ ρ₂ →
        ρ₁.lookup pos = some v_rhs →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      SubstEnvRef pos v_rhs j (d + 1) ρ₁ ρ₂ →
      ρ₁.lookup pos = some v_rhs →
      ListRel (ValueRefinesK j) done₁ done₂ →
      StackRefK ValueRefinesK j π₁ π₂ →
      StackRefK ValueRefinesK j (.constrField tag done₁ ms₁ ρ₁ :: π₁)
                                 (.constrField tag done₂ ms₂ ρ₂ :: π₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
    cases ms₂ with
    | cons => exact absurd hfields id
    | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv hexact hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hrev : ListRel (ValueRefinesK n) ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse
          (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone))
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueRefinesK (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse))
        (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
    exact obsRefinesK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m₁ ms₁' ih =>
    cases ms₂ with
    | nil => exact absurd hfields id
    | cons m₂ ms₂' =>
    have hm := hfields.1
    have hfs := hfields.2
    intro j hj done₁ done₂ π₁ π₂ henv hexact hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (substEnvRef_mono (by omega) henv) hexact
      (show ListRel (ValueRefinesK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone⟩)
      (stackRefK_mono (by omega) hπ)

end ConstrHelper

section MainTheorem

mutual
theorem substRefinesR_body
    (pos : Nat) (r : Term) (v_rhs : CekValue)
    (k d : Nat) (t : Term)
    (ht : closedAt (d + 1) t = true)
    (hr : closedAt d r = true)
    (hpos : 1 ≤ pos) (hposd : pos ≤ d + 1)
    (hrhs : RHaltsRelN r v_rhs k d) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂,
      SubstEnvRef pos v_rhs j (d + 1) ρ₁ ρ₂ →
      ρ₁.lookup pos = some v_rhs →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ t)
          (.compute π₂ ρ₂ (substTerm pos r t)) := by
  intro j hj ρ₁ ρ₂ henv hexact i hi π₁ π₂ hπ
  match t with
  | .Constant c =>
    simp [substTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ => simp only [ValueRefinesK])

  | .Builtin b =>
    simp [substTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
      | succ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial, trivial⟩)

  | .Error =>
    simp [substTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp [step]; exact obsRefinesK_error _

  | .Var n =>
    simp only [substTerm]
    by_cases hn_eq : n = pos
    · subst hn_eq
      simp only []
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      have hρ₂_sized : ∀ n, 0 < n → n ≤ d → ∃ v, ρ₂.lookup n = some v :=
        sized_rhs_of_substEnvRef henv hpos (by omega)
      obtain ⟨m, v_rhs', hsteps_rhs, _, hval_rel⟩ := rHaltsRelN_zero hrhs ρ₂ π₂ hρ₂_sized
      have hval_mono : ValueRefinesK i' v_rhs v_rhs' :=
        valueRefinesK_mono (by omega : i' ≤ k) v_rhs v_rhs' hval_rel
      have hstack_obs : ObsRefinesK i' (.ret π₁ v_rhs) (.ret π₂ v_rhs') :=
        hπ i' (by omega) v_rhs v_rhs' hval_mono
      have hreach : Reaches (.compute π₂ ρ₂ r) (.ret π₂ v_rhs') :=
        ⟨m, hsteps_rhs⟩
      exact obsRefinesK_of_lhs_var_lookup hexact
        (obsRefinesK_prepend_rhs hreach hstack_obs)
    · by_cases hn_gt : n > pos
      · simp only [hn_eq, hn_gt, ite_false, ite_true]
        simp [closedAt] at ht
        match i with
        | 0 => obsRefinesK_zero_nonhalt_auto
        | i' + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        by_cases hn0 : n = 0
        · omega
        · have hn_pos : 0 < n := by omega
          obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ :=
            substEnvRef_above_pos henv hn_pos (by omega) hn_gt
          rw [hl₁, hl₂]
          exact hπ i' (by omega) v₁ v₂ (valueRefinesK_mono (by omega) v₁ v₂ hrel)
      · have h_lt : n < pos := by omega
        simp only [hn_eq, hn_gt, ite_false]
        simp [closedAt] at ht
        match i with
        | 0 => obsRefinesK_zero_nonhalt_auto
        | i' + 1 =>
        obsRefinesK_of_step_auto
        simp only [step]
        by_cases hn0 : n = 0
        · subst hn0
          rw [lookup_zero ρ₁, lookup_zero ρ₂]
          exact obsRefinesK_error _
        · have hn_pos : 0 < n := by omega
          obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ :=
            substEnvRef_below_pos henv hn_pos (by omega) h_lt
          rw [hl₁, hl₂]
          exact hπ i' (by omega) v₁ v₂ (valueRefinesK_mono (by omega) v₁ v₂ hrel)

  | .Lam name body =>
    simp only [substTerm]
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hr' : closedAt (d + 1) (renameTerm (shiftRename 1) r) = true :=
      closedAt_shift hr
    have hrhs' : RHaltsRelN (renameTerm (shiftRename 1) r) v_rhs k (d + 1) :=
      rHaltsRelN_shift hrhs
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ m =>
        simp only [ValueRefinesK]
        intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
        have henv' : SubstEnvRef (pos + 1) v_rhs j' (d + 2) (ρ₁.extend arg₁) (ρ₂.extend arg₂) :=
          substEnvRef_extend hpos hargs (substEnvRef_mono (by omega) henv)
        have hexact' : (ρ₁.extend arg₁).lookup (pos + 1) = some v_rhs := by
          rw [extend_lookup_succ ρ₁ arg₁ pos hpos]
          exact hexact
        exact substRefinesR_body (pos + 1) (renameTerm (shiftRename 1) r)
          v_rhs m (d + 1) body ht hr' (by omega) (by omega) (rHaltsRelN_mono (by omega) hrhs')
          j' hj' (ρ₁.extend arg₁) (ρ₂.extend arg₂)
          henv' hexact'
          ib hib π₁' π₂' hπ')

  | .Delay body =>
    simp only [substTerm]
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ m =>
        simp only [ValueRefinesK]
        intro j' hj' ib hib π₁' π₂' hπ'
        exact substRefinesR_body pos r v_rhs m d body ht hr hpos hposd
          (rHaltsRelN_mono (by omega) hrhs)
          j' hj' ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact
          ib hib π₁' π₂' hπ')

  | .Apply f x =>
    simp only [substTerm]
    simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply substRefinesR_body pos r v_rhs k d f hf hr hpos hposd hrhs
      (i'+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact i' (by omega)
    intro i₁ hi₁ v₁ v₂ hv
    match i₁ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₁ + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply substRefinesR_body pos r v_rhs k d x hx hr hpos hposd hrhs
      (m₁+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact m₁ (by omega)
    intro i₂ hi₂ w₁ w₂ hw
    match i₂ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₂ + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
      simp only [step, ValueRefinesK] at hv ⊢
      exact hv m₂ (by omega) w₁ w₂ (valueRefinesK_mono (by omega) w₁ w₂ hw)
        m₂ (Nat.le_refl _) π₁ π₂ (stackRefK_mono (by omega) hπ)
    | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
      simp only [ValueRefinesK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv
      simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (m₂ + 1)
              (.VBuiltin b₁ (w₁ :: args₁) rest) (.VBuiltin b₁ (w₂ :: args₂) rest) := by
            simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩; simp only [ListRel]
            exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                   listRel_mono (fun a b h => valueRefinesK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
          exact obsRefinesK_mono (by omega) (hπ (m₂ + 1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines
            (by simp only [ListRel]
                exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                  listRel_mono (fun a b h => valueRefinesK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩)
            (stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
    | .VDelay _ _, .VDelay _ _ => simp only [step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv

  | .Force e =>
    simp only [substTerm]
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply substRefinesR_body pos r v_rhs k d e ht hr hpos hposd hrhs
      (i'+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact i' (by omega)
    intro j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VDelay body₁ ρ₁', .VDelay body₂ ρ₂' =>
      simp only [step, ValueRefinesK] at hv ⊢
      exact hv m (by omega) m (by omega) π₁ π₂ (stackRefK_mono (by omega) hπ)
    | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
      simp only [ValueRefinesK] at hv; obtain ⟨rfl, rfl, hargs_rel⟩ := hv; simp only [step]
      split
      · split
        · rename_i rest _
          have hval : ValueRefinesK (m + 1)
              (.VBuiltin b₁ args₁ rest) (.VBuiltin b₁ args₂ rest) := by
            simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs_rel⟩
          exact obsRefinesK_mono (by omega) (hπ (m + 1) (by omega) _ _ hval)
        · exact evalBuiltin_compat_refines hargs_rel (stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ => simp only [step]; exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ => simp only [step]; exact obsRefinesK_error _
    | .VConstr _ _, .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv

  | .Constr tag fields =>
    simp only [substTerm]
    match fields with
    | [] =>
      simp [substTermList]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      have : ValueRefinesK i' (.VConstr tag []) (.VConstr tag []) := by
        cases i' with
        | zero => simp only [ValueRefinesK]
        | succ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial⟩
      exact hπ i' (by omega) _ _ this
    | m :: ms =>
      simp [closedAt] at ht
      have hm : closedAt (d + 1) m = true := by
        have := ht; simp [closedAtList] at this; exact this.1
      have hms : closedAtList (d + 1) ms = true := by
        have := ht; simp [closedAtList] at this; exact this.2
      simp [substTermList]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply substRefinesR_body pos r v_rhs k d m hm hr hpos hposd hrhs
        (i'+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact i' (by omega)
      exact substRefinesConstrField
        (substRefinesR_bodyList pos r v_rhs k d ms tag hms hr hpos hposd hrhs)
        (by omega) (substEnvRef_mono (by omega) henv) hexact
        trivial (stackRefK_mono (by omega) hπ)

  | .Case scrut alts =>
    simp only [substTerm]
    simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply substRefinesR_body pos r v_rhs k d scrut hscrut hr hpos hposd hrhs
      (i'+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact i' (by omega)
    intro j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
      simp only [step]
      have haltsList := substRefinesR_bodyList pos r v_rhs (i'+1) d alts 0 halts hr hpos hposd
        (rHaltsRelN_mono (by omega) hrhs)
      have hlen_eq : (substTermList pos r alts).length = alts.length :=
        substTermList_length _ _ _
      split
      · rename_i alt₁ halt₁
        have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
        have hi₂ : tag₁ < alts.length := hsome₁.1
        have hi₁ : tag₁ < (substTermList pos r alts).length := by
          rw [hlen_eq]; exact hi₂
        have hidx := substTermList_getElem pos r alts tag₁ hi₂
        have halt_subst : (substTermList pos r alts)[tag₁]? =
            some (substTerm pos r (alts[tag₁])) := by
          rw [List.getElem?_eq_some_iff]; exact ⟨hi₁, hidx⟩
        rw [halt_subst]; simp only []
        have heq₁ : alt₁ = alts[tag₁] := hsome₁.2.symm
        subst heq₁
        have halt_shift := listRel_getElem haltsList hi₂
        rw [hidx] at halt_shift
        apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact n (by omega)
        exact applyArgFrames_stackRefK
          (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
          (stackRefK_mono (by omega) hπ)
      · rename_i hnone₁
        have hnone_subst : (substTermList pos r alts)[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff]
          have := (List.getElem?_eq_none_iff.mp hnone₁)
          omega
        rw [hnone_subst]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hv; subst hv
      simp only [step]
      have haltsList := substRefinesR_bodyList pos r v_rhs (i'+1) d alts 0 halts hr hpos hposd
        (rHaltsRelN_mono (by omega) hrhs)
      have hlen_eq : (substTermList pos r alts).length = alts.length :=
        substTermList_length _ _ _
      split
      · rename_i tag numCtors fields htag
        have hif_eq : (decide (numCtors > 0) && decide ((substTermList pos r alts).length > numCtors)) =
            (decide (numCtors > 0) && decide (alts.length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq]; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq]; simp [h_check]
          split
          · rename_i alt₁ halt₁
            have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
            have hi₂ : tag < alts.length := hsome₁.1
            have hi₁ : tag < (substTermList pos r alts).length := by rw [hlen_eq]; exact hi₂
            have hidx := substTermList_getElem pos r alts tag hi₂
            have halt_subst : (substTermList pos r alts)[tag]? =
                some (substTerm pos r (alts[tag])) := by
              rw [List.getElem?_eq_some_iff]; exact ⟨hi₁, hidx⟩
            rw [halt_subst]; simp only []
            have heq₁ : alt₁ = alts[tag] := hsome₁.2.symm
            subst heq₁
            have halt_shift := listRel_getElem haltsList hi₂
            rw [hidx] at halt_shift
            have hfields_vcon := constToTagAndFields_fields_vcon c₁
            rw [htag] at hfields_vcon
            apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (substEnvRef_mono (by omega) henv) hexact n (by omega)
            exact applyArgFrames_stackRefK
              (listRel_refl_vcon_refines n fields hfields_vcon)
              (stackRefK_mono (by omega) hπ)
          · rename_i hnone₁
            have hnone_subst : (substTermList pos r alts)[tag]? = none := by
              rw [List.getElem?_eq_none_iff]
              have := (List.getElem?_eq_none_iff.mp hnone₁)
              omega
            rw [hnone_subst]; simp only []; exact obsRefinesK_error _
      · exact obsRefinesK_error _
    | .VLam _ _, .VLam _ _ | .VDelay _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VBuiltin _ _ _ => simp only [step]; exact obsRefinesK_error _
    | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
    | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
    | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
    | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
    | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
    | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
    | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
    | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
  termination_by sizeOf t

theorem substRefinesR_bodyList
    (pos : Nat) (r : Term) (v_rhs : CekValue)
    (k d : Nat) (ts : List Term) (tag : Nat)
    (hts : closedAtList (d + 1) ts = true)
    (hr : closedAt d r = true)
    (hpos : 1 ≤ pos) (hposd : pos ≤ d + 1)
    (hrhs : RHaltsRelN r v_rhs k d) :
    ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂,
        SubstEnvRef pos v_rhs j (d + 1) ρ₁ ρ₂ →
        ρ₁.lookup pos = some v_rhs →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
      ts (substTermList pos r ts) := by
  match ts, hts with
  | [], _ => simp [substTermList]; trivial
  | t :: rest, hts =>
    simp [closedAtList] at hts
    simp [substTermList]
    exact ⟨fun j hj ρ₁ ρ₂ he hp i hi π₁ π₂ hπ =>
             substRefinesR_body pos r v_rhs k d t hts.1 hr hpos hposd hrhs j hj ρ₁ ρ₂ he hp i hi π₁ π₂ hπ,
           substRefinesR_bodyList pos r v_rhs k d rest tag hts.2 hr hpos hposd hrhs⟩
  termination_by sizeOf ts
end

end MainTheorem

end Moist.Verified.SubstRefines
