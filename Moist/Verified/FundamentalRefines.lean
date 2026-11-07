import Moist.Verified.Equivalence
import Moist.Verified.RenameBase
import Moist.Verified.ClosedAt
import Moist.Verified.Definitions.StepIndexed
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Semantics

/-! # Renaming refinement (fundamental theorem of the logical relation)

`renameRefines2 r₁ r₂` relates `renameTerm r₁ t` (left) to `renameTerm r₂ t`
(right) in environments related through `RenameEnvRef2 r₁ r₂`, for any
0-preserving renamings. Its instances:

* `ftlr` (`r₁ = r₂ = id`): a closed term refines itself;
* `renameRefines r` (`r₂ = id`) / `renameRefinesR r` (`r₁ = id`): the
  renamed term on the left / right, e.g. `shiftRename 1` for dead lets.
-/

namespace Moist.Verified.FundamentalRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines

/-! ## 1. Is0Preserving renamings -/

/-- `r` is **0-preserving** when it sends the unused position 0 to itself
    and keeps all positive indices positive. Both `id` and
    `shiftRename c` (for `c ≥ 1`) satisfy this. -/
def Is0Preserving (r : Nat → Nat) : Prop :=
  r 0 = 0 ∧ ∀ n, n ≥ 1 → r n ≥ 1

theorem is0preserving_id : Is0Preserving id :=
  ⟨rfl, fun _ h => h⟩

theorem is0preserving_shiftRename {c : Nat} (hc : c ≥ 1) :
    Is0Preserving (Moist.Verified.shiftRename c) := by
  refine ⟨?_, ?_⟩
  · show Moist.Verified.shiftRename c 0 = 0
    have hnc : ¬ (0 ≥ c) := by omega
    simp [Moist.Verified.shiftRename, hnc]
  · intro n hn
    show Moist.Verified.shiftRename c n ≥ 1
    by_cases hnc : n ≥ c
    · simp [Moist.Verified.shiftRename, hnc]
    · simp [Moist.Verified.shiftRename, hnc]; omega

/-- `liftRename r` is *always* 0-preserving, regardless of `r`. -/
theorem is0preserving_lift (r : Nat → Nat) :
    Is0Preserving (Moist.Verified.liftRename r) := by
  refine ⟨rfl, ?_⟩
  intro n hn
  match n with
  | 0 => omega
  | 1 =>
    show Moist.Verified.liftRename r 1 ≥ 1
    show (1 : Nat) ≥ 1
    omega
  | k + 2 =>
    show Moist.Verified.liftRename r (k + 2) ≥ 1
    show r (k + 1) + 1 ≥ 1
    omega

/-! ## 2. Renaming environment relations -/

/-- Two-sided renaming environment relation: source position `n ∈ [1,d]` is
    looked up at `r₁ n` on the left and `r₂ n` on the right; both lookups
    succeed with related values or both fail. -/
def RenameEnvRef2 (r₁ r₂ : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (r₁ n), ρ₂.lookup (r₂ n) with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

/-- Left-renaming instance (`r₂ = id`). -/
def RenameEnvRef (r : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (r n), ρ₂.lookup n with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

/-- Right-renaming instance (`r₁ = id`). -/
def RenameEnvRefR (r : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup (r n) with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

theorem renameEnvRef_iff {r : Nat → Nat} {k d : Nat} {ρ₁ ρ₂ : CekEnv} :
    RenameEnvRef r k d ρ₁ ρ₂ ↔ RenameEnvRef2 r id k d ρ₁ ρ₂ := Iff.rfl

theorem renameEnvRefR_iff {r : Nat → Nat} {k d : Nat} {ρ₁ ρ₂ : CekEnv} :
    RenameEnvRefR r k d ρ₁ ρ₂ ↔ RenameEnvRef2 id r k d ρ₁ ρ₂ := Iff.rfl

theorem renameEnvRef2_mono {r₁ r₂ : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRef2 r₁ r₂ k d ρ₁ ρ₂) :
    RenameEnvRef2 r₁ r₂ j d ρ₁ ρ₂ := by
  intro n hn hnd
  have := h n hn hnd
  cases h₁ : ρ₁.lookup (r₁ n) <;> cases h₂ : ρ₂.lookup (r₂ n) <;> simp_all
  exact valueRefinesK_mono hjk _ _ this

theorem renameEnvRef_mono {r : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRef r k d ρ₁ ρ₂) : RenameEnvRef r j d ρ₁ ρ₂ :=
  renameEnvRef2_mono hjk h

theorem renameEnvRefR_mono {r : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRefR r k d ρ₁ ρ₂) : RenameEnvRefR r j d ρ₁ ρ₂ :=
  renameEnvRef2_mono hjk h

private theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat)
    (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  match m, hm with
  | k + 1, _ => rfl

private theorem extend_lookup_one (ρ : CekEnv) (v : CekValue) :
    (ρ.extend v).lookup 1 = some v := rfl

private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

/-- `liftRename r` sends `n ≥ 2` past the new binder. -/
private theorem extend_lookup_lift {r : Nat → Nat} (h_r : Is0Preserving r)
    (ρ : CekEnv) (v : CekValue) (n : Nat) (hn : n ≥ 2) :
    (ρ.extend v).lookup (Moist.Verified.liftRename r n) = ρ.lookup (r (n - 1)) := by
  match n, hn with
  | k + 2, _ => exact extend_lookup_succ ρ v (r (k + 1)) (h_r.2 (k + 1) (by omega))

/-- Extending both environments by related values lifts both renamings. -/
theorem renameEnvRef2_extend {r₁ r₂ : Nat → Nat} (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRef2 r₁ r₂ k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRef2 (Moist.Verified.liftRename r₁) (Moist.Verified.liftRename r₂) k (d + 1)
      (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1; exact hv
  · rw [extend_lookup_lift h₁ ρ₁ v₁ n (by omega), extend_lookup_lift h₂ ρ₂ v₂ n (by omega)]
    exact henv (n - 1) (by omega) (by omega)

theorem renameEnvRef_extend {r : Nat → Nat} (h_r : Is0Preserving r)
    {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRef r k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRef (Moist.Verified.liftRename r) k (d + 1)
                 (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  have h := renameEnvRef2_extend h_r is0preserving_id henv hv
  rwa [Moist.Verified.liftRename_id] at h

theorem renameEnvRefR_extend {r : Nat → Nat} (h_r : Is0Preserving r)
    {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRefR r k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRefR (Moist.Verified.liftRename r) k (d + 1)
                  (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  have h := renameEnvRef2_extend is0preserving_id h_r henv hv
  rwa [Moist.Verified.liftRename_id] at h

/-! ## 3. Bridges from `EnvRefinesK` -/

theorem envRefinesK_to_renameEnvRef2_id {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvRefinesK k d ρ₁ ρ₂) : RenameEnvRef2 id id k d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match ρ₁.lookup n, ρ₂.lookup n with
       | some v₁, some v₂ => ValueRefinesK k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hl, hr]; exact hrel

theorem envRefinesK_to_renameEnvRef_id {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvRefinesK k d ρ₁ ρ₂) : RenameEnvRef id k d ρ₁ ρ₂ :=
  envRefinesK_to_renameEnvRef2_id h

/-- `EnvRefinesK → RenameEnvRef (shiftRename 1)` on an `extend`-ed left env. -/
theorem envRefinesK_to_renameEnvRef_shift {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    {w : CekValue} (h : EnvRefinesK k d ρ₁ ρ₂) :
    RenameEnvRef (Moist.Verified.shiftRename 1) k d (ρ₁.extend w) ρ₂ := by
  intro n hn hnd
  have hsr : Moist.Verified.shiftRename 1 n = n + 1 := by
    simp [Moist.Verified.shiftRename]; omega
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match (ρ₁.extend w).lookup (Moist.Verified.shiftRename 1 n), ρ₂.lookup n with
       | some v₁, some v₂ => ValueRefinesK k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hsr, extend_lookup_succ ρ₁ w n hn, hl, hr]
  exact hrel

/-- `EnvRefinesK → RenameEnvRefR (shiftRename 1)` on an `extend`-ed right env. -/
theorem envRefinesK_to_renameEnvRefR_shift {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    {w : CekValue} (h : EnvRefinesK k d ρ₁ ρ₂) :
    RenameEnvRefR (Moist.Verified.shiftRename 1) k d ρ₁ (ρ₂.extend w) := by
  intro n hn hnd
  have hsr : Moist.Verified.shiftRename 1 n = n + 1 := by
    simp [Moist.Verified.shiftRename]; omega
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match ρ₁.lookup n, (ρ₂.extend w).lookup (Moist.Verified.shiftRename 1 n) with
       | some v₁, some v₂ => ValueRefinesK k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hsr, hl, extend_lookup_succ ρ₂ w n hn, hr]
  exact hrel

/-! ## 4. Stack frame builder for the `Constr` case -/

/-- `StackRefK` builder for a `.constrField` frame, for any monotone
    environment relation `E`. -/
theorem constrField_stackRefK {E : Nat → CekEnv → CekEnv → Prop}
    (E_mono : ∀ {j k ρ₁ ρ₂}, j ≤ k → E k ρ₁ ρ₂ → E j ρ₁ ρ₂)
    {tag k : Nat} {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, E j ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      E j ρ₁ ρ₂ → ListRel (ValueRefinesK j) done₁ done₂ →
      StackRefK ValueRefinesK j π₁ π₂ →
      StackRefK ValueRefinesK j (.constrField tag done₁ ms₁ ρ₁ :: π₁)
                                 (.constrField tag done₂ ms₂ ρ₂ :: π₂) := by
  induction ms₁ generalizing ms₂ with
  | nil =>
    cases ms₂ with
    | cons => exact absurd hfields id
    | nil =>
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
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
      cases n <;> (simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩)
    exact obsRefinesK_mono (by omega) (hπ (n + 1) (by omega) _ _ hval)
  | cons m₁ ms₁' ih =>
    cases ms₂ with
    | nil => exact absurd hfields id
    | cons m₂ ms₂' =>
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply hfields.1 (n + 1) (by omega) ρ₁ ρ₂ (E_mono (by omega) henv) n (by omega)
    exact ih hfields.2 (by omega : n ≤ k) (E_mono (by omega) henv)
      ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
       listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone⟩
      (stackRefK_mono (by omega) hπ)

/-! ## 5. The main theorem: `renameRefines2` -/

private theorem renameTermList_getElem? (r : Nat → Nat) (ts : List Term) (i : Nat) :
    (Moist.Verified.renameTermList r ts)[i]? = ts[i]?.map (Moist.Verified.renameTerm r) := by
  induction ts generalizing i with
  | nil => rfl
  | cons t rest ih => cases i <;> simp [Moist.Verified.renameTermList, ih]

mutual

/-- Two-sided renaming refinement: `renameTerm r₁ t` under `(ρ₁, π₁)`
    Obs-refines `renameTerm r₂ t` under `(ρ₂, π₂)`. -/
theorem renameRefines2 (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁) (h₂ : Is0Preserving r₂)
    (d : Nat) (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef2 r₁ r₂ j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (Moist.Verified.renameTerm r₁ t))
          (.compute π₂ ρ₂ (Moist.Verified.renameTerm r₂ t)) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match i with
  | 0 => obsRefinesK_zero_nonhalt_auto
  | i' + 1 =>
  obsRefinesK_of_step_auto
  match t with
  | .Var n =>
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht
    by_cases hn : n = 0
    · subst hn
      rw [h₁.1, h₂.1, lookup_zero, lookup_zero]
      exact obsRefinesK_error _
    · have h_n := henv n (by omega) ht
      revert h_n
      cases ρ₁.lookup (r₁ n) <;> cases ρ₂.lookup (r₂ n) <;> intro h_n
      · exact obsRefinesK_error _
      · exact absurd h_n id
      · exact absurd h_n id
      · exact hπ i' (by omega) _ _ (valueRefinesK_mono (by omega : i' ≤ j) _ _ h_n)
  | .Constant _ =>
    simp only [Moist.Verified.renameTerm, step]
    exact hπ i' (by omega) _ _ (by cases i' <;> simp only [ValueRefinesK])
  | .Builtin _ =>
    simp only [Moist.Verified.renameTerm, step]
    exact hπ i' (by omega) _ _ (by cases i' <;> simp [ValueRefinesK, ListRel])
  | .Error =>
    simp only [Moist.Verified.renameTerm, step]; exact obsRefinesK_error _
  | .Lam name body =>
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ m =>
        simp only [ValueRefinesK]
        intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
        exact renameRefines2 _ _ (is0preserving_lift r₁) (is0preserving_lift r₂) (d + 1)
          body ht j' j' (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
          (renameEnvRef2_extend h₁ h₂ (renameEnvRef2_mono (by omega) henv) hargs)
          ib hib π₁' π₂' hπ')
  | .Delay body =>
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ m =>
        simp only [ValueRefinesK]
        intro j' hj' ib hib π₁' π₂' hπ'
        exact renameRefines2 r₁ r₂ h₁ h₂ d body ht j' j' (Nat.le_refl _) ρ₁ ρ₂
          (renameEnvRef2_mono (by omega) henv) ib hib π₁' π₂' hπ')
  | .Apply f x =>
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
    apply renameRefines2 r₁ r₂ h₁ h₂ d f hf (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef2_mono (by omega) henv) i' (by omega)
    intro i₁ hi₁ v₁ v₂ hv
    match i₁ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₁ + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefines2 r₁ r₂ h₁ h₂ d x hx (m₁+1)
      (m₁+1) (by omega) ρ₁ ρ₂ (renameEnvRef2_mono (by omega) henv) m₁ (by omega)
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
      have hargs : ListRel (ValueRefinesK m₂) (w₁ :: args₁) (w₂ :: args₂) :=
        ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
         listRel_mono (fun a b h => valueRefinesK_mono (by omega : m₂ ≤ m₁) a b h) hargs_rel⟩
      simp only [step]
      split
      · split
        · rename_i rest _
          exact obsRefinesK_mono (by omega)
            (hπ (m₂ + 1) (by omega) _ _ (by simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs⟩))
        · exact evalBuiltin_compat_refines hargs (stackRefK_mono (by omega) hπ)
      · exact obsRefinesK_error _
    | .VCon _, .VCon _ | .VDelay _ _, .VDelay _ _ | .VConstr _ _, .VConstr _ _ =>
      simp only [step]; exact obsRefinesK_error _
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
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht
    apply renameRefines2 r₁ r₂ h₁ h₂ d e ht (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef2_mono (by omega) henv) i' (by omega)
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
        · exact obsRefinesK_mono (by omega)
            (hπ (m + 1) (by omega) _ _ (by simp only [ValueRefinesK]; exact ⟨trivial, trivial, hargs_rel⟩))
        · exact evalBuiltin_compat_refines hargs_rel (stackRefK_mono (by omega) hπ)
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
    | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
  | .Constr tag [] =>
    simp only [Moist.Verified.renameTerm, Moist.Verified.renameTermList, step]
    exact hπ i' (by omega) _ _ (by cases i' <;> simp [ValueRefinesK, ListRel])
  | .Constr tag (m :: ms) =>
    simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
    simp only [Moist.Verified.renameTerm, Moist.Verified.renameTermList, step]
    apply renameRefines2 r₁ r₂ h₁ h₂ d m ht.1 (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef2_mono (by omega) henv) i' (by omega)
    exact constrField_stackRefK (E := fun j => RenameEnvRef2 r₁ r₂ j d)
      (fun hjk h => renameEnvRef2_mono hjk h)
      (renameRefines2List r₁ r₂ h₁ h₂ d ms ht.2 (i'+1))
      (by omega) (renameEnvRef2_mono (by omega) henv) trivial (stackRefK_mono (by omega) hπ)
  | .Case scrut alts =>
    simp only [Moist.Verified.renameTerm, step]
    simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
    apply renameRefines2 r₁ r₂ h₁ h₂ d scrut hscrut (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef2_mono (by omega) henv) i' (by omega)
    intro j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    -- Dispatch to a related alternative with related field frames.
    have dispatch : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue},
        ListRel (ValueRefinesK n) fs₁ fs₂ →
        ObsRefinesK n
          (match (Moist.Verified.renameTermList r₁ alts)[tag]? with
           | some alt => .compute (fs₁.map Frame.applyArg ++ π₁) ρ₁ alt
           | none => .error)
          (match (Moist.Verified.renameTermList r₂ alts)[tag]? with
           | some alt => .compute (fs₂.map Frame.applyArg ++ π₂) ρ₂ alt
           | none => .error) := by
      intro tag fs₁ fs₂ hfs
      rw [renameTermList_getElem?, renameTermList_getElem?]
      cases halt : alts[tag]? with
      | none => exact obsRefinesK_error _
      | some alt =>
        have hlt := (List.getElem?_eq_some_iff.mp halt).1
        have hrel := listRel_getElem (renameRefines2List r₁ r₂ h₁ h₂ d alts halts (i'+1))
          (by rw [Moist.Verified.renameTermList_length]; exact hlt)
        rw [Moist.Verified.renameTermList_getElem _ _ _ hlt,
          Moist.Verified.renameTermList_getElem _ _ _ hlt,
          (List.getElem?_eq_some_iff.mp halt).2] at hrel
        exact hrel (n+1) (by omega) ρ₁ ρ₂ (renameEnvRef2_mono (by omega) henv) n (by omega)
          _ _ (applyArgFrames_stackRefK hfs (stackRefK_mono (by omega) hπ))
    match v₁, v₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
      simp only [step]
      exact dispatch tag₁ (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hv; subst hv
      simp only [step, Moist.Verified.renameTermList_length]
      cases htag : constToTagAndFields c₁ with
      | none => exact obsRefinesK_error _
      | some triple =>
        obtain ⟨tag, numCtors, fields⟩ := triple
        simp only []
        split
        · exact obsRefinesK_error _
        · have hfields_vcon := constToTagAndFields_fields_vcon c₁
          rw [htag] at hfields_vcon
          exact dispatch tag (listRel_refl_vcon_refines n fields hfields_vcon)
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

theorem renameRefines2List (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) (d : Nat) (ts : List Term) (hts : closedAtList d ts = true)
    (k : Nat) :
    ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef2 r₁ r₂ j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
      (Moist.Verified.renameTermList r₁ ts) (Moist.Verified.renameTermList r₂ ts) := by
  match ts, hts with
  | [], _ => exact trivial
  | t :: rest, hts =>
    simp only [closedAtList, Bool.and_eq_true] at hts
    exact ⟨renameRefines2 r₁ r₂ h₁ h₂ d t hts.1 k,
      renameRefines2List r₁ r₂ h₁ h₂ d rest hts.2 k⟩
  termination_by sizeOf ts

end

/-! ## 6. Specializations -/

/-- Left renaming: `renameTerm r t` on the left refines `t` on the right. -/
theorem renameRefines (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef r j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (Moist.Verified.renameTerm r t))
          (.compute π₂ ρ₂ t) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines2 r id h_r is0preserving_id d t ht k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  rwa [Moist.Verified.renameTerm_id] at h

/-- Right renaming: `t` on the left refines `renameTerm r t` on the right. -/
theorem renameRefinesR (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR r j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ t)
          (.compute π₂ ρ₂ (Moist.Verified.renameTerm r t)) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines2 id r is0preserving_id h_r d t ht k j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  rwa [Moist.Verified.renameTerm_id] at h

/-- The reflexive **fundamental theorem of the logical relation**:
    a closed term Obs-refines itself in `EnvRefinesK`-related envs. -/
theorem ftlr (d : Nat) (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i (.compute π₁ ρ₁ t) (.compute π₂ ρ₂ t) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines2 id id is0preserving_id is0preserving_id d t ht k j hj ρ₁ ρ₂
    (envRefinesK_to_renameEnvRef2_id henv) i hi π₁ π₂ hπ
  rwa [Moist.Verified.renameTerm_id] at h

theorem renameRefines_shift1 (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef (Moist.Verified.shiftRename 1) j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t))
          (.compute π₂ ρ₂ t) :=
  renameRefines (Moist.Verified.shiftRename 1) (is0preserving_shiftRename (by omega)) d t ht k

theorem renameRefinesR_shift1 (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR (Moist.Verified.shiftRename 1) j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ t)
          (.compute π₂ ρ₂ (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t)) :=
  renameRefinesR (Moist.Verified.shiftRename 1) (is0preserving_shiftRename (by omega)) d t ht k

end Moist.Verified.FundamentalRefines
