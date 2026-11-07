import Moist.Verified.Equivalence
import Moist.Verified.RenameBase
import Moist.Verified.ClosedAt
import Moist.Verified.Definitions.StepIndexed
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Semantics

/-! # Renaming refinement (fundamental theorem of the logical relation)

`renameRefinesG W r₁ r₂` relates `renameTerm r₁ t` (left) to `renameTerm r₂ t`
(right) in environments related through `RenameEnvRef2 (ValueRel W) r₁ r₂`,
for any guard `W` and 0-preserving renamings. Its `Guard.trivial` instances:

* `ftlr` (`r₁ = r₂ = id`): a closed term refines itself;
* `renameRefines r` (`r₂ = id`) / `renameRefinesR r` (`r₁ = id`): the
  renamed term on the left / right, e.g. `shiftRename 1` for dead lets.

The well-formedness instance is `FundamentalRefinesWF.ftlr_wf`.
-/

namespace Moist.Verified.FundamentalRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines
open Moist.Verified.Contextual.Guarded

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

/-- Two-sided renaming environment relation over a value relation `V`: source
    position `n ∈ [1,d]` is looked up at `r₁ n` on the left and `r₂ n` on the
    right; both lookups succeed with related values or both fail. -/
def RenameEnvRef2 (V : Nat → CekValue → CekValue → Prop) (r₁ r₂ : Nat → Nat)
    (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (r₁ n), ρ₂.lookup (r₂ n) with
    | some v₁, some v₂ => V k v₁ v₂
    | none, none => True
    | _, _ => False

/-- Left-renaming instance (`RenameEnvRef2 ValueRefinesK r id`). -/
def RenameEnvRef (r : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (r n), ρ₂.lookup n with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

/-- Right-renaming instance (`RenameEnvRef2 ValueRefinesK id r`). -/
def RenameEnvRefR (r : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup (r n) with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

theorem renameEnvRef2_map {V V' : Nat → CekValue → CekValue → Prop}
    {r₁ r₂ : Nat → Nat} {j k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (hV : ∀ v₁ v₂, V k v₁ v₂ → V' j v₁ v₂) (h : RenameEnvRef2 V r₁ r₂ k d ρ₁ ρ₂) :
    RenameEnvRef2 V' r₁ r₂ j d ρ₁ ρ₂ := by
  intro n hn hnd
  have := h n hn hnd
  revert this
  cases ρ₁.lookup (r₁ n) <;> cases ρ₂.lookup (r₂ n) <;> first | exact id | exact hV _ _

theorem renameEnvRef_mono {r : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRef r k d ρ₁ ρ₂) : RenameEnvRef r j d ρ₁ ρ₂ :=
  renameEnvRef2_map (V := ValueRefinesK) (r₂ := id) (fun _ _ => valueRefinesK_mono hjk _ _) h

theorem renameEnvRefR_mono {r : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRefR r k d ρ₁ ρ₂) : RenameEnvRefR r j d ρ₁ ρ₂ :=
  renameEnvRef2_map (V := ValueRefinesK) (r₁ := id) (fun _ _ => valueRefinesK_mono hjk _ _) h

private theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat)
    (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  match m, hm with
  | k + 1, _ => rfl

private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  cases ρ <;> rfl

/-- `liftRename r` sends `n ≥ 2` past the new binder. -/
private theorem extend_lookup_lift {r : Nat → Nat} (h_r : Is0Preserving r)
    (ρ : CekEnv) (v : CekValue) (n : Nat) (hn : n ≥ 2) :
    (ρ.extend v).lookup (Moist.Verified.liftRename r n) = ρ.lookup (r (n - 1)) := by
  match n, hn with
  | k + 2, _ => exact extend_lookup_succ ρ v (r (k + 1)) (h_r.2 (k + 1) (by omega))

/-- Extending both environments by related values lifts both renamings. -/
theorem renameEnvRef2_extend {V : Nat → CekValue → CekValue → Prop}
    {r₁ r₂ : Nat → Nat} (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRef2 V r₁ r₂ k d ρ₁ ρ₂) (hv : V k v₁ v₂) :
    RenameEnvRef2 V (Moist.Verified.liftRename r₁) (Moist.Verified.liftRename r₂) k (d + 1)
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
  have h := renameEnvRef2_extend (V := ValueRefinesK) h_r is0preserving_id henv hv
  rwa [Moist.Verified.liftRename_id] at h

theorem renameEnvRefR_extend {r : Nat → Nat} (h_r : Is0Preserving r)
    {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRefR r k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRefR (Moist.Verified.liftRename r) k (d + 1)
                  (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  have h := renameEnvRef2_extend (V := ValueRefinesK) is0preserving_id h_r henv hv
  rwa [Moist.Verified.liftRename_id] at h

/-! ## 3. Bridges from `EnvRefinesK` -/

/-- A strict environment relation is a renaming relation for `id`. -/
theorem renameEnvRef2_id {V : Nat → CekValue → CekValue → Prop} {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : ∀ n, 0 < n → n ≤ d →
      ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ V k v₁ v₂) :
    RenameEnvRef2 V id id k d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match ρ₁.lookup n, ρ₂.lookup n with
       | some v₁, some v₂ => V k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hl, hr]; exact hrel

theorem envRefinesK_to_renameEnvRef_id {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvRefinesK k d ρ₁ ρ₂) : RenameEnvRef id k d ρ₁ ρ₂ :=
  renameEnvRef2_id h

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

/-! ## 4. The main theorem: `renameRefinesG` -/

mutual

/-- Two-sided renaming refinement under a guard: `renameTerm r₁ t` and
    `renameTerm r₂ t` evaluate to related observations in renaming-related
    environments. -/
theorem renameRefinesG (W : Guard) (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) (d : Nat) (t : Term) (ht : closedAt d t = true) (k : Nat)
    {ρ₁ ρ₂ : CekEnv} (henv : RenameEnvRef2 (ValueRel W) r₁ r₂ k d ρ₁ ρ₂) :
    Eval W k ρ₁ ρ₂ (Moist.Verified.renameTerm r₁ t) (Moist.Verified.renameTerm r₂ t) := by
  have mono : ∀ {j}, j ≤ k → RenameEnvRef2 (ValueRel W) r₁ r₂ j d ρ₁ ρ₂ :=
    fun hj => renameEnvRef2_map (fun _ _ h => valueRel_mono hj h) henv
  match t with
  | .Var n =>
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    simp only [Moist.Verified.renameTerm, step] at hst₁ hst₂ ⊢
    simp [closedAt] at ht
    by_cases hn : n = 0
    · subst hn
      rw [h₁.1, h₂.1, lookup_zero, lookup_zero]
      exact obsRefinesK_error_error j
    · have h_n := henv n (by omega) ht
      revert h_n hst₁ hst₂
      cases ρ₁.lookup (r₁ n) <;> cases ρ₂.lookup (r₂ n) <;> intro hst₁ hst₂ h_n
      · exact obsRefinesK_error_error j
      · exact absurd h_n id
      · exact absurd h_n id
      · exact ret_obs (valueRel_mono (by omega) h_n) hst₁ hst₂ hπ
  | .Constant _ =>
    exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ => ret_obs (valueRel_vcon j _) hst₁ hst₂ hπ
  | .Builtin _ =>
    exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
      ret_obs (valueRel_builtin (k := j) trivial) hst₁ hst₂ hπ
  | .Error => exact eval_of_step fun j _ _ _ _ _ _ => obsRefinesK_error_error j
  | .Lam _ body =>
    simp only [closedAt] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    refine ret_obs (valueRel_lam (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
      fun j' hj' a₁ a₂ ha _ _ => ?_) hst₁ hst₂ hπ
    exact renameRefinesG W _ _ (is0preserving_lift r₁) (is0preserving_lift r₂) (d + 1) body ht j'
      (renameEnvRef2_extend h₁ h₂ (mono (by omega)) ha)
  | .Delay body =>
    simp only [closedAt] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact ret_obs (valueRel_delay (W.ret.mp hst₁).2 (W.ret.mp hst₂).2
      fun j' hj' => renameRefinesG W r₁ r₂ h₁ h₂ d body ht j' (mono (by omega))) hst₁ hst₂ hπ
  | .Apply f x =>
    simp only [closedAt, Bool.and_eq_true] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact renameRefinesG W r₁ r₂ h₁ h₂ d f ht.1 j (mono (by omega)) j (Nat.le_refl _) _ _
      (arg_stackRel (renameRefinesG W r₁ r₂ h₁ h₂ d x ht.2 j (mono (by omega)))
        (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  | .Force e =>
    simp only [closedAt] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact renameRefinesG W r₁ r₂ h₁ h₂ d e ht j (mono (by omega)) j (Nat.le_refl _) _ _
      (force_stackRel hπ) hst₁ hst₂
  | .Constr tag [] =>
    exact eval_of_step fun j _ _ _ hπ hst₁ hst₂ =>
      ret_obs (valueRel_constr (k := j) trivial) hst₁ hst₂ hπ
  | .Constr tag (m :: ms) =>
    simp only [closedAt, closedAtList, Bool.and_eq_true] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact renameRefinesG W r₁ r₂ h₁ h₂ d m ht.1 j (mono (by omega)) j (Nat.le_refl _) _ _
      (constrField_stackRel (renameRefinesGList W r₁ r₂ h₁ h₂ d ms ht.2 j (mono (by omega)))
        trivial (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  | .Case scrut alts =>
    simp only [closedAt, Bool.and_eq_true] at ht
    refine eval_of_step fun j hj π₁ π₂ hπ hst₁ hst₂ => ?_
    exact renameRefinesG W r₁ r₂ h₁ h₂ d scrut ht.1 j (mono (by omega)) j (Nat.le_refl _) _ _
      (case_stackRel (altsRel_of_listRel
          (renameRefinesGList W r₁ r₂ h₁ h₂ d alts ht.2 j (mono (by omega))))
        (W.compute hst₁) (W.compute hst₂) hπ) hst₁ hst₂
  termination_by sizeOf t

theorem renameRefinesGList (W : Guard) (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) (d : Nat) (ts : List Term) (hts : closedAtList d ts = true)
    (k : Nat) {ρ₁ ρ₂ : CekEnv} (henv : RenameEnvRef2 (ValueRel W) r₁ r₂ k d ρ₁ ρ₂) :
    ListRel (Eval W k ρ₁ ρ₂)
      (Moist.Verified.renameTermList r₁ ts) (Moist.Verified.renameTermList r₂ ts) := by
  match ts, hts with
  | [], _ => exact trivial
  | t :: rest, hts =>
    simp only [closedAtList, Bool.and_eq_true] at hts
    exact ⟨renameRefinesG W r₁ r₂ h₁ h₂ d t hts.1 k henv,
      renameRefinesGList W r₁ r₂ h₁ h₂ d rest hts.2 k henv⟩
  termination_by sizeOf ts

end

/-! ## 5. `Guard.trivial` specializations -/

/-- `renameRefinesG` at `Guard.trivial`, stated with `ValueRefinesK` / `StackRefK`. -/
private theorem renameRefines_trivial (r₁ r₂ : Nat → Nat) (h₁ : Is0Preserving r₁)
    (h₂ : Is0Preserving r₂) (d : Nat) (t : Term) (ht : closedAt d t = true)
    {j : Nat} {ρ₁ ρ₂ : CekEnv} (henv : RenameEnvRef2 ValueRefinesK r₁ r₂ j d ρ₁ ρ₂)
    {i : Nat} (hi : i ≤ j) {π₁ π₂ : Stack} (hπ : StackRefK ValueRefinesK i π₁ π₂) :
    ObsRefinesK i (.compute π₁ ρ₁ (Moist.Verified.renameTerm r₁ t))
      (.compute π₂ ρ₂ (Moist.Verified.renameTerm r₂ t)) :=
  renameRefinesG Guard.trivial r₁ r₂ h₁ h₂ d t ht j
    (renameEnvRef2_map (fun a b h => (valueRel_trivial j a b).mpr h) henv) i hi π₁ π₂
    (stackRefK_iff_stackRel.mp hπ) trivial trivial

/-- Left renaming: `renameTerm r t` on the left refines `t` on the right. -/
theorem renameRefines (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef r j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (Moist.Verified.renameTerm r t))
          (.compute π₂ ρ₂ t) := by
  intro j _ ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines_trivial r id h_r is0preserving_id d t ht henv hi hπ
  rwa [Moist.Verified.renameTerm_id] at h

/-- Right renaming: `t` on the left refines `renameTerm r t` on the right. -/
theorem renameRefinesR (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR r j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ t)
          (.compute π₂ ρ₂ (Moist.Verified.renameTerm r t)) := by
  intro j _ ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines_trivial id r is0preserving_id h_r d t ht henv hi hπ
  rwa [Moist.Verified.renameTerm_id] at h

/-- The reflexive **fundamental theorem of the logical relation**:
    a closed term Obs-refines itself in `EnvRefinesK`-related envs. -/
theorem ftlr (d : Nat) (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i (.compute π₁ ρ₁ t) (.compute π₂ ρ₂ t) := by
  intro j _ ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines_trivial id id is0preserving_id is0preserving_id d t ht
    (renameEnvRef2_id henv) hi hπ
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
