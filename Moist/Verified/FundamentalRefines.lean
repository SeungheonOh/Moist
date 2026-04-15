import Moist.Verified.Equivalence
import Moist.Verified.RenameBase
import Moist.Verified.ClosedAt
import Moist.Verified.Definitions.StepIndexed
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Semantics

/-! # Generalized renaming refinement (FTLR + shift unified)

This module provides `renameRefines`, a generalized fundamental theorem
of the logical relation parameterized by a 0-preserving renaming
function `r : Nat → Nat`.

## Specializations

* For `r = id`, `renameTerm id t = t` and `renameRefines` collapses to
  the **reflexive FTLR**: any closed term in `EnvRefinesK`-related envs
  has Obs-refining behaviors. Used by ANF normalization soundness.

* For `r = shiftRename c` (with `c ≥ 1`), `renameRefines` recovers the
  **shift compatibility** lemma `shiftRefines` previously inlined in
  `DeadLet.lean`. Used by dead-let elimination soundness.

* Other 0-preserving renamings (e.g. `liftRename` of these) are also
  supported via the same theorem.

## Proof structure

`renameRefines` is a structural recursion on the term, mutually defined
with `renameRefinesList` for the `Constr` / `Case` branches. Each case
performs a single CEK step on both sides, then either returns via the
stack relation (leaf cases) or recurses on a sub-term. The
`Lam`/`Delay` cases lift the renaming via `liftRename r` when descending
under a binder.

The constraint `Is0Preserving r` (i.e. `r 0 = 0` and `r n ≥ 1` for
`n ≥ 1`) is required for `renameEnvRef_extend` to align positions of
the extended environments. `liftRename` always preserves this property,
so the constraint propagates automatically through recursive calls.
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

/-! ## 2. RenameEnvRef — generalized parameterized environment relation -/

/-- Parameterized environment refinement: positions `1..d` of `ρ₂` relate
    via `ValueRefinesK k` to positions `r n` of `ρ₁`. Mirrors the lax
    pattern of the bespoke `ShiftEnvRefK` (allowing `none/none` ghost
    cells) so that downstream proofs that lift through env extensions
    don't need to track exact lengths. -/
def RenameEnvRef (r : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup (r n), ρ₂.lookup n with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

theorem renameEnvRef_mono {r : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRef r k d ρ₁ ρ₂) :
    RenameEnvRef r j d ρ₁ ρ₂ := by
  intro n hn hnd
  have := h n hn hnd
  cases h₁ : ρ₁.lookup (r n) <;> cases h₂ : ρ₂.lookup n <;> simp_all
  exact valueRefinesK_mono hjk _ _ this

/-! ### Lookup helper for env extension -/

/-- `extend` shifts every positive position up by 1: `(ρ.extend v).lookup
    (m + 1) = ρ.lookup m` for `m ≥ 1`. -/
private theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat)
    (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  show (CekEnv.cons v ρ).lookup (m + 1) = ρ.lookup m
  match m, hm with
  | k + 1, _ => rfl

/-- The new top of an `extend`ed env at position 1. -/
private theorem extend_lookup_one (ρ : CekEnv) (v : CekValue) :
    (ρ.extend v).lookup 1 = some v := by
  show (CekEnv.cons v ρ).lookup 1 = some v
  rfl

/-- The unused position 0 always returns `none`. -/
private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  match ρ with
  | .nil => rfl
  | .cons _ _ => rfl

/-- Extending both sides of a `RenameEnvRef`-related pair by related
    values produces a `RenameEnvRef (liftRename r)`-related pair at the
    bumped depth. The 0-preservation hypothesis on `r` is what aligns
    position 1 in the extended envs (since `liftRename r 1 = r 0 + 1
    = 1`). -/
theorem renameEnvRef_extend {r : Nat → Nat} (h_r : Is0Preserving r)
    {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRef r k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRef (Moist.Verified.liftRename r) k (d + 1)
                 (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1
    have hlift : Moist.Verified.liftRename r 1 = 1 := rfl
    rw [hlift, extend_lookup_one ρ₁ v₁, extend_lookup_one ρ₂ v₂]
    exact hv
  · have hn2 : n ≥ 2 := by omega
    -- liftRename r n = r (n - 1) + 1 for n ≥ 2.
    have hlift : Moist.Verified.liftRename r n = r (n - 1) + 1 := by
      match n, hn2 with
      | k + 2, _ =>
        show Moist.Verified.liftRename r (k + 2) = r ((k + 2) - 1) + 1
        rfl
    rw [hlift]
    have hn1' : n - 1 ≥ 1 := by omega
    have hnd' : n - 1 ≤ d := by omega
    have h_rn1 : r (n - 1) ≥ 1 := h_r.2 (n - 1) hn1'
    have h_lhs : (ρ₁.extend v₁).lookup (r (n - 1) + 1) = ρ₁.lookup (r (n - 1)) :=
      extend_lookup_succ ρ₁ v₁ (r (n - 1)) h_rn1
    have h_rhs : (ρ₂.extend v₂).lookup n = ρ₂.lookup (n - 1) := by
      have : n = (n - 1) + 1 := by omega
      rw [this]
      exact extend_lookup_succ ρ₂ v₂ (n - 1) hn1'
    rw [h_lhs, h_rhs]
    exact henv (n - 1) hn1' hnd'

/-! ## 3. Bridge from existing `EnvRefinesK` -/

/-- The strict `EnvRefinesK` always implies the lax `RenameEnvRef id`. -/
theorem envRefinesK_to_renameEnvRef_id {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : EnvRefinesK k d ρ₁ ρ₂) :
    RenameEnvRef id k d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match ρ₁.lookup (id n), ρ₂.lookup n with
       | some v₁, some v₂ => ValueRefinesK k v₁ v₂
       | none, none => True
       | _, _ => False
  simp only [id]
  rw [hl, hr]
  exact hrel

/-- Bridge `EnvRefinesK → RenameEnvRef (shiftRename 1)` on an
    `extend`-ed left env. Generalizes the bespoke
    `envRefinesK_to_shiftEnvRefK`. -/
theorem envRefinesK_to_renameEnvRef_shift {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    {w : CekValue} (h : EnvRefinesK k d ρ₁ ρ₂) :
    RenameEnvRef (Moist.Verified.shiftRename 1) k d (ρ₁.extend w) ρ₂ := by
  intro n hn hnd
  -- shiftRename 1 n = n + 1 for n ≥ 1
  have hsr : Moist.Verified.shiftRename 1 n = n + 1 := by
    simp [Moist.Verified.shiftRename]; omega
  obtain ⟨v₁, v₂, hl, hr, hrel⟩ := h n hn hnd
  show match (ρ₁.extend w).lookup (Moist.Verified.shiftRename 1 n), ρ₂.lookup n with
       | some v₁, some v₂ => ValueRefinesK k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hsr, extend_lookup_succ ρ₁ w n hn, hl, hr]
  exact hrel

/-! ## 4. Stack frame builder for the `Constr` case -/

/-- `StackRefK` builder for a `.constrField` frame. Mirror of
    `shiftRefinesConstrField` parameterized by the renaming. -/
private theorem renameRefinesConstrField {r : Nat → Nat}
    {d tag k : Nat} {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef r j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      RenameEnvRef r j d ρ₁ ρ₂ → ListRel (ValueRefinesK j) done₁ done₂ →
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
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (renameEnvRef_mono (by omega) henv)
      (show ListRel (ValueRefinesK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone⟩)
      (stackRefK_mono (by omega) hπ)

/-! ## 5. The main theorem: `renameRefines`

Mutual structural induction on terms, mirroring the existing
`shiftRefines` but generalized to an arbitrary 0-preserving renaming. -/

mutual

/-- Generalized renaming refinement: `t` evaluated under `(ρ₁, π₁)` with
    its variables renamed via `r` Obs-refines `t` evaluated under
    `(ρ₂, π₂)`, when the environments are `RenameEnvRef r`-related and
    the stacks are `StackRefK ValueRefinesK`-related. -/
def renameRefines (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef r j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (Moist.Verified.renameTerm r t))
          (.compute π₂ ρ₂ t) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match t with
  | .Var n =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    simp [closedAt] at ht
    by_cases hn : n = 0
    · subst hn
      have h_r0 : r 0 = 0 := h_r.1
      have h1 : ρ₁.lookup 0 = none := lookup_zero ρ₁
      have h2 : ρ₂.lookup 0 = none := lookup_zero ρ₂
      simp [h_r0, h1, h2]
      exact obsRefinesK_error _
    · have h_n := henv n (by omega) ht
      revert h_n
      cases ρ₁.lookup (r n) <;>
        cases ρ₂.lookup n <;> intro h_n
      · exact obsRefinesK_error _
      · exact absurd h_n id
      · exact absurd h_n id
      · exact hπ i' (by omega) _ _
          (valueRefinesK_mono (by omega : i' ≤ j) _ _ h_n)
  | .Constant c' =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ => simp only [ValueRefinesK])
  | .Builtin b =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
      | succ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial, trivial⟩)
  | .Error =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp [step]; exact obsRefinesK_error _
  | .Lam name body =>
    simp only [Moist.Verified.renameTerm]
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
        intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
        exact renameRefines (Moist.Verified.liftRename r) (is0preserving_lift r) (d + 1)
          body ht j' j' (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
          (renameEnvRef_extend h_r (renameEnvRef_mono (by omega) henv) hargs)
          ib hib π₁' π₂' hπ')
  | .Delay body =>
    simp only [Moist.Verified.renameTerm]
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
        exact renameRefines r h_r d body ht j'
          j' (Nat.le_refl _) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv)
          ib hib π₁' π₂' hπ')
  | .Apply f x =>
    simp only [Moist.Verified.renameTerm]
    simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefines r h_r d f hf (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) i' (by omega)
    intro i₁ hi₁ v₁ v₂ hv
    match i₁ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₁ + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefines r h_r d x hx (m₁+1)
      (m₁+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) m₁ (by omega)
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
    simp only [Moist.Verified.renameTerm]
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefines r h_r d e ht (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) i' (by omega)
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
    simp only [Moist.Verified.renameTerm]
    match fields with
    | [] =>
      simp [Moist.Verified.renameTermList]
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
      have hm : closedAt d m = true := by
        have := ht; simp [closedAtList] at this; exact this.1
      have hms : closedAtList d ms = true := by
        have := ht; simp [closedAtList] at this; exact this.2
      simp [Moist.Verified.renameTermList]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply renameRefines r h_r d m hm (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) i' (by omega)
      exact renameRefinesConstrField (renameRefinesList r h_r d ms hms (i'+1))
        (by omega) (renameEnvRef_mono (by omega) henv) trivial (stackRefK_mono (by omega) hπ)
  | .Case scrut alts =>
    simp only [Moist.Verified.renameTerm]
    simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefines r h_r d scrut hscrut (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) i' (by omega)
    intro j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
      simp only [step]
      split
      · rename_i alt₁ halt₁
        have hlen_eq : (Moist.Verified.renameTermList r alts).length = alts.length :=
          Moist.Verified.renameTermList_length _ _
        have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
        have hi₁ : tag₁ < (Moist.Verified.renameTermList r alts).length := hsome₁.1
        have hi₂ : tag₁ < alts.length := by omega
        have halt₂ : alts[tag₁]? = some (alts[tag₁]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
        rw [halt₂]; simp only []
        have hidx : (Moist.Verified.renameTermList r alts)[tag₁]'hi₁ =
            Moist.Verified.renameTerm r (alts[tag₁]) :=
          Moist.Verified.renameTermList_getElem _ _ _ hi₂
        have heq₁ : alt₁ = Moist.Verified.renameTerm r (alts[tag₁]) := by
          have := hsome₁.2; rw [hidx] at this; exact this.symm
        rw [heq₁]
        have haltsList := renameRefinesList r h_r d alts halts (i'+1)
        have halt_shift := listRel_getElem haltsList
          (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
        rw [hidx] at halt_shift
        apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) n (by omega)
        exact applyArgFrames_stackRefK
          (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
          (stackRefK_mono (by omega) hπ)
      · rename_i hnone₁
        have hlen_eq : (Moist.Verified.renameTermList r alts).length = alts.length :=
          Moist.Verified.renameTermList_length _ _
        have hnone₂ : alts[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
        rw [hnone₂]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hv; subst hv
      simp only [step]
      have hlen_eq : (Moist.Verified.renameTermList r alts).length = alts.length :=
        Moist.Verified.renameTermList_length _ _
      split
      · rename_i tag numCtors fields htag
        have hif_eq : (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList r alts).length > numCtors)) =
            (decide (numCtors > 0) && decide (alts.length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]
          split
          · rename_i alt₁ halt₁
            have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
            have hi₁ : tag < (Moist.Verified.renameTermList r alts).length := hsome₁.1
            have hi₂ : tag < alts.length := by omega
            have halt₂ : alts[tag]? = some (alts[tag]) := List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
            rw [halt₂]; simp only []
            have hidx : (Moist.Verified.renameTermList r alts)[tag]'hi₁ =
                Moist.Verified.renameTerm r (alts[tag]) :=
              Moist.Verified.renameTermList_getElem _ _ _ hi₂
            have heq₁ : alt₁ = Moist.Verified.renameTerm r (alts[tag]) := by
              have := hsome₁.2; rw [hidx] at this; exact this.symm
            rw [heq₁]
            have haltsList := renameRefinesList r h_r d alts halts (i'+1)
            have halt_shift := listRel_getElem haltsList
              (by rw [Moist.Verified.renameTermList_length]; exact hi₂)
            rw [hidx] at halt_shift
            apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (renameEnvRef_mono (by omega) henv) n (by omega)
            have hfields_vcon := constToTagAndFields_fields_vcon c₁
            rw [htag] at hfields_vcon
            exact applyArgFrames_stackRefK
              (listRel_refl_vcon_refines n fields hfields_vcon)
              (stackRefK_mono (by omega) hπ)
          · rename_i hnone₁
            have hnone₂ : alts[tag]? = none := by
              rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
            rw [hnone₂]; simp only []; exact obsRefinesK_error _
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

/-- List version of `renameRefines`: each element of the renamed list is
    related to the corresponding element of the original list. -/
def renameRefinesList (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (ts : List Term) (hts : closedAtList d ts = true) (k : Nat) :
    ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef r j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
      (Moist.Verified.renameTermList r ts) ts := by
  match ts, hts with
  | [], _ => simp [Moist.Verified.renameTermList]; trivial
  | t :: rest, hts =>
    simp [closedAtList] at hts
    simp [Moist.Verified.renameTermList]
    exact ⟨renameRefines r h_r d t hts.1 k, renameRefinesList r h_r d rest hts.2 k⟩
  termination_by sizeOf ts

end

/-! ## 6. Specializations -/

/-- The reflexive **fundamental theorem of the logical relation**:
    a closed term Obs-refines itself in `EnvRefinesK`-related envs. -/
theorem ftlr (d : Nat) (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, EnvRefinesK j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i (.compute π₁ ρ₁ t) (.compute π₂ ρ₂ t) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  have h := renameRefines id is0preserving_id d t ht k j hj ρ₁ ρ₂
    (envRefinesK_to_renameEnvRef_id henv) i hi π₁ π₂ hπ
  -- renameTerm id t = t
  have hid : Moist.Verified.renameTerm id t = t := Moist.Verified.renameTerm_id t
  rw [hid] at h
  exact h

/-- Specialization to the shift-1 case, replacing the bespoke
    `shiftRefines` previously defined inside `DeadLet.lean`. -/
theorem renameRefines_shift1 (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRef (Moist.Verified.shiftRename 1) j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t))
          (.compute π₂ ρ₂ t) :=
  renameRefines (Moist.Verified.shiftRename 1) (is0preserving_shiftRename (by omega)) d t ht k

/-! ## 7. Right-side renaming refinement

The dual of `renameRefines` where the renamed term is on the **right** side
of the refinement instead of the left. This is the version needed for
let-hoist primitives' forward directions where the "shifted" form appears
on the RHS of `MIRRefines` (because the inner expression is now under an
extra binder).

The relation `RenameEnvRefR r d ρ₁ ρ₂` says: for `n ∈ [1,d]`, `ρ₁.lookup n`
relates via `ValueRefinesK` to `ρ₂.lookup (r n)`. Note the order in
the value relation: LHS-side value first, RHS-side value second — opposite
position-wise from `RenameEnvRef`, but matching the orientation of the
refinement conclusion. -/

def RenameEnvRefR (r : Nat → Nat) (k d : Nat) (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    match ρ₁.lookup n, ρ₂.lookup (r n) with
    | some v₁, some v₂ => ValueRefinesK k v₁ v₂
    | none, none => True
    | _, _ => False

theorem renameEnvRefR_mono {r : Nat → Nat} {j k d : Nat} (hjk : j ≤ k)
    {ρ₁ ρ₂ : CekEnv} (h : RenameEnvRefR r k d ρ₁ ρ₂) :
    RenameEnvRefR r j d ρ₁ ρ₂ := by
  intro n hn hnd
  have := h n hn hnd
  cases h₁ : ρ₁.lookup n <;> cases h₂ : ρ₂.lookup (r n) <;> simp_all
  exact valueRefinesK_mono hjk _ _ this

/-- Extending both sides of a `RenameEnvRefR`-related pair by related
    values produces a `RenameEnvRefR (liftRename r)`-related pair at the
    bumped depth. -/
theorem renameEnvRefR_extend {r : Nat → Nat} (h_r : Is0Preserving r)
    {k d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (henv : RenameEnvRefR r k d ρ₁ ρ₂) (hv : ValueRefinesK k v₁ v₂) :
    RenameEnvRefR (Moist.Verified.liftRename r) k (d + 1)
                  (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · subst hn1
    have hlift : Moist.Verified.liftRename r 1 = 1 := rfl
    rw [hlift, extend_lookup_one ρ₁ v₁, extend_lookup_one ρ₂ v₂]
    exact hv
  · have hn2 : n ≥ 2 := by omega
    have hlift : Moist.Verified.liftRename r n = r (n - 1) + 1 := by
      match n, hn2 with
      | k + 2, _ =>
        show Moist.Verified.liftRename r (k + 2) = r ((k + 2) - 1) + 1
        rfl
    rw [hlift]
    have hn1' : n - 1 ≥ 1 := by omega
    have hnd' : n - 1 ≤ d := by omega
    have h_rn1 : r (n - 1) ≥ 1 := h_r.2 (n - 1) hn1'
    have h_lhs : (ρ₁.extend v₁).lookup n = ρ₁.lookup (n - 1) := by
      have : n = (n - 1) + 1 := by omega
      rw [this]
      exact extend_lookup_succ ρ₁ v₁ (n - 1) hn1'
    have h_rhs : (ρ₂.extend v₂).lookup (r (n - 1) + 1) = ρ₂.lookup (r (n - 1)) :=
      extend_lookup_succ ρ₂ v₂ (r (n - 1)) h_rn1
    rw [h_lhs, h_rhs]
    exact henv (n - 1) hn1' hnd'

/-- Bridge `EnvRefinesK → RenameEnvRefR (shiftRename 1)` on an
    `extend`-ed RIGHT env. The dual of `envRefinesK_to_renameEnvRef_shift`. -/
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

/-- Stack frame builder for the `Constr` case (right-side variant). -/
private theorem renameRefinesRConstrField {r : Nat → Nat}
    {d tag k : Nat} {ms₁ ms₂ : List Term} {ρ₁ ρ₂ : CekEnv}
    (hfields : ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR r j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂)) ms₁ ms₂) :
    ∀ {j}, j ≤ k → ∀ {done₁ done₂ π₁ π₂},
      RenameEnvRefR r j d ρ₁ ρ₂ → ListRel (ValueRefinesK j) done₁ done₂ →
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
    intro j hj done₁ done₂ π₁ π₂ henv hdone hπ j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply hm (n + 1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) n (by omega)
    exact ih hfs (by omega : n ≤ k)
      (renameEnvRefR_mono (by omega) henv)
      (show ListRel (ValueRefinesK n) (v₁ :: done₁) (v₂ :: done₂) from
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
         listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hdone⟩)
      (stackRefK_mono (by omega) hπ)

mutual

/-- Right-side renaming refinement: `t` evaluated under `(ρ₁, π₁)` Obs-refines
    `renameTerm r t` evaluated under `(ρ₂, π₂)`, when `RenameEnvRefR r d ρ₁ ρ₂`
    holds (i.e., `ρ₂` is the renamed/shifted view of `ρ₁`).

    The proof structure is a mirror of `renameRefines` with the renamed term
    on the right side of the refinement. -/
def renameRefinesR (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR r j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ t)
          (.compute π₂ ρ₂ (Moist.Verified.renameTerm r t)) := by
  intro j hj ρ₁ ρ₂ henv i hi π₁ π₂ hπ
  match t with
  | .Var n =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    simp [closedAt] at ht
    by_cases hn : n = 0
    · subst hn
      have h_r0 : r 0 = 0 := h_r.1
      have h1 : ρ₁.lookup 0 = none := lookup_zero ρ₁
      have h2 : ρ₂.lookup 0 = none := lookup_zero ρ₂
      simp [h_r0, h1, h2]
      exact obsRefinesK_error _
    · have h_n := henv n (by omega) ht
      -- henv : RenameEnvRefR r d ρ₁ ρ₂
      -- so h_n : match ρ₁.lookup n, ρ₂.lookup (r n) with ...
      revert h_n
      cases ρ₁.lookup n <;>
        cases ρ₂.lookup (r n) <;> intro h_n
      · exact obsRefinesK_error _
      · exact absurd h_n id
      · exact absurd h_n id
      · -- h_n : ValueRefinesK j v₁ v₂ where v₁ from ρ₁, v₂ from ρ₂.
        exact hπ i' (by omega) _ _
          (valueRefinesK_mono (by omega : i' ≤ j) _ _ h_n)
  | .Constant c' =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]
      | succ => simp only [ValueRefinesK])
  | .Builtin b =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    exact hπ i' (by omega) _ _ (by cases i' with
      | zero => simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
      | succ => simp only [ValueRefinesK, ListRel]; exact ⟨trivial, trivial, trivial⟩)
  | .Error =>
    simp [Moist.Verified.renameTerm]
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp [step]; exact obsRefinesK_error _
  | .Lam name body =>
    simp only [Moist.Verified.renameTerm]
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
        intro j' hj' arg₁ arg₂ hargs ib hib π₁' π₂' hπ'
        have henv_ext : RenameEnvRefR (Moist.Verified.liftRename r) j' (d + 1)
            (ρ₁.extend arg₁) (ρ₂.extend arg₂) :=
          renameEnvRefR_extend h_r (renameEnvRefR_mono (by omega) henv) hargs
        exact renameRefinesR (Moist.Verified.liftRename r) (is0preserving_lift r) (d + 1)
          body ht j' j' (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
          henv_ext ib hib π₁' π₂' hπ')
  | .Delay body =>
    simp only [Moist.Verified.renameTerm]
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
        exact renameRefinesR r h_r d body ht j'
          j' (Nat.le_refl _) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv)
          ib hib π₁' π₂' hπ')
  | .Apply f x =>
    simp only [Moist.Verified.renameTerm]
    simp [closedAt] at ht; obtain ⟨hf, hx⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefinesR r h_r d f hf (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) i' (by omega)
    intro i₁ hi₁ v₁ v₂ hv
    match i₁ with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | m₁ + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefinesR r h_r d x hx (m₁+1)
      (m₁+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) m₁ (by omega)
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
    simp only [Moist.Verified.renameTerm]
    simp [closedAt] at ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefinesR r h_r d e ht (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) i' (by omega)
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
    simp only [Moist.Verified.renameTerm]
    match fields with
    | [] =>
      simp [Moist.Verified.renameTermList]
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
      have hm : closedAt d m = true := by
        have := ht; simp [closedAtList] at this; exact this.1
      have hms : closedAtList d ms = true := by
        have := ht; simp [closedAtList] at this; exact this.2
      simp [Moist.Verified.renameTermList]
      match i with
      | 0 => obsRefinesK_zero_nonhalt_auto
      | i' + 1 =>
      obsRefinesK_of_step_auto
      simp only [step]
      apply renameRefinesR r h_r d m hm (i'+1)
        (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) i' (by omega)
      exact renameRefinesRConstrField (renameRefinesRList r h_r d ms hms (i'+1))
        (by omega) (renameEnvRefR_mono (by omega) henv) trivial (stackRefK_mono (by omega) hπ)
  | .Case scrut alts =>
    simp only [Moist.Verified.renameTerm]
    simp [closedAt] at ht; obtain ⟨hscrut, halts⟩ := ht
    match i with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | i' + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    apply renameRefinesR r h_r d scrut hscrut (i'+1)
      (i'+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) i' (by omega)
    intro j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    match v₁, v₂ with
    | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
      simp only [ValueRefinesK] at hv; obtain ⟨rfl, hfields_v⟩ := hv
      simp only [step]
      split
      · rename_i alt₁ halt₁
        have hlen_eq : alts.length = (Moist.Verified.renameTermList r alts).length :=
          (Moist.Verified.renameTermList_length _ _).symm
        have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
        have hi₁ : tag₁ < alts.length := hsome₁.1
        have hi₂ : tag₁ < (Moist.Verified.renameTermList r alts).length := by omega
        have halt₂ : (Moist.Verified.renameTermList r alts)[tag₁]? =
            some ((Moist.Verified.renameTermList r alts)[tag₁]) :=
          List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
        rw [halt₂]; simp only []
        have hidx : (Moist.Verified.renameTermList r alts)[tag₁]'hi₂ =
            Moist.Verified.renameTerm r (alts[tag₁]) :=
          Moist.Verified.renameTermList_getElem _ _ _ hi₁
        have heq₁ : alt₁ = alts[tag₁] := by
          have := hsome₁.2; exact this.symm
        rw [heq₁, hidx]
        have haltsList := renameRefinesRList r h_r d alts halts (i'+1)
        have halt_shift := listRel_getElem haltsList hi₁
        rw [hidx] at halt_shift
        apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) n (by omega)
        exact applyArgFrames_stackRefK
          (listRel_mono (fun a b h => valueRefinesK_mono (by omega) a b h) hfields_v)
          (stackRefK_mono (by omega) hπ)
      · rename_i hnone₁
        have hlen_eq : alts.length = (Moist.Verified.renameTermList r alts).length :=
          (Moist.Verified.renameTermList_length _ _).symm
        have hnone₂ : (Moist.Verified.renameTermList r alts)[tag₁]? = none := by
          rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
        rw [hnone₂]; simp only []; exact obsRefinesK_error _
    | .VCon c₁, .VCon c₂ =>
      simp only [ValueRefinesK] at hv; subst hv
      simp only [step]
      have hlen_eq : alts.length = (Moist.Verified.renameTermList r alts).length :=
        (Moist.Verified.renameTermList_length _ _).symm
      split
      · rename_i tag numCtors fields htag
        have hif_eq : (decide (numCtors > 0) && decide (alts.length > numCtors)) =
            (decide (numCtors > 0) && decide ((Moist.Verified.renameTermList r alts).length > numCtors)) := by
          rw [hlen_eq]
        split
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]; exact obsRefinesK_error _
        · rename_i h_check
          rw [hif_eq] at h_check; simp [h_check]
          split
          · rename_i alt₁ halt₁
            have hsome₁ := List.getElem?_eq_some_iff.mp halt₁
            have hi₁ : tag < alts.length := hsome₁.1
            have hi₂ : tag < (Moist.Verified.renameTermList r alts).length := by omega
            have halt₂ : (Moist.Verified.renameTermList r alts)[tag]? =
                some ((Moist.Verified.renameTermList r alts)[tag]) :=
              List.getElem?_eq_some_iff.mpr ⟨hi₂, rfl⟩
            rw [halt₂]; simp only []
            have hidx : (Moist.Verified.renameTermList r alts)[tag]'hi₂ =
                Moist.Verified.renameTerm r (alts[tag]) :=
              Moist.Verified.renameTermList_getElem _ _ _ hi₁
            have heq₁ : alt₁ = alts[tag] := by
              have := hsome₁.2; exact this.symm
            rw [heq₁, hidx]
            have haltsList := renameRefinesRList r h_r d alts halts (i'+1)
            have halt_shift := listRel_getElem haltsList hi₁
            rw [hidx] at halt_shift
            apply halt_shift (n+1) (by omega) ρ₁ ρ₂ (renameEnvRefR_mono (by omega) henv) n (by omega)
            have hfields_vcon := constToTagAndFields_fields_vcon c₁
            rw [htag] at hfields_vcon
            exact applyArgFrames_stackRefK
              (listRel_refl_vcon_refines n fields hfields_vcon)
              (stackRefK_mono (by omega) hπ)
          · rename_i hnone₁
            have hnone₂ : (Moist.Verified.renameTermList r alts)[tag]? = none := by
              rw [List.getElem?_eq_none_iff] at hnone₁ ⊢; omega
            rw [hnone₂]; simp only []; exact obsRefinesK_error _
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

/-- List version of `renameRefinesR`. -/
def renameRefinesRList (r : Nat → Nat) (h_r : Is0Preserving r) (d : Nat)
    (ts : List Term) (hts : closedAtList d ts = true) (k : Nat) :
    ListRel (fun t₁ t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR r j d ρ₁ ρ₂ →
        ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
          ObsRefinesK i (.compute π₁ ρ₁ t₁) (.compute π₂ ρ₂ t₂))
      ts (Moist.Verified.renameTermList r ts) := by
  match ts, hts with
  | [], _ => simp [Moist.Verified.renameTermList]; trivial
  | t :: rest, hts =>
    simp [closedAtList] at hts
    simp [Moist.Verified.renameTermList]
    exact ⟨renameRefinesR r h_r d t hts.1 k, renameRefinesRList r h_r d rest hts.2 k⟩
  termination_by sizeOf ts

end

/-- Specialization of `renameRefinesR` to the shift-1 case. -/
theorem renameRefinesR_shift1 (d : Nat)
    (t : Term) (ht : closedAt d t = true) (k : Nat) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, RenameEnvRefR (Moist.Verified.shiftRename 1) j d ρ₁ ρ₂ →
      ∀ i ≤ j, ∀ π₁ π₂, StackRefK ValueRefinesK i π₁ π₂ →
        ObsRefinesK i
          (.compute π₁ ρ₁ t)
          (.compute π₂ ρ₂ (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t)) :=
  renameRefinesR (Moist.Verified.shiftRename 1) (is0preserving_shiftRename (by omega)) d t ht k

end Moist.Verified.FundamentalRefines
