import Moist.Verified.Definitions.StepIndexed
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.ClosedAt
import Moist.Verified.RenameBase
import Moist.Verified.StepLift
import Moist.Verified.FundamentalRefines

/-! # Infrastructure for the step-indexed β-value refinement

This module collects the foundational lemmas used by the step-indexed
substitution proof of the UPLC β-value rule:

  `Apply (Lam n body) v_rhs  ⊑  substTerm 1 v_rhs body`   (when `v_rhs` is a value)

The main (downstream) theorem is not stated here — this file hosts only
the infrastructure pieces:

* `closedAt_rename`, `closedAtList_renameTermList` — closedness is
  preserved under variable renamings that respect the depth bound.

* `closedAt_substTerm`, `closedAtList_substTermList` — closedness is
  preserved under UPLC-level open substitution.

* `SubstEnvRef` — the logical relation between two CEK environments
  which differ by one "substituted" position: `ρ₁` has an extra
  binding at position `pos`, which is related (via `ValueRefinesK`)
  to a stand-alone value `v_rhs` supplied from outside, and every
  other position of `ρ₁` is related to the corresponding (possibly
  shifted) position of `ρ₂`.

* `substEnvRef_mono`, `substEnvRef_extend` — monotonicity in the step
  index and preservation under simultaneous `.extend` on both sides.

* `vstep_eq` — propositional equality bridge between the two
  syntactically distinct copies of `steps` that appear in the
  codebase (`Verified.Equivalence.steps` and `Verified.Semantics.steps`).

* `value_stack_poly` — lift a halt-witness / no-error witness from the
  empty stack to an arbitrary stack, using `StepLift.steps_liftState`.

* `extend_lookup_succ`, `extend_lookup_one`, `lookup_zero` — standard
  `CekEnv` lookup identities re-exposed at the module level (they are
  `private` in `FundamentalRefines`).
-/

namespace Moist.Verified.BetaValueRefines

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual.SoundnessRefines

--------------------------------------------------------------------------------
-- 1. Standard CekEnv lookup identities
--
-- These mirror the `private` helpers in `FundamentalRefines.lean`. Re-exposed
-- here so downstream callers (the main β-value refinement proof in a sibling
-- file) do not need to reach into that module's private namespace.
--------------------------------------------------------------------------------

/-- The unused position 0 always returns `none`. -/
theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  match ρ with
  | .nil => rfl
  | .cons _ _ => rfl

/-- The new top of an `extend`ed env at position 1. -/
theorem extend_lookup_one (ρ : CekEnv) (v : CekValue) :
    (ρ.extend v).lookup 1 = some v := by
  show (CekEnv.cons v ρ).lookup 1 = some v
  rfl

/-- `extend` shifts every positive position up by 1: `(ρ.extend v).lookup
    (m + 1) = ρ.lookup m` for `m ≥ 1`. -/
theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat)
    (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  show (CekEnv.cons v ρ).lookup (m + 1) = ρ.lookup m
  match m, hm with
  | k + 1, _ => rfl

--------------------------------------------------------------------------------
-- 2. closedAt under renaming
--
-- If `t` is closed at depth `d` and a renaming `σ` maps every `n ≤ d` to a
-- value ≤ `d'`, then `renameTerm σ t` is closed at depth `d'`. Under a `Lam`
-- the depth bumps by 1 on both sides and `σ` is lifted to `liftRename σ`,
-- which preserves the "≤" respect property.
--------------------------------------------------------------------------------

/-- Lifting preserves a bound-respecting renaming. -/
private theorem liftRename_preserves_bound {σ : Nat → Nat} {d d' : Nat}
    (h_σ : ∀ n, n ≤ d → σ n ≤ d') :
    ∀ n, n ≤ d + 1 → liftRename σ n ≤ d' + 1 := by
  intro n hn
  match n with
  | 0 => exact Nat.zero_le _
  | 1 => simp [liftRename]
  | k + 2 =>
    simp only [liftRename]
    have : k + 1 ≤ d := by omega
    have := h_σ (k + 1) this
    omega

mutual

/-- Closedness is preserved under renaming, provided the renaming respects
    the depth bound. -/
theorem closedAt_rename :
    ∀ (σ : Nat → Nat) (t : Term) (d d' : Nat),
      closedAt d t = true →
      (∀ n, n ≤ d → σ n ≤ d') →
      closedAt d' (renameTerm σ t) = true
  | σ, .Var n, d, d', h, h_σ => by
    simp only [renameTerm, closedAt, decide_eq_true_eq] at h ⊢
    exact h_σ n h
  | σ, .Lam _ body, d, d', h, h_σ => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_rename (liftRename σ) body (d + 1) (d' + 1) h
      (liftRename_preserves_bound h_σ)
  | σ, .Apply f x, d, d', h, h_σ => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_rename σ f d d' h.1 h_σ,
           closedAt_rename σ x d d' h.2 h_σ⟩
  | σ, .Force e, d, d', h, h_σ => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_rename σ e d d' h h_σ
  | σ, .Delay e, d, d', h, h_σ => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAt_rename σ e d d' h h_σ
  | σ, .Constr _ args, d, d', h, h_σ => by
    simp only [renameTerm, closedAt] at h ⊢
    exact closedAtList_renameTermList σ args d d' h h_σ
  | σ, .Case scrut alts, d, d', h, h_σ => by
    simp only [renameTerm, closedAt, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_rename σ scrut d d' h.1 h_σ,
           closedAtList_renameTermList σ alts d d' h.2 h_σ⟩
  | _, .Constant _, _, _, _, _ => by simp [closedAt, renameTerm]
  | _, .Builtin _, _, _, _, _ => by simp [closedAt, renameTerm]
  | _, .Error, _, _, _, _ => by simp [closedAt, renameTerm]
termination_by σ t _ _ _ _ => sizeOf t

/-- List version of `closedAt_rename`. -/
theorem closedAtList_renameTermList :
    ∀ (σ : Nat → Nat) (ts : List Term) (d d' : Nat),
      closedAtList d ts = true →
      (∀ n, n ≤ d → σ n ≤ d') →
      closedAtList d' (renameTermList σ ts) = true
  | _, [], _, _, _, _ => by simp [closedAtList, renameTermList]
  | σ, t :: rest, d, d', h, h_σ => by
    simp only [closedAtList, renameTermList, Bool.and_eq_true] at h ⊢
    exact ⟨closedAt_rename σ t d d' h.1 h_σ,
           closedAtList_renameTermList σ rest d d' h.2 h_σ⟩
termination_by σ ts _ _ _ _ => sizeOf ts

end

--------------------------------------------------------------------------------
-- 3. closedAt under substitution
--
-- If `r` is closed at depth `d` and `t` is closed at depth `d + 1` (we're
-- substituting away one binder), then `substTerm pos r t` is closed at
-- depth `d`. This is the runtime analogue of the "substitution preserves
-- typing" lemma for our open-semantics β-reduction.
--------------------------------------------------------------------------------

mutual

/-- Closedness is preserved under UPLC open substitution. -/
theorem closedAt_substTerm :
    ∀ (pos : Nat) (r : Term) (t : Term) (d : Nat),
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d r = true →
      closedAt (d + 1) t = true →
      closedAt d (substTerm pos r t) = true
  | pos, r, .Var n, d, hpos, hposd, hr, ht => by
    simp only [substTerm]
    by_cases hn_eq : n = pos
    · simp [hn_eq, hr]
    · simp only [hn_eq, if_false]
      by_cases hn_gt : n > pos
      · simp only [hn_gt, if_true]
        simp only [closedAt, decide_eq_true_eq] at ht ⊢
        omega
      · simp only [hn_gt, if_false]
        simp only [closedAt, decide_eq_true_eq] at ht ⊢
        have : n < pos := by
          have : n ≠ pos := hn_eq
          omega
        omega
  | pos, r, .Lam _ body, d, hpos, hposd, hr, ht => by
    simp only [substTerm, closedAt] at ht ⊢
    -- goal: closedAt (d + 1) (substTerm (pos + 1) (rename (shiftRename 1) r) body)
    have hr' : closedAt (d + 1) (renameTerm (shiftRename 1) r) = true := by
      apply closedAt_rename (shiftRename 1) r d (d + 1) hr
      intro n hn
      unfold shiftRename
      by_cases h1 : n ≥ 1
      · simp [h1]; omega
      · simp [h1]
        have : n = 0 := by omega
        omega
    exact closedAt_substTerm (pos + 1) (renameTerm (shiftRename 1) r) body (d + 1)
      (by omega) (by omega) hr' ht
  | pos, r, .Apply f x, d, hpos, hposd, hr, ht => by
    simp only [substTerm, closedAt, Bool.and_eq_true] at ht ⊢
    exact ⟨closedAt_substTerm pos r f d hpos hposd hr ht.1,
           closedAt_substTerm pos r x d hpos hposd hr ht.2⟩
  | pos, r, .Force e, d, hpos, hposd, hr, ht => by
    simp only [substTerm, closedAt] at ht ⊢
    exact closedAt_substTerm pos r e d hpos hposd hr ht
  | pos, r, .Delay e, d, hpos, hposd, hr, ht => by
    simp only [substTerm, closedAt] at ht ⊢
    exact closedAt_substTerm pos r e d hpos hposd hr ht
  | pos, r, .Constr _ args, d, hpos, hposd, hr, ht => by
    simp only [substTerm, closedAt] at ht ⊢
    exact closedAtList_substTermList pos r args d hpos hposd hr ht
  | pos, r, .Case scrut alts, d, hpos, hposd, hr, ht => by
    simp only [substTerm, closedAt, Bool.and_eq_true] at ht ⊢
    exact ⟨closedAt_substTerm pos r scrut d hpos hposd hr ht.1,
           closedAtList_substTermList pos r alts d hpos hposd hr ht.2⟩
  | _, _, .Constant _, _, _, _, _, _ => by simp [closedAt, substTerm]
  | _, _, .Builtin _, _, _, _, _, _ => by simp [closedAt, substTerm]
  | _, _, .Error, _, _, _, _, _ => by simp [closedAt, substTerm]
termination_by _ _ t _ _ _ _ _ => sizeOf t

/-- List version of `closedAt_substTerm`. -/
theorem closedAtList_substTermList :
    ∀ (pos : Nat) (r : Term) (ts : List Term) (d : Nat),
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d r = true →
      closedAtList (d + 1) ts = true →
      closedAtList d (substTermList pos r ts) = true
  | _, _, [], _, _, _, _, _ => by simp [closedAtList, substTermList]
  | pos, r, t :: rest, d, hpos, hposd, hr, ht => by
    simp only [closedAtList, substTermList, Bool.and_eq_true] at ht ⊢
    exact ⟨closedAt_substTerm pos r t d hpos hposd hr ht.1,
           closedAtList_substTermList pos r rest d hpos hposd hr ht.2⟩
termination_by _ _ ts _ _ _ _ _ => sizeOf ts

end

--------------------------------------------------------------------------------
-- 4. `SubstEnvRef` — environment-substitution relation at step index k
--
-- `SubstEnvRef pos v_rhs k d ρ₁ ρ₂` says: `ρ₂` is the shape of `ρ₁` after
-- eliminating position `pos`; and the value at that position in `ρ₁` is
-- related (at step index `k`) to `v_rhs`. Every other position is related
-- pointwise between the two envs (with a `−1` shift for positions above
-- `pos` on the `ρ₂` side).
--------------------------------------------------------------------------------

/-- Substitution environment relation: `ρ₂` is obtained from `ρ₁` by
    "dropping" position `pos` and relating its former content to `v_rhs`.
    At every other covered position `n ≤ d`, `ρ₁` and `ρ₂` have
    `ValueRefinesK`-related values (with a shift of 1 for positions
    above `pos`). -/
def SubstEnvRef (pos : Nat) (v_rhs : CekValue) (k d : Nat)
    (ρ₁ ρ₂ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d →
    if n < pos then
      match ρ₁.lookup n, ρ₂.lookup n with
      | some v₁, some v₂ => ValueRefinesK k v₁ v₂
      | _, _ => False
    else if n = pos then
      match ρ₁.lookup n with
      | some v₁ => ValueRefinesK k v₁ v_rhs
      | none => False
    else
      match ρ₁.lookup n, ρ₂.lookup (n - 1) with
      | some v₁, some v₂ => ValueRefinesK k v₁ v₂
      | _, _ => False

/-- `SubstEnvRef` is monotone in the step index: dropping observations
    is always safe. -/
theorem substEnvRef_mono {j k pos d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} (hjk : j ≤ k)
    (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂) :
    SubstEnvRef pos v_rhs j d ρ₁ ρ₂ := by
  intro n hn hnd
  have hn_cases := h n hn hnd
  by_cases h1 : n < pos
  · simp only [h1, if_true] at hn_cases ⊢
    match hρ₁ : ρ₁.lookup n, hρ₂ : ρ₂.lookup n with
    | some v₁, some v₂ =>
      rw [hρ₁, hρ₂] at hn_cases
      exact valueRefinesK_mono hjk v₁ v₂ hn_cases
    | some _, none => rw [hρ₁, hρ₂] at hn_cases; exact hn_cases
    | none, some _ => rw [hρ₁, hρ₂] at hn_cases; exact hn_cases
    | none, none => rw [hρ₁, hρ₂] at hn_cases; exact hn_cases
  · simp only [h1, if_false] at hn_cases ⊢
    by_cases h2 : n = pos
    · simp only [h2, if_true] at hn_cases ⊢
      match hρ₁ : ρ₁.lookup pos with
      | some v₁ =>
        rw [hρ₁] at hn_cases
        exact valueRefinesK_mono hjk v₁ v_rhs hn_cases
      | none => rw [hρ₁] at hn_cases; exact hn_cases
    · simp only [h2, if_false] at hn_cases ⊢
      match hρ₁ : ρ₁.lookup n, hρ₂ : ρ₂.lookup (n - 1) with
      | some v₁, some v₂ =>
        rw [hρ₁, hρ₂] at hn_cases
        exact valueRefinesK_mono hjk v₁ v₂ hn_cases
      | some _, none => rw [hρ₁, hρ₂] at hn_cases; exact hn_cases
      | none, some _ => rw [hρ₁, hρ₂] at hn_cases; exact hn_cases
      | none, none => rw [hρ₁, hρ₂] at hn_cases; exact hn_cases

/-- Extending both sides of a `SubstEnvRef`-related pair by a related pair
    produces a `SubstEnvRef`-related pair at the bumped `pos` and depth.
    At the new position 1, the extending values are related; the old
    position `pos` in the un-extended envs sits at `pos + 1` in the new
    envs, one unit above the shared "new" binding. -/
theorem substEnvRef_extend {k pos d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hpos : 1 ≤ pos)
    (hv : ValueRefinesK k v₁ v₂)
    (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂) :
    SubstEnvRef (pos + 1) v_rhs k (d + 1)
      (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro n hn hnd
  by_cases hn1 : n = 1
  · -- Extended position 1
    subst hn1
    have h_lt : (1 : Nat) < pos + 1 := by omega
    simp only [h_lt, if_true]
    rw [extend_lookup_one ρ₁ v₁, extend_lookup_one ρ₂ v₂]
    exact hv
  · -- n ≥ 2 — shift down to original env reasoning
    have hn_ge2 : n ≥ 2 := by omega
    -- Decompose n as m + 1 with m ≥ 1
    match n, hn_ge2 with
    | m + 1, _ =>
      have hm : m ≥ 1 := by omega
      have hmd : m ≤ d := by omega
      -- Look up in extended envs
      have hlook₁ : (ρ₁.extend v₁).lookup (m + 1) = ρ₁.lookup m :=
        extend_lookup_succ ρ₁ v₁ m hm
      have hlook₂ : (ρ₂.extend v₂).lookup (m + 1) = ρ₂.lookup m :=
        extend_lookup_succ ρ₂ v₂ m hm
      -- Invoke original relation at m
      have hm_cases := h m hm hmd
      by_cases h1 : m < pos
      · -- m < pos ⇔ m + 1 < pos + 1
        have h_lt' : m + 1 < pos + 1 := by omega
        simp only [h_lt', if_true]
        rw [hlook₁, hlook₂]
        simp only [h1, if_true] at hm_cases
        exact hm_cases
      · by_cases h2 : m = pos
        · -- m = pos ⇔ m + 1 = pos + 1
          have h_eq' : m + 1 = pos + 1 := by omega
          have h_not_lt : ¬ (m + 1 < pos + 1) := by omega
          -- Goal: the `n = pos+1` branch of SubstEnvRef at position pos+1.
          show (if m + 1 < pos + 1 then
                  match (ρ₁.extend v₁).lookup (m + 1), (ρ₂.extend v₂).lookup (m + 1) with
                  | some v₁', some v₂' => ValueRefinesK k v₁' v₂'
                  | _, _ => False
                else if m + 1 = pos + 1 then
                  match (ρ₁.extend v₁).lookup (m + 1) with
                  | some v₁' => ValueRefinesK k v₁' v_rhs
                  | none => False
                else
                  match (ρ₁.extend v₁).lookup (m + 1), (ρ₂.extend v₂).lookup ((m + 1) - 1) with
                  | some v₁', some v₂' => ValueRefinesK k v₁' v₂'
                  | _, _ => False)
          rw [if_neg h_not_lt, if_pos h_eq', hlook₁]
          have h_not_m_lt : ¬ (m < pos) := h1
          rw [if_neg h_not_m_lt, if_pos h2] at hm_cases
          exact hm_cases
        · -- m > pos ⇔ m + 1 > pos + 1
          have h_not_lt : ¬ (m + 1 < pos + 1) := by omega
          have h_not_eq : m + 1 ≠ pos + 1 := by omega
          simp only [h_not_lt, h_not_eq, if_false]
          -- (m + 1) - 1 = m, so ρ₂_ext.lookup ((m+1) - 1) = ρ₂_ext.lookup m
          show match (ρ₁.extend v₁).lookup (m + 1),
                     (ρ₂.extend v₂).lookup ((m + 1) - 1) with
               | some v₁', some v₂' => ValueRefinesK k v₁' v₂'
               | _, _ => False
          have h_nm1 : (m + 1) - 1 = m := by omega
          rw [h_nm1, hlook₁]
          -- Now need: match ρ₁.lookup m, (ρ₂.extend v₂).lookup m with | ...
          -- Need to case on m itself.
          match m, hm with
          | 1, _ =>
            -- pos < 1 is impossible since pos ≥ 1; combined with h1 (¬ m < pos)
            -- and h2 (m ≠ pos), this case is vacuous.
            exfalso
            have : pos = 1 ∨ pos ≥ 2 := by omega
            cases this with
            | inl hp1 => exact h2 hp1.symm
            | inr hp2 => exact h1 (by omega)
          | k' + 2, _ =>
            -- m = k' + 2, so (ρ₂.extend v₂).lookup (k' + 2) =
            -- (CekEnv.cons v₂ ρ₂).lookup (k' + 2) = ρ₂.lookup (k' + 1)
            have hlook₂' : (ρ₂.extend v₂).lookup (k' + 2) = ρ₂.lookup (k' + 1) := by
              show (CekEnv.cons v₂ ρ₂).lookup (k' + 2) = ρ₂.lookup (k' + 1)
              rfl
            rw [hlook₂']
            -- Need ρ₂.lookup (m - 1) = ρ₂.lookup (k' + 1)
            have hk'_eq : (k' + 2) - 1 = k' + 1 := by omega
            simp only [h1, h2, if_false] at hm_cases
            rw [hk'_eq] at hm_cases
            exact hm_cases

--------------------------------------------------------------------------------
-- 5. Bridge between the two copies of `steps`
--------------------------------------------------------------------------------

/-- The two `steps` definitions (`Verified.Semantics.steps` and
    `Verified.Equivalence.steps`) both iterate `Moist.CEK.step`; they are
    propositionally equal by induction on the step count. Re-exposed from
    `DeadLet.lean` (where the analogous private helper lives). -/
theorem vstep_eq : ∀ (n : Nat) (s : State),
    Moist.Verified.Equivalence.steps n s = Moist.Verified.Semantics.steps n s
  | 0, _ => rfl
  | n + 1, s => by
    show Moist.Verified.Equivalence.steps n (step s) =
         Moist.Verified.Semantics.steps n (step s)
    exact vstep_eq n (step s)

--------------------------------------------------------------------------------
-- 6. Stack-polymorphic value evaluation
--
-- Given a witness that `t` under `ρ` halts (on the empty stack) and never
-- errors, we can lift the trace to an arbitrary initial stack `π`: the
-- trace still hits `ret π v` and is error-free along the way. Uses
-- `StepLift.steps_liftState` + `firstInactive`, following the template
-- of `DeadLet.dead_let_pure_stack_poly`.
--------------------------------------------------------------------------------

/-- Stack-polymorphic version of the halt-and-no-error promise: from a
    halt witness + no-error witness on the empty stack, derive a halt-to-
    `ret π v` witness + no-error witness on every stack `π`.

    Proof structure mirrors `DeadLet.dead_let_pure_stack_poly`:
    1. Bridge the halt/no-error witnesses from `Equivalence.steps` to
       `Semantics.steps` via `vstep_eq`.
    2. Locate the first inactive step via `StepLift.firstInactive`.
    3. That inactive step is either `halt v'` or `ret [] v'` (not `.error`
       since the input promises no errors, and not a still-active state
       since `isActive = false`).
    4. Apply `steps_liftState` to transport that trace onto the larger
       stack, yielding `ret π v'`.
    5. Bridge back to `Equivalence.steps` and verify error-freeness at
       every intermediate step via the same active-trace observation. -/
theorem value_stack_poly (ρ : CekEnv) (t : Term) (d : Nat)
    (_hwf : Moist.Verified.Semantics.WellSizedEnv d ρ)
    (_hclosed : closedAt d t = true)
    (h_halt : ∃ v, Reaches (.compute [] ρ t) (.halt v))
    (h_noerr : ∀ k, steps k (.compute [] ρ t) ≠ .error) :
    ∀ π, ∃ m v, steps m (.compute π ρ t) = .ret π v ∧
      ∀ k ≤ m, steps k (.compute π ρ t) ≠ .error := by
  intro π
  -- Unpack the halt witness (Equivalence.steps form).
  obtain ⟨v, n_halt, h_halt_v⟩ := h_halt
  -- Bridge to Semantics.steps form.
  have h_halt_v' : Moist.Verified.Semantics.steps n_halt (.compute [] ρ t) = .halt v := by
    rw [← vstep_eq]; exact h_halt_v
  -- No-error in the Semantics.steps form.
  have h_noerr' : ∀ k, Moist.Verified.Semantics.steps k (.compute [] ρ t) ≠ .error := by
    intro k h_err
    apply h_noerr k
    rw [vstep_eq]; exact h_err
  -- The halt state at step n_halt is inactive.
  have h_halt_inactive : Moist.Verified.StepLift.isActive
      (Moist.Verified.Semantics.steps n_halt (.compute [] ρ t)) = false := by
    rw [h_halt_v']; simp [Moist.Verified.StepLift.isActive]
  -- Locate the first inactive step K ≤ n_halt.
  obtain ⟨K, _hK_le, hK_inact, hK_min⟩ := Moist.Verified.StepLift.firstInactive
    (.compute [] ρ t) n_halt ⟨n_halt, Nat.le_refl _, h_halt_inactive⟩
  -- At step K the state is inactive and not error.
  have hK_not_err : Moist.Verified.Semantics.steps K (.compute [] ρ t) ≠ .error :=
    h_noerr' K
  -- Case-analyze: inactive + not-error ⇒ either `halt v'` or `ret [] v'`;
  -- in both cases `liftState π` produces `ret π v'`.
  have hK_state_ret_pi : ∃ v',
      Moist.Verified.StepLift.liftState π
        (Moist.Verified.Semantics.steps K (.compute [] ρ t)) = .ret π v' := by
    cases h_s : Moist.Verified.Semantics.steps K (.compute [] ρ t) with
    | compute _ _ _ =>
      rw [h_s] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact
    | ret π' v' =>
      cases π' with
      | nil =>
        refine ⟨v', ?_⟩
        simp [Moist.Verified.StepLift.liftState]
      | cons _ _ =>
        rw [h_s] at hK_inact; simp [Moist.Verified.StepLift.isActive] at hK_inact
    | halt v' =>
      refine ⟨v', ?_⟩
      simp [Moist.Verified.StepLift.liftState]
    | error => exact absurd h_s hK_not_err
  obtain ⟨v_ret, h_lift_K⟩ := hK_state_ret_pi
  -- Identify compute π ρ t with liftState π (compute [] ρ t).
  have h_lift_start : (.compute π ρ t : State) =
      Moist.Verified.StepLift.liftState π (.compute [] ρ t) := by
    simp [Moist.Verified.StepLift.liftState]
  -- Use steps_liftState at step K.
  have h_steps_K : Moist.Verified.Semantics.steps K
      (Moist.Verified.StepLift.liftState π (.compute [] ρ t)) =
      Moist.Verified.StepLift.liftState π
        (Moist.Verified.Semantics.steps K (.compute [] ρ t)) :=
    Moist.Verified.StepLift.steps_liftState π K (.compute [] ρ t) hK_min
  rw [h_lift_K] at h_steps_K
  -- Bridge back to Equivalence.steps.
  have h_reach_ret : steps K (.compute π ρ t) = .ret π v_ret := by
    rw [vstep_eq, h_lift_start]; exact h_steps_K
  refine ⟨K, v_ret, h_reach_ret, ?_⟩
  intro k hk
  -- No-error for every k ≤ K.
  by_cases hk_eq : k = K
  · rw [hk_eq, h_reach_ret]; exact State.noConfusion
  · have hk_lt : k < K := by omega
    -- steps_liftState at step k (all j < k ≤ K - 1 are active via hK_min).
    have h_lift_k : Moist.Verified.Semantics.steps k
        (Moist.Verified.StepLift.liftState π (.compute [] ρ t)) =
        Moist.Verified.StepLift.liftState π
          (Moist.Verified.Semantics.steps k (.compute [] ρ t)) := by
      apply Moist.Verified.StepLift.steps_liftState
      intro j hj; exact hK_min j (by omega)
    have h_equiv_k : steps k (.compute π ρ t) =
        Moist.Verified.StepLift.liftState π
          (Moist.Verified.Semantics.steps k (.compute [] ρ t)) := by
      rw [vstep_eq, h_lift_start]; exact h_lift_k
    intro h_err
    rw [h_err] at h_equiv_k
    -- Active inner state cannot lift to `.error`.
    have h_active_k : Moist.Verified.StepLift.isActive
        (Moist.Verified.Semantics.steps k (.compute [] ρ t)) = true := hK_min k hk_lt
    cases hs : Moist.Verified.Semantics.steps k (.compute [] ρ t) with
    | compute _ _ _ =>
      rw [hs] at h_equiv_k; simp [Moist.Verified.StepLift.liftState] at h_equiv_k
    | ret π' v' =>
      cases π' with
      | nil =>
        rw [hs] at h_active_k
        simp [Moist.Verified.StepLift.isActive] at h_active_k
      | cons _ _ =>
        rw [hs] at h_equiv_k; simp [Moist.Verified.StepLift.liftState] at h_equiv_k
    | halt v' =>
      rw [hs] at h_active_k
      simp [Moist.Verified.StepLift.isActive] at h_active_k
    | error =>
      rw [hs] at h_active_k
      simp [Moist.Verified.StepLift.isActive] at h_active_k

--------------------------------------------------------------------------------
-- 7. Well-formedness predicates
--
-- Mutually-inductive unary predicates on CEK values / environments that
-- capture closure well-formedness:
--
-- * `ValueWellFormed v` — every embedded closure body is closed at the
--   corresponding environment depth (+1 for lambdas).
-- * `EnvWellFormed k ρ` — every index `1..k` of `ρ` resolves to a
--   well-formed value.
-- * `ValueListWellFormed vs` — pointwise well-formedness on a list.
--
-- These mirror the pattern of `LocalValue`/`LocalEnv`/`LocalValueList` in
-- `Moist.Verified.Contextual.BisimRef`, but as unary "diagonal" versions.
--------------------------------------------------------------------------------

mutual

/-- A CEK value is well-formed when every embedded closure is closed
    at the appropriate depth and its captured env is well-formed at its
    length. -/
inductive ValueWellFormed : CekValue → Prop
  | vcon : ∀ (c : Const), ValueWellFormed (.VCon c)
  | vlam : ∀ {body : Term} {ρ : CekEnv} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      closedAt (k + 1) body = true →
      ValueWellFormed (.VLam body ρ)
  | vdelay : ∀ {body : Term} {ρ : CekEnv} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      closedAt k body = true →
      ValueWellFormed (.VDelay body ρ)
  | vconstr : ∀ (tag : Nat) {fs : List CekValue},
      ValueListWellFormed fs →
      ValueWellFormed (.VConstr tag fs)
  | vbuiltin : ∀ (b : BuiltinFun) (ea : ExpectedArgs) {args : List CekValue},
      ValueListWellFormed args →
      ValueWellFormed (.VBuiltin b args ea)

/-- An environment is well-formed at depth `k` when every index `1..k`
    resolves to a well-formed value. -/
inductive EnvWellFormed : Nat → CekEnv → Prop
  | zero : ∀ {ρ : CekEnv}, EnvWellFormed 0 ρ
  | succ : ∀ {k : Nat} {ρ : CekEnv} {v : CekValue},
      EnvWellFormed k ρ →
      k + 1 ≤ ρ.length →
      ρ.lookup (k + 1) = some v →
      ValueWellFormed v →
      EnvWellFormed (k + 1) ρ

/-- Pointwise well-formedness on a list of CEK values. -/
inductive ValueListWellFormed : List CekValue → Prop
  | nil : ValueListWellFormed []
  | cons : ∀ {v : CekValue} {vs : List CekValue},
      ValueWellFormed v → ValueListWellFormed vs →
      ValueListWellFormed (v :: vs)

end

/-- A stack frame is well-formed when its embedded terms are closed at
    the env depth and every embedded value/env is itself well-formed. -/
inductive FrameWellFormed : Frame → Prop
  | force : FrameWellFormed .force
  | arg : ∀ {t : Term} {ρ : CekEnv} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      closedAt k t = true →
      FrameWellFormed (.arg t ρ)
  | funV : ∀ {v : CekValue}, ValueWellFormed v → FrameWellFormed (.funV v)
  | applyArg : ∀ {v : CekValue}, ValueWellFormed v → FrameWellFormed (.applyArg v)
  | constrField : ∀ (tag : Nat) {done : List CekValue}
      {todo : List Term} {ρ : CekEnv} {k : Nat},
      ValueListWellFormed done →
      EnvWellFormed k ρ → k ≤ ρ.length →
      closedAtList k todo = true →
      FrameWellFormed (.constrField tag done todo ρ)
  | caseScrutinee : ∀ {alts : List Term} {ρ : CekEnv} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      closedAtList k alts = true →
      FrameWellFormed (.caseScrutinee alts ρ)

/-- A stack is well-formed when every frame is. -/
inductive StackWellFormed : Stack → Prop
  | nil : StackWellFormed []
  | cons : ∀ {f : Frame} {π : Stack},
      FrameWellFormed f → StackWellFormed π →
      StackWellFormed (f :: π)

--------------------------------------------------------------------------------
-- 8. Env well-formedness helpers
--------------------------------------------------------------------------------

/-- `EnvWellFormed` always holds vacuously at depth 0. -/
theorem envWellFormed_zero (ρ : CekEnv) : EnvWellFormed 0 ρ := EnvWellFormed.zero

/-- Narrow a well-formedness depth down to a smaller one. -/
theorem envWellFormed_narrow : ∀ (k : Nat) {k' : Nat} {ρ : CekEnv},
    EnvWellFormed k ρ → k' ≤ k → EnvWellFormed k' ρ := by
  intro k
  induction k with
  | zero =>
    intro k' _ _ hle
    have : k' = 0 := Nat.le_zero.mp hle
    subst this
    exact EnvWellFormed.zero
  | succ n ih =>
    intro k' _ h hle
    by_cases h_eq : k' = n + 1
    · subst h_eq; exact h
    · cases h with
      | succ h_rest _ _ _ =>
        exact ih h_rest (by omega)

/-- Lookups within a well-formed env return well-formed values. -/
theorem envWellFormed_lookup : ∀ (k : Nat) {ρ : CekEnv},
    EnvWellFormed k ρ → ∀ {n : Nat}, 0 < n → n ≤ k →
      ∃ v, ρ.lookup n = some v ∧ ValueWellFormed v := by
  intro k
  induction k with
  | zero => intro _ _ _ _ hle; omega
  | succ n ih =>
    intro _ h m hm hle
    cases h with
    | succ h_rest _ hl h_v =>
      by_cases h_eq : m = n + 1
      · subst h_eq; exact ⟨_, hl, h_v⟩
      · exact ih h_rest hm (by omega)

/-- Extending a well-formed env at depth `k` with a well-formed value
    yields a well-formed env at depth `k + 1`. -/
theorem envWellFormed_extend : ∀ (k : Nat) {ρ : CekEnv} {v : CekValue},
    EnvWellFormed k ρ → k ≤ ρ.length →
    ValueWellFormed v →
    EnvWellFormed (k + 1) (ρ.extend v) := by
  intro k
  induction k with
  | zero =>
    intro ρ _ _ hle h_v
    refine EnvWellFormed.succ EnvWellFormed.zero ?_ ?_ h_v
    · simp [CekEnv.extend, CekEnv.length]
    · simp [CekEnv.extend, CekEnv.lookup]
  | succ n ih =>
    intro ρ _ h hle h_v
    cases h with
    | succ h_rest hl_len hl_look h_inner =>
      have ih' := ih h_rest (by omega) h_v
      refine EnvWellFormed.succ ih' ?_ ?_ h_inner
      · simp [CekEnv.extend, CekEnv.length]; omega
      · show (CekEnv.cons _ ρ).lookup (n + 1 + 1) = _
        exact hl_look

/-- A well-formed env at depth `k` has length ≥ `k`. -/
theorem envWellFormed_length : ∀ (k : Nat) {ρ : CekEnv},
    EnvWellFormed k ρ → k ≤ ρ.length := by
  intro k
  cases k with
  | zero => intro _ _; exact Nat.zero_le _
  | succ n =>
    intro _ h
    cases h with
    | succ _ hlen _ _ => exact hlen

--------------------------------------------------------------------------------
-- 9. ValueRefinesK reflexivity
--
-- Prove by induction on the step index that every well-formed value is
-- `ValueRefinesK k`-reflexive. Relies on `ftlr` for the closure cases.
--------------------------------------------------------------------------------

/-- `EnvRefinesK k d ρ ρ` for a well-formed `ρ` at depth `d`, assuming
    `valueRefinesK_refl` has been established at step index `k`. Used
    as a helper for the closure cases inside `valueRefinesK_refl`. -/
private theorem envRefinesK_refl_of_valueRefl
    {k d : Nat} {ρ : CekEnv}
    (hρ : EnvWellFormed d ρ)
    (hvrefl : ∀ v, ValueWellFormed v → ValueRefinesK k v v) :
    EnvRefinesK k d ρ ρ := by
  intro n hn hnd
  obtain ⟨v, hl, hv⟩ := envWellFormed_lookup d hρ hn hnd
  exact ⟨v, v, hl, hl, hvrefl v hv⟩

/-- `ListRel (ValueRefinesK k) vs vs` for a well-formed `vs`. -/
private theorem listRel_valueRefinesK_refl_of_valueRefl {k : Nat}
    (hvrefl : ∀ v, ValueWellFormed v → ValueRefinesK k v v) :
    ∀ {vs : List CekValue}, ValueListWellFormed vs →
      ListRel (ValueRefinesK k) vs vs
  | [], _ => by trivial
  | v :: rest, h => by
    cases h with
    | cons hv hrest =>
      refine ⟨hvrefl v hv, ?_⟩
      exact listRel_valueRefinesK_refl_of_valueRefl hvrefl hrest

/-- **Main value reflexivity**: for every well-formed value `v` and every
    step index `k`, `ValueRefinesK k v v`. Proved by induction on `k`. -/
theorem valueRefinesK_refl : ∀ (k : Nat) (v : CekValue),
    ValueWellFormed v → ValueRefinesK k v v := by
  intro k
  induction k with
  | zero =>
    intro v hv
    cases hv with
    | vcon c => simp only [ValueRefinesK]
    | vlam _ _ _ => simp only [ValueRefinesK]
    | vdelay _ _ _ => simp only [ValueRefinesK]
    | vconstr tag _ => simp only [ValueRefinesK]
    | @vbuiltin b ea args _ =>
      show ValueRefinesK 0 (.VBuiltin b args ea) (.VBuiltin b args ea)
      simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
  | succ k ih =>
    intro v hv
    cases hv with
    | vcon c => simp only [ValueRefinesK]
    | @vlam body ρ d hρ hlen hc =>
      -- ValueRefinesK (k+1) (VLam body ρ) (VLam body ρ) unfolds to
      --   ∀ j ≤ k, ∀ arg₁ arg₂, ValueRefinesK j arg₁ arg₂ →
      --     ∀ i ≤ j, ∀ π₁ π₂, stack-ref →
      --       ObsRefinesK i (compute π₁ (ρ.extend arg₁) body)
      --                      (compute π₂ (ρ.extend arg₂) body)
      -- We discharge via ftlr at depth d+1, using envRefinesK extension.
      simp only [ValueRefinesK]
      intro j hj arg₁ arg₂ harg i hi π₁ π₂ hπ
      -- Build EnvRefinesK j (d+1) (ρ.extend arg₁) (ρ.extend arg₂)
      -- Use ih (at step k) then monotonicity to j; but we need ValueRefinesK j.
      -- Use valueRefinesK_refl at step j via outer ih — but IH is at k only.
      -- Instead, use valueRefinesK_mono to drop from k+1 to j (but ih is at k).
      -- Approach: at j ≤ k, use ih for each arg + envRefinesK from wellformedness.
      -- Since j ≤ k, we can invoke ih and then mono from k to j for each lookup.
      have hρ_refl : EnvRefinesK j d ρ ρ := by
        have hρ_refl_k : EnvRefinesK k d ρ ρ :=
          envRefinesK_refl_of_valueRefl hρ ih
        intro n hn hnd'
        obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ := hρ_refl_k n hn hnd'
        exact ⟨v₁, v₂, hl₁, hl₂, valueRefinesK_mono hj _ _ hrel⟩
      have hclosed : closedAt (d + 1) body = true := hc
      -- Extend: we need EnvRefinesK j (d+1) (ρ.extend arg₁) (ρ.extend arg₂).
      have hext : EnvRefinesK j (d + 1) (ρ.extend arg₁) (ρ.extend arg₂) := by
        intro n hn hnd'
        by_cases h1 : n = 1
        · subst h1
          refine ⟨arg₁, arg₂, ?_, ?_, harg⟩
          · exact extend_lookup_one ρ arg₁
          · exact extend_lookup_one ρ arg₂
        · have hn2 : n ≥ 2 := by omega
          match n, hn2 with
          | m + 2, _ =>
            have hm1 : m + 1 ≥ 1 := by omega
            have hmd : m + 1 ≤ d := by omega
            obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ := hρ_refl (m + 1) hm1 hmd
            refine ⟨v₁, v₂, ?_, ?_, hrel⟩
            · show (ρ.extend arg₁).lookup (m + 1 + 1) = some v₁
              rw [extend_lookup_succ ρ arg₁ (m + 1) hm1]
              exact hl₁
            · show (ρ.extend arg₂).lookup (m + 1 + 1) = some v₂
              rw [extend_lookup_succ ρ arg₂ (m + 1) hm1]
              exact hl₂
      -- Apply ftlr.
      exact Moist.Verified.FundamentalRefines.ftlr (d + 1) body hclosed j
        j (Nat.le_refl _) (ρ.extend arg₁) (ρ.extend arg₂) hext i hi π₁ π₂ hπ
    | @vdelay body ρ d hρ hlen hc =>
      simp only [ValueRefinesK]
      intro j hj i hi π₁ π₂ hπ
      have hρ_refl : EnvRefinesK j d ρ ρ := by
        have hρ_refl_k : EnvRefinesK k d ρ ρ :=
          envRefinesK_refl_of_valueRefl hρ ih
        intro n hn hnd'
        obtain ⟨v₁, v₂, hl₁, hl₂, hrel⟩ := hρ_refl_k n hn hnd'
        exact ⟨v₁, v₂, hl₁, hl₂, valueRefinesK_mono hj _ _ hrel⟩
      exact Moist.Verified.FundamentalRefines.ftlr d body hc j
        j (Nat.le_refl _) ρ ρ hρ_refl i hi π₁ π₂ hπ
    | vconstr tag hfs =>
      simp only [ValueRefinesK]
      refine ⟨trivial, ?_⟩
      exact listRel_valueRefinesK_refl_of_valueRefl ih hfs
    | vbuiltin b ea hargs =>
      simp only [ValueRefinesK]
      refine ⟨trivial, trivial, ?_⟩
      exact listRel_valueRefinesK_refl_of_valueRefl ih hargs

/-- **Env reflexivity**: `EnvRefinesK k d ρ ρ` whenever `ρ` is well-formed
    at a depth at least `d`. -/
theorem envRefinesK_refl {k d : Nat} {ρ : CekEnv}
    (hρ : EnvWellFormed d ρ) : EnvRefinesK k d ρ ρ := by
  intro n hn hnd
  obtain ⟨v, hl, hv⟩ := envWellFormed_lookup d hρ hn hnd
  exact ⟨v, v, hl, hl, valueRefinesK_refl k v hv⟩

/-- **List reflexivity**: `ListRel (ValueRefinesK k) vs vs` for a
    well-formed value list. -/
theorem listRel_valueRefinesK_refl (k : Nat) {vs : List CekValue}
    (h : ValueListWellFormed vs) : ListRel (ValueRefinesK k) vs vs :=
  listRel_valueRefinesK_refl_of_valueRefl (valueRefinesK_refl k) h

--------------------------------------------------------------------------------
-- 9b. Closedness-of-list inversions
--------------------------------------------------------------------------------

/-- Closedness is inherited by every element of a closed list. -/
theorem closedAt_of_mem : ∀ {d : Nat} {ts : List Term} {t : Term},
    closedAtList d ts = true → t ∈ ts → closedAt d t = true
  | _, [], _, _, h => by cases h
  | _, _ :: _, _, hc, hmem => by
    simp only [closedAtList, Bool.and_eq_true] at hc
    cases hmem with
    | head => exact hc.1
    | tail _ h => exact closedAt_of_mem hc.2 h

/-- Fields produced by `constToTagAndFields` are always VCon values. -/
theorem vcon_fields_of_constToTagAndFields :
    ∀ {c : Const} {tag numCtors : Nat} {fs : List CekValue},
      constToTagAndFields c = some (tag, numCtors, fs) →
      ∀ v ∈ fs, ∃ c', v = .VCon c' := by
  intro c _ _ fs hc v hmem
  cases c with
  | Integer n =>
    simp only [constToTagAndFields] at hc
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs; cases hmem
    · exact Option.noConfusion hc
  | ByteString _ => simp [constToTagAndFields] at hc
  | String _ => simp [constToTagAndFields] at hc
  | Unit =>
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc; subst hfs; cases hmem
  | Bool b =>
    cases b <;>
    · simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs; cases hmem
  | Data _ => simp [constToTagAndFields] at hc
  | ConstList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs; cases hmem
    | cons h t =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      cases hmem with
      | head => exact ⟨h, rfl⟩
      | tail _ h2 =>
        cases h2 with
        | head => exact ⟨.ConstList t, rfl⟩
        | tail _ h3 => cases h3
  | ConstDataList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs; cases hmem
    | cons h t =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      cases hmem with
      | head => exact ⟨.Data h, rfl⟩
      | tail _ h2 =>
        cases h2 with
        | head => exact ⟨.ConstDataList t, rfl⟩
        | tail _ h3 => cases h3
  | ConstPairDataList _ => simp [constToTagAndFields] at hc
  | ConstArray _ => simp [constToTagAndFields] at hc
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc; subst hfs
    cases hmem with
    | head => exact ⟨a, rfl⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨b, rfl⟩
      | tail _ h3 => cases h3
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc; subst hfs
    cases hmem with
    | head => exact ⟨.Data a, rfl⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨.Data b, rfl⟩
      | tail _ h3 => cases h3
  | Bls12_381_G1_element => simp [constToTagAndFields] at hc
  | Bls12_381_G2_element => simp [constToTagAndFields] at hc
  | Bls12_381_MlResult => simp [constToTagAndFields] at hc

--------------------------------------------------------------------------------
-- 10. StackRefK reflexivity
--
-- By induction on the stack, showing `StackRefK ValueRefinesK k π π` for
-- any well-formed `π`. Each frame case involves stepping both sides of
-- `.ret (f :: π) v` once and rejoining via value/stack refinement.
--
-- The `.constrField` frame case requires an auxiliary lemma that threads
-- a `ListRel (ValueRefinesK k)` on the `done` list (which differs between
-- the two sides because we're building it up from freshly-stepped values).
--------------------------------------------------------------------------------

/-- Stack refinement for a `.constrField` frame with asymmetric `done₁
    / done₂`. Generalized over both sides of the done list; the todo
    list is identical. Induction on `todo`. -/
private theorem stackRefK_refl_constrField_asym
    {k tag d : Nat}
    {done₁ done₂ : List CekValue} {todo : List Term}
    {ρ : CekEnv} {rest : Stack}
    (hρ : EnvWellFormed d ρ)
    (htodo : closedAtList d todo = true)
    (hrest : StackRefK ValueRefinesK k rest rest)
    (hdone : ListRel (ValueRefinesK k) done₁ done₂) :
    ∀ {j}, j ≤ k →
      StackRefK ValueRefinesK j
        (.constrField tag done₁ todo ρ :: rest)
        (.constrField tag done₂ todo ρ :: rest) := by
  induction todo generalizing done₁ done₂ rest k with
  | nil =>
    intro j hj j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hrev : ListRel (ValueRefinesK n)
        ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) := by
      simp only [List.reverse_cons]
      exact listRel_append
        (listRel_reverse
          (listRel_valueRefinesK_mono (by omega : n ≤ k) hdone))
        ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, trivial⟩
    have hval : ValueRefinesK (n + 1)
        (.VConstr tag ((v₁ :: done₁).reverse))
        (.VConstr tag ((v₂ :: done₂).reverse)) := by
      cases n with
      | zero => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
      | succ m => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
    exact obsRefinesK_mono (by omega)
      ((stackRefK_mono (by omega : n + 1 ≤ k) hrest) (n + 1) (by omega) _ _ hval)
  | cons m ms ih_ms =>
    simp only [closedAtList, Bool.and_eq_true] at htodo
    obtain ⟨hm_closed, hms_closed⟩ := htodo
    intro j hj j' hj' v₁ v₂ hv
    match j' with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    simp only [step]
    have hdone' : ListRel (ValueRefinesK n) (v₁ :: done₁) (v₂ :: done₂) :=
      ⟨valueRefinesK_mono (by omega) v₁ v₂ hv,
       listRel_valueRefinesK_mono (by omega : n ≤ k) hdone⟩
    have hrest' : StackRefK ValueRefinesK n rest rest :=
      stackRefK_mono (by omega : n ≤ k) hrest
    have hπ_new : StackRefK ValueRefinesK n
        (.constrField tag (v₁ :: done₁) ms ρ :: rest)
        (.constrField tag (v₂ :: done₂) ms ρ :: rest) :=
      ih_ms hms_closed hrest' hdone' (Nat.le_refl _)
    have hρ_refl : EnvRefinesK n d ρ ρ := envRefinesK_refl hρ
    exact Moist.Verified.FundamentalRefines.ftlr d m hm_closed n
      n (Nat.le_refl _) ρ ρ hρ_refl n (Nat.le_refl _) _ _ hπ_new

/-- **Stack reflexivity**: every well-formed stack is `StackRefK`-reflexive
    at every step index. -/
theorem stackRefK_refl : ∀ (k : Nat) (π : Stack),
    StackWellFormed π → StackRefK ValueRefinesK k π π := by
  intro k π
  induction π generalizing k with
  | nil =>
    intro _
    exact Moist.Verified.Contextual.SoundnessRefines.stackRefK_nil k
  | cons f rest ih =>
    intro hwf
    cases hwf with
    | cons hf hrest =>
    intro j hj v₁ v₂ hv
    -- We need: ObsRefinesK j (.ret (f :: rest) v₁) (.ret (f :: rest) v₂)
    match j with
    | 0 => obsRefinesK_zero_nonhalt_auto
    | n + 1 =>
    obsRefinesK_of_step_auto
    -- Step both states at the frame
    cases hf with
    | force =>
      -- step (.ret (.force :: rest) v)
      match v₁, v₂ with
      | .VDelay body₁ ρ₁, .VDelay body₂ ρ₂ =>
        simp only [step, ValueRefinesK] at hv ⊢
        -- hv says: ∀ j' ≤ n, ∀ i ≤ j', ∀ π₁ π₂, stack-ref → ObsRefinesK i
        --           (compute π₁ ρ₁ body₁) (compute π₂ ρ₂ body₂)
        -- The ih applied at n gives StackRefK ValueRefinesK n rest rest
        exact hv n (Nat.le_refl _) n (Nat.le_refl _) rest rest (ih n hrest)
      | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
        simp only [ValueRefinesK] at hv
        obtain ⟨rfl, rfl, hargs⟩ := hv
        simp only [step]
        -- The ea head/tail dispatches identically; we do a split by ea.head.
        split
        · -- ea.head = argQ: either consume a rest or evalBuiltin
          split
          · rename_i rest' _
            -- produce VBuiltin with rest'; ret with it.
            have hval : ValueRefinesK (n + 1)
                (.VBuiltin b₁ args₁ rest') (.VBuiltin b₁ args₂ rest') := by
              simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩
              exact listRel_valueRefinesK_mono (by omega) hargs
            exact obsRefinesK_mono (by omega) ((ih (n + 1) hrest) (n + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat_refines hargs (ih n hrest)
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
    | @arg t ρ d hρ hlen hc =>
      -- step (.ret (.arg t ρ :: rest) v) = compute (.funV v :: rest) ρ t
      simp only [step]
      -- Apply ftlr on t with the frame `.funV v` pushed.
      -- We need StackRefK ValueRefinesK n (.funV v₁ :: rest) (.funV v₂ :: rest)
      have hπ_new : StackRefK ValueRefinesK n (.funV v₁ :: rest) (.funV v₂ :: rest) := by
        intro j' hj' w₁ w₂ hw
        match j' with
        | 0 => obsRefinesK_zero_nonhalt_auto
        | m + 1 =>
        obsRefinesK_of_step_auto
        -- step (.ret (.funV v :: rest) w)
        match v₁, v₂ with
        | .VLam body₁ ρ₁', .VLam body₂ ρ₂' =>
          simp only [step, ValueRefinesK] at hv ⊢
          exact hv m (by omega) w₁ w₂ (valueRefinesK_mono (by omega) w₁ w₂ hw)
            m (Nat.le_refl _) rest rest
            (stackRefK_mono (by omega) (ih m hrest))
        | .VBuiltin b₁ args₁ exp₁, .VBuiltin b₂ args₂ exp₂ =>
          simp only [ValueRefinesK] at hv
          obtain ⟨rfl, rfl, hargs_rel⟩ := hv
          simp only [step]
          split
          · split
            · rename_i rest' _
              have hval : ValueRefinesK (m + 1)
                  (.VBuiltin b₁ (w₁ :: args₁) rest') (.VBuiltin b₁ (w₂ :: args₂) rest') := by
                simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩
                simp only [ListRel]
                exact ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                       listRel_valueRefinesK_mono (by omega : m ≤ n) hargs_rel⟩
              exact obsRefinesK_mono (by omega)
                ((ih (m + 1) hrest) (m + 1) (by omega) _ _ hval)
            · exact evalBuiltin_compat_refines
                ⟨valueRefinesK_mono (by omega) w₁ w₂ hw,
                 listRel_valueRefinesK_mono (by omega : m ≤ n) hargs_rel⟩
                (ih m hrest)
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
      -- Apply ftlr to t.
      have henv : EnvRefinesK n d ρ ρ := envRefinesK_refl hρ
      exact Moist.Verified.FundamentalRefines.ftlr d t hc n
        n (Nat.le_refl _) ρ ρ henv n (Nat.le_refl _) _ _ hπ_new
    | @funV v hvwf =>
      -- step (.ret (.funV v :: rest) v_arg)
      -- v_arg should be the top of stack; we have v₁, v₂ as the incoming pair.
      -- Shape: v is the saved function, v₁/v₂ are the arguments.
      match v with
      | .VLam body ρ =>
        -- step (.ret (.funV (VLam body ρ) :: rest) v_arg) = compute rest (ρ.extend v_arg) body
        simp only [step]
        cases hvwf with
        | @vlam _ _ d hρ hlen hc =>
          -- Directly construct ObsRefinesK via ftlr with extended env.
          have hρ_refl : EnvRefinesK n d ρ ρ := envRefinesK_refl hρ
          have hext : EnvRefinesK n (d + 1) (ρ.extend v₁) (ρ.extend v₂) := by
            intro m hm hmd
            by_cases h1 : m = 1
            · subst h1
              refine ⟨v₁, v₂, ?_, ?_, valueRefinesK_mono (by omega) v₁ v₂ hv⟩
              · exact extend_lookup_one ρ v₁
              · exact extend_lookup_one ρ v₂
            · have hm2 : m ≥ 2 := by omega
              match m, hm2 with
              | q + 2, _ =>
                have hq1 : q + 1 ≥ 1 := by omega
                have hqd : q + 1 ≤ d := by omega
                obtain ⟨v_l, v_r, hl₁, hl₂, hrel⟩ := hρ_refl (q + 1) hq1 hqd
                refine ⟨v_l, v_r, ?_, ?_, hrel⟩
                · show (ρ.extend v₁).lookup (q + 1 + 1) = some v_l
                  rw [extend_lookup_succ ρ v₁ (q + 1) hq1]; exact hl₁
                · show (ρ.extend v₂).lookup (q + 1 + 1) = some v_r
                  rw [extend_lookup_succ ρ v₂ (q + 1) hq1]; exact hl₂
          exact Moist.Verified.FundamentalRefines.ftlr (d + 1) body hc n
            n (Nat.le_refl _) (ρ.extend v₁) (ρ.extend v₂) hext n (Nat.le_refl _) rest rest
            (ih n hrest)
      | .VBuiltin b args ea =>
        simp only [step]
        cases hvwf with
        | vbuiltin _ _ hargs =>
        split
        · split
          · rename_i rest' _
            have hargs_rel : ListRel (ValueRefinesK n) args args :=
              listRel_valueRefinesK_refl n hargs
            have hval : ValueRefinesK (n + 1)
                (.VBuiltin b (v₁ :: args) rest') (.VBuiltin b (v₂ :: args) rest') := by
              simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩
              simp only [ListRel]
              exact ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, hargs_rel⟩
            exact obsRefinesK_mono (by omega) ((ih (n + 1) hrest) (n + 1) (by omega) _ _ hval)
          · have hargs_rel : ListRel (ValueRefinesK n) args args :=
              listRel_valueRefinesK_refl n hargs
            exact evalBuiltin_compat_refines
              (show ListRel (ValueRefinesK n) (v₁ :: args) (v₂ :: args) from
                ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, hargs_rel⟩)
              (ih n hrest)
        · exact obsRefinesK_error _
      | .VCon _ => simp only [step]; exact obsRefinesK_error _
      | .VDelay _ _ => simp only [step]; exact obsRefinesK_error _
      | .VConstr _ _ => simp only [step]; exact obsRefinesK_error _
    | @applyArg vx hvxwf =>
      -- step (.ret (.applyArg vx :: rest) v) — here v₁/v₂ are the function value,
      -- vx is the saved argument.
      simp only [step]
      match v₁, v₂ with
      | .VLam body₁ ρ₁, .VLam body₂ ρ₂ =>
        simp only [ValueRefinesK] at hv
        -- hv = ∀ j' ≤ n, ∀ arg₁ arg₂, VR j' → ∀ i ≤ j', ∀ π₁ π₂, stack-ref → ObsR i (compute π₁ (ρ₁.extend arg₁) body₁) (compute π₂ (ρ₂.extend arg₂) body₂)
        have hvxrefl : ValueRefinesK n vx vx := valueRefinesK_refl n vx hvxwf
        exact hv n (Nat.le_refl _) vx vx hvxrefl n (Nat.le_refl _) rest rest (ih n hrest)
      | .VBuiltin b₁ args₁ ea₁, .VBuiltin b₂ args₂ ea₂ =>
        simp only [ValueRefinesK] at hv
        obtain ⟨rfl, rfl, hargs_rel⟩ := hv
        have hvxrefl : ValueRefinesK n vx vx := valueRefinesK_refl n vx hvxwf
        simp only
        split
        · split
          · rename_i rest' _
            have hval : ValueRefinesK (n + 1)
                (.VBuiltin b₁ (vx :: args₁) rest') (.VBuiltin b₁ (vx :: args₂) rest') := by
              simp only [ValueRefinesK]; refine ⟨trivial, trivial, ?_⟩
              simp only [ListRel]
              exact ⟨hvxrefl, listRel_valueRefinesK_mono (by omega : n ≤ n) hargs_rel⟩
            exact obsRefinesK_mono (by omega) ((ih (n + 1) hrest) (n + 1) (by omega) _ _ hval)
          · exact evalBuiltin_compat_refines
              ⟨hvxrefl, listRel_valueRefinesK_mono (by omega : n ≤ n) hargs_rel⟩
              (ih n hrest)
        · exact obsRefinesK_error _
      | .VCon _, .VCon _ => simp only; exact obsRefinesK_error _
      | .VDelay _ _, .VDelay _ _ => simp only; exact obsRefinesK_error _
      | .VConstr _ _, .VConstr _ _ => simp only; exact obsRefinesK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv
    | @constrField tag done todo ρ d hdone hρ hlen hc =>
      -- Two cases on todo: empty (finish constr) or not (continue with next field).
      simp only [step]
      cases todo with
      | nil =>
        -- .ret (.constrField tag done [] ρ :: rest) v → .ret rest (VConstr tag ((v :: done).reverse))
        have hdone_rel : ListRel (ValueRefinesK n) done done :=
          listRel_valueRefinesK_refl n hdone
        have hrev : ListRel (ValueRefinesK n)
            ((v₁ :: done).reverse) ((v₂ :: done).reverse) := by
          simp only [List.reverse_cons]
          exact listRel_append
            (listRel_reverse hdone_rel)
            ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, trivial⟩
        have hval : ValueRefinesK (n + 1)
            (.VConstr tag ((v₁ :: done).reverse))
            (.VConstr tag ((v₂ :: done).reverse)) := by
          cases n with
          | zero => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
          | succ m => simp only [ValueRefinesK]; exact ⟨trivial, hrev⟩
        exact obsRefinesK_mono (by omega) ((ih (n + 1) hrest) (n + 1) (by omega) _ _ hval)
      | cons m ms =>
        -- .ret (.constrField tag done (m :: ms) ρ :: rest) v
        --   → compute (.constrField tag (v :: done) ms ρ :: rest) ρ m
        simp only [closedAtList, Bool.and_eq_true] at hc
        obtain ⟨hm_closed, hms_closed⟩ := hc
        have hρ_refl : EnvRefinesK n d ρ ρ := envRefinesK_refl hρ
        have hdone_rel : ListRel (ValueRefinesK n) done done :=
          listRel_valueRefinesK_refl n hdone
        -- Build the new stack refinement for .constrField tag (v :: done) ms ρ :: rest
        have hnew_done : ListRel (ValueRefinesK n) (v₁ :: done) (v₂ :: done) :=
          ⟨valueRefinesK_mono (by omega) v₁ v₂ hv, hdone_rel⟩
        have hπ_new : StackRefK ValueRefinesK n
            (.constrField tag (v₁ :: done) ms ρ :: rest)
            (.constrField tag (v₂ :: done) ms ρ :: rest) :=
          stackRefK_refl_constrField_asym hρ hms_closed
            (ih n hrest) hnew_done (Nat.le_refl _)
        exact Moist.Verified.FundamentalRefines.ftlr d m hm_closed n
          n (Nat.le_refl _) ρ ρ hρ_refl n (Nat.le_refl _) _ _ hπ_new
    | @caseScrutinee alts ρ d hρ hlen hc =>
      -- .ret (.caseScrutinee alts ρ :: rest) v
      -- Behaviour depends on v: VConstr → dispatch alts[tag]?; VCon → constToTagAndFields
      -- Both sides dispatch identically via ValueRefinesK.
      simp only [step]
      match v₁, v₂ with
      | .VConstr tag₁ fields₁, .VConstr tag₂ fields₂ =>
        simp only [ValueRefinesK] at hv
        obtain ⟨rfl, hfields⟩ := hv
        simp only
        -- alts[tag]? is the same on both sides.
        cases halts : alts[tag₁]? with
        | none => simp only ; exact obsRefinesK_error _
        | some alt =>
          simp only
          -- compute ((fields.map applyArg) ++ rest) ρ alt
          have halt_closed : closedAt d alt = true := by
            have : alt ∈ alts := List.mem_of_getElem? halts
            exact closedAt_of_mem hc this
          have hρ_refl : EnvRefinesK n d ρ ρ := envRefinesK_refl hρ
          have hfields_rel : ListRel (ValueRefinesK n) fields₁ fields₂ :=
            listRel_valueRefinesK_mono (by omega : n ≤ n) hfields
          have hπ_new : StackRefK ValueRefinesK n
              (fields₁.map Frame.applyArg ++ rest) (fields₂.map Frame.applyArg ++ rest) :=
            applyArgFrames_stackRefK hfields_rel (ih n hrest)
          exact Moist.Verified.FundamentalRefines.ftlr d alt halt_closed n
            n (Nat.le_refl _) ρ ρ hρ_refl n (Nat.le_refl _) _ _ hπ_new
      | .VCon c₁, .VCon c₂ =>
        have hc_eq : c₁ = c₂ := by
          cases n with
          | zero => simp only [ValueRefinesK] at hv; exact hv
          | succ m => simp only [ValueRefinesK] at hv; exact hv
        subst hc_eq
        simp only
        cases hctf : constToTagAndFields c₁ with
        | none => simp only; exact obsRefinesK_error _
        | some val =>
          obtain ⟨tag, numCtors, fields⟩ := val
          simp only
          by_cases hcheck : (numCtors > 0 && alts.length > numCtors) = true
          · simp only [hcheck]
            exact obsRefinesK_error _
          · simp only [hcheck]
            cases halts : alts[tag]? with
            | none => simp only; exact obsRefinesK_error _
            | some alt =>
              simp only
              have halt_closed : closedAt d alt = true := by
                have : alt ∈ alts := List.mem_of_getElem? halts
                exact closedAt_of_mem hc this
              have hρ_refl : EnvRefinesK n d ρ ρ := envRefinesK_refl hρ
              have hfields_rel : ListRel (ValueRefinesK n) fields fields :=
                listRel_refl_vcon_refines n fields
                  (vcon_fields_of_constToTagAndFields hctf)
              have hπ_new : StackRefK ValueRefinesK n
                  (fields.map Frame.applyArg ++ rest) (fields.map Frame.applyArg ++ rest) :=
                applyArgFrames_stackRefK hfields_rel (ih n hrest)
              exact Moist.Verified.FundamentalRefines.ftlr d alt halt_closed n
                n (Nat.le_refl _) ρ ρ hρ_refl n (Nat.le_refl _) _ _ hπ_new
      | .VLam _ _, .VLam _ _ => exact obsRefinesK_error _
      | .VDelay _ _, .VDelay _ _ => exact obsRefinesK_error _
      | .VBuiltin _ _ _, .VBuiltin _ _ _ => exact obsRefinesK_error _
      | .VCon _, .VLam _ _ | .VCon _, .VDelay _ _ | .VCon _, .VConstr _ _
      | .VCon _, .VBuiltin _ _ _ | .VLam _ _, .VCon _ | .VLam _ _, .VDelay _ _
      | .VLam _ _, .VConstr _ _ | .VLam _ _, .VBuiltin _ _ _
      | .VDelay _ _, .VCon _ | .VDelay _ _, .VLam _ _ | .VDelay _ _, .VConstr _ _
      | .VDelay _ _, .VBuiltin _ _ _ | .VConstr _ _, .VCon _
      | .VConstr _ _, .VLam _ _ | .VConstr _ _, .VDelay _ _
      | .VConstr _ _, .VBuiltin _ _ _ | .VBuiltin _ _ _, .VCon _
      | .VBuiltin _ _ _, .VLam _ _ | .VBuiltin _ _ _, .VDelay _ _
      | .VBuiltin _ _ _, .VConstr _ _ => simp only [ValueRefinesK] at hv

--------------------------------------------------------------------------------
-- 11. Halt/error shift refinement: ObsRefinesK core for β-value proof
--
-- The step-indexed core observation used by the β-value refinement: the
-- original term under `ρ` stack `π` is `ObsRefinesK`-refined by the shifted
-- term under `ρ.extend arg` on the same stack `π`. This follows directly
-- from `renameRefinesR_shift1` (the right-side specialization of the
-- generalized rename fundamental theorem) once we establish reflexivity
-- of the environment and stack via `envRefinesK_refl` / `stackRefK_refl`.
--
-- **Note on formulation**: The originally requested form of this theorem
-- used `steps m _ = .ret π v` / `.ret π v'` halt-witness style statements.
-- That formulation is **not provable in isolation** because:
--   * `ObsRefinesK`'s halt clause requires `.halt v`, not `.ret π v`.
--     Bridging `.ret π v` to a halt witness requires case analysis on `π`
--     (empty stack halts in one more step; non-empty stack processes frames
--     with complex, stack-descending behaviour).
--   * `ObsRefinesK`'s error clause says `LHS.error → RHS.error`, not the
--     direction needed to conclude `RHS.no-error` from `LHS.no-error`.
--     The latter direction requires a **bidirectional** relation (e.g.,
--     `ObsEqK`) which is not what `renameRefinesR_shift1` provides.
--
-- The `ObsRefinesK`-valued form below is the strongest statement
-- derivable from `renameRefinesR_shift1` + reflexivity, and it is
-- sufficient for the downstream β-value refinement argument: callers
-- extract whatever halt/error information they need from the refinement.
--------------------------------------------------------------------------------

/-- **Shift refinement**: the original term `r` under `ρ` with stack `π`
    is `ObsRefinesK`-refined by the shifted term `renameTerm (shiftRename 1) r`
    under `ρ.extend arg` with the same stack `π`. Follows from
    `renameRefinesR_shift1` combined with reflexivity of `ρ` (via
    `envRefinesK_refl`) and of `π` (via `stackRefK_refl`). The extended
    value `arg` becomes position 1 of the RHS env; the shift lifts every
    variable in `r` by one to skip over it.

    Callers needing a halt/error-specific witness unpack the `ObsRefinesK`
    at the appropriate step index and invoke its halt or error clause.

    Parameters:
    * `r` / `d` / `hclosed` — the term and its closedness depth.
    * `ρ` / `arg` / `π` with well-formedness hypotheses — the runtime
      data for both sides of the refinement.
    * `k` — the step index at which the refinement is stated. -/
theorem halt_reach_shift (r : Term) (d : Nat)
    (hclosed : closedAt d r = true)
    (k : Nat)
    (ρ : CekEnv) (arg : CekValue) (π : Stack)
    (hwf_env : EnvWellFormed d ρ)
    (_hwf_arg : ValueWellFormed arg)
    (hwf_π : StackWellFormed π) :
    ObsRefinesK k
      (.compute π ρ r)
      (.compute π (ρ.extend arg)
         (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) r)) := by
  -- Reflexivity of the environment at step index `k`.
  have h_env_refl : EnvRefinesK k d ρ ρ := envRefinesK_refl hwf_env
  -- Bridge to `RenameEnvRefR (shiftRename 1)`, the form expected by
  -- `renameRefinesR_shift1`.
  have h_rename_env :
      Moist.Verified.FundamentalRefines.RenameEnvRefR
        (Moist.Verified.shiftRename 1) k d ρ (ρ.extend arg) :=
    Moist.Verified.FundamentalRefines.envRefinesK_to_renameEnvRefR_shift h_env_refl
  -- Reflexivity of the stack at step index `k`.
  have h_stack_refl : StackRefK ValueRefinesK k π π := stackRefK_refl k π hwf_π
  -- Assemble via `renameRefinesR_shift1`.
  exact Moist.Verified.FundamentalRefines.renameRefinesR_shift1 d r hclosed k k
    (Nat.le_refl _) ρ (ρ.extend arg) h_rename_env k (Nat.le_refl _) π π h_stack_refl

--------------------------------------------------------------------------------
-- 12. Step-composition helpers
--
-- Local copies of `steps_trans` / `steps_halt_fixed` / `steps_error_eq`.
-- Re-exposed since the originals in DeadLet.lean are `private`.
--------------------------------------------------------------------------------

/-- Transitivity of `steps`: stepping `m + n` equals stepping `n` after stepping `m`. -/
theorem steps_trans (m n : Nat) (s : State) :
    steps (m + n) s = steps n (steps m s) := by
  induction m generalizing s with
  | zero => simp [steps]
  | succ m ih => simp only [Nat.succ_add, steps]; exact ih (step s)

/-- `halt v` is a fixed point of `step`. -/
theorem steps_halt_fixed (n : Nat) (v : CekValue) :
    steps n (.halt v) = .halt v := by
  induction n with
  | zero => rfl
  | succ n ih => simp [steps, step, ih]

/-- `.error` is a fixed point of `step`. -/
theorem steps_error_fixed : ∀ (n : Nat), steps n (.error : State) = .error
  | 0 => rfl
  | n + 1 => by simp only [steps, step]; exact steps_error_fixed n

--------------------------------------------------------------------------------
-- 13. Leftward ObsRefinesK propagation
--
-- If LHS takes `n` deterministic steps to `s₁'` and `s₁'` Obs-refines `s₂`,
-- then the pre-step `s₁` also Obs-refines `s₂`.
--------------------------------------------------------------------------------

theorem obsRefinesK_of_steps_left {k n : Nat} {s₁ s₁' s₂ : State}
    (h_steps : steps n s₁ = s₁') (h : ObsRefinesK k s₁' s₂) :
    ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v ⟨m, hmk, hsteps_v⟩
    by_cases hmn : m ≤ n
    · have hs₁'_halt : s₁' = .halt v := by
        rw [← h_steps]
        have hsplit : n = m + (n - m) := by omega
        rw [hsplit, steps_trans, hsteps_v, steps_halt_fixed]
      rw [hs₁'_halt] at h
      exact h.1 v ⟨0, Nat.zero_le _, rfl⟩
    · have h_s₁'_halt : steps (m - n) s₁' = .halt v := by
        have hsplit : m = n + (m - n) := by omega
        rw [← h_steps, ← steps_trans, ← hsplit]
        exact hsteps_v
      have hmn_le : m - n ≤ k := by omega
      exact h.1 v ⟨m - n, hmn_le, h_s₁'_halt⟩
  · intro n' hn' herr
    by_cases hmn : n' ≤ n
    · have hs₁'_err : s₁' = .error := by
        rw [← h_steps]
        have hsplit : n = n' + (n - n') := by omega
        rw [hsplit, steps_trans, herr, steps_error_fixed]
      rw [hs₁'_err] at h
      exact h.2 0 (Nat.zero_le _) rfl
    · have h_s₁'_err : steps (n' - n) s₁' = .error := by
        have hsplit : n' = n + (n' - n) := by omega
        rw [← h_steps, ← steps_trans, ← hsplit]
        exact herr
      have hmn_le : n' - n ≤ k := by omega
      exact h.2 (n' - n) hmn_le h_s₁'_err

/-- Rightward propagation: if RHS reaches `s₂'` in `n` steps and `s₁`
    Obs-refines `s₂'`, then `s₁` also Obs-refines the pre-step `s₂`. -/
theorem obsRefinesK_of_steps_right {k n : Nat} {s₁ s₂ s₂' : State}
    (h_steps : steps n s₂ = s₂') (h : ObsRefinesK k s₁ s₂') :
    ObsRefinesK k s₁ s₂ := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨v', m, hm⟩ := h.1 v hv
    refine ⟨v', n + m, ?_⟩
    rw [steps_trans n m, h_steps]; exact hm
  · intro n' hn' herr
    obtain ⟨m, hm⟩ := h.2 n' hn' herr
    refine ⟨n + m, ?_⟩
    rw [steps_trans n m, h_steps]; exact hm

--------------------------------------------------------------------------------
-- 14. substRefinesR — the substitution fundamental theorem
--
-- Given a term `t` closed at depth `d + 1` and a replacement `r` closed at
-- depth `d`, for any `SubstEnvRef`-related pair of envs at position `pos`
-- with witness `v_rhs`, and any related stacks, we have
--   ObsRefinesK i (compute π₁ ρ₁ t) (compute π₂ ρ₂ (substTerm pos r t))
-- assuming `r` evaluates (from any sized env, on any initial stack) to a
-- value that `ValueRefinesK`-relates to `v_rhs`.
--
-- The `h_r_eval` hypothesis captures the required evaluation:
--   "r halts in any sized env, to a value related to v_rhs"
-- This is what lets the `Var n = pos` case step the RHS through `r`'s
-- evaluation and close using `SubstEnvRef`'s `v_rhs`-relation at position `pos`.
--------------------------------------------------------------------------------

/-- Evaluation precondition on `r`: for any sized env `ρ`, any stack `π`, `r`
    halts deterministically (and without error) to a value `v_r'` that
    `ValueRefinesK k v_rhs v_r'`. This is exactly the property consumed by
    the `Var n = pos` case of `substRefinesR`. -/
def RHalts (r : Term) (v_rhs : CekValue) (k d : Nat) : Prop :=
  ∀ (ρ : CekEnv) (π : Stack),
    (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
    ∃ (m : Nat) (v_r' : CekValue),
      steps m (.compute π ρ r) = .ret π v_r' ∧
      (∀ k' ≤ m, steps k' (.compute π ρ r) ≠ .error) ∧
      ValueRefinesK k v_rhs v_r'

/-- Apply `SubstEnvRef` at `n < pos`: lookups on both sides give
    `ValueRefinesK`-related values. -/
private theorem substEnvRef_below_pos {pos k d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂)
    {n : Nat} (hn : 0 < n) (hnd : n ≤ d) (h_lt : n < pos) :
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧
      ValueRefinesK k v₁ v₂ := by
  have hcase := h n hn hnd
  simp only [h_lt, if_true] at hcase
  match hρ₁ : ρ₁.lookup n, hρ₂ : ρ₂.lookup n with
  | some v₁, some v₂ =>
    rw [hρ₁, hρ₂] at hcase
    exact ⟨v₁, v₂, rfl, rfl, hcase⟩
  | some _, none => rw [hρ₁, hρ₂] at hcase; exact hcase.elim
  | none, some _ => rw [hρ₁, hρ₂] at hcase; exact hcase.elim
  | none, none => rw [hρ₁, hρ₂] at hcase; exact hcase.elim

/-- Apply `SubstEnvRef` at `n = pos`: lookup on LHS gives value related to
    `v_rhs`. -/
private theorem substEnvRef_at_pos {pos k d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂)
    (hn : 0 < pos) (hnd : pos ≤ d) :
    ∃ v₁, ρ₁.lookup pos = some v₁ ∧ ValueRefinesK k v₁ v_rhs := by
  have hcase := h pos hn hnd
  have h_not_lt : ¬ (pos < pos) := Nat.lt_irrefl _
  simp only [h_not_lt, if_false, if_true] at hcase
  match hρ₁ : ρ₁.lookup pos with
  | some v₁ =>
    rw [hρ₁] at hcase
    exact ⟨v₁, rfl, hcase⟩
  | none => rw [hρ₁] at hcase; exact hcase.elim

/-- Apply `SubstEnvRef` at `n > pos`: lookups give `ValueRefinesK`-related
    values at positions `n` on LHS and `n - 1` on RHS. -/
private theorem substEnvRef_above_pos {pos k d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂)
    {n : Nat} (hn : 0 < n) (hnd : n ≤ d) (h_gt : n > pos) :
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup (n - 1) = some v₂ ∧
      ValueRefinesK k v₁ v₂ := by
  have hcase := h n hn hnd
  have h_not_lt : ¬ (n < pos) := by omega
  have h_not_eq : n ≠ pos := by omega
  simp only [h_not_lt, h_not_eq, if_false] at hcase
  match hρ₁ : ρ₁.lookup n, hρ₂ : ρ₂.lookup (n - 1) with
  | some v₁, some v₂ =>
    rw [hρ₁, hρ₂] at hcase
    exact ⟨v₁, v₂, rfl, rfl, hcase⟩
  | some _, none => rw [hρ₁, hρ₂] at hcase; exact hcase.elim
  | none, some _ => rw [hρ₁, hρ₂] at hcase; exact hcase.elim
  | none, none => rw [hρ₁, hρ₂] at hcase; exact hcase.elim

/-- `ρ₁` is sized at depth `d`: every index `1..d` has a value. -/
private theorem sized_of_substEnvRef {pos k d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} (h : SubstEnvRef pos v_rhs k d ρ₁ ρ₂)
    (hpos : 1 ≤ pos) (hposd : pos ≤ d) :
    ∀ n, 0 < n → n ≤ d → ∃ v, ρ₁.lookup n = some v := by
  intro n hn hnd
  by_cases h1 : n < pos
  · obtain ⟨v₁, _, hl₁, _, _⟩ := substEnvRef_below_pos h hn hnd h1
    exact ⟨v₁, hl₁⟩
  · by_cases h2 : n = pos
    · subst h2
      obtain ⟨v₁, hl₁, _⟩ := substEnvRef_at_pos h hn hnd
      exact ⟨v₁, hl₁⟩
    · have h_gt : n > pos := by omega
      obtain ⟨v₁, _, hl₁, _, _⟩ := substEnvRef_above_pos h hn hnd h_gt
      exact ⟨v₁, hl₁⟩

/-- `substTermList`'s `getElem` distributes through the element access. -/
theorem substTermList_getElem (pos : Nat) (r : Term) (ts : List Term) (i : Nat)
    (hi : i < ts.length) :
    (Moist.Verified.substTermList pos r ts)[i]'(by
      rw [Moist.Verified.substTermList_length]; exact hi) =
    Moist.Verified.substTerm pos r (ts[i]) := by
  induction ts generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons t rest ih =>
    cases i with
    | zero => simp [Moist.Verified.substTermList]
    | succ j =>
      simp only [Moist.Verified.substTermList, List.getElem_cons_succ]
      exact ih j (by simp at hi; omega)

/-- `substEnvRef_extend` specialized: when `pos` is `1`, extending by a pair
    of related values pushes `pos` up to `2` while keeping `v_rhs` at
    position `2` (one above the new binding). -/
private theorem substEnvRef_extend_from_one {k d : Nat} {v_rhs : CekValue}
    {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue}
    (hv : ValueRefinesK k v₁ v₂)
    (h : SubstEnvRef 1 v_rhs k d ρ₁ ρ₂) :
    SubstEnvRef 2 v_rhs k (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) :=
  substEnvRef_extend (by omega : 1 ≤ 1) hv h

--------------------------------------------------------------------------------
-- 15. Stack-suffix discipline inversion (public port from DeadLet.lean).
--
-- If CEK execution starting from a state whose stack has `baseπ` as a suffix
-- eventually halts, then the execution must pass through `ret baseπ v_inner`
-- for some value. This is the "stack base discipline" fact used by the
-- β-value refinement proof to extract the rhs's final value without a purity
-- precondition on rhs.
--------------------------------------------------------------------------------

/-- Stack-suffix invariant: `s`'s stack contains `baseπ` as a suffix. -/
def hasSuffix (baseπ : Stack) : State → Prop
  | .compute π _ _ => ∃ rest, π = rest ++ baseπ
  | .ret π _ => ∃ rest, π = rest ++ baseπ
  | _ => False

/-- `steps n .error = .error`. -/
theorem steps_error_eq : ∀ (n : Nat), steps n (.error : State) = .error
  | 0 => rfl
  | n + 1 => by simp only [steps, step]; exact steps_error_eq n

/-- Packaging: given that `s` steps to `s'` (via `hstep`), `s'` has the
    invariant, and `ih` gives a witness for `s'` at halt time `n'`, produce
    a witness for `s` at halt time `n' + 1`. -/
private theorem halt_descends_package
    {baseπ : Stack} {s s' : State} {n' : Nat} {v_halt : CekValue}
    (hstep : step s = s')
    (hs_next : steps n' s' = .halt v_halt)
    (h_next_inv : hasSuffix baseπ s')
    (ih : ∀ (s : State) (v_halt : CekValue),
            steps n' s = .halt v_halt → hasSuffix baseπ s →
            ∃ m, m ≤ n' ∧ ∃ v_inner, steps m s = .ret baseπ v_inner) :
    ∃ m, m ≤ n' + 1 ∧ ∃ v_inner, steps m s = .ret baseπ v_inner := by
  obtain ⟨m, hm_le, v_inner, hm_steps⟩ := ih s' v_halt hs_next h_next_inv
  refine ⟨m + 1, by omega, v_inner, ?_⟩
  show steps (m + 1) s = .ret baseπ v_inner
  simp only [steps]
  rw [hstep]
  exact hm_steps

/-- The inversion lemma. Proved by strong induction on `n` with explicit case
    analysis on the state shape. For each state case, we compute `step s` via
    direct reflexivity and recurse on the stepped state. -/
theorem halt_descends_to_baseπ {baseπ : Stack} :
    ∀ (n : Nat) (s : State) (v_halt : CekValue),
      steps n s = .halt v_halt →
      hasSuffix baseπ s →
      ∃ m, m ≤ n ∧ ∃ v_inner, steps m s = .ret baseπ v_inner := by
  intro n
  induction n with
  | zero =>
    intro s v_halt hs hinv
    simp only [steps] at hs
    subst hs
    cases hinv
  | succ n' ih =>
    intro s v_halt hs hinv
    by_cases hat : ∃ v, s = .ret baseπ v
    · obtain ⟨v, rfl⟩ := hat
      exact ⟨0, by omega, v, by simp [steps]⟩
    · have hs_next : steps n' (step s) = .halt v_halt := by
        have heq : steps (n' + 1) s = steps n' (step s) := by simp only [steps]
        rw [← heq]; exact hs
      have h_not_err : step s ≠ .error := by
        intro heq
        rw [heq, steps_error_eq] at hs_next
        exact State.noConfusion hs_next
      -- Case analyze s. Use tactic `cases` throughout.
      cases s with
      | error => exact absurd hinv (by intro h; cases h)
      | halt _ => exact absurd hinv (by intro h; cases h)
      | compute π ρ t =>
        obtain ⟨rest, hrest⟩ := hinv
        subst hrest
        cases t with
        | Var x =>
          cases hlk : ρ.lookup x with
          | none =>
            exfalso; apply h_not_err
            show step (.compute (rest ++ baseπ) ρ (.Var x)) = .error
            simp only [step, hlk]
          | some v_val =>
            have hstep : step (.compute (rest ++ baseπ) ρ (.Var x)) =
                .ret (rest ++ baseπ) v_val := by
              simp only [step, hlk]
            exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Constant c_pair =>
          obtain ⟨c, ty⟩ := c_pair
          have hstep : step (.compute (rest ++ baseπ) ρ (.Constant (c, ty))) =
              .ret (rest ++ baseπ) (.VCon c) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Builtin b =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Builtin b)) =
              .ret (rest ++ baseπ) (.VBuiltin b [] (expectedArgs b)) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Lam name body =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Lam name body)) =
              .ret (rest ++ baseπ) (.VLam body ρ) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Delay body =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Delay body)) =
              .ret (rest ++ baseπ) (.VDelay body ρ) := rfl
          exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
        | Force e =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Force e)) =
              .compute (.force :: (rest ++ baseπ)) ρ e := rfl
          have h_inv_next : hasSuffix baseπ (.compute (.force :: (rest ++ baseπ)) ρ e) := by
            refine ⟨.force :: rest, ?_⟩
            simp
          exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Apply f a =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Apply f a)) =
              .compute (.arg a ρ :: (rest ++ baseπ)) ρ f := rfl
          have h_inv_next : hasSuffix baseπ (.compute (.arg a ρ :: (rest ++ baseπ)) ρ f) := by
            refine ⟨.arg a ρ :: rest, ?_⟩
            simp
          exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Constr tag fs =>
          cases fs with
          | nil =>
            have hstep : step (.compute (rest ++ baseπ) ρ (.Constr tag [])) =
                .ret (rest ++ baseπ) (.VConstr tag []) := rfl
            exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest, rfl⟩ ih
          | cons m ms =>
            have hstep : step (.compute (rest ++ baseπ) ρ (.Constr tag (m :: ms))) =
                .compute (.constrField tag [] ms ρ :: (rest ++ baseπ)) ρ m := rfl
            have h_inv_next : hasSuffix baseπ
                (.compute (.constrField tag [] ms ρ :: (rest ++ baseπ)) ρ m) := by
              refine ⟨.constrField tag [] ms ρ :: rest, ?_⟩
              simp
            exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Case scrut alts =>
          have hstep : step (.compute (rest ++ baseπ) ρ (.Case scrut alts)) =
              .compute (.caseScrutinee alts ρ :: (rest ++ baseπ)) ρ scrut := rfl
          have h_inv_next : hasSuffix baseπ
              (.compute (.caseScrutinee alts ρ :: (rest ++ baseπ)) ρ scrut) := by
            refine ⟨.caseScrutinee alts ρ :: rest, ?_⟩
            simp
          exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
        | Error =>
          exfalso; apply h_not_err
          show step (.compute (rest ++ baseπ) ρ .Error) = .error
          rfl
      | ret π v =>
        obtain ⟨rest, hrest⟩ := hinv
        subst hrest
        cases rest with
        | nil => exact absurd ⟨v, rfl⟩ hat
        | cons f rest' =>
          cases f with
          | force =>
            cases v with
            | VDelay body ρ_v =>
              have hstep : step (.ret (.force :: rest' ++ baseπ) (.VDelay body ρ_v)) =
                  .compute (rest' ++ baseπ) ρ_v body := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | VBuiltin b args ea =>
              have hstep_form : step (.ret (.force :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                  (match ea.head with
                   | .argQ => (match ea.tail with
                       | some r => (.ret (rest' ++ baseπ) (.VBuiltin b args r) : State)
                       | none => (match evalBuiltin b args with
                           | some v' => .ret (rest' ++ baseπ) v'
                           | none => .error))
                   | .argV => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases heh : ea.head with
              | argV =>
                rw [heh] at h_not_err
                exact absurd rfl h_not_err
              | argQ =>
                rw [heh] at hs_next h_not_err
                cases het : ea.tail with
                | some r =>
                  rw [het] at hs_next h_not_err
                  have h_inv_next : hasSuffix baseπ
                      (.ret (rest' ++ baseπ) (.VBuiltin b args r)) := ⟨rest', rfl⟩
                  obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                    ih (.ret (rest' ++ baseπ) (.VBuiltin b args r)) v_halt hs_next h_inv_next
                  refine ⟨m + 1, by omega, v_inner, ?_⟩
                  show steps (m + 1) (.ret (.force :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                      .ret baseπ v_inner
                  simp only [steps]
                  rw [hstep_form, heh, het]
                  exact hm_steps
                | none =>
                  rw [het] at hs_next h_not_err
                  cases hev : evalBuiltin b args with
                  | none =>
                    rw [hev] at h_not_err
                    exact absurd rfl h_not_err
                  | some v' =>
                    rw [hev] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ (.ret (rest' ++ baseπ) v') := ⟨rest', rfl⟩
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.ret (rest' ++ baseπ) v') v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1) (.ret (.force :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, heh, het, hev]
                    exact hm_steps
            | VCon c =>
              exfalso; apply h_not_err
              show step (.ret (.force :: rest' ++ baseπ) (.VCon c)) = .error
              rfl
            | VLam body ρ_l =>
              exfalso; apply h_not_err
              show step (.ret (.force :: rest' ++ baseπ) (.VLam body ρ_l)) = .error
              rfl
            | VConstr tag fields =>
              exfalso; apply h_not_err
              show step (.ret (.force :: rest' ++ baseπ) (.VConstr tag fields)) = .error
              rfl
          | arg a ρ_a =>
            have hstep : step (.ret (.arg a ρ_a :: rest' ++ baseπ) v) =
                .compute (.funV v :: (rest' ++ baseπ)) ρ_a a := rfl
            have h_inv_next : hasSuffix baseπ
                (.compute (.funV v :: (rest' ++ baseπ)) ρ_a a) := by
              refine ⟨.funV v :: rest', ?_⟩
              simp
            exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
          | funV vf =>
            cases vf with
            | VLam body ρ_l =>
              have hstep : step (.ret (.funV (.VLam body ρ_l) :: rest' ++ baseπ) v) =
                  .compute (rest' ++ baseπ) (ρ_l.extend v) body := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | VBuiltin b args ea =>
              have hstep_form : step (.ret (.funV (.VBuiltin b args ea) :: rest' ++ baseπ) v) =
                  (match ea.head with
                   | .argV => (match ea.tail with
                       | some r => (.ret (rest' ++ baseπ) (.VBuiltin b (v :: args) r) : State)
                       | none => (match evalBuiltin b (v :: args) with
                           | some v' => .ret (rest' ++ baseπ) v'
                           | none => .error))
                   | .argQ => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases heh : ea.head with
              | argQ =>
                rw [heh] at h_not_err
                exact absurd rfl h_not_err
              | argV =>
                rw [heh] at hs_next h_not_err
                cases het : ea.tail with
                | some r =>
                  rw [het] at hs_next h_not_err
                  have h_inv_next : hasSuffix baseπ
                      (.ret (rest' ++ baseπ) (.VBuiltin b (v :: args) r)) := ⟨rest', rfl⟩
                  obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                    ih (.ret (rest' ++ baseπ) (.VBuiltin b (v :: args) r)) v_halt hs_next h_inv_next
                  refine ⟨m + 1, by omega, v_inner, ?_⟩
                  show steps (m + 1) (.ret (.funV (.VBuiltin b args ea) :: rest' ++ baseπ) v) =
                      .ret baseπ v_inner
                  simp only [steps]
                  rw [hstep_form, heh, het]
                  exact hm_steps
                | none =>
                  rw [het] at hs_next h_not_err
                  cases hev : evalBuiltin b (v :: args) with
                  | none =>
                    rw [hev] at h_not_err
                    exact absurd rfl h_not_err
                  | some v' =>
                    rw [hev] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ (.ret (rest' ++ baseπ) v') := ⟨rest', rfl⟩
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.ret (rest' ++ baseπ) v') v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1) (.ret (.funV (.VBuiltin b args ea) :: rest' ++ baseπ) v) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, heh, het, hev]
                    exact hm_steps
            | VCon c =>
              exfalso; apply h_not_err
              show step (.ret (.funV (.VCon c) :: rest' ++ baseπ) v) = .error
              rfl
            | VDelay body ρ_d =>
              exfalso; apply h_not_err
              show step (.ret (.funV (.VDelay body ρ_d) :: rest' ++ baseπ) v) = .error
              rfl
            | VConstr tag fields =>
              exfalso; apply h_not_err
              show step (.ret (.funV (.VConstr tag fields) :: rest' ++ baseπ) v) = .error
              rfl
          | applyArg vx =>
            cases v with
            | VLam body ρ_l =>
              have hstep : step (.ret (.applyArg vx :: rest' ++ baseπ) (.VLam body ρ_l)) =
                  .compute (rest' ++ baseπ) (ρ_l.extend vx) body := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | VBuiltin b args ea =>
              have hstep_form : step (.ret (.applyArg vx :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                  (match ea.head with
                   | .argV => (match ea.tail with
                       | some r => (.ret (rest' ++ baseπ) (.VBuiltin b (vx :: args) r) : State)
                       | none => (match evalBuiltin b (vx :: args) with
                           | some v' => .ret (rest' ++ baseπ) v'
                           | none => .error))
                   | .argQ => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases heh : ea.head with
              | argQ =>
                rw [heh] at h_not_err
                exact absurd rfl h_not_err
              | argV =>
                rw [heh] at hs_next h_not_err
                cases het : ea.tail with
                | some r =>
                  rw [het] at hs_next h_not_err
                  have h_inv_next : hasSuffix baseπ
                      (.ret (rest' ++ baseπ) (.VBuiltin b (vx :: args) r)) := ⟨rest', rfl⟩
                  obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                    ih (.ret (rest' ++ baseπ) (.VBuiltin b (vx :: args) r)) v_halt hs_next h_inv_next
                  refine ⟨m + 1, by omega, v_inner, ?_⟩
                  show steps (m + 1) (.ret (.applyArg vx :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                      .ret baseπ v_inner
                  simp only [steps]
                  rw [hstep_form, heh, het]
                  exact hm_steps
                | none =>
                  rw [het] at hs_next h_not_err
                  cases hev : evalBuiltin b (vx :: args) with
                  | none =>
                    rw [hev] at h_not_err
                    exact absurd rfl h_not_err
                  | some v' =>
                    rw [hev] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ (.ret (rest' ++ baseπ) v') := ⟨rest', rfl⟩
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.ret (rest' ++ baseπ) v') v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1) (.ret (.applyArg vx :: rest' ++ baseπ) (.VBuiltin b args ea)) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, heh, het, hev]
                    exact hm_steps
            | VCon c =>
              exfalso; apply h_not_err
              show step (.ret (.applyArg vx :: rest' ++ baseπ) (.VCon c)) = .error
              rfl
            | VDelay body ρ_d =>
              exfalso; apply h_not_err
              show step (.ret (.applyArg vx :: rest' ++ baseπ) (.VDelay body ρ_d)) = .error
              rfl
            | VConstr tag fields =>
              exfalso; apply h_not_err
              show step (.ret (.applyArg vx :: rest' ++ baseπ) (.VConstr tag fields)) = .error
              rfl
          | constrField tag done ms ρ_c =>
            cases ms with
            | nil =>
              have hstep : step (.ret (.constrField tag done [] ρ_c :: rest' ++ baseπ) v) =
                  .ret (rest' ++ baseπ) (.VConstr tag ((v :: done).reverse)) := rfl
              exact halt_descends_package hstep (hstep ▸ hs_next) ⟨rest', rfl⟩ ih
            | cons m ms_rest =>
              have hstep : step (.ret (.constrField tag done (m :: ms_rest) ρ_c :: rest' ++ baseπ) v) =
                  .compute (.constrField tag (v :: done) ms_rest ρ_c :: (rest' ++ baseπ)) ρ_c m := rfl
              have h_inv_next : hasSuffix baseπ
                  (.compute (.constrField tag (v :: done) ms_rest ρ_c :: (rest' ++ baseπ)) ρ_c m) := by
                refine ⟨.constrField tag (v :: done) ms_rest ρ_c :: rest', ?_⟩
                simp
              exact halt_descends_package hstep (hstep ▸ hs_next) h_inv_next ih
          | caseScrutinee alts ρ_cs =>
            cases v with
            | VConstr tag_v fields_v =>
              have hstep_form :
                  step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VConstr tag_v fields_v)) =
                  (match alts[tag_v]? with
                   | some alt => (.compute (fields_v.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt : State)
                   | none => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases halts : alts[tag_v]? with
              | none =>
                rw [halts] at h_not_err
                exact absurd rfl h_not_err
              | some alt =>
                rw [halts] at hs_next h_not_err
                have h_inv_next : hasSuffix baseπ
                    (.compute (fields_v.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt) := by
                  refine ⟨fields_v.map Frame.applyArg ++ rest', ?_⟩
                  simp
                obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                  ih (.compute (fields_v.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt)
                     v_halt hs_next h_inv_next
                refine ⟨m + 1, by omega, v_inner, ?_⟩
                show steps (m + 1)
                    (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VConstr tag_v fields_v)) =
                    .ret baseπ v_inner
                simp only [steps]
                rw [hstep_form, halts]
                exact hm_steps
            | VCon c =>
              have hstep_form : step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VCon c)) =
                  (match constToTagAndFields c with
                   | some (tag, numCtors, fields) =>
                     (if numCtors > 0 && alts.length > numCtors then .error
                      else match alts[tag]? with
                        | some alt => (.compute (fields.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt : State)
                        | none => .error)
                   | none => .error) := rfl
              rw [hstep_form] at hs_next h_not_err
              cases htag : constToTagAndFields c with
              | none =>
                rw [htag] at h_not_err
                exact absurd rfl h_not_err
              | some triple =>
                obtain ⟨tag, numCtors, fields⟩ := triple
                rw [htag] at hs_next h_not_err
                dsimp only at hs_next h_not_err
                cases hb : (numCtors > 0 && alts.length > numCtors : Bool) with
                | true =>
                  rw [hb] at h_not_err
                  exact absurd rfl h_not_err
                | false =>
                  rw [hb] at hs_next h_not_err
                  cases halts : alts[tag]? with
                  | none =>
                    rw [halts] at h_not_err
                    exact absurd rfl h_not_err
                  | some alt =>
                    rw [halts] at hs_next h_not_err
                    have h_inv_next : hasSuffix baseπ
                        (.compute (fields.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt) := by
                      refine ⟨fields.map Frame.applyArg ++ rest', ?_⟩
                      simp
                    obtain ⟨m, hm_le, v_inner, hm_steps⟩ :=
                      ih (.compute (fields.map Frame.applyArg ++ (rest' ++ baseπ)) ρ_cs alt)
                         v_halt hs_next h_inv_next
                    refine ⟨m + 1, by omega, v_inner, ?_⟩
                    show steps (m + 1)
                        (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VCon c)) =
                        .ret baseπ v_inner
                    simp only [steps]
                    rw [hstep_form, htag]
                    dsimp only
                    rw [hb, halts]
                    exact hm_steps
            | VLam body ρ_l =>
              exfalso; apply h_not_err
              show step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VLam body ρ_l)) = .error
              rfl
            | VDelay body ρ_d =>
              exfalso; apply h_not_err
              show step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VDelay body ρ_d)) = .error
              rfl
            | VBuiltin b args ea =>
              exfalso; apply h_not_err
              show step (.ret (.caseScrutinee alts ρ_cs :: rest' ++ baseπ) (.VBuiltin b args ea)) = .error
              rfl

--------------------------------------------------------------------------------
-- 16. Strengthened RHalts (RHaltsRel): halt-witness + ValueRefinesK to v_rhs.
--
-- This is the hypothesis shape consumed by the `Var n = pos` case of
-- `substRefinesR_body`. It strengthens the plain `RHalts` with the
-- conclusion `ValueRefinesK k v_rhs v_rhs'`, so the substitution FTLR
-- can close without needing a separate `halt_reach_shift`-style bridge
-- to relate LHS/RHS halt values.
--------------------------------------------------------------------------------

/-- Strengthened `RHalts`: in addition to halt-no-error, the halt value
    is `ValueRefinesK`-related to a fixed witness `v_rhs`. This form
    provides the relation to a fixed witness value — exactly what the
    substitution FTLR's `Var = pos` case needs. -/
def RHaltsRel (t_rhs : Moist.Plutus.Term.Term) (v_rhs : CekValue) (k d : Nat) : Prop :=
  ∀ (ρ : CekEnv) (π : Stack),
    (∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v) →
    ∃ (m : Nat) (v_rhs' : CekValue),
      steps m (.compute π ρ t_rhs) = .ret π v_rhs' ∧
      (∀ k' ≤ m, steps k' (.compute π ρ t_rhs) ≠ .error) ∧
      ValueRefinesK k v_rhs v_rhs'

/-- Monotonicity of `RHaltsRel` in the step index. -/
theorem rHaltsRel_mono {j k d : Nat} (hjk : j ≤ k) {t_rhs : Moist.Plutus.Term.Term}
    {v_rhs : CekValue} (h : RHaltsRel t_rhs v_rhs k d) :
    RHaltsRel t_rhs v_rhs j d := by
  intro ρ π hρ
  obtain ⟨m, v_rhs', hm, hne, hrel⟩ := h ρ π hρ
  exact ⟨m, v_rhs', hm, hne, valueRefinesK_mono hjk v_rhs v_rhs' hrel⟩

--------------------------------------------------------------------------------
-- 16b. `RHaltsRelWF` — strengthened `RHaltsRel` bundling well-formedness.
--
-- This is the hypothesis shape used by the state-level shift proof. In
-- addition to the halt witness and the value-refinement to `v_rhs`, this
-- variant bundles:
--   * `closedAt d t_rhs` — closedness of the RHS term at depth `d`.
--   * `ValueWellFormed v_rhs` — well-formedness of the fixed witness value.
--   * `ValueWellFormed v_rhs'` — well-formedness of the halt value.
-- The universal ρ/π clause takes `EnvWellFormed d ρ` and `StackWellFormed π`
-- as hypotheses (rather than the weaker "every position ≤ d is some").
--------------------------------------------------------------------------------

/-- Strengthened `RHaltsRel` bundling well-formedness on both sides: the
    RHS term is closed at depth `d`, the witness `v_rhs` and halt value
    `v_rhs'` are both well-formed, and the universal ρ/π clause ranges
    over well-formed environments and stacks. -/
def RHaltsRelWF (t_rhs : Moist.Plutus.Term.Term) (v_rhs : CekValue)
    (k d : Nat) : Prop :=
  closedAt d t_rhs = true ∧
  ValueWellFormed v_rhs ∧
  ∀ (ρ : CekEnv) (π : Stack),
    EnvWellFormed d ρ → StackWellFormed π →
    ∃ (m : Nat) (v_rhs' : CekValue),
      steps m (.compute π ρ t_rhs) = .ret π v_rhs' ∧
      (∀ k' ≤ m, steps k' (.compute π ρ t_rhs) ≠ .error) ∧
      ValueRefinesK k v_rhs v_rhs' ∧
      ValueWellFormed v_rhs'

/-- Monotonicity of `RHaltsRelWF` in the step index. -/
theorem rHaltsRelWF_mono {j k d : Nat} (hjk : j ≤ k)
    {t_rhs : Moist.Plutus.Term.Term} {v_rhs : CekValue}
    (h : RHaltsRelWF t_rhs v_rhs k d) :
    RHaltsRelWF t_rhs v_rhs j d := by
  obtain ⟨hclosed, hv_rhs, heval⟩ := h
  refine ⟨hclosed, hv_rhs, ?_⟩
  intro ρ π hρ hπ
  obtain ⟨m, v_rhs', hm, hne, hrel, hwf⟩ := heval ρ π hρ hπ
  exact ⟨m, v_rhs', hm, hne, valueRefinesK_mono hjk v_rhs v_rhs' hrel, hwf⟩

/-- Closedness extraction from `RHaltsRelWF`. -/
theorem rHaltsRelWF_closed {t_rhs : Moist.Plutus.Term.Term} {v_rhs : CekValue}
    {k d : Nat} (h : RHaltsRelWF t_rhs v_rhs k d) :
    closedAt d t_rhs = true := h.1

/-- Witness well-formedness extraction from `RHaltsRelWF`. -/
theorem rHaltsRelWF_wf {t_rhs : Moist.Plutus.Term.Term} {v_rhs : CekValue}
    {k d : Nat} (h : RHaltsRelWF t_rhs v_rhs k d) :
    ValueWellFormed v_rhs := h.2.1

/-- Forgetting well-formedness: `RHaltsRelWF` implies the underlying
    `RHaltsRel`-style quantification (restricted to well-formed envs
    and stacks). -/
theorem rHaltsRel_of_rHaltsRelWF_wfEnv
    {t_rhs : Moist.Plutus.Term.Term} {v_rhs : CekValue} {k d : Nat}
    (h : RHaltsRelWF t_rhs v_rhs k d) :
    ∀ (ρ : CekEnv) (π : Stack), EnvWellFormed d ρ → StackWellFormed π →
      ∃ (m : Nat) (v_rhs' : CekValue),
        steps m (.compute π ρ t_rhs) = .ret π v_rhs' ∧
        (∀ k' ≤ m, steps k' (.compute π ρ t_rhs) ≠ .error) ∧
        ValueRefinesK k v_rhs v_rhs' := by
  intro ρ π hρ hπ
  obtain ⟨m, v_rhs', hm, hne, hrel, _⟩ := h.2.2 ρ π hρ hπ
  exact ⟨m, v_rhs', hm, hne, hrel⟩

/-- A well-formed env at depth `d` satisfies the sized-lookup predicate at
    depth `d`. Bridge used when adapting `RHaltsRel`-style hypotheses. -/
private theorem envWellFormed_sized_lookup {d : Nat} {ρ : CekEnv}
    (h : EnvWellFormed d ρ) :
    ∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v := by
  intro n hn hnd
  obtain ⟨v, hl, _⟩ := envWellFormed_lookup d h hn hnd
  exact ⟨v, hl⟩

--------------------------------------------------------------------------------
-- 16c. Environment decomposition for `EnvWellFormed (d + 1)`.
--
-- A well-formed env at positive depth `d + 1` must have cons-structure
-- `.cons v rest`, with `v` well-formed and `rest` well-formed at depth `d`.
-- This decomposition is the foundation of the shift-lifting proof: given
-- a well-formed `ρ_full` at depth `d + 1`, we extract `v0` and `ρ_tail`
-- with `ρ_full = ρ_tail.extend v0`.
--------------------------------------------------------------------------------

/-- `EnvWellFormed` at positive depth narrows the cons: if
    `EnvWellFormed (d + 1) (.cons v rest)`, then `EnvWellFormed d rest`
    (positions 1..d in rest correspond to positions 2..d+1 in the cons).
    Proved by structural induction on `d`. -/
private theorem envWellFormed_cons_tail_shift : ∀ (d : Nat) {v : CekValue} {rest : CekEnv},
    EnvWellFormed (d + 1) (.cons v rest) → EnvWellFormed d rest
  | 0, _, _, _ => EnvWellFormed.zero
  | d + 1, v, rest, h => by
    cases h with
    | @succ _ _ val h_rest h_len h_look h_val =>
      -- h_rest : EnvWellFormed (d + 1) (cons v rest)
      -- h_len : d + 2 ≤ (cons v rest).length
      -- h_look : (cons v rest).lookup (d + 2) = some val
      -- Need: EnvWellFormed (d + 1) rest.
      have ih : EnvWellFormed d rest := envWellFormed_cons_tail_shift d h_rest
      have h_rest_len : d + 1 ≤ rest.length := by
        have h_len_eq : (CekEnv.cons v rest).length = rest.length + 1 := by
          simp [CekEnv.length]
        rw [h_len_eq] at h_len; omega
      have h_look_rest : rest.lookup (d + 1) = some val := by
        have h_trans : (CekEnv.cons v rest).lookup (d + 1 + 1) = rest.lookup (d + 1) := rfl
        rw [h_trans] at h_look; exact h_look
      exact EnvWellFormed.succ ih h_rest_len h_look_rest h_val

/-- When `ρ` has length ≥ `d + 1` ≥ 1, we can decompose it as a cons. -/
private theorem envWellFormed_succ_cons {d : Nat} {ρ : CekEnv}
    (h : EnvWellFormed (d + 1) ρ) :
    ∃ (v : CekValue) (rest : CekEnv), ρ = .cons v rest := by
  have h_len : d + 1 ≤ ρ.length := envWellFormed_length (d + 1) h
  match ρ, h_len with
  | .cons v rest, _ => exact ⟨v, rest, rfl⟩

/-- From `EnvWellFormed (d + 1) (.cons v rest)`, extract the head value's
    well-formedness and the tail's well-formedness at depth `d`. -/
private theorem envWellFormed_cons_decompose {d : Nat} {v : CekValue} {rest : CekEnv}
    (h : EnvWellFormed (d + 1) (.cons v rest)) :
    EnvWellFormed d rest ∧ ValueWellFormed v := by
  have h_narrow : EnvWellFormed d rest := envWellFormed_cons_tail_shift d h
  have h_head : ValueWellFormed v := by
    cases h with
    | succ h_rest _ h_look h_val =>
      by_cases hd : d = 0
      · subst hd
        -- d + 1 = 1: the `.succ` constructor gave us lookup at position 1.
        have h_pos1 : (CekEnv.cons v rest).lookup 1 = some v := rfl
        rw [h_pos1] at h_look
        cases h_look
        exact h_val
      · -- d ≥ 1: use envWellFormed_lookup on h_rest at position 1.
        have h_rest_d_pos : 1 ≤ d := by omega
        obtain ⟨v_lookup, hl_eq, hv_wf⟩ :=
          envWellFormed_lookup d h_rest (by omega : 0 < 1) h_rest_d_pos
        have h_pos1 : (CekEnv.cons v rest).lookup 1 = some v := rfl
        rw [h_pos1] at hl_eq
        cases hl_eq
        exact hv_wf
  exact ⟨h_narrow, h_head⟩

--------------------------------------------------------------------------------
-- 16d. Step-composition helpers for halt-witness extraction.
--
-- Bridge `.ret [] v` halt traces (produced by `RHaltsRel` at π = []) to the
-- `.halt v` form consumed by `ObsRefinesK`'s halt clause: stepping a
-- `.ret [] v` state produces `.halt v`.
--------------------------------------------------------------------------------

/-- One more step from `.ret [] v` reaches `.halt v`. -/
theorem steps_ret_empty_halt {n : Nat} {s : State} {v : CekValue}
    (h : steps n s = .ret [] v) :
    steps (n + 1) s = .halt v := by
  have h_split : steps (n + 1) s = steps 1 (steps n s) := steps_trans n 1 s
  rw [h_split, h]
  rfl

/-- Existence halt-form: if `steps m s = .ret [] v`, then `s` reaches `.halt v`. -/
theorem reaches_halt_of_ret_empty {s : State} {m : Nat} {v : CekValue}
    (h : steps m s = .ret [] v) :
    Reaches s (.halt v) := ⟨m + 1, steps_ret_empty_halt h⟩

/-- `halt_reach_shift` specialized to produce an existence-of-halt witness:
    if the LHS halts in ≤ k' steps, the shifted RHS reaches halt. -/
theorem halt_reach_shift_existence (r : Moist.Plutus.Term.Term) (d : Nat)
    (hclosed : closedAt d r = true)
    (k' : Nat)
    (ρ : CekEnv) (arg : CekValue) (π : Stack)
    (hwf_env : EnvWellFormed d ρ)
    (hwf_arg : ValueWellFormed arg)
    (hwf_π : StackWellFormed π)
    {n : Nat} {v : CekValue} (h_halt : steps n (.compute π ρ r) = .halt v)
    (hn : n ≤ k') :
    ∃ (v'' : CekValue),
      Reaches (.compute π (ρ.extend arg)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) r)) (.halt v'') := by
  have h_obs : ObsRefinesK k'
      (.compute π ρ r)
      (.compute π (ρ.extend arg)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) r)) :=
    halt_reach_shift r d hclosed k' ρ arg π hwf_env hwf_arg hwf_π
  exact h_obs.1 v ⟨n, hn, h_halt⟩

--------------------------------------------------------------------------------
-- 16e. `rHalts_shift_WF` — state-level shift lemma.
--
-- STATUS: Proved CONDITIONALLY on an external `ValueShiftsPreserve`
-- hypothesis that delivers the `ValueRefinesK` and `ValueWellFormed`
-- conclusions on the RHS halt value. The halt-existence itself is
-- proved unconditionally via `halt_reach_shift` composed with the
-- `.ret [] v` → `.halt v` bridge, and lifted from π = [] to arbitrary
-- π via `value_stack_poly`.
--
-- The unconditional `rHalts_shift_WF` is blocked on the value-level
-- shift preservation (`valueRefinesK_shift_right`) — see memory notes
-- `rHalts_shift ValueRefinesK blocker` and `valueRefinesK_shift_right
-- blocker`. The state-level approach reaches the same fundamental wall:
-- halt values on both sides of the refinement are structurally distinct
-- (closures capture different envs: `ρ_tail` vs `ρ_tail.extend v0`),
-- and the only relation bridging them is `ValueRefinesK`, which is not
-- preserved by `shiftValue` in general without a deep step-indexed
-- induction.
--
-- The conditional form `rHalts_shift_WF_cond` below is fully usable by
-- callers: they supply the value-shift preservation as part of their
-- own preconditions.
--------------------------------------------------------------------------------

/-- **Value-shift hypothesis**: the external obligation carrying
    `ValueRefinesK` and `ValueWellFormed` from LHS halt values to the
    corresponding RHS halt values of `shift t_rhs`.

    This is the precise gap blocking an unconditional `rHalts_shift_WF`.
    Delivered separately (as a value-level shift preservation or a
    state-level bisim); see memory notes for current status on the
    general proof. -/
def ValueShiftsPreserve (t_rhs : Moist.Plutus.Term.Term) (v_rhs : CekValue)
    (k d : Nat) : Prop :=
  ∀ (ρ_full : CekEnv) (π : Stack),
    EnvWellFormed (d + 1) ρ_full → StackWellFormed π →
    ∀ (m : Nat) (v' : CekValue),
      steps m (.compute π ρ_full
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) = .ret π v' →
      ValueRefinesK k v_rhs v' ∧ ValueWellFormed v'

/-- Closedness lift: if `t` is closed at depth `d`, then `shift t` is
    closed at depth `d + 1`. -/
theorem closedAt_shift {d : Nat} {t : Moist.Plutus.Term.Term}
    (h : closedAt d t = true) :
    closedAt (d + 1) (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t) = true := by
  apply closedAt_rename (Moist.Verified.shiftRename 1) t d (d + 1) h
  intro n hn
  by_cases h_eq : n = 0
  · subst h_eq
    rw [Moist.Verified.shiftRename_lt (by omega : (0:Nat) < 1)]
    omega
  · have hn_pos : n ≥ 1 := by omega
    rw [Moist.Verified.shiftRename_ge hn_pos]
    omega

/-- **Conditional state-level shift lemma**: given the external
    value-shift obligation `h_preserve`, `RHaltsRelWF t_rhs v_rhs k d`
    lifts to `RHaltsRelWF (shift t_rhs) v_rhs k (d + 1)`.

    The proof:
    1. Decomposes `ρ_full` as `.cons v0 ρ_tail` via `envWellFormed_succ_cons`.
    2. Recognizes `.cons v0 ρ_tail = ρ_tail.extend v0`.
    3. Applies `h` at `ρ_tail` with π = [] to obtain the LHS halt witness
       `.ret [] v0'`, stepping once more to `.halt v0'`.
    4. Extracts the halt existence on the RHS via `halt_reach_shift`.
    5. Transports the π = [] halt witness to the general π via
       `value_stack_poly`, yielding `.ret π v_final` on the shifted RHS.
    6. Uses `h_preserve` at `(ρ_full, π)` to upgrade `v_final` into a
       `ValueRefinesK`-related, well-formed value. -/
theorem rHalts_shift_WF_cond {k d : Nat} {t_rhs : Moist.Plutus.Term.Term}
    {v_rhs : CekValue}
    (h : RHaltsRelWF t_rhs v_rhs k d)
    (h_preserve : ValueShiftsPreserve t_rhs v_rhs k d) :
    RHaltsRelWF (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)
      v_rhs k (d + 1) := by
  obtain ⟨hclosed, hv_rhs, heval⟩ := h
  refine ⟨closedAt_shift hclosed, hv_rhs, ?_⟩
  intro ρ_full π hwf_full hwf_π
  -- Decompose ρ_full = cons v0 ρ_tail.
  obtain ⟨v0, ρ_tail, hρ_eq⟩ := envWellFormed_succ_cons hwf_full
  subst hρ_eq
  obtain ⟨hwf_tail, hwf_v0⟩ := envWellFormed_cons_decompose hwf_full
  -- Get LHS halt witness at ρ_tail, π = [] to use halt_reach_shift.
  obtain ⟨m0, v0', h0_steps, _h0_noerr, _h0_rel, _h0_wf⟩ :=
    heval ρ_tail [] hwf_tail StackWellFormed.nil
  -- Bridge .ret [] v0' to .halt v0' in one more step.
  have h0_halt : steps (m0 + 1) (.compute [] ρ_tail t_rhs) = .halt v0' :=
    steps_ret_empty_halt h0_steps
  -- Apply halt_reach_shift at step index m0 + 1.
  have hreach :=
    halt_reach_shift_existence t_rhs d hclosed (m0 + 1) ρ_tail v0 []
      hwf_tail hwf_v0 StackWellFormed.nil h0_halt (Nat.le_refl _)
  obtain ⟨v_shifted, h_reaches⟩ := hreach
  -- Establish closedAt (d+1) on the shifted term.
  have h_closed_shift := closedAt_shift hclosed
  -- No-error at π = [] for the shifted term: derived from the halt trace.
  have h_noerr_0 : ∀ k_, steps k_ (.compute [] (ρ_tail.extend v0)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) ≠ .error := by
    intro k_ h_err
    obtain ⟨n_halt, h_halt_full⟩ := h_reaches
    by_cases h_le : k_ ≤ n_halt
    · have h_split : n_halt = k_ + (n_halt - k_) := by omega
      have h_via_err : steps n_halt (.compute [] (ρ_tail.extend v0)
          (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) = .error := by
        rw [h_split, steps_trans, h_err, steps_error_eq]
      rw [h_halt_full] at h_via_err
      exact State.noConfusion h_via_err
    · have h_gt : n_halt < k_ := Nat.lt_of_not_ge h_le
      have h_split : k_ = n_halt + (k_ - n_halt) := by omega
      have : steps k_ (.compute [] (ρ_tail.extend v0)
          (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs)) = .halt v_shifted := by
        rw [h_split, steps_trans, h_halt_full, steps_halt_fixed]
      rw [this] at h_err
      exact State.noConfusion h_err
  -- Apply value_stack_poly to lift halt from π = [] to given π.
  have hwf_size : Moist.Verified.Semantics.WellSizedEnv (d + 1) (ρ_tail.extend v0) := by
    intro n hn hnd
    have hn_pos : 0 < n := by omega
    obtain ⟨v, hl, _⟩ := envWellFormed_lookup (d + 1) hwf_full hn_pos hnd
    exact ⟨v, hl⟩
  obtain ⟨m_final, v_final, h_final_steps, h_final_noerr⟩ :=
    value_stack_poly (ρ_tail.extend v0)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t_rhs) (d + 1)
      hwf_size h_closed_shift ⟨v_shifted, h_reaches⟩ h_noerr_0 π
  -- Use h_preserve at (ρ_full, π) to extract ValueRefinesK and ValueWellFormed.
  obtain ⟨h_vref, h_vwf⟩ :=
    h_preserve (ρ_tail.extend v0) π hwf_full hwf_π m_final v_final h_final_steps
  exact ⟨m_final, v_final, h_final_steps, h_final_noerr, h_vref, h_vwf⟩

--------------------------------------------------------------------------------
-- 16f. `ValueRefinesK` inversions for constant witnesses.
--
-- When `v_rhs = .VCon c`, `ValueRefinesK k v_rhs v'` forces `v' = .VCon c`
-- at every step index. This makes the VCon case of `ValueShiftsPreserve`
-- reducible to a shape identification on the RHS halt value.
--------------------------------------------------------------------------------

/-- `ValueRefinesK k (.VCon c) v'` forces `v' = .VCon c`. -/
theorem valueRefinesK_VCon_inv (k : Nat) (c : Moist.Plutus.Term.Const) (v' : CekValue)
    (h : ValueRefinesK k (.VCon c) v') :
    v' = .VCon c := by
  cases v' with
  | VCon c' =>
    cases k with
    | zero => simp only [ValueRefinesK] at h; subst h; rfl
    | succ _ => simp only [ValueRefinesK] at h; subst h; rfl
  | VLam _ _ =>
    cases k with
    | zero => simp only [ValueRefinesK] at h
    | succ _ => simp only [ValueRefinesK] at h
  | VDelay _ _ =>
    cases k with
    | zero => simp only [ValueRefinesK] at h
    | succ _ => simp only [ValueRefinesK] at h
  | VConstr _ _ =>
    cases k with
    | zero => simp only [ValueRefinesK] at h
    | succ _ => simp only [ValueRefinesK] at h
  | VBuiltin _ _ _ =>
    cases k with
    | zero => simp only [ValueRefinesK] at h
    | succ _ => simp only [ValueRefinesK] at h

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- 17. Value-level shift operations and step-level bisimulation
--
-- Lift CEK values, environments, frames, stacks, and states from a depth-`d`
-- world to a depth-`(d+1)` world by inserting a fresh position 1 value `v0`
-- and renaming all embedded terms through `shiftRename 1`. Prove that CEK
-- `step` commutes with `shiftState`: this is the foundational bisimulation
-- lemma used downstream by `rHalts_shift` and `substRefinesR_body`.
--------------------------------------------------------------------------------

mutual
/-- Shift a CEK value by inserting a fresh position 1 in all captured envs.
    Used to "lift" values from depth-d world to depth-(d+1) world. -/
def shiftValue (v0 : CekValue) : CekValue → CekValue
  | .VCon c => .VCon c
  | .VLam body ρ =>
      .VLam (Moist.Verified.renameTerm (Moist.Verified.liftRename (Moist.Verified.shiftRename 1)) body)
            ((shiftEnv v0 ρ).extend v0)
  | .VDelay body ρ =>
      .VDelay (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) body)
              ((shiftEnv v0 ρ).extend v0)
  | .VConstr tag fs => .VConstr tag (shiftValueList v0 fs)
  | .VBuiltin b args ea => .VBuiltin b (shiftValueList v0 args) ea
termination_by v => sizeOf v

/-- Shift every value in a CEK environment. -/
def shiftEnv (v0 : CekValue) : CekEnv → CekEnv
  | .nil => .nil
  | .cons v rest => .cons (shiftValue v0 v) (shiftEnv v0 rest)
termination_by ρ => sizeOf ρ

/-- Shift every value in a list of CEK values. -/
def shiftValueList (v0 : CekValue) : List CekValue → List CekValue
  | [] => []
  | v :: rest => shiftValue v0 v :: shiftValueList v0 rest
termination_by vs => sizeOf vs
end

/-- Shift a frame by shifting all embedded values/envs and renaming embedded terms. -/
def shiftFrame (v0 : CekValue) : Frame → Frame
  | .force => .force
  | .arg t ρ =>
      .arg (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t)
           ((shiftEnv v0 ρ).extend v0)
  | .funV v => .funV (shiftValue v0 v)
  | .applyArg v => .applyArg (shiftValue v0 v)
  | .constrField tag done todo ρ =>
      .constrField tag (shiftValueList v0 done)
        (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) todo)
        ((shiftEnv v0 ρ).extend v0)
  | .caseScrutinee alts ρ =>
      .caseScrutinee (Moist.Verified.renameTermList (Moist.Verified.shiftRename 1) alts)
        ((shiftEnv v0 ρ).extend v0)

def shiftStack (v0 : CekValue) : Stack → Stack := List.map (shiftFrame v0)

def shiftState (v0 : CekValue) : State → State
  | .compute π ρ t =>
      .compute (shiftStack v0 π) ((shiftEnv v0 ρ).extend v0)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) t)
  | .ret π v => .ret (shiftStack v0 π) (shiftValue v0 v)
  | .halt v => .halt (shiftValue v0 v)
  | .error => .error

/-! ## Basic unfolding lemmas -/

@[simp] theorem shiftStack_nil (v0 : CekValue) : shiftStack v0 [] = [] := rfl

@[simp] theorem shiftStack_cons (v0 : CekValue) (f : Frame) (rest : Stack) :
    shiftStack v0 (f :: rest) = shiftFrame v0 f :: shiftStack v0 rest := rfl

@[simp] theorem shiftValueList_nil (v0 : CekValue) : shiftValueList v0 [] = [] := by
  simp [shiftValueList]

@[simp] theorem shiftValueList_cons (v0 : CekValue) (v : CekValue) (rest : List CekValue) :
    shiftValueList v0 (v :: rest) = shiftValue v0 v :: shiftValueList v0 rest := by
  simp [shiftValueList]

/-- `shiftEnv v0 (ρ.extend v) = (shiftEnv v0 ρ).extend (shiftValue v0 v)`. -/
theorem shiftEnv_extend (v0 : CekValue) (ρ : CekEnv) (v : CekValue) :
    shiftEnv v0 (ρ.extend v) = (shiftEnv v0 ρ).extend (shiftValue v0 v) := by
  show shiftEnv v0 (.cons v ρ) = .cons (shiftValue v0 v) (shiftEnv v0 ρ)
  simp [shiftEnv]

/-! ## Lookup: shifting an env commutes with lookup at shifted positions -/

/-- Lookups on a shifted env at any index yield the shifted original value.
    Indices `0` on both sides yield `none`.

    Proved by recursion on `ρ` (rather than `induction`, which is unsupported
    for mutually inductive `CekEnv`). -/
private theorem shiftEnv_lookup_raw : ∀ (v0 : CekValue) (ρ : CekEnv) (n : Nat),
    (shiftEnv v0 ρ).lookup n = (ρ.lookup n).map (shiftValue v0)
  | v0, .nil, 0 => by
    show (shiftEnv v0 .nil).lookup 0 = (CekEnv.nil.lookup 0).map (shiftValue v0)
    simp [shiftEnv, CekEnv.lookup]
  | v0, .nil, _ + 1 => by
    show (shiftEnv v0 .nil).lookup _ = (CekEnv.nil.lookup _).map (shiftValue v0)
    simp [shiftEnv, CekEnv.lookup]
  | v0, .cons w _, 0 => by
    show (shiftEnv v0 (.cons w _)).lookup 0 =
        ((CekEnv.cons w _).lookup 0).map (shiftValue v0)
    simp [shiftEnv, CekEnv.lookup]
  | v0, .cons v rest, 1 => by
    show (shiftEnv v0 (.cons v rest)).lookup 1 =
        ((CekEnv.cons v rest).lookup 1).map (shiftValue v0)
    simp [shiftEnv, CekEnv.lookup]
  | v0, .cons w rest, n + 2 => by
    show (shiftEnv v0 (.cons w rest)).lookup (n + 2) =
        ((CekEnv.cons w rest).lookup (n + 2)).map (shiftValue v0)
    have h1 : shiftEnv v0 (.cons w rest) = .cons (shiftValue v0 w) (shiftEnv v0 rest) := by
      simp [shiftEnv]
    rw [h1]
    show (shiftEnv v0 rest).lookup (n + 1) = (rest.lookup (n + 1)).map (shiftValue v0)
    exact shiftEnv_lookup_raw v0 rest (n + 1)

/-- Key lookup lemma: lookups on `(shiftEnv v0 ρ).extend v0` at the
    `shiftRename 1`-translated index match the shifted original lookup.

    - At `n = 0`: both sides yield `none` (position 0 is invalid).
    - At `n ≥ 1`: `shiftRename 1 n = n + 1`, and
      `((shiftEnv v0 ρ).extend v0).lookup (n + 1) = (shiftEnv v0 ρ).lookup n`
      which by `shiftEnv_lookup_raw` is `(ρ.lookup n).map (shiftValue v0)`. -/
theorem shiftEnv_lookup (v0 : CekValue) (ρ : CekEnv) (n : Nat) :
    ((shiftEnv v0 ρ).extend v0).lookup (Moist.Verified.shiftRename 1 n) =
      (ρ.lookup n).map (shiftValue v0) := by
  by_cases hn : n ≥ 1
  · rw [Moist.Verified.shiftRename_ge hn]
    show ((shiftEnv v0 ρ).extend v0).lookup (n + 1) = (ρ.lookup n).map (shiftValue v0)
    rw [extend_lookup_succ _ _ _ hn]
    exact shiftEnv_lookup_raw v0 ρ n
  · have hn0 : n = 0 := by omega
    subst hn0
    show ((shiftEnv v0 ρ).extend v0).lookup (Moist.Verified.shiftRename 1 0) =
      (CekEnv.lookup ρ 0).map (shiftValue v0)
    rw [Moist.Verified.shiftRename_lt (by omega : (0 : Nat) < 1)]
    rw [lookup_zero, lookup_zero]
    rfl

/-! ## `shiftValueList` structural lemmas -/

theorem shiftValueList_append (v0 : CekValue) (xs ys : List CekValue) :
    shiftValueList v0 (xs ++ ys) = shiftValueList v0 xs ++ shiftValueList v0 ys := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    show shiftValueList v0 (x :: (rest ++ ys)) =
      shiftValueList v0 (x :: rest) ++ shiftValueList v0 ys
    simp [shiftValueList_cons, ih]

theorem shiftValueList_reverse (v0 : CekValue) (vs : List CekValue) :
    shiftValueList v0 vs.reverse = (shiftValueList v0 vs).reverse := by
  induction vs with
  | nil => simp
  | cons v rest ih =>
    show shiftValueList v0 ((v :: rest).reverse) = (shiftValueList v0 (v :: rest)).reverse
    simp only [List.reverse_cons, shiftValueList_cons]
    rw [shiftValueList_append, ih]
    simp only [shiftValueList_cons, shiftValueList_nil]

/-! ## `extractConsts` preservation under shift -/

/-- `shiftValue v0 (.VCon c) = .VCon c` — constants survive the shift unchanged. -/
@[simp] theorem shiftValue_VCon (v0 : CekValue) (c : Moist.Plutus.Term.Const) :
    shiftValue v0 (.VCon c) = .VCon c := by
  simp [shiftValue]

/-- A shifted VCon is a VCon: inversion for `shiftValue`. -/
private theorem shiftValue_eq_VCon_iff (v0 : CekValue) (v : CekValue) (c : Moist.Plutus.Term.Const) :
    shiftValue v0 v = .VCon c ↔ v = .VCon c := by
  constructor
  · intro h
    cases v with
    | VCon c' => simp [shiftValue] at h; rw [h]
    | VLam _ _ => simp [shiftValue] at h
    | VDelay _ _ => simp [shiftValue] at h
    | VConstr _ _ => simp [shiftValue] at h
    | VBuiltin _ _ _ => simp [shiftValue] at h
  · intro h; subst h; simp [shiftValue]

/-- Extracting constants commutes with shifting the argument list. -/
private theorem extractConsts_shift (v0 : CekValue) (args : List CekValue) :
    extractConsts (shiftValueList v0 args) = extractConsts args := by
  induction args with
  | nil =>
    show extractConsts (shiftValueList v0 []) = extractConsts []
    rw [shiftValueList_nil]
  | cons a rest ih =>
    show extractConsts (shiftValueList v0 (a :: rest)) = extractConsts (a :: rest)
    rw [shiftValueList_cons]
    cases a with
    | VCon c =>
      rw [shiftValue_VCon]
      simp only [extractConsts, ih]
    | VLam _ _ => simp [shiftValue, extractConsts]
    | VDelay _ _ => simp [shiftValue, extractConsts]
    | VConstr _ _ => simp [shiftValue, extractConsts]
    | VBuiltin _ _ _ => simp [shiftValue, extractConsts]

/-! ## `evalBuiltinPassThrough` preservation under shift -/

/-! ### passThrough case analysis.

`evalBuiltinPassThrough b args` returns `none` except for these six builtins
with specific arg patterns:
- `IfThenElse [elseV, thenV, VCon (Bool cond)]` returns `thenV`/`elseV`
- `ChooseUnit [result, VCon Unit]` returns `result`
- `Trace [result, VCon (String _)]` returns `result`
- `ChooseData [bC, iC, lC, mC, cC, VCon (Data d)]` returns one of bC..cC
- `ChooseList [consC, nilC, VCon (ConstDataList _)]`/`[consC, nilC, VCon (ConstList _)]`
  returns `consC`/`nilC`
- `MkCons [VCon (ConstList _), VCon c]` returns `VCon (ConstList (c :: _))`

We break the proof into one small lemma per builtin. -/

/-- `evalBuiltinPassThrough` returns `none` on arg lists of length ≥ 7
    (no passThrough builtin takes more than 6 args). -/
private theorem evalBuiltinPassThrough_too_many_args (b : Moist.Plutus.Term.BuiltinFun)
    (a1 a2 a3 a4 a5 a6 a7 : CekValue) (rest : List CekValue) :
    evalBuiltinPassThrough b (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest) = none := by
  cases b <;> simp [evalBuiltinPassThrough]

/-- Normalize `shiftValueList v0 (a :: rest)` inside a 7-deep prefix to cons-form. -/
private theorem shiftValueList_7 (v0 : CekValue) (a1 a2 a3 a4 a5 a6 a7 : CekValue)
    (rest : List CekValue) :
    shiftValueList v0 (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest) =
      shiftValue v0 a1 :: shiftValue v0 a2 :: shiftValue v0 a3 :: shiftValue v0 a4 ::
      shiftValue v0 a5 :: shiftValue v0 a6 :: shiftValue v0 a7 :: shiftValueList v0 rest := by
  simp only [shiftValueList_cons]

private theorem evalBuiltinPassThrough_IfThenElse_shift (v0 : CekValue) (args : List CekValue) :
    evalBuiltinPassThrough .IfThenElse (shiftValueList v0 args) =
      (evalBuiltinPassThrough .IfThenElse args).map (shiftValue v0) := by
  match args with
  | [] =>
    rw [shiftValueList_nil]
    rfl
  | [a] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a, b] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [elseV, thenV, a3] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    cases a3 with
    | VCon c =>
      rw [shiftValue_VCon]
      cases c with
      | Bool b =>
        simp only [evalBuiltinPassThrough]
        cases b <;> simp [Option.map]
      | _ => simp [evalBuiltinPassThrough]
    | _ => simp [evalBuiltinPassThrough, shiftValue]
  | [a1, a2, a3, a4] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5, a6] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    rw [shiftValueList_7]
    rw [evalBuiltinPassThrough_too_many_args, evalBuiltinPassThrough_too_many_args]
    rfl

private theorem evalBuiltinPassThrough_ChooseUnit_shift (v0 : CekValue) (args : List CekValue) :
    evalBuiltinPassThrough .ChooseUnit (shiftValueList v0 args) =
      (evalBuiltinPassThrough .ChooseUnit args).map (shiftValue v0) := by
  match args with
  | [] =>
    rw [shiftValueList_nil]
    rfl
  | [a] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [result, a2] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    cases a2 with
    | VCon c =>
      rw [shiftValue_VCon]
      cases c with
      | Unit => simp [evalBuiltinPassThrough, Option.map]
      | _ => simp [evalBuiltinPassThrough]
    | _ => simp [evalBuiltinPassThrough, shiftValue]
  | [a1, a2, a3] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5, a6] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    rw [shiftValueList_7]
    rw [evalBuiltinPassThrough_too_many_args, evalBuiltinPassThrough_too_many_args]
    rfl

private theorem evalBuiltinPassThrough_Trace_shift (v0 : CekValue) (args : List CekValue) :
    evalBuiltinPassThrough .Trace (shiftValueList v0 args) =
      (evalBuiltinPassThrough .Trace args).map (shiftValue v0) := by
  match args with
  | [] =>
    rw [shiftValueList_nil]
    rfl
  | [a] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [result, a2] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    cases a2 with
    | VCon c =>
      rw [shiftValue_VCon]
      cases c with
      | String _ => simp [evalBuiltinPassThrough, Option.map]
      | _ => simp [evalBuiltinPassThrough]
    | _ => simp [evalBuiltinPassThrough, shiftValue]
  | [a1, a2, a3] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5, a6] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    rw [shiftValueList_7]
    rw [evalBuiltinPassThrough_too_many_args, evalBuiltinPassThrough_too_many_args]
    rfl

private theorem evalBuiltinPassThrough_ChooseData_shift (v0 : CekValue) (args : List CekValue) :
    evalBuiltinPassThrough .ChooseData (shiftValueList v0 args) =
      (evalBuiltinPassThrough .ChooseData args).map (shiftValue v0) := by
  match args with
  | [] =>
    rw [shiftValueList_nil]
    rfl
  | [a] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a, b] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a, b, c] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a, b, c, d] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a, b, c, d, e] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [bC, iC, lC, mC, cC, a6] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    cases a6 with
    | VCon c =>
      rw [shiftValue_VCon]
      cases c with
      | Data d =>
        simp only [evalBuiltinPassThrough]
        cases d <;> simp [Option.map]
      | _ => simp [evalBuiltinPassThrough]
    | _ => simp [evalBuiltinPassThrough, shiftValue]
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    rw [shiftValueList_7]
    rw [evalBuiltinPassThrough_too_many_args, evalBuiltinPassThrough_too_many_args]
    rfl

private theorem evalBuiltinPassThrough_ChooseList_shift (v0 : CekValue) (args : List CekValue) :
    evalBuiltinPassThrough .ChooseList (shiftValueList v0 args) =
      (evalBuiltinPassThrough .ChooseList args).map (shiftValue v0) := by
  match args with
  | [] =>
    rw [shiftValueList_nil]
    rfl
  | [a] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a, b] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [consC, nilC, a3] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    cases a3 with
    | VCon c =>
      rw [shiftValue_VCon]
      cases c with
      | ConstDataList l =>
        simp only [evalBuiltinPassThrough, Option.map]
        by_cases hl : l = [] <;> simp [hl]
      | ConstList l =>
        simp only [evalBuiltinPassThrough, Option.map]
        by_cases hl : l = [] <;> simp [hl]
      | _ => simp [evalBuiltinPassThrough]
    | _ => simp [evalBuiltinPassThrough, shiftValue]
  | [a1, a2, a3, a4] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5, a6] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    rw [shiftValueList_7]
    rw [evalBuiltinPassThrough_too_many_args, evalBuiltinPassThrough_too_many_args]
    rfl

private theorem evalBuiltinPassThrough_MkCons_shift (v0 : CekValue) (args : List CekValue) :
    evalBuiltinPassThrough .MkCons (shiftValueList v0 args) =
      (evalBuiltinPassThrough .MkCons args).map (shiftValue v0) := by
  match args with
  | [] =>
    rw [shiftValueList_nil]
    rfl
  | [a] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, elem] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    cases a1 with
    | VCon c1 =>
      rw [shiftValue_VCon]
      cases c1 with
      | ConstList tail =>
        cases elem with
        | VCon c2 =>
          rw [shiftValue_VCon]
          simp [evalBuiltinPassThrough, Option.map]
        | _ => simp [evalBuiltinPassThrough, shiftValue]
      | _ => simp [evalBuiltinPassThrough]
    | _ => simp [evalBuiltinPassThrough, shiftValue]
  | [a1, a2, a3] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | [a1, a2, a3, a4, a5, a6] =>
    simp only [shiftValueList_cons, shiftValueList_nil]
    simp [evalBuiltinPassThrough, Option.map]
  | a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest =>
    rw [shiftValueList_7]
    rw [evalBuiltinPassThrough_too_many_args, evalBuiltinPassThrough_too_many_args]
    rfl

/-- `evalBuiltinPassThrough` commutes with shifting its argument list. -/
private theorem evalBuiltinPassThrough_shift (v0 : CekValue) (b : Moist.Plutus.Term.BuiltinFun)
    (args : List CekValue) :
    evalBuiltinPassThrough b (shiftValueList v0 args) =
      (evalBuiltinPassThrough b args).map (shiftValue v0) := by
  -- For any builtin `b` that is not one of the 6 passThrough builtins,
  -- `evalBuiltinPassThrough b args = none` for all args. Since
  -- `none.map _ = none`, both sides are `none`.
  by_cases hpt : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                 b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hpt with h | h | h | h | h | h <;> subst h
    · exact evalBuiltinPassThrough_IfThenElse_shift v0 args
    · exact evalBuiltinPassThrough_ChooseUnit_shift v0 args
    · exact evalBuiltinPassThrough_Trace_shift v0 args
    · exact evalBuiltinPassThrough_ChooseData_shift v0 args
    · exact evalBuiltinPassThrough_ChooseList_shift v0 args
    · exact evalBuiltinPassThrough_MkCons_shift v0 args
  · -- None of the 6 passThrough builtins — use the existing helper.
    have hnot : b ≠ .IfThenElse ∧ b ≠ .ChooseUnit ∧ b ≠ .Trace ∧
                b ≠ .ChooseData ∧ b ≠ .ChooseList ∧ b ≠ .MkCons := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (intro heq; apply hpt; simp [heq])
    rw [evalBuiltinPassThrough_none_of_not_passthrough b (shiftValueList v0 args) hnot]
    rw [evalBuiltinPassThrough_none_of_not_passthrough b args hnot]
    rfl

/-- `evalBuiltin` commutes with shifting its argument list. -/
theorem evalBuiltin_shift (v0 : CekValue) (b : Moist.Plutus.Term.BuiltinFun)
    (args : List CekValue) :
    evalBuiltin b (shiftValueList v0 args) =
      (evalBuiltin b args).map (shiftValue v0) := by
  simp only [evalBuiltin]
  rw [evalBuiltinPassThrough_shift v0 b args]
  cases hpt : evalBuiltinPassThrough b args with
  | some v => rfl
  | none =>
    simp only [Option.map]
    rw [extractConsts_shift v0 args]
    -- Now both sides have the same `extractConsts` call; they should match up.
    cases hec : extractConsts args with
    | some cs =>
      simp only
      cases hev : evalBuiltinConst b cs with
      | some c => simp only [shiftValue_VCon]
      | none => rfl
    | none => rfl

/-! ## `fields.map Frame.applyArg ++ rest` case-rewriting -/

/-- Maps commute: `(fields.map f).map g = fields.map (g ∘ f)`. Specialized for
    shifting `Frame.applyArg`-wrapped fields. -/
private theorem shiftStack_map_applyArg (v0 : CekValue) (fields : List CekValue) :
    (fields.map Frame.applyArg).map (shiftFrame v0) =
      (shiftValueList v0 fields).map Frame.applyArg := by
  induction fields with
  | nil => simp [shiftValueList_nil]
  | cons f rest ih =>
    simp only [List.map_cons, shiftValueList_cons]
    show shiftFrame v0 (Frame.applyArg f) :: (rest.map Frame.applyArg).map (shiftFrame v0) =
         Frame.applyArg (shiftValue v0 f) :: (shiftValueList v0 rest).map Frame.applyArg
    rw [ih]
    show shiftFrame v0 (Frame.applyArg f) :: _ = Frame.applyArg (shiftValue v0 f) :: _
    rw [show shiftFrame v0 (Frame.applyArg f) = Frame.applyArg (shiftValue v0 f) from rfl]

/-- `shiftStack` commutes with `++`. -/
private theorem shiftStack_append (v0 : CekValue) (xs ys : Stack) :
    shiftStack v0 (xs ++ ys) = shiftStack v0 xs ++ shiftStack v0 ys := by
  simp [shiftStack, List.map_append]


/-! ## Projection helpers on `shiftState` -/

/-- `shiftState v0 .error = .error`. -/
theorem shiftState_error_eq (v0 : CekValue) :
    shiftState v0 .error = .error := rfl

/-- `shiftState v0 (.halt v) = .halt (shiftValue v0 v)`. -/
theorem shiftState_halt_eq (v0 : CekValue) (v : CekValue) :
    shiftState v0 (.halt v) = .halt (shiftValue v0 v) := rfl

/-- When `shiftState v0 s = .error`, then `s = .error`. -/
theorem shiftState_eq_error (v0 : CekValue) (s : State)
    (h : shiftState v0 s = .error) : s = .error := by
  cases s with
  | compute _ _ _ => simp [shiftState] at h
  | ret _ _ => simp [shiftState] at h
  | halt _ => simp [shiftState] at h
  | error => rfl

/-- When `shiftState v0 s = .halt v'`, recover the original `.halt v` structure. -/
theorem shiftState_eq_halt (v0 : CekValue) (s : State) (v' : CekValue)
    (h : shiftState v0 s = .halt v') :
    ∃ v, s = .halt v ∧ v' = shiftValue v0 v := by
  cases s with
  | compute _ _ _ => simp [shiftState] at h
  | ret _ _ => simp [shiftState] at h
  | halt v =>
    refine ⟨v, rfl, ?_⟩
    simp [shiftState] at h
    exact h.symm
  | error => simp [shiftState] at h

/-- When `shiftState v0 s = .ret π v'`, recover the original π-structure. -/
theorem shiftState_eq_ret (v0 : CekValue) (s : State) (π' : Stack) (v' : CekValue)
    (h : shiftState v0 s = .ret π' v') :
    ∃ π v, s = .ret π v ∧ π' = shiftStack v0 π ∧ v' = shiftValue v0 v := by
  cases s with
  | compute _ _ _ => simp [shiftState] at h
  | ret π v =>
    refine ⟨π, v, rfl, ?_, ?_⟩
    · simp [shiftState] at h; exact h.1.symm
    · simp [shiftState] at h; exact h.2.symm
  | halt _ => simp [shiftState] at h
  | error => simp [shiftState] at h

--------------------------------------------------------------------------------
-- 18. Value-level shift preservation for ValueRefinesK.
--
-- This section provides the supporting helpers for the value-level shift
-- refinement needed by downstream `rHalts_shift` and `substRefinesR_body`.
--
-- The helpers (`shiftEnv_length`, `shiftValue_wellFormed`,
-- `shiftEnv_wellFormed_body`, `shiftValueList_wellFormed`,
-- `shiftEnv_wellFormed`) are fully proved.
--
-- The main theorem `valueRefinesK_shift_right` is STATED but NOT CLOSED
-- inline due to fundamental infrastructure gaps. The VLam / VDelay cases
-- require a state-level rename bisim (`step_shift_bisim`) that would
-- require ~1500-2500 additional lines of CEK frame case analysis
-- (see memory notes `valueRefinesK_shift_right blocker` and
-- `step_shift_bisim unprovable syntactically`).
--
-- Specifically, the blocker is: unfolding `ValueRefinesK (k+1) v₁
-- (shiftValue v0 v₂)` at the VLam/VDelay case yields an `ObsRefinesK i`
-- obligation between LHS `compute π₁ ρ₁.extend(arg₁) body₁` and goal-RHS
-- `compute π₂ newEnv.extend(arg₂) renamedBody₂`. The hypothesis `href`
-- provides an intermediate `ObsRefinesK i` with the mid-state
-- `compute π₂ ρ₂.extend(arg₂) body₂`. Bridging mid → goal-RHS requires
-- `renameRefinesR` applied with `StackRefK V k' π₂ π₂` (stack self-ref
-- at arbitrary `k'`), which is not derivable from the goal's
-- `hπ : StackRefK V i π₁ π₂` without stack well-formedness — a hypothesis
-- absent from the theorem signature.
--------------------------------------------------------------------------------

/-- `(shiftEnv v0 ρ).length = ρ.length`. -/
theorem shiftEnv_length : ∀ (v0 : CekValue) (ρ : CekEnv),
    (shiftEnv v0 ρ).length = ρ.length
  | _, .nil => by
    show (shiftEnv _ .nil).length = CekEnv.nil.length
    simp [shiftEnv, CekEnv.length]
  | v0, .cons v rest => by
    show (shiftEnv v0 (.cons v rest)).length = (CekEnv.cons v rest).length
    simp only [shiftEnv]
    show ((shiftEnv v0 rest).cons (shiftValue v0 v)).length = (rest.cons v).length
    simp [CekEnv.length]
    exact shiftEnv_length v0 rest

--------------------------------------------------------------------------------
-- 19. Shift bisimulation (semantic).
--
-- Mutual inductive relation pairing "original" state with its "shifted"
-- counterpart. Each closure-forming constructor existentially quantifies
-- over its own σ (`Is0Preserving` rename), encoding that the RHS's term
-- is `renameTerm σ` of the LHS's term, at the current level. Under
-- binders, σ is lifted to `liftRename σ` — this is exactly the renaming
-- structure produced by stepping, so the "env-ordering" apparent conflict
-- resolves because the σ "bakes in" the positional correspondence.
--
-- Structure mirrors `Moist.Verified.Contextual.BisimRef.lean`.
--------------------------------------------------------------------------------

open Moist.Verified.FundamentalRefines (Is0Preserving is0preserving_id
  is0preserving_shiftRename is0preserving_lift)

mutual

inductive ShiftBisimState : State → State → Prop
  | compute : ∀ {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {t : Moist.Plutus.Term.Term}
      {σ : Nat → Nat} {d : Nat},
      Is0Preserving σ →
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      closedAt d t = true →
      ShiftBisimStack π₁ π₂ →
      ShiftBisimState (.compute π₁ ρ₁ t) (.compute π₂ ρ₂ (Moist.Verified.renameTerm σ t))
  | ret : ∀ {π₁ π₂ : Stack} {v₁ v₂ : CekValue},
      ShiftBisimValue v₁ v₂ → ShiftBisimStack π₁ π₂ →
      ShiftBisimState (.ret π₁ v₁) (.ret π₂ v₂)
  | halt : ∀ {v₁ v₂ : CekValue}, ShiftBisimValue v₁ v₂ →
      ShiftBisimState (.halt v₁) (.halt v₂)
  | error : ShiftBisimState .error .error

/-- Environments related at depth `d` under renaming `σ`: for each
    position `n` with `1 ≤ n ≤ d`, `ρ₁.lookup n` and `ρ₂.lookup (σ n)`
    return `ShiftBisimValue`-related values. -/
inductive ShiftBisimEnv : (Nat → Nat) → Nat → CekEnv → CekEnv → Prop
  | zero : ∀ {σ : Nat → Nat} {ρ₁ ρ₂ : CekEnv}, ShiftBisimEnv σ 0 ρ₁ ρ₂
  | succ : ∀ {σ : Nat → Nat} {d : Nat} {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue},
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      ρ₁.lookup (d + 1) = some v₁ →
      ρ₂.lookup (σ (d + 1)) = some v₂ →
      ShiftBisimValue v₁ v₂ →
      ShiftBisimEnv σ (d + 1) ρ₁ ρ₂

inductive ShiftBisimValue : CekValue → CekValue → Prop
  | vcon : ∀ (c : Moist.Plutus.Term.Const), ShiftBisimValue (.VCon c) (.VCon c)
  | vlam : ∀ {body : Moist.Plutus.Term.Term} {ρ₁ ρ₂ : CekEnv}
      {σ : Nat → Nat} {d : Nat},
      Is0Preserving σ →
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      closedAt (d + 1) body = true →
      ShiftBisimValue (.VLam body ρ₁)
        (.VLam (Moist.Verified.renameTerm (Moist.Verified.liftRename σ) body) ρ₂)
  | vdelay : ∀ {body : Moist.Plutus.Term.Term} {ρ₁ ρ₂ : CekEnv}
      {σ : Nat → Nat} {d : Nat},
      Is0Preserving σ →
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      closedAt d body = true →
      ShiftBisimValue (.VDelay body ρ₁)
        (.VDelay (Moist.Verified.renameTerm σ body) ρ₂)
  | vconstr : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue},
      ShiftBisimValueList fs₁ fs₂ →
      ShiftBisimValue (.VConstr tag fs₁) (.VConstr tag fs₂)
  | vbuiltin : ∀ (b : Moist.Plutus.Term.BuiltinFun) (ea : ExpectedArgs)
      {args₁ args₂ : List CekValue},
      ShiftBisimValueList args₁ args₂ →
      ShiftBisimValue (.VBuiltin b args₁ ea) (.VBuiltin b args₂ ea)

inductive ShiftBisimValueList : List CekValue → List CekValue → Prop
  | nil : ShiftBisimValueList [] []
  | cons : ∀ {v₁ v₂ : CekValue} {vs₁ vs₂ : List CekValue},
      ShiftBisimValue v₁ v₂ → ShiftBisimValueList vs₁ vs₂ →
      ShiftBisimValueList (v₁ :: vs₁) (v₂ :: vs₂)

inductive ShiftBisimStack : Stack → Stack → Prop
  | nil : ShiftBisimStack [] []
  | cons : ∀ {f₁ f₂ : Frame} {π₁ π₂ : Stack},
      ShiftBisimFrame f₁ f₂ → ShiftBisimStack π₁ π₂ →
      ShiftBisimStack (f₁ :: π₁) (f₂ :: π₂)

inductive ShiftBisimFrame : Frame → Frame → Prop
  | force : ShiftBisimFrame .force .force
  | arg : ∀ {t : Moist.Plutus.Term.Term} {ρ₁ ρ₂ : CekEnv}
      {σ : Nat → Nat} {d : Nat},
      Is0Preserving σ →
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      closedAt d t = true →
      ShiftBisimFrame (.arg t ρ₁) (.arg (Moist.Verified.renameTerm σ t) ρ₂)
  | funV : ∀ {v₁ v₂ : CekValue},
      ShiftBisimValue v₁ v₂ → ShiftBisimFrame (.funV v₁) (.funV v₂)
  | applyArg : ∀ {v₁ v₂ : CekValue},
      ShiftBisimValue v₁ v₂ → ShiftBisimFrame (.applyArg v₁) (.applyArg v₂)
  | constrField : ∀ (tag : Nat) {done₁ done₂ : List CekValue}
      {todo : List Moist.Plutus.Term.Term} {ρ₁ ρ₂ : CekEnv}
      {σ : Nat → Nat} {d : Nat},
      Is0Preserving σ →
      ShiftBisimValueList done₁ done₂ →
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      closedAtList d todo = true →
      ShiftBisimFrame (.constrField tag done₁ todo ρ₁)
        (.constrField tag done₂ (Moist.Verified.renameTermList σ todo) ρ₂)
  | caseScrutinee : ∀ {alts : List Moist.Plutus.Term.Term} {ρ₁ ρ₂ : CekEnv}
      {σ : Nat → Nat} {d : Nat},
      Is0Preserving σ →
      ShiftBisimEnv σ d ρ₁ ρ₂ →
      closedAtList d alts = true →
      ShiftBisimFrame (.caseScrutinee alts ρ₁)
        (.caseScrutinee (Moist.Verified.renameTermList σ alts) ρ₂)
end

--------------------------------------------------------------------------------
-- 19b. ShiftBisimEnv helpers
--------------------------------------------------------------------------------

/-- `ShiftBisimEnv σ 0` always holds trivially. -/
theorem shiftBisimEnv_zero {σ : Nat → Nat} (ρ₁ ρ₂ : CekEnv) :
    ShiftBisimEnv σ 0 ρ₁ ρ₂ := ShiftBisimEnv.zero

/-- Narrow a `ShiftBisimEnv` down to a smaller depth. -/
theorem shiftBisimEnv_narrow : ∀ (σ : Nat → Nat) (d : Nat) {d' : Nat}
    {ρ₁ ρ₂ : CekEnv}, ShiftBisimEnv σ d ρ₁ ρ₂ → d' ≤ d → ShiftBisimEnv σ d' ρ₁ ρ₂ := by
  intro σ d
  induction d with
  | zero =>
    intro d' _ _ _ hle
    have : d' = 0 := Nat.le_zero.mp hle
    subst this
    exact ShiftBisimEnv.zero
  | succ n ih =>
    intro d' _ _ h hle
    by_cases h_eq : d' = n + 1
    · subst h_eq; exact h
    · cases h with
      | succ h_rest _ _ _ => exact ih h_rest (by omega)

/-- Lookup within a `ShiftBisimEnv σ d` returns a matching `ShiftBisimValue`
    pair at positions `(n, σ n)`. -/
theorem shiftBisimEnv_lookup : ∀ (σ : Nat → Nat) (d : Nat) {ρ₁ ρ₂ : CekEnv},
    ShiftBisimEnv σ d ρ₁ ρ₂ → ∀ {n : Nat}, 0 < n → n ≤ d →
      ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup (σ n) = some v₂ ∧
        ShiftBisimValue v₁ v₂ := by
  intro σ d
  induction d with
  | zero => intro _ _ _ _ _ hle; omega
  | succ n ih =>
    intro _ _ h m hm hle
    cases h with
    | succ h_rest hl₁ hl₂ h_v =>
      by_cases h_eq : m = n + 1
      · subst h_eq; exact ⟨_, _, hl₁, hl₂, h_v⟩
      · exact ih h_rest hm (by omega)

/-- Extending two `ShiftBisimEnv σ d`-related envs with a related pair
    gives a `ShiftBisimEnv (liftRename σ) (d+1)`-related pair. Mirrors
    `renameEnvRefR_extend`. -/
theorem shiftBisimEnv_extend : ∀ {σ : Nat → Nat} (h_σ : Is0Preserving σ)
    (d : Nat) {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue},
    ShiftBisimEnv σ d ρ₁ ρ₂ → ShiftBisimValue v₁ v₂ →
    ShiftBisimEnv (Moist.Verified.liftRename σ) (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro σ h_σ d
  induction d with
  | zero =>
    intro ρ₁ ρ₂ _ _ _ h_v
    refine ShiftBisimEnv.succ ShiftBisimEnv.zero ?_ ?_ h_v
    · simp [CekEnv.extend, CekEnv.lookup]
    · show (CekEnv.cons _ ρ₂).lookup (Moist.Verified.liftRename σ 1) = _
      have : Moist.Verified.liftRename σ 1 = 1 := rfl
      rw [this]; rfl
  | succ n ih =>
    intro ρ₁ ρ₂ v_new₁ v_new₂ h h_v
    cases h with
    | @succ _ _ _ _ v₁ v₂ h_rest hl₁ hl₂ h_inner =>
      have ih' := ih h_rest h_v
      refine ShiftBisimEnv.succ ih' ?_ ?_ h_inner
      · show (CekEnv.cons v_new₁ ρ₁).lookup (n + 1 + 1) = some v₁
        have heq : (CekEnv.cons v_new₁ ρ₁).lookup (n + 1 + 1) = ρ₁.lookup (n + 1) :=
          extend_lookup_succ ρ₁ v_new₁ (n + 1) (by omega)
        rw [heq]; exact hl₁
      · have hlift : Moist.Verified.liftRename σ (n + 1 + 1) = σ (n + 1) + 1 := by
          show Moist.Verified.liftRename σ (n + 2) = σ (n + 1) + 1
          rfl
        rw [hlift]
        have hσ_ge : σ (n + 1) ≥ 1 := h_σ.2 (n + 1) (by omega)
        show (CekEnv.cons v_new₂ ρ₂).lookup (σ (n + 1) + 1) = some v₂
        have heq : (CekEnv.cons v_new₂ ρ₂).lookup (σ (n + 1) + 1) =
                   ρ₂.lookup (σ (n + 1)) :=
          extend_lookup_succ ρ₂ v_new₂ (σ (n + 1)) hσ_ge
        rw [heq]; exact hl₂

/-- `ShiftBisimValueList` has the same length on both sides. -/
theorem shiftBisimValueList_length_eq : ∀ {xs₁ xs₂ : List CekValue},
    ShiftBisimValueList xs₁ xs₂ → xs₁.length = xs₂.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons _ hr => simp [shiftBisimValueList_length_eq hr]

/-- Inversion for `ShiftBisimValueList` on empty head list. -/
theorem shiftBisimValueList_nil_inv : ∀ {xs : List CekValue},
    ShiftBisimValueList [] xs → xs = []
  | _, h => by cases h; rfl

/-- Inversion for `ShiftBisimValueList` on cons head list. -/
theorem shiftBisimValueList_cons_inv : ∀ {v : CekValue} {vs xs : List CekValue},
    ShiftBisimValueList (v :: vs) xs →
    ∃ w ws, xs = w :: ws ∧ ShiftBisimValue v w ∧ ShiftBisimValueList vs ws
  | _, _, _, h => by cases h with | cons hv hr => exact ⟨_, _, rfl, hv, hr⟩

/-- Reverse inversion: when the RIGHT list is empty, so is the LEFT. -/
theorem shiftBisimValueList_nil_inv_right : ∀ {xs : List CekValue},
    ShiftBisimValueList xs [] → xs = []
  | [], _ => rfl
  | _ :: _, h => by cases h

/-- Reverse inversion: when the RIGHT list is `w :: ws`, the LEFT is
    `v :: vs` for some related `v`, `vs`. -/
theorem shiftBisimValueList_cons_inv_right : ∀ {w : CekValue} {ws xs : List CekValue},
    ShiftBisimValueList xs (w :: ws) →
    ∃ v vs, xs = v :: vs ∧ ShiftBisimValue v w ∧ ShiftBisimValueList vs ws
  | _, _, [], h => by cases h
  | _, _, _ :: _, h => by cases h with | cons hv hr => exact ⟨_, _, rfl, hv, hr⟩

/-- Reverse inversion for `VCon` on RHS. -/
theorem shiftBisimValue_vcon_inv_right : ∀ {c : Moist.Plutus.Term.Const} {v : CekValue},
    ShiftBisimValue v (.VCon c) → v = .VCon c
  | _, _, h => by cases h; rfl

/-- Inversion for `ShiftBisimValue` on `VCon`. -/
theorem shiftBisimValue_vcon_inv : ∀ {c : Moist.Plutus.Term.Const} {v : CekValue},
    ShiftBisimValue (.VCon c) v → v = .VCon c
  | _, _, h => by cases h; rfl

/-- `ShiftBisimValueList` is closed under `append`. -/
theorem shiftBisimValueList_append : ∀ (xs₁ : List CekValue)
    {xs₂ ys₁ ys₂ : List CekValue},
    ShiftBisimValueList xs₁ xs₂ → ShiftBisimValueList ys₁ ys₂ →
    ShiftBisimValueList (xs₁ ++ ys₁) (xs₂ ++ ys₂)
  | [], _, _, _, hxs, hys => by cases hxs; exact hys
  | _ :: rest, _, _, _, hxs, hys => by
    cases hxs with
    | cons hv hrest =>
      exact ShiftBisimValueList.cons hv (shiftBisimValueList_append rest hrest hys)

/-- `List.reverse` preserves `ShiftBisimValueList`. -/
theorem shiftBisimValueList_reverse : ∀ (xs₁ : List CekValue)
    {xs₂ : List CekValue},
    ShiftBisimValueList xs₁ xs₂ →
    ShiftBisimValueList xs₁.reverse xs₂.reverse
  | [], _, hxs => by cases hxs; exact ShiftBisimValueList.nil
  | x :: rest, _, hxs => by
    cases hxs with
    | cons hv hrest =>
      simp only [List.reverse_cons]
      exact shiftBisimValueList_append _ (shiftBisimValueList_reverse rest hrest)
              (ShiftBisimValueList.cons hv ShiftBisimValueList.nil)

/-- Mapping `Frame.applyArg` + prepending preserves stack relation. -/
theorem shiftBisimValueList_to_applyArg_stack : ∀ (fs₁ : List CekValue)
    {fs₂ : List CekValue} {π₁ π₂ : Stack},
    ShiftBisimValueList fs₁ fs₂ → ShiftBisimStack π₁ π₂ →
    ShiftBisimStack (fs₁.map Frame.applyArg ++ π₁) (fs₂.map Frame.applyArg ++ π₂)
  | [], _, _, _, hfs, hπ => by cases hfs; exact hπ
  | _ :: rest, _, _, _, hfs, hπ => by
    cases hfs with
    | cons hv hrest =>
      exact ShiftBisimStack.cons (ShiftBisimFrame.applyArg hv)
              (shiftBisimValueList_to_applyArg_stack rest hrest hπ)

/-- `closedAtList d alts → alts[n]? = some alt → closedAt d alt`. -/
theorem shiftBisim_closedAtList_get : ∀ (d : Nat) (alts : List Moist.Plutus.Term.Term)
    (n : Nat) (alt : Moist.Plutus.Term.Term),
    closedAtList d alts = true →
    alts[n]? = some alt →
    closedAt d alt = true
  | _, [], _, _, _, h => by simp at h
  | d, a :: rest, 0, _, h_cl, h_get => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h_get
    subst h_get
    simp only [closedAtList, Bool.and_eq_true] at h_cl
    exact h_cl.1
  | d, _ :: rest, n + 1, alt, h_cl, h_get => by
    simp only [List.getElem?_cons_succ] at h_get
    simp only [closedAtList, Bool.and_eq_true] at h_cl
    exact shiftBisim_closedAtList_get d rest n alt h_cl.2 h_get

/-- `extractConsts` yields the same output on `ShiftBisimValueList`-related
    lists. Our ShiftBisimValue.vcon forces literal equality. -/
theorem shiftBisimValueList_extractConsts :
    ∀ (args₁ : List CekValue) {args₂ : List CekValue},
    ShiftBisimValueList args₁ args₂ → extractConsts args₁ = extractConsts args₂ := by
  intro args₁
  induction args₁ with
  | nil =>
    intro args₂ h
    cases h
    rfl
  | cons v rest ih =>
    intro args₂ h
    obtain ⟨w, rest₂, heq, hv, hrest⟩ := shiftBisimValueList_cons_inv h
    subst heq
    cases hv with
    | vcon c =>
      simp only [extractConsts]
      rw [ih hrest]
    | vlam _ _ _ => rfl
    | vdelay _ _ _ => rfl
    | vconstr _ _ => rfl
    | vbuiltin _ _ _ => rfl


--------------------------------------------------------------------------------
-- 19c. evalBuiltin compat under ShiftBisimValueList (adapted from BisimRef)
--------------------------------------------------------------------------------

/-- For a pass-through builtin, if LHS succeeds with `some v₁`, then RHS
    succeeds with `some v₂` where `ShiftBisimValue v₁ v₂`. -/
theorem shiftBisimValueList_evalBuiltinPassThrough_some : ∀ (b : BuiltinFun) {args₁ args₂ : List CekValue},
    ShiftBisimValueList args₁ args₂ →
    ∀ v₁, evalBuiltinPassThrough b args₁ = some v₁ →
      ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ ShiftBisimValue v₁ v₂ := by
  intro b args₁ args₂ h v₁ hv₁
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    -- ==================== IfThenElse: [e, t, .VCon (.Bool cond)] ====================
    · match args₁, h, hv₁ with
      | [e₁, t₁, .VCon (.Bool cond)], h_args, hv₁ =>
        obtain ⟨e₂, _, he₁, h_e, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨t₂, _, he₂, h_t, hr'⟩ := shiftBisimValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := shiftBisimValueList_cons_inv hr'
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases shiftBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if cond then t₂ else e₂, rfl, ?_⟩
        by_cases hc : cond
        · subst hc; exact h_t
        · simp only [hc]; exact h_e
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ==================== ChooseUnit: [r, .VCon .Unit] ====================
    · match args₁, h, hv₁ with
      | [r₁, .VCon .Unit], h_args, hv₁ =>
        obtain ⟨r₂, _, he₁, h_r, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := shiftBisimValueList_cons_inv hr
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases shiftBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨r₂, rfl, h_r⟩
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ==================== Trace: [r, .VCon (.String _)] ====================
    · match args₁, h, hv₁ with
      | [r₁, .VCon (.String _)], h_args, hv₁ =>
        obtain ⟨r₂, _, he₁, h_r, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := shiftBisimValueList_cons_inv hr
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases shiftBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨r₂, rfl, h_r⟩
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ========= ChooseData: [b, i, l, m, c, .VCon (.Data d)] =========
    · match args₁, h, hv₁ with
      | [b₁, i₁, l₁, m₁, cr₁, .VCon (.Data d)], h_args, hv₁ =>
        obtain ⟨b₂, _, he₁, h_b, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨i₂, _, he₂, h_i, hr₂⟩ := shiftBisimValueList_cons_inv hr
        obtain ⟨l₂, _, he₃, h_l, hr₃⟩ := shiftBisimValueList_cons_inv hr₂
        obtain ⟨m₂, _, he₄, h_m, hr₄⟩ := shiftBisimValueList_cons_inv hr₃
        obtain ⟨cr₂, _, he₅, h_cr, hr₅⟩ := shiftBisimValueList_cons_inv hr₄
        obtain ⟨w, _, he₆, h_w, hrn⟩ := shiftBisimValueList_cons_inv hr₅
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃ he₄ he₅ he₆
        cases shiftBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough] at hv₁
        cases d with
        | Constr _ _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨cr₂, rfl, h_cr⟩
        | Map _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨m₂, rfl, h_m⟩
        | List _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨l₂, rfl, h_l⟩
        | I _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨i₂, rfl, h_i⟩
        | B _ =>
          simp only [Option.some.injEq] at hv₁; subst hv₁
          exact ⟨b₂, rfl, h_b⟩
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstPairDataList _)], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Bls12_381_G1_element], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Bls12_381_G2_element], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VCon .Bls12_381_MlResult], _, hv₁ =>
          simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, _, _, _, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- ChooseList: [consC, nilC, .VCon (.ConstDataList l)] or [consC, nilC, .VCon (.ConstList l)]
    · match args₁, h, hv₁ with
      | [c₁, n₁, .VCon (.ConstDataList l)], h_args, hv₁ =>
        obtain ⟨c₂, _, he₁, h_c, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨n₂, _, he₂, h_n, hr'⟩ := shiftBisimValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := shiftBisimValueList_cons_inv hr'
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases shiftBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if l.isEmpty then n₂ else c₂, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [c₁, n₁, .VCon (.ConstList l)], h_args, hv₁ =>
        obtain ⟨c₂, _, he₁, h_c, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨n₂, _, he₂, h_n, hr'⟩ := shiftBisimValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := shiftBisimValueList_cons_inv hr'
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases shiftBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if l.isEmpty then n₂ else c₂, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Integer _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ByteString _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.String _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Unit], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Bool _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstPairDataList _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Pair _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.PairData _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.Data _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon (.ConstArray _)], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G1_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_G2_element], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VCon .Bls12_381_MlResult], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_, _, .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
    -- MkCons: [.VCon (.ConstList tail), .VCon elem] → .VCon (.ConstList (elem :: tail))
    · match args₁, h, hv₁ with
      | [.VCon (.ConstList tail), .VCon c], h_args, hv₁ =>
        obtain ⟨w₁, _, he₁, h_w₁, hr⟩ := shiftBisimValueList_cons_inv h_args
        obtain ⟨w₂, _, he₂, h_w₂, hrn⟩ := shiftBisimValueList_cons_inv hr
        have hnil := shiftBisimValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases shiftBisimValue_vcon_inv h_w₁
        cases shiftBisimValue_vcon_inv h_w₂
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨.VCon (.ConstList (c :: tail)), rfl, ShiftBisimValue.vcon _⟩
      | [.VCon (.ConstList _), .VDelay _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstList _), .VLam _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstList _), .VConstr _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstList _), .VBuiltin _ _ _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [_], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Integer _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ByteString _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.String _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Unit, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Bool _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstDataList _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstPairDataList _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Pair _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.PairData _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.Data _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon (.ConstArray _), _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Bls12_381_G1_element, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Bls12_381_G2_element, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VCon .Bls12_381_MlResult, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VDelay _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VLam _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VConstr _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | [.VBuiltin _ _ _, _], _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
      | _ :: _ :: _ :: _, _, hv₁ => simp [evalBuiltinPassThrough] at hv₁
  · -- Default case: b is not a pass-through builtin
    exfalso
    have h1 : b ≠ .IfThenElse := fun heq => hb (Or.inl heq)
    have h2 : b ≠ .ChooseUnit := fun heq => hb (Or.inr (Or.inl heq))
    have h3 : b ≠ .Trace := fun heq => hb (Or.inr (Or.inr (Or.inl heq)))
    have h4 : b ≠ .ChooseData := fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inl heq))))
    have h5 : b ≠ .ChooseList :=
      fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl heq)))))
    have h6 : b ≠ .MkCons :=
      fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr heq)))))
    have h_none := evalBuiltinPassThrough_none_of_not_passthrough b args₁ ⟨h1, h2, h3, h4, h5, h6⟩
    rw [h_none] at hv₁
    exact Option.noConfusion hv₁


/-- Reverse direction of `_some`: if RHS succeeds, LHS succeeds with related output. -/
theorem shiftBisimValueList_evalBuiltinPassThrough_some_rev : ∀ (b : BuiltinFun) {args₁ args₂ : List CekValue},
    ShiftBisimValueList args₁ args₂ →
    ∀ v₂, evalBuiltinPassThrough b args₂ = some v₂ →
      ∃ v₁, evalBuiltinPassThrough b args₁ = some v₁ ∧ ShiftBisimValue v₁ v₂ := by
  intro b args₁ args₂ h v₂ hv₂
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    -- IfThenElse
    · match args₂, h, hv₂ with
      | [e₂, t₂, .VCon (.Bool cond)], h_args, hv₂ =>
        obtain ⟨e₁, _, he₁, h_e, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨t₁, _, he₂, h_t, hr'⟩ := shiftBisimValueList_cons_inv_right hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := shiftBisimValueList_cons_inv_right hr'
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃
        cases shiftBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        refine ⟨if cond then t₁ else e₁, rfl, ?_⟩
        by_cases hc : cond
        · subst hc; exact h_t
        · simp only [hc]; exact h_e
      | [], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Integer _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ByteString _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.String _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Unit], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ConstList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ConstDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ConstPairDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Pair _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.PairData _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Data _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ConstArray _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Bls12_381_G1_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Bls12_381_G2_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Bls12_381_MlResult], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VDelay _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VLam _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VConstr _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VBuiltin _ _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | _ :: _ :: _ :: _ :: _, _, hv => simp [evalBuiltinPassThrough] at hv
    -- ChooseUnit
    · match args₂, h, hv₂ with
      | [r₂, .VCon .Unit], h_args, hv₂ =>
        obtain ⟨r₁, _, he₁, h_r, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := shiftBisimValueList_cons_inv_right hr
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂
        cases shiftBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        exact ⟨r₁, rfl, h_r⟩
      | [], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Integer _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ByteString _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.String _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Bool _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstPairDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Pair _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.PairData _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Data _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstArray _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Bls12_381_G1_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Bls12_381_G2_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Bls12_381_MlResult], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VDelay _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VLam _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VConstr _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VBuiltin _ _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | _ :: _ :: _ :: _, _, hv => simp [evalBuiltinPassThrough] at hv
    -- Trace
    · match args₂, h, hv₂ with
      | [r₂, .VCon (.String _)], h_args, hv₂ =>
        obtain ⟨r₁, _, he₁, h_r, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := shiftBisimValueList_cons_inv_right hr
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂
        cases shiftBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        exact ⟨r₁, rfl, h_r⟩
      | [], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Integer _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ByteString _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Unit], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Bool _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstPairDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Pair _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.PairData _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.Data _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon (.ConstArray _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Bls12_381_G1_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Bls12_381_G2_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VCon .Bls12_381_MlResult], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VDelay _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VLam _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VConstr _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, .VBuiltin _ _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | _ :: _ :: _ :: _, _, hv => simp [evalBuiltinPassThrough] at hv
    -- ChooseData
    · match args₂, h, hv₂ with
      | [b₂, i₂, l₂, m₂, cr₂, .VCon (.Data d)], h_args, hv₂ =>
        obtain ⟨b₁, _, he₁, h_b, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨i₁, _, he₂, h_i, hr₂⟩ := shiftBisimValueList_cons_inv_right hr
        obtain ⟨l₁, _, he₃, h_l, hr₃⟩ := shiftBisimValueList_cons_inv_right hr₂
        obtain ⟨m₁, _, he₄, h_m, hr₄⟩ := shiftBisimValueList_cons_inv_right hr₃
        obtain ⟨cr₁, _, he₅, h_cr, hr₅⟩ := shiftBisimValueList_cons_inv_right hr₄
        obtain ⟨w, _, he₆, h_w, hrn⟩ := shiftBisimValueList_cons_inv_right hr₅
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃ he₄ he₅ he₆
        cases shiftBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough] at hv₂
        cases d with
        | Constr _ _ =>
          simp only [Option.some.injEq] at hv₂; subst hv₂
          exact ⟨cr₁, rfl, h_cr⟩
        | Map _ =>
          simp only [Option.some.injEq] at hv₂; subst hv₂
          exact ⟨m₁, rfl, h_m⟩
        | List _ =>
          simp only [Option.some.injEq] at hv₂; subst hv₂
          exact ⟨l₁, rfl, h_l⟩
        | I _ =>
          simp only [Option.some.injEq] at hv₂; subst hv₂
          exact ⟨i₁, rfl, h_i⟩
        | B _ =>
          simp only [Option.some.injEq] at hv₂; subst hv₂
          exact ⟨b₁, rfl, h_b⟩
      | [], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.Integer _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.ByteString _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.String _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon .Unit], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.Bool _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.ConstList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.ConstDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.ConstPairDataList _)], _, hv =>
          simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.Pair _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.PairData _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon (.ConstArray _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon .Bls12_381_G1_element], _, hv =>
          simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon .Bls12_381_G2_element], _, hv =>
          simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VCon .Bls12_381_MlResult], _, hv =>
          simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VDelay _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VLam _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VConstr _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, _, _, _, .VBuiltin _ _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, hv => simp [evalBuiltinPassThrough] at hv
    -- ChooseList
    · match args₂, h, hv₂ with
      | [c₂, n₂, .VCon (.ConstDataList l)], h_args, hv₂ =>
        obtain ⟨c₁, _, he₁, h_c, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨n₁, _, he₂, h_n, hr'⟩ := shiftBisimValueList_cons_inv_right hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := shiftBisimValueList_cons_inv_right hr'
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃
        cases shiftBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        refine ⟨if l.isEmpty then n₁ else c₁, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [c₂, n₂, .VCon (.ConstList l)], h_args, hv₂ =>
        obtain ⟨c₁, _, he₁, h_c, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨n₁, _, he₂, h_n, hr'⟩ := shiftBisimValueList_cons_inv_right hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := shiftBisimValueList_cons_inv_right hr'
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃
        cases shiftBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        refine ⟨if l.isEmpty then n₁ else c₁, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Integer _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ByteString _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.String _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Unit], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Bool _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ConstPairDataList _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Pair _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.PairData _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.Data _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon (.ConstArray _)], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Bls12_381_G1_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Bls12_381_G2_element], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VCon .Bls12_381_MlResult], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VDelay _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VLam _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VConstr _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_, _, .VBuiltin _ _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | _ :: _ :: _ :: _ :: _, _, hv => simp [evalBuiltinPassThrough] at hv
    -- MkCons
    · match args₂, h, hv₂ with
      | [.VCon (.ConstList tail), .VCon c], h_args, hv₂ =>
        obtain ⟨w₁, _, he₁, h_w₁, hr⟩ := shiftBisimValueList_cons_inv_right h_args
        obtain ⟨w₂, _, he₂, h_w₂, hrn⟩ := shiftBisimValueList_cons_inv_right hr
        have hnil := shiftBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂
        cases shiftBisimValue_vcon_inv_right h_w₁
        cases shiftBisimValue_vcon_inv_right h_w₂
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        exact ⟨.VCon (.ConstList (c :: tail)), rfl, ShiftBisimValue.vcon _⟩
      | [.VCon (.ConstList _), .VDelay _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ConstList _), .VLam _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ConstList _), .VConstr _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ConstList _), .VBuiltin _ _ _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [], _, hv => simp [evalBuiltinPassThrough] at hv
      | [_], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.Integer _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ByteString _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.String _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon .Unit, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.Bool _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ConstDataList _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ConstPairDataList _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.Pair _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.PairData _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.Data _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon (.ConstArray _), _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon .Bls12_381_G1_element, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon .Bls12_381_G2_element, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VCon .Bls12_381_MlResult, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VDelay _ _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VLam _ _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VConstr _ _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | [.VBuiltin _ _ _, _], _, hv => simp [evalBuiltinPassThrough] at hv
      | _ :: _ :: _ :: _, _, hv => simp [evalBuiltinPassThrough] at hv
  · exfalso
    have h1 : b ≠ .IfThenElse := fun heq => hb (Or.inl heq)
    have h2 : b ≠ .ChooseUnit := fun heq => hb (Or.inr (Or.inl heq))
    have h3 : b ≠ .Trace := fun heq => hb (Or.inr (Or.inr (Or.inl heq)))
    have h4 : b ≠ .ChooseData := fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inl heq))))
    have h5 : b ≠ .ChooseList :=
      fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl heq)))))
    have h6 : b ≠ .MkCons :=
      fun heq => hb (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr heq)))))
    have h_none := evalBuiltinPassThrough_none_of_not_passthrough b args₂ ⟨h1, h2, h3, h4, h5, h6⟩
    rw [h_none] at hv₂
    exact Option.noConfusion hv₂

/-- Full bidirectional evalBuiltinPassThrough compat. -/
theorem shiftBisimValueList_evalBuiltinPassThrough (b : BuiltinFun)
    {args₁ args₂ : List CekValue} (h : ShiftBisimValueList args₁ args₂) :
    (∀ v₁, evalBuiltinPassThrough b args₁ = some v₁ →
      ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ ShiftBisimValue v₁ v₂) ∧
    (evalBuiltinPassThrough b args₁ = none ↔ evalBuiltinPassThrough b args₂ = none) := by
  refine ⟨shiftBisimValueList_evalBuiltinPassThrough_some b h, ?_, ?_⟩
  · intro hn
    cases heq : evalBuiltinPassThrough b args₂ with
    | none => rfl
    | some v₂ =>
      exfalso
      obtain ⟨v₁, hv₁, _⟩ :=
        shiftBisimValueList_evalBuiltinPassThrough_some_rev b h v₂ heq
      rw [hn] at hv₁
      exact Option.noConfusion hv₁
  · intro hn
    cases heq : evalBuiltinPassThrough b args₁ with
    | none => rfl
    | some v₁ =>
      exfalso
      obtain ⟨v₂, hv₂, _⟩ :=
        shiftBisimValueList_evalBuiltinPassThrough_some b h v₁ heq
      rw [hn] at hv₂
      exact Option.noConfusion hv₂

/-- Full evalBuiltin compat: bisim-preserves both Some (with related value)
    and None directions under ShiftBisimValueList. -/
theorem shiftBisimValueList_evalBuiltin {b : BuiltinFun}
    {args₁ args₂ : List CekValue} (h : ShiftBisimValueList args₁ args₂) :
    (∀ v₁, evalBuiltin b args₁ = some v₁ →
      ∃ v₂, evalBuiltin b args₂ = some v₂ ∧ ShiftBisimValue v₁ v₂) ∧
    (evalBuiltin b args₁ = none ↔ evalBuiltin b args₂ = none) := by
  have h_ext : extractConsts args₁ = extractConsts args₂ :=
    shiftBisimValueList_extractConsts _ h
  obtain ⟨h_pt_some, h_pt_iff⟩ := shiftBisimValueList_evalBuiltinPassThrough b h
  refine ⟨?_, ?_⟩
  -- SOME direction
  · intro v₁ hv₁
    cases hpt₁ : evalBuiltinPassThrough b args₁ with
    | some v_pt =>
      obtain ⟨v₂, hpt₂, h_rel⟩ := h_pt_some v_pt hpt₁
      refine ⟨v₂, ?_, ?_⟩
      · simp only [evalBuiltin, hpt₂]
      · have heq : v₁ = v_pt := by
          have h1 : evalBuiltin b args₁ = some v_pt := by
            simp only [evalBuiltin, hpt₁]
          rw [hv₁] at h1
          exact Option.some.inj h1
        rw [heq]
        exact h_rel
    | none =>
      have hpt₂ : evalBuiltinPassThrough b args₂ = none := h_pt_iff.mp hpt₁
      cases hec₁ : extractConsts args₁ with
      | none =>
        exfalso
        have : evalBuiltin b args₁ = none := by
          simp only [evalBuiltin, hpt₁, hec₁]
        rw [hv₁] at this
        exact Option.noConfusion this
      | some cs =>
        have hec₂ : extractConsts args₂ = some cs := h_ext ▸ hec₁
        cases hbc : evalBuiltinConst b cs with
        | none =>
          exfalso
          have : evalBuiltin b args₁ = none := by
            simp only [evalBuiltin, hpt₁, hec₁, hbc]
          rw [hv₁] at this
          exact Option.noConfusion this
        | some c =>
          refine ⟨.VCon c, ?_, ?_⟩
          · simp only [evalBuiltin, hpt₂, hec₂, hbc]
          · have heq : v₁ = .VCon c := by
              have h1 : evalBuiltin b args₁ = some (.VCon c) := by
                simp only [evalBuiltin, hpt₁, hec₁, hbc]
              rw [hv₁] at h1
              exact Option.some.inj h1
            rw [heq]
            exact ShiftBisimValue.vcon c
  -- NONE ↔ NONE direction
  · constructor
    · intro hn
      cases hpt₁ : evalBuiltinPassThrough b args₁ with
      | some v =>
        exfalso
        have : evalBuiltin b args₁ = some v := by
          simp only [evalBuiltin, hpt₁]
        rw [hn] at this
        exact Option.noConfusion this
      | none =>
        have hpt₂ := h_pt_iff.mp hpt₁
        cases hec₁ : extractConsts args₁ with
        | none =>
          have hec₂ : extractConsts args₂ = none := h_ext ▸ hec₁
          simp only [evalBuiltin, hpt₂, hec₂]
        | some cs =>
          have hec₂ : extractConsts args₂ = some cs := h_ext ▸ hec₁
          cases hbc : evalBuiltinConst b cs with
          | none =>
            simp only [evalBuiltin, hpt₂, hec₂, hbc]
          | some c =>
            exfalso
            have : evalBuiltin b args₁ = some (.VCon c) := by
              simp only [evalBuiltin, hpt₁, hec₁, hbc]
            rw [hn] at this
            exact Option.noConfusion this
    · intro hn
      cases hpt₂ : evalBuiltinPassThrough b args₂ with
      | some v =>
        exfalso
        have : evalBuiltin b args₂ = some v := by
          simp only [evalBuiltin, hpt₂]
        rw [hn] at this
        exact Option.noConfusion this
      | none =>
        have hpt₁ := h_pt_iff.mpr hpt₂
        cases hec₂ : extractConsts args₂ with
        | none =>
          have hec₁ : extractConsts args₁ = none := by rw [h_ext]; exact hec₂
          simp only [evalBuiltin, hpt₁, hec₁]
        | some cs =>
          have hec₁ : extractConsts args₁ = some cs := by rw [h_ext]; exact hec₂
          cases hbc : evalBuiltinConst b cs with
          | none =>
            simp only [evalBuiltin, hpt₁, hec₁, hbc]
          | some c =>
            exfalso
            have : evalBuiltin b args₂ = some (.VCon c) := by
              simp only [evalBuiltin, hpt₂, hec₂, hbc]
            rw [hn] at this
            exact Option.noConfusion this

theorem shiftBisimValueList_constToTagAndFields_refl :
    ∀ {c : Const} {tag numCtors : Nat} {fs : List CekValue},
      constToTagAndFields c = some (tag, numCtors, fs) → ShiftBisimValueList fs fs := by
  intro c tag numCtors fs hc
  cases c with
  | Integer n =>
    simp only [constToTagAndFields] at hc
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact ShiftBisimValueList.nil
    · exact Option.noConfusion hc
  | ByteString _ => simp [constToTagAndFields] at hc
  | String _ => simp [constToTagAndFields] at hc
  | Unit =>
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc
    subst hfs
    exact ShiftBisimValueList.nil
  | Bool b =>
    cases b <;>
    · simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact ShiftBisimValueList.nil
  | ConstList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact ShiftBisimValueList.nil
    | cons head tail =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact ShiftBisimValueList.cons (ShiftBisimValue.vcon _)
              (ShiftBisimValueList.cons (ShiftBisimValue.vcon _) ShiftBisimValueList.nil)
  | ConstDataList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact ShiftBisimValueList.nil
    | cons head tail =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact ShiftBisimValueList.cons (ShiftBisimValue.vcon _)
              (ShiftBisimValueList.cons (ShiftBisimValue.vcon _) ShiftBisimValueList.nil)
  | ConstPairDataList _ => simp [constToTagAndFields] at hc
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc
    subst hfs
    exact ShiftBisimValueList.cons (ShiftBisimValue.vcon _)
            (ShiftBisimValueList.cons (ShiftBisimValue.vcon _) ShiftBisimValueList.nil)
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc
    subst hfs
    exact ShiftBisimValueList.cons (ShiftBisimValue.vcon _)
            (ShiftBisimValueList.cons (ShiftBisimValue.vcon _) ShiftBisimValueList.nil)
  | Data _ => simp [constToTagAndFields] at hc
  | ConstArray _ => simp [constToTagAndFields] at hc
  | Bls12_381_G1_element => simp [constToTagAndFields] at hc
  | Bls12_381_G2_element => simp [constToTagAndFields] at hc
  | Bls12_381_MlResult => simp [constToTagAndFields] at hc

--------------------------------------------------------------------------------
-- 19d. step_preserves — the main shift bisimulation theorem
--------------------------------------------------------------------------------

/-- The shift bisimulation is preserved by one CEK step. -/
theorem shiftBisimState_step_preserves : ∀ {s₁ s₂ : State},
    ShiftBisimState s₁ s₂ → ShiftBisimState (step s₁) (step s₂) := by
  intro s₁ s₂ h
  cases h with
  | halt h_v => exact ShiftBisimState.halt h_v
  | error => exact ShiftBisimState.error
  | @compute π₁ π₂ ρ₁ ρ₂ t σ d h_σ hρ h_closed hπ =>
    cases t with
    | Var n =>
      -- LHS: compute π₁ ρ₁ (.Var n) → match ρ₁.lookup n
      -- RHS: compute π₂ ρ₂ (renameTerm σ (.Var n)) = compute π₂ ρ₂ (.Var (σ n)) →
      --       match ρ₂.lookup (σ n)
      show ShiftBisimState
        (match ρ₁.lookup n with | some v => .ret π₁ v | none => .error)
        (match ρ₂.lookup (σ n) with | some v => .ret π₂ v | none => .error)
      by_cases hn : n = 0
      · subst hn
        have h_σ0 : σ 0 = 0 := h_σ.1
        have h1 : ρ₁.lookup 0 = none := by cases ρ₁ <;> rfl
        have h2 : ρ₂.lookup 0 = none := by cases ρ₂ <;> rfl
        rw [h1]
        rw [h_σ0, h2]
        exact ShiftBisimState.error
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn
        have h_n_le_d : n ≤ d := by
          simp only [closedAt, decide_eq_true_eq] at h_closed
          exact h_closed
        obtain ⟨v₁, v₂, hl₁, hl₂, h_v⟩ := shiftBisimEnv_lookup σ d hρ hpos h_n_le_d
        rw [hl₁, hl₂]
        exact ShiftBisimState.ret h_v hπ
    | Constant p =>
      show ShiftBisimState (.ret π₁ (.VCon p.1)) (.ret π₂ (.VCon p.1))
      exact ShiftBisimState.ret (ShiftBisimValue.vcon p.1) hπ
    | Builtin b =>
      show ShiftBisimState (.ret π₁ (.VBuiltin b [] (expectedArgs b)))
                            (.ret π₂ (.VBuiltin b [] (expectedArgs b)))
      exact ShiftBisimState.ret
        (ShiftBisimValue.vbuiltin b (expectedArgs b) ShiftBisimValueList.nil) hπ
    | Lam _ body =>
      have h_body : closedAt (d + 1) body = true := by
        simp only [closedAt] at h_closed; exact h_closed
      show ShiftBisimState (.ret π₁ (.VLam body ρ₁))
                            (.ret π₂ (.VLam (Moist.Verified.renameTerm
                              (Moist.Verified.liftRename σ) body) ρ₂))
      exact ShiftBisimState.ret (ShiftBisimValue.vlam h_σ hρ h_body) hπ
    | Delay body =>
      have h_body : closedAt d body = true := by
        simp only [closedAt] at h_closed; exact h_closed
      show ShiftBisimState (.ret π₁ (.VDelay body ρ₁))
                            (.ret π₂ (.VDelay (Moist.Verified.renameTerm σ body) ρ₂))
      exact ShiftBisimState.ret (ShiftBisimValue.vdelay h_σ hρ h_body) hπ
    | Force e =>
      have h_e : closedAt d e = true := by
        simp only [closedAt] at h_closed; exact h_closed
      show ShiftBisimState (.compute (.force :: π₁) ρ₁ e)
                            (.compute (.force :: π₂) ρ₂ (Moist.Verified.renameTerm σ e))
      exact ShiftBisimState.compute h_σ hρ h_e
        (ShiftBisimStack.cons ShiftBisimFrame.force hπ)
    | Apply f x =>
      have h_fx : closedAt d f = true ∧ closedAt d x = true := by
        simp only [closedAt, Bool.and_eq_true] at h_closed; exact h_closed
      show ShiftBisimState (.compute (.arg x ρ₁ :: π₁) ρ₁ f)
                            (.compute (.arg (Moist.Verified.renameTerm σ x) ρ₂ :: π₂) ρ₂
                              (Moist.Verified.renameTerm σ f))
      exact ShiftBisimState.compute h_σ hρ h_fx.1
              (ShiftBisimStack.cons (ShiftBisimFrame.arg h_σ hρ h_fx.2) hπ)
    | Constr tag args =>
      cases args with
      | nil =>
        show ShiftBisimState (.ret π₁ (.VConstr tag [])) (.ret π₂ (.VConstr tag []))
        exact ShiftBisimState.ret
          (ShiftBisimValue.vconstr tag ShiftBisimValueList.nil) hπ
      | cons m ms =>
        have h_mms : closedAt d m = true ∧ closedAtList d ms = true := by
          simp only [closedAt, closedAtList, Bool.and_eq_true] at h_closed
          exact h_closed
        show ShiftBisimState (.compute (.constrField tag [] ms ρ₁ :: π₁) ρ₁ m)
                              (.compute (.constrField tag [] (Moist.Verified.renameTermList σ ms)
                                ρ₂ :: π₂) ρ₂ (Moist.Verified.renameTerm σ m))
        exact ShiftBisimState.compute h_σ hρ h_mms.1
                (ShiftBisimStack.cons
                  (ShiftBisimFrame.constrField tag h_σ ShiftBisimValueList.nil hρ h_mms.2)
                  hπ)
    | Case scrut alts =>
      have h_sa : closedAt d scrut = true ∧ closedAtList d alts = true := by
        simp only [closedAt, Bool.and_eq_true] at h_closed; exact h_closed
      show ShiftBisimState (.compute (.caseScrutinee alts ρ₁ :: π₁) ρ₁ scrut)
                            (.compute (.caseScrutinee (Moist.Verified.renameTermList σ alts)
                              ρ₂ :: π₂) ρ₂ (Moist.Verified.renameTerm σ scrut))
      exact ShiftBisimState.compute h_σ hρ h_sa.1
              (ShiftBisimStack.cons
                (ShiftBisimFrame.caseScrutinee h_σ hρ h_sa.2)
                hπ)
    | Error => exact ShiftBisimState.error
  | @ret π₁ π₂ v₁ v₂ h_v hπ =>
    cases hπ with
    | nil => exact ShiftBisimState.halt h_v
    | @cons f₁ f₂ π₁' π₂' h_f h_rest =>
      cases h_f with
      | force =>
        cases h_v with
        | vcon c => exact ShiftBisimState.error
        | vlam _ _ _ => exact ShiftBisimState.error
        | @vdelay body ρ₁' ρ₂' σ' d' h_σ' hρ' h_body =>
          show ShiftBisimState (.compute π₁' ρ₁' body)
                                (.compute π₂' ρ₂' (Moist.Verified.renameTerm σ' body))
          exact ShiftBisimState.compute h_σ' hρ' h_body h_rest
        | vconstr tag _ => exact ShiftBisimState.error
        | @vbuiltin b ea args₁ args₂ h_args =>
          cases ea with
          | one k =>
            cases k with
            | argV => exact ShiftBisimState.error
            | argQ =>
              have ⟨h_some, h_iff⟩ := @shiftBisimValueList_evalBuiltin b args₁ args₂ h_args
              cases he₁ : evalBuiltin b args₁ with
              | some v₁' =>
                obtain ⟨v₂', he₂, h_v_rel⟩ := h_some v₁' he₁
                show ShiftBisimState
                  (match evalBuiltin b args₁ with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b args₂ with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact ShiftBisimState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b args₂ = none := h_iff.mp he₁
                show ShiftBisimState
                  (match evalBuiltin b args₁ with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b args₂ with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact ShiftBisimState.error
          | more k rest =>
            cases k with
            | argV => exact ShiftBisimState.error
            | argQ =>
              exact ShiftBisimState.ret
                (ShiftBisimValue.vbuiltin b rest h_args) h_rest
      | @arg t ρ₁' ρ₂' σ' d' h_σ' hρ' h_t =>
        show ShiftBisimState (.compute (.funV v₁ :: π₁') ρ₁' t)
                              (.compute (.funV v₂ :: π₂') ρ₂'
                                (Moist.Verified.renameTerm σ' t))
        exact ShiftBisimState.compute h_σ' hρ' h_t
                (ShiftBisimStack.cons (ShiftBisimFrame.funV h_v) h_rest)
      | @funV v_f₁ v_f₂ h_vf =>
        cases h_vf with
        | vcon _ => exact ShiftBisimState.error
        | @vlam body ρ₁' ρ₂' σ' d' h_σ' hρ' h_body =>
          show ShiftBisimState (.compute π₁' (ρ₁'.extend v₁) body)
                                (.compute π₂' (ρ₂'.extend v₂)
                                  (Moist.Verified.renameTerm
                                    (Moist.Verified.liftRename σ') body))
          have hρ'' := shiftBisimEnv_extend h_σ' d' hρ' h_v
          exact ShiftBisimState.compute (is0preserving_lift σ') hρ'' h_body h_rest
        | vdelay _ _ _ => exact ShiftBisimState.error
        | vconstr _ _ => exact ShiftBisimState.error
        | @vbuiltin b ea args₁ args₂ h_args =>
          cases ea with
          | one k =>
            cases k with
            | argQ => exact ShiftBisimState.error
            | argV =>
              have h_args' : ShiftBisimValueList (v₁ :: args₁) (v₂ :: args₂) :=
                ShiftBisimValueList.cons h_v h_args
              have ⟨h_some, h_iff⟩ :=
                @shiftBisimValueList_evalBuiltin b (v₁ :: args₁) (v₂ :: args₂) h_args'
              cases he₁ : evalBuiltin b (v₁ :: args₁) with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show ShiftBisimState
                  (match evalBuiltin b (v₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact ShiftBisimState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b (v₂ :: args₂) = none := h_iff.mp he₁
                show ShiftBisimState
                  (match evalBuiltin b (v₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact ShiftBisimState.error
          | more k rest =>
            cases k with
            | argQ => exact ShiftBisimState.error
            | argV =>
              exact ShiftBisimState.ret
                (ShiftBisimValue.vbuiltin b rest (ShiftBisimValueList.cons h_v h_args))
                h_rest
      | @applyArg v_x₁ v_x₂ h_vx =>
        cases h_v with
        | vcon _ => exact ShiftBisimState.error
        | @vlam body ρ₁' ρ₂' σ' d' h_σ' hρ' h_body =>
          show ShiftBisimState (.compute π₁' (ρ₁'.extend v_x₁) body)
                                (.compute π₂' (ρ₂'.extend v_x₂)
                                  (Moist.Verified.renameTerm
                                    (Moist.Verified.liftRename σ') body))
          have hρ'' := shiftBisimEnv_extend h_σ' d' hρ' h_vx
          exact ShiftBisimState.compute (is0preserving_lift σ') hρ'' h_body h_rest
        | vdelay _ _ _ => exact ShiftBisimState.error
        | vconstr _ _ => exact ShiftBisimState.error
        | @vbuiltin b ea args₁ args₂ h_args =>
          cases ea with
          | one k =>
            cases k with
            | argQ => exact ShiftBisimState.error
            | argV =>
              have h_args' : ShiftBisimValueList (v_x₁ :: args₁) (v_x₂ :: args₂) :=
                ShiftBisimValueList.cons h_vx h_args
              have ⟨h_some, h_iff⟩ :=
                @shiftBisimValueList_evalBuiltin b (v_x₁ :: args₁) (v_x₂ :: args₂) h_args'
              cases he₁ : evalBuiltin b (v_x₁ :: args₁) with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show ShiftBisimState
                  (match evalBuiltin b (v_x₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v_x₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact ShiftBisimState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b (v_x₂ :: args₂) = none := h_iff.mp he₁
                show ShiftBisimState
                  (match evalBuiltin b (v_x₁ :: args₁) with
                    | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v_x₂ :: args₂) with
                    | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact ShiftBisimState.error
          | more k rest =>
            cases k with
            | argQ => exact ShiftBisimState.error
            | argV =>
              exact ShiftBisimState.ret
                (ShiftBisimValue.vbuiltin b rest (ShiftBisimValueList.cons h_vx h_args))
                h_rest
      | @constrField tag done₁ done₂ todo ρ₁' ρ₂' σ' d' h_σ' h_done hρ' h_todo =>
        cases todo with
        | nil =>
          show ShiftBisimState (.ret π₁' (.VConstr tag ((v₁ :: done₁).reverse)))
                                (.ret π₂' (.VConstr tag ((v₂ :: done₂).reverse)))
          exact ShiftBisimState.ret
            (ShiftBisimValue.vconstr tag
              (shiftBisimValueList_reverse _ (ShiftBisimValueList.cons h_v h_done))) h_rest
        | cons m ms =>
          have h_mms : closedAt d' m = true ∧ closedAtList d' ms = true := by
            simp only [closedAtList, Bool.and_eq_true] at h_todo
            exact h_todo
          show ShiftBisimState (.compute (.constrField tag (v₁ :: done₁) ms ρ₁' :: π₁') ρ₁' m)
                                (.compute
                                  (.constrField tag (v₂ :: done₂)
                                    (Moist.Verified.renameTermList σ' ms) ρ₂' :: π₂')
                                  ρ₂' (Moist.Verified.renameTerm σ' m))
          exact ShiftBisimState.compute h_σ' hρ' h_mms.1
                  (ShiftBisimStack.cons
                    (ShiftBisimFrame.constrField tag h_σ'
                      (ShiftBisimValueList.cons h_v h_done) hρ' h_mms.2)
                    h_rest)
      | @caseScrutinee alts ρ₁' ρ₂' σ' d' h_σ' hρ' h_alts =>
        cases h_v with
        | vcon c =>
          show ShiftBisimState
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₁') ρ₁' alt
                  | none => State.error
              | none => State.error)
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && (Moist.Verified.renameTermList σ' alts).length > numCtors
                then State.error
                else match (Moist.Verified.renameTermList σ' alts)[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₂') ρ₂' alt
                  | none => State.error
              | none => State.error)
          cases hc : constToTagAndFields c with
          | none => exact ShiftBisimState.error
          | some r =>
            obtain ⟨tag, numCtors, fields⟩ := r
            have h_len_eq : (Moist.Verified.renameTermList σ' alts).length = alts.length :=
              Moist.Verified.renameTermList_length σ' alts
            by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
            · have hnum' : (numCtors > 0 && (Moist.Verified.renameTermList σ' alts).length > numCtors) = true := by
                rw [h_len_eq]; exact hnum
              simp only [hnum, hnum', if_true]
              exact ShiftBisimState.error
            · have hnum' : (numCtors > 0 && (Moist.Verified.renameTermList σ' alts).length > numCtors) = false := by
                rw [h_len_eq]
                cases hn : (numCtors > 0 && alts.length > numCtors) with
                | true => exact absurd hn hnum
                | false => rfl
              simp only [hnum, hnum', if_false, Bool.false_eq_true]
              cases ha : alts[tag]? with
              | none =>
                have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
                have hge' : tag ≥ (Moist.Verified.renameTermList σ' alts).length := by
                  rw [h_len_eq]; exact hge
                have ha' : (Moist.Verified.renameTermList σ' alts)[tag]? = none :=
                  List.getElem?_eq_none hge'
                rw [ha']
                exact ShiftBisimState.error
              | some alt =>
                have h_alt := shiftBisim_closedAtList_get d' alts tag alt h_alts ha
                have hlt : tag < alts.length := by
                  rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                  · exact h_case
                  · rw [List.getElem?_eq_none h_case] at ha; cases ha
                have hlt' : tag < (Moist.Verified.renameTermList σ' alts).length := by
                  rw [h_len_eq]; exact hlt
                have heq_val : alts[tag] = alt := by
                  have := List.getElem?_eq_some_iff.mp ha
                  exact this.2
                have ha' : (Moist.Verified.renameTermList σ' alts)[tag]? =
                    some (Moist.Verified.renameTerm σ' alt) := by
                  rw [List.getElem?_eq_some_iff.mpr]
                  refine ⟨hlt', ?_⟩
                  rw [Moist.Verified.renameTermList_getElem σ' alts tag hlt, heq_val]
                rw [ha']
                have h_fs_refl : ShiftBisimValueList fields fields :=
                  shiftBisimValueList_constToTagAndFields_refl hc
                exact ShiftBisimState.compute h_σ' hρ' h_alt
                        (shiftBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
        | vlam _ _ _ => exact ShiftBisimState.error
        | vdelay _ _ _ => exact ShiftBisimState.error
        | @vconstr tag fs₁ fs₂ h_fs =>
          show ShiftBisimState
            (match alts[tag]? with
              | some alt => State.compute (fs₁.map Frame.applyArg ++ π₁') ρ₁' alt
              | none => State.error)
            (match (Moist.Verified.renameTermList σ' alts)[tag]? with
              | some alt => State.compute (fs₂.map Frame.applyArg ++ π₂') ρ₂' alt
              | none => State.error)
          have h_len_eq : (Moist.Verified.renameTermList σ' alts).length = alts.length :=
            Moist.Verified.renameTermList_length σ' alts
          cases ha : alts[tag]? with
          | none =>
            have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
            have hge' : tag ≥ (Moist.Verified.renameTermList σ' alts).length := by
              rw [h_len_eq]; exact hge
            have ha' : (Moist.Verified.renameTermList σ' alts)[tag]? = none :=
              List.getElem?_eq_none hge'
            rw [ha']
            exact ShiftBisimState.error
          | some alt =>
            have h_alt := shiftBisim_closedAtList_get d' alts tag alt h_alts ha
            have hlt : tag < alts.length := by
              rcases Nat.lt_or_ge tag alts.length with h_case | h_case
              · exact h_case
              · rw [List.getElem?_eq_none h_case] at ha; cases ha
            have hlt' : tag < (Moist.Verified.renameTermList σ' alts).length := by
              rw [h_len_eq]; exact hlt
            have heq_val : alts[tag] = alt := by
              have := List.getElem?_eq_some_iff.mp ha
              exact this.2
            have ha' : (Moist.Verified.renameTermList σ' alts)[tag]? =
                some (Moist.Verified.renameTerm σ' alt) := by
              rw [List.getElem?_eq_some_iff.mpr]
              refine ⟨hlt', ?_⟩
              rw [Moist.Verified.renameTermList_getElem σ' alts tag hlt, heq_val]
            rw [ha']
            exact ShiftBisimState.compute h_σ' hρ' h_alt
                    (shiftBisimValueList_to_applyArg_stack fs₁ h_fs h_rest)
        | vbuiltin _ _ _ => exact ShiftBisimState.error

--------------------------------------------------------------------------------
-- 19e. Iterated step + halt/error inversions
--------------------------------------------------------------------------------

/-- Iterated version of `step_preserves`: `ShiftBisimState` is preserved
    under any number of `step` calls. -/
theorem shiftBisimState_steps_preserves : ∀ (n : Nat) {s₁ s₂ : State},
    ShiftBisimState s₁ s₂ → ShiftBisimState (steps n s₁) (steps n s₂) := by
  intro n
  induction n with
  | zero => intro _ _ h; exact h
  | succ m ih =>
    intro s₁ s₂ h
    show ShiftBisimState (steps m (step s₁)) (steps m (step s₂))
    exact ih (shiftBisimState_step_preserves h)

/-- Halt inversion: if `ShiftBisimState (halt v) s`, then `s` is `halt v'`
    for some `v'` with `ShiftBisimValue v v'`. -/
theorem shiftBisimState_halt_inv : ∀ {v : CekValue} {s : State},
    ShiftBisimState (.halt v) s → ∃ v', s = .halt v' ∧ ShiftBisimValue v v'
  | _, _, .halt h_v => ⟨_, rfl, h_v⟩

/-- Error inversion: if `ShiftBisimState .error s`, then `s = .error`. -/
theorem shiftBisimState_error_inv : ∀ {s : State},
    ShiftBisimState .error s → s = .error
  | _, .error => rfl

/-- Ret inversion: `ShiftBisimState (ret π v) s` forces s = ret π' v' with relations. -/
theorem shiftBisimState_ret_inv : ∀ {π : Stack} {v : CekValue} {s : State},
    ShiftBisimState (.ret π v) s →
    ∃ π' v', s = .ret π' v' ∧ ShiftBisimValue v v' ∧ ShiftBisimStack π π'
  | _, _, _, .ret h_v h_π => ⟨_, _, rfl, h_v, h_π⟩

--------------------------------------------------------------------------------
-- 19f. ShiftBisimValue → ValueRefinesK extraction
--
-- Shows ShiftBisimValue implies ValueRefinesK at any step index.
-- Uses mutual induction on step index and value structure.
-- Closure cases use renameRefinesR_shift1 (via renameRefinesR with liftRename).
--------------------------------------------------------------------------------

section ShiftBisimValueRefines
open Moist.Verified.FundamentalRefines (renameRefinesR is0preserving_lift)

/-- Convert `ShiftBisimEnv σ d ρ₁ ρ₂` to `RenameEnvRefR σ k d ρ₁ ρ₂` at a
    specific step index k, assuming `ShiftBisimValue` implies `ValueRefinesK`
    at k. -/
private theorem shiftBisimEnv_to_renameEnvRefR_at (k : Nat)
    (hvrel : ∀ (v₁ v₂ : CekValue), ShiftBisimValue v₁ v₂ →
      ValueRefinesK k v₁ v₂)
    {σ : Nat → Nat} {d : Nat} {ρ₁ ρ₂ : CekEnv}
    (h : ShiftBisimEnv σ d ρ₁ ρ₂) :
    Moist.Verified.FundamentalRefines.RenameEnvRefR σ k d ρ₁ ρ₂ := by
  intro n hn hnd
  obtain ⟨v₁, v₂, hl₁, hl₂, h_v⟩ := shiftBisimEnv_lookup σ d h hn hnd
  show match ρ₁.lookup n, ρ₂.lookup (σ n) with
       | some v₁, some v₂ => ValueRefinesK k v₁ v₂
       | none, none => True
       | _, _ => False
  rw [hl₁, hl₂]
  exact hvrel v₁ v₂ h_v

/-- Helper: ShiftBisimValueList → ListRel ValueRefinesK, by structural
    recursion (since it's mutually inductive, direct induction fails). -/
private theorem shiftBisimValueList_to_listRel_valueRefinesK
    (hvrel : ∀ (v₁ v₂ : CekValue), ShiftBisimValue v₁ v₂ → ValueRefinesK k v₁ v₂) :
    ∀ {xs ys : List CekValue}, ShiftBisimValueList xs ys →
      ListRel (ValueRefinesK k) xs ys
  | [], _, h => by cases h; exact True.intro
  | _ :: _, _, h => by
    cases h with
    | cons hv hrest =>
      exact ⟨hvrel _ _ hv, shiftBisimValueList_to_listRel_valueRefinesK hvrel hrest⟩

/-- `ShiftBisimValue v₁ v₂` implies `ValueRefinesK k v₁ v₂` for all k. -/
theorem shiftBisimValue_to_valueRefinesK :
    ∀ (k : Nat) (v₁ v₂ : CekValue), ShiftBisimValue v₁ v₂ → ValueRefinesK k v₁ v₂ := by
  intro k
  induction k with
  | zero =>
    intro v₁ v₂ h
    cases h with
    | vcon c => simp only [ValueRefinesK]
    | vlam _ _ _ => simp only [ValueRefinesK]
    | vdelay _ _ _ => simp only [ValueRefinesK]
    | vconstr tag _ => simp only [ValueRefinesK]
    | vbuiltin b ea _ => simp only [ValueRefinesK]; exact ⟨trivial, trivial⟩
  | succ k ih =>
    -- ih at index k → use valueRefinesK_mono to get any j ≤ k.
    have ih_mono : ∀ (j : Nat), j ≤ k → ∀ (v₁ v₂ : CekValue),
        ShiftBisimValue v₁ v₂ → ValueRefinesK j v₁ v₂ := by
      intro j hj v₁ v₂ h
      exact valueRefinesK_mono hj v₁ v₂ (ih v₁ v₂ h)
    intro v₁ v₂ h
    cases h with
    | vcon c => simp only [ValueRefinesK]
    | @vlam body ρ₁ ρ₂ σ d h_σ hρ hclosed =>
      simp only [ValueRefinesK]
      intro j hj arg₁ arg₂ harg i hi π₁ π₂ hπ
      have henv_ext : Moist.Verified.FundamentalRefines.RenameEnvRefR
          (Moist.Verified.liftRename σ) j (d + 1) (ρ₁.extend arg₁) (ρ₂.extend arg₂) :=
        Moist.Verified.FundamentalRefines.renameEnvRefR_extend h_σ
          (shiftBisimEnv_to_renameEnvRefR_at j (ih_mono j hj) hρ) harg
      exact renameRefinesR (Moist.Verified.liftRename σ) (is0preserving_lift σ) (d + 1)
        body hclosed j j (Nat.le_refl _) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
        henv_ext i hi π₁ π₂ hπ
    | @vdelay body ρ₁ ρ₂ σ d h_σ hρ hclosed =>
      simp only [ValueRefinesK]
      intro j hj i hi π₁ π₂ hπ
      exact renameRefinesR σ h_σ d body hclosed j j (Nat.le_refl _) ρ₁ ρ₂
        (shiftBisimEnv_to_renameEnvRefR_at j (ih_mono j hj) hρ) i hi π₁ π₂ hπ
    | @vconstr tag fs₁ fs₂ h_fs =>
      simp only [ValueRefinesK]
      exact ⟨trivial, shiftBisimValueList_to_listRel_valueRefinesK ih h_fs⟩
    | @vbuiltin b ea args₁ args₂ h_args =>
      simp only [ValueRefinesK]
      exact ⟨trivial, trivial, shiftBisimValueList_to_listRel_valueRefinesK ih h_args⟩

end ShiftBisimValueRefines

end Moist.Verified.BetaValueRefines
