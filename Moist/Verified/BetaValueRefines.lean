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

/-- Apply `SubstEnvRef` at `n < pos`: lookups on both sides give
    `ValueRefinesK`-related values. -/
theorem substEnvRef_below_pos {pos k d : Nat} {v_rhs : CekValue}
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

/-- Apply `SubstEnvRef` at `n > pos`: lookups give `ValueRefinesK`-related
    values at positions `n` on LHS and `n - 1` on RHS. -/
theorem substEnvRef_above_pos {pos k d : Nat} {v_rhs : CekValue}
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
-- 16c. Environment decomposition for `EnvWellFormed (d + 1)`.
--
-- A well-formed env at positive depth `d + 1` must have cons-structure
-- `.cons v rest`, with `v` well-formed and `rest` well-formed at depth `d`.
-- This decomposition is the foundation of the shift-lifting proof: given
-- a well-formed `ρ_full` at depth `d + 1`, we extract `v0` and `ρ_tail`
-- with `ρ_full = ρ_tail.extend v0`.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 16d. Step-composition helpers for halt-witness extraction.
--
-- Bridge `.ret [] v` halt traces (produced by `RHaltsRel` at π = []) to the
-- `.halt v` form consumed by `ObsRefinesK`'s halt clause: stepping a
-- `.ret [] v` state produces `.halt v`.
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- 16f. `ValueRefinesK` inversions for constant witnesses.
--
-- When `v_rhs = .VCon c`, `ValueRefinesK k v_rhs v'` forces `v' = .VCon c`
-- at every step index. This makes the VCon case of `ValueShiftsPreserve`
-- reducible to a shape identification on the RHS halt value.
--------------------------------------------------------------------------------

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

/-! ## Basic unfolding lemmas -/

/-! ## Lookup: shifting an env commutes with lookup at shifted positions -/

/-! ## `shiftValueList` structural lemmas -/

/-! ## `extractConsts` preservation under shift -/

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

/-! ## `fields.map Frame.applyArg ++ rest` case-rewriting -/

/-! ## Projection helpers on `shiftState` -/

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

end ShiftBisimValueRefines

--------------------------------------------------------------------------------
-- 19g. ShiftBisim reflexivity at identity σ on well-formed structures.
--------------------------------------------------------------------------------

section ShiftBisimRefl
open Moist.Verified.FundamentalRefines (is0preserving_id)

mutual

theorem shiftBisimValue_refl_id_aux : ∀ {v : CekValue}
    (h : ValueWellFormed v), ShiftBisimValue v v
  | _, .vcon c => ShiftBisimValue.vcon c
  | _, .vlam (body := body) (ρ := ρ) (k := k) hρ hlen hc => by
    have hρrefl : ShiftBisimEnv id k ρ ρ := shiftBisimEnv_refl_id_aux hρ
    have h_result := ShiftBisimValue.vlam is0preserving_id hρrefl hc
    have h_eq : Moist.Verified.renameTerm (Moist.Verified.liftRename id) body = body := by
      rw [Moist.Verified.liftRename_id]; exact Moist.Verified.renameTerm_id body
    rw [h_eq] at h_result
    exact h_result
  | _, .vdelay (body := body) (ρ := ρ) (k := k) hρ hlen hc => by
    have hρrefl : ShiftBisimEnv id k ρ ρ := shiftBisimEnv_refl_id_aux hρ
    have h_result := ShiftBisimValue.vdelay is0preserving_id hρrefl hc
    have h_eq : Moist.Verified.renameTerm id body = body := Moist.Verified.renameTerm_id body
    rw [h_eq] at h_result
    exact h_result
  | _, .vconstr tag hfs =>
    ShiftBisimValue.vconstr tag (shiftBisimValueList_refl_id_aux hfs)
  | _, .vbuiltin b ea hargs =>
    ShiftBisimValue.vbuiltin b ea (shiftBisimValueList_refl_id_aux hargs)

theorem shiftBisimValueList_refl_id_aux : ∀ {vs : List CekValue}
    (h : ValueListWellFormed vs), ShiftBisimValueList vs vs
  | _, .nil => ShiftBisimValueList.nil
  | _, .cons hv hrest =>
    ShiftBisimValueList.cons (shiftBisimValue_refl_id_aux hv)
      (shiftBisimValueList_refl_id_aux hrest)

theorem shiftBisimEnv_refl_id_aux : ∀ {d : Nat} {ρ : CekEnv}
    (h : EnvWellFormed d ρ), ShiftBisimEnv id d ρ ρ
  | _, _, .zero => ShiftBisimEnv.zero
  | _, _, .succ hrest hlen hlookup hvwf =>
    ShiftBisimEnv.succ (shiftBisimEnv_refl_id_aux hrest)
      hlookup hlookup (shiftBisimValue_refl_id_aux hvwf)

end

/-- Public alias. -/
theorem shiftBisimValue_refl_id : ∀ (v : CekValue),
    ValueWellFormed v → ShiftBisimValue v v := fun _ h => shiftBisimValue_refl_id_aux h

end ShiftBisimRefl

--------------------------------------------------------------------------------
-- 19j. `valueRefinesK_trans_shiftBisim`: compose ValueRefinesK with ShiftBisim.
--------------------------------------------------------------------------------

private theorem renameEnvRefR_of_shiftBisimEnv_wf
    {σ : Nat → Nat} {j d : Nat} {ρ₁ ρ₂ : CekEnv}
    (conv : ∀ v₁ v₂, ValueWellFormed v₁ → ShiftBisimValue v₁ v₂ →
        Contextual.SoundnessRefines.ValueRefinesK j v₁ v₂)
    (hbisim : ShiftBisimEnv σ d ρ₁ ρ₂)
    (hwf_at : ∀ n, 0 < n → n ≤ d → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v) :
    FundamentalRefines.RenameEnvRefR σ j d ρ₁ ρ₂ := by
  induction d with
  | zero => intro n hn; omega
  | succ n ih =>
    cases hbisim with
    | @succ _ _ _ _ v₁ v₂ hrest hl₁ hl₂ hbv =>
      intro m hm hmd
      by_cases hm_eq : m = n + 1
      · subst hm_eq
        show match ρ₁.lookup (n + 1), ρ₂.lookup (σ (n + 1)) with
             | some _, some _ => _ | none, none => True | _, _ => False
        rw [hl₁, hl₂]
        exact conv v₁ v₂ (hwf_at (n + 1) (by omega) (Nat.le_refl _) v₁ hl₁) hbv
      · exact ih hrest (fun m' hm' hmd' v hv => hwf_at m' hm' (by omega) v hv) m hm (by omega)

private theorem listRelVRK_of_shiftBisim_wf_aux (k : Nat)
    (conv : ∀ v₁ v₂, ValueWellFormed v₁ → ShiftBisimValue v₁ v₂ →
        Contextual.SoundnessRefines.ValueRefinesK k v₁ v₂) :
    ∀ (vs₁ vs₂ : List CekValue),
    ValueListWellFormed vs₁ → ShiftBisimValueList vs₁ vs₂ →
    Equivalence.ListRel (Contextual.SoundnessRefines.ValueRefinesK k) vs₁ vs₂
  | [], [], _, .nil => trivial
  | _ :: _, _ :: _, hwf, .cons hv hvs => by
    cases hwf with | cons hv_wf hvs_wf =>
    exact ⟨conv _ _ hv_wf hv,
           listRelVRK_of_shiftBisim_wf_aux k conv _ _ hvs_wf hvs⟩

theorem valueRefinesK_of_shiftBisim_wf : ∀ (k : Nat) (v₁ v₂ : CekValue),
    ValueWellFormed v₁ → ShiftBisimValue v₁ v₂ →
    Contextual.SoundnessRefines.ValueRefinesK k v₁ v₂ := by
  intro k
  induction k with
  | zero =>
    intro v₁ v₂ _hwf hbisim
    cases hbisim with
    | vcon => simp [Contextual.SoundnessRefines.ValueRefinesK]
    | vlam _ _ _ => simp [Contextual.SoundnessRefines.ValueRefinesK]
    | vdelay _ _ _ => simp [Contextual.SoundnessRefines.ValueRefinesK]
    | vconstr _ _ => simp [Contextual.SoundnessRefines.ValueRefinesK]
    | vbuiltin _ _ _ => simp [Contextual.SoundnessRefines.ValueRefinesK]
  | succ k ih =>
    intro v₁ v₂ hwf hbisim
    cases hbisim with
    | vcon => simp [Contextual.SoundnessRefines.ValueRefinesK]
    | @vconstr tag fs₁ fs₂ hfs =>
      cases hwf with | vconstr _ hwf_fs =>
      simp only [Contextual.SoundnessRefines.ValueRefinesK]
      exact ⟨trivial, listRelVRK_of_shiftBisim_wf_aux k ih fs₁ fs₂ hwf_fs hfs⟩
    | @vbuiltin b ea args₁ args₂ hargs =>
      cases hwf with | vbuiltin _ _ hwf_args =>
      simp only [Contextual.SoundnessRefines.ValueRefinesK]
      exact ⟨trivial, trivial, listRelVRK_of_shiftBisim_wf_aux k ih args₁ args₂ hwf_args hargs⟩
    | @vlam body ρ₁ ρ₂ σ d hσ henv_bisim hclosed =>
      cases hwf with | @vlam _ _ d_wf henv_wf hlen hclosed_wf =>
      simp only [Contextual.SoundnessRefines.ValueRefinesK]
      intro j hj arg₁ arg₂ hargs i hi π₁ π₂ hπ
      by_cases hle : d ≤ d_wf
      · have hwf_at : ∀ n, 0 < n → n ≤ d → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
          fun n hn hnd v hv => by
            obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn (by omega)
            rw [hv] at hv'; cases hv'; exact hvwf'
        have henvR_k := renameEnvRefR_of_shiftBisimEnv_wf ih henv_bisim hwf_at
        have henvR_ext := FundamentalRefines.renameEnvRefR_extend hσ
          (FundamentalRefines.renameEnvRefR_mono hj henvR_k) hargs
        exact FundamentalRefines.renameRefinesR _ (FundamentalRefines.is0preserving_lift _)
          _ body hclosed (k + 1) j (by omega) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
          henvR_ext i hi π₁ π₂ hπ
      · have hle' : d_wf ≤ d := by omega
        have henv_bisim' := shiftBisimEnv_narrow σ d henv_bisim hle'
        have hwf_at : ∀ n, 0 < n → n ≤ d_wf → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
          fun n hn hnd v hv => by
            obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn hnd
            rw [hv] at hv'; cases hv'; exact hvwf'
        have henvR_k := renameEnvRefR_of_shiftBisimEnv_wf ih henv_bisim' hwf_at
        have henvR_ext := FundamentalRefines.renameEnvRefR_extend hσ
          (FundamentalRefines.renameEnvRefR_mono hj henvR_k) hargs
        exact FundamentalRefines.renameRefinesR _ (FundamentalRefines.is0preserving_lift _)
          _ body hclosed_wf (k + 1) j (by omega) (ρ₁.extend arg₁) (ρ₂.extend arg₂)
          henvR_ext i hi π₁ π₂ hπ
    | @vdelay body ρ₁ ρ₂ σ d hσ henv_bisim hclosed =>
      cases hwf with | @vdelay _ _ d_wf henv_wf hlen hclosed_wf =>
      simp only [Contextual.SoundnessRefines.ValueRefinesK]
      intro j hj i hi π₁ π₂ hπ
      by_cases hle : d ≤ d_wf
      · have hwf_at : ∀ n, 0 < n → n ≤ d → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
          fun n hn hnd v hv => by
            obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn (by omega)
            rw [hv] at hv'; cases hv'; exact hvwf'
        have henvR_k := renameEnvRefR_of_shiftBisimEnv_wf ih henv_bisim hwf_at
        exact FundamentalRefines.renameRefinesR _ hσ _ body hclosed (k + 1) j (by omega)
          ρ₁ ρ₂ (FundamentalRefines.renameEnvRefR_mono hj henvR_k) i hi π₁ π₂ hπ
      · have hle' : d_wf ≤ d := by omega
        have henv_bisim' := shiftBisimEnv_narrow σ d henv_bisim hle'
        have hwf_at : ∀ n, 0 < n → n ≤ d_wf → ∀ v, ρ₁.lookup n = some v → ValueWellFormed v :=
          fun n hn hnd v hv => by
            obtain ⟨v', hv', hvwf'⟩ := envWellFormed_lookup d_wf henv_wf hn hnd
            rw [hv] at hv'; cases hv'; exact hvwf'
        have henvR_k := renameEnvRefR_of_shiftBisimEnv_wf ih henv_bisim' hwf_at
        exact FundamentalRefines.renameRefinesR _ hσ _ body hclosed_wf (k + 1) j (by omega)
          ρ₁ ρ₂ (FundamentalRefines.renameEnvRefR_mono hj henvR_k) i hi π₁ π₂ hπ

end Moist.Verified.BetaValueRefines
