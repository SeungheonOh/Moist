import Moist.Verified.Definitions.StepIndexed
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Contextual
import Moist.Verified.ClosedAt
import Moist.Verified.RenameBase
import Moist.Verified.StepLift
import Moist.Verified.FundamentalRefines

/-! # Substitution Bisimulation

This module defines a semantic bisimulation capturing the UPLC β-substitution
refinement:

    `Apply (Lam 0 body) rhs  ≈  substTerm 1 rhs body`

when `rhs` evaluates to `v_repl` in the outer env. The bisim relates two
CEK states that differ by "eliminating a binder via substitution": the LHS
has an extra env position holding `v_repl`, the RHS has that position
removed and `substTerm` applied to the term.

Design mirrors `Moist.Verified.BetaValueRefines.lean`'s `ShiftBisim` but
encodes the **inverse** transformation (remove binder vs. add binder).

Helper lemmas (`closedAt_rename`, `extend_lookup_*`, well-formedness
predicates) are duplicated inline rather than imported from BetaValueRefines.

## Structure

1. Inline helper lemmas (copied from BetaValueRefines).
2. Well-formedness predicates (copied).
3. `SubstBisim{State,Env,Value,ValueList,Stack,Frame}` mutual inductive.
4. Helper lemmas (`substBisimEnv_lookup`, `substBisimEnv_extend`, inversions).
5. evalBuiltin compatibility (copied pattern).
6. `substBisimState_step_preserves` — the main bisim theorem.
7. Iterated step preservation + halt/error/ret inversions.
8. `substBisimState_to_obsRefines` — lifting to non-step-indexed ObsRefines.
9. `substBisim_to_ctxRefines` — wrapping in contexts for CtxRefines.
-/

namespace Moist.Verified.SubstBisim

open Moist.CEK
open Moist.Plutus.Term
open Moist.Verified
open Moist.Verified.Equivalence
open Moist.Verified.Contextual
open Moist.Verified.Contextual.SoundnessRefines

--------------------------------------------------------------------------------
-- 1. Copied helper lemmas (from BetaValueRefines.lean / FundamentalRefines.lean)
--------------------------------------------------------------------------------

/-- The unused position 0 always returns `none`. -/
private theorem lookup_zero (ρ : CekEnv) : ρ.lookup 0 = none := by
  match ρ with
  | .nil => rfl
  | .cons _ _ => rfl

/-- The new top of an `extend`ed env at position 1. -/
private theorem extend_lookup_one (ρ : CekEnv) (v : CekValue) :
    (ρ.extend v).lookup 1 = some v := by
  show (CekEnv.cons v ρ).lookup 1 = some v
  rfl

/-- `extend` shifts every positive position up by 1. -/
private theorem extend_lookup_succ (ρ : CekEnv) (v : CekValue) (m : Nat)
    (hm : m ≥ 1) :
    (ρ.extend v).lookup (m + 1) = ρ.lookup m := by
  show (CekEnv.cons v ρ).lookup (m + 1) = ρ.lookup m
  match m, hm with
  | k + 1, _ => rfl

--------------------------------------------------------------------------------
-- 2. Well-formedness predicates (copied from BetaValueRefines.lean section 7)
--------------------------------------------------------------------------------

mutual

/-- A CEK value is well-formed when every embedded closure is closed
    at the appropriate depth and its captured env is well-formed. -/
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

inductive EnvWellFormed : Nat → CekEnv → Prop
  | zero : ∀ {ρ : CekEnv}, EnvWellFormed 0 ρ
  | succ : ∀ {k : Nat} {ρ : CekEnv} {v : CekValue},
      EnvWellFormed k ρ →
      k + 1 ≤ ρ.length →
      ρ.lookup (k + 1) = some v →
      ValueWellFormed v →
      EnvWellFormed (k + 1) ρ

inductive ValueListWellFormed : List CekValue → Prop
  | nil : ValueListWellFormed []
  | cons : ∀ {v : CekValue} {vs : List CekValue},
      ValueWellFormed v → ValueListWellFormed vs →
      ValueListWellFormed (v :: vs)

end

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

inductive StackWellFormed : Stack → Prop
  | nil : StackWellFormed []
  | cons : ∀ {f : Frame} {π : Stack},
      FrameWellFormed f → StackWellFormed π →
      StackWellFormed (f :: π)

--------------------------------------------------------------------------------
-- 3. SubstBisim mutual inductive
--
-- Key intuition: the LHS state has an extra binder at some position `pos`
-- whose value is v_repl (the CekValue cached from evaluating `replacement`
-- in the outer env). The RHS has that position removed, and the term has
-- `substTerm pos replacement` applied.
--
-- Under binders (VLam case), pos increments (to pos+1, shifting to skip
-- the new binder) and replacement gets shifted via `shiftRename 1`. The
-- cached v_repl stays the same (since it's the value in the outermost env).
--------------------------------------------------------------------------------

mutual

inductive SubstBisimState : State → State → Prop
  | compute : ∀ {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {t : Term} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      closedAt (d + 1) t = true →
      SubstBisimStack π₁ π₂ →
      SubstBisimState
        (.compute π₁ ρ₁ t)
        (.compute π₂ ρ₂ (Moist.Verified.substTerm pos replacement t))
  | ret : ∀ {π₁ π₂ : Stack} {v₁ v₂ : CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimStack π₁ π₂ →
      SubstBisimState (.ret π₁ v₁) (.ret π₂ v₂)
  | halt : ∀ {v₁ v₂ : CekValue}, SubstBisimValue v₁ v₂ →
      SubstBisimState (.halt v₁) (.halt v₂)
  | error : SubstBisimState .error .error

/-- Env relation: ρ₁ has v_repl at position pos; ρ₂ is ρ₁ with pos removed.
    - At n < pos: ρ₁.lookup n and ρ₂.lookup n are SubstBisimValue-related.
    - At n = pos: ρ₁.lookup n is v_repl (literal equality).
    - At n > pos: ρ₁.lookup n and ρ₂.lookup (n-1) are SubstBisimValue-related. -/
inductive SubstBisimEnv : Nat → Term → CekValue → Nat → CekEnv → CekEnv → Prop
  | zero : ∀ {pos replacement v_repl ρ₁ ρ₂},
      SubstBisimEnv pos replacement v_repl 0 ρ₁ ρ₂
  | succ_below : ∀ {pos replacement v_repl d ρ₁ ρ₂ v₁ v₂},
      -- extending at position d+1 where d+1 < pos
      d + 1 < pos →
      SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
      ρ₁.lookup (d + 1) = some v₁ →
      ρ₂.lookup (d + 1) = some v₂ →
      SubstBisimValue v₁ v₂ →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂
  | succ_at : ∀ {pos replacement v_repl d ρ₁ ρ₂},
      -- extending at position d+1 = pos (the substitution position)
      d + 1 = pos →
      SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
      ρ₁.lookup (d + 1) = some v_repl →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂
  | succ_above : ∀ {pos replacement v_repl d ρ₁ ρ₂ v₁ v₂},
      -- extending at position d+1 > pos
      d + 1 > pos →
      SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
      ρ₁.lookup (d + 1) = some v₁ →
      ρ₂.lookup ((d + 1) - 1) = some v₂ →
      SubstBisimValue v₁ v₂ →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂

inductive SubstBisimValue : CekValue → CekValue → Prop
  | vcon : ∀ (c : Const), SubstBisimValue (.VCon c) (.VCon c)
  | vlam : ∀ {body : Term} {ρ₁ ρ₂ : CekEnv} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      closedAt (d + 2) body = true →
      SubstBisimValue
        (.VLam body ρ₁)
        (.VLam (Moist.Verified.substTerm (pos + 1)
          (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) replacement) body) ρ₂)
  | vdelay : ∀ {body : Term} {ρ₁ ρ₂ : CekEnv} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      closedAt (d + 1) body = true →
      SubstBisimValue
        (.VDelay body ρ₁)
        (.VDelay (Moist.Verified.substTerm pos replacement body) ρ₂)
  | vconstr : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue},
      SubstBisimValueList fs₁ fs₂ →
      SubstBisimValue (.VConstr tag fs₁) (.VConstr tag fs₂)
  | vbuiltin : ∀ (b : BuiltinFun) (ea : ExpectedArgs) {args₁ args₂ : List CekValue},
      SubstBisimValueList args₁ args₂ →
      SubstBisimValue (.VBuiltin b args₁ ea) (.VBuiltin b args₂ ea)

inductive SubstBisimValueList : List CekValue → List CekValue → Prop
  | nil : SubstBisimValueList [] []
  | cons : ∀ {v₁ v₂ : CekValue} {vs₁ vs₂ : List CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimValueList vs₁ vs₂ →
      SubstBisimValueList (v₁ :: vs₁) (v₂ :: vs₂)

inductive SubstBisimStack : Stack → Stack → Prop
  | nil : SubstBisimStack [] []
  | cons : ∀ {f₁ f₂ : Frame} {π₁ π₂ : Stack},
      SubstBisimFrame f₁ f₂ → SubstBisimStack π₁ π₂ →
      SubstBisimStack (f₁ :: π₁) (f₂ :: π₂)

inductive SubstBisimFrame : Frame → Frame → Prop
  | force : SubstBisimFrame .force .force
  | arg : ∀ {t : Term} {ρ₁ ρ₂ : CekEnv} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      closedAt (d + 1) t = true →
      SubstBisimFrame
        (.arg t ρ₁)
        (.arg (Moist.Verified.substTerm pos replacement t) ρ₂)
  | funV : ∀ {v₁ v₂ : CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimFrame (.funV v₁) (.funV v₂)
  | applyArg : ∀ {v₁ v₂ : CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimFrame (.applyArg v₁) (.applyArg v₂)
  | constrField : ∀ (tag : Nat) {done₁ done₂ : List CekValue}
      {todo : List Term} {ρ₁ ρ₂ : CekEnv} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d replacement = true →
      SubstBisimValueList done₁ done₂ →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      closedAtList (d + 1) todo = true →
      SubstBisimFrame
        (.constrField tag done₁ todo ρ₁)
        (.constrField tag done₂ (Moist.Verified.substTermList pos replacement todo) ρ₂)
  | caseScrutinee : ∀ {alts : List Term} {ρ₁ ρ₂ : CekEnv} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos → pos ≤ d + 1 →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      closedAtList (d + 1) alts = true →
      SubstBisimFrame
        (.caseScrutinee alts ρ₁)
        (.caseScrutinee (Moist.Verified.substTermList pos replacement alts) ρ₂)
end

--------------------------------------------------------------------------------
-- 4. Inversion lemmas for SubstBisimValueList
--------------------------------------------------------------------------------

theorem substBisimValueList_nil_inv : ∀ {xs : List CekValue},
    SubstBisimValueList [] xs → xs = []
  | _, h => by cases h; rfl

theorem substBisimValueList_cons_inv : ∀ {v : CekValue} {vs xs : List CekValue},
    SubstBisimValueList (v :: vs) xs →
    ∃ w ws, xs = w :: ws ∧ SubstBisimValue v w ∧ SubstBisimValueList vs ws
  | _, _, _, h => by cases h with | cons hv hr => exact ⟨_, _, rfl, hv, hr⟩

theorem substBisimValueList_nil_inv_right : ∀ {xs : List CekValue},
    SubstBisimValueList xs [] → xs = []
  | [], _ => rfl
  | _ :: _, h => by cases h

theorem substBisimValueList_cons_inv_right : ∀ {w : CekValue} {ws xs : List CekValue},
    SubstBisimValueList xs (w :: ws) →
    ∃ v vs, xs = v :: vs ∧ SubstBisimValue v w ∧ SubstBisimValueList vs ws
  | _, _, [], h => by cases h
  | _, _, _ :: _, h => by cases h with | cons hv hr => exact ⟨_, _, rfl, hv, hr⟩

theorem substBisimValue_vcon_inv : ∀ {c : Const} {v : CekValue},
    SubstBisimValue (.VCon c) v → v = .VCon c
  | _, _, h => by cases h; rfl

theorem substBisimValue_vcon_inv_right : ∀ {c : Const} {v : CekValue},
    SubstBisimValue v (.VCon c) → v = .VCon c
  | _, _, h => by cases h; rfl

/-- Length preservation. -/
theorem substBisimValueList_length_eq : ∀ {xs₁ xs₂ : List CekValue},
    SubstBisimValueList xs₁ xs₂ → xs₁.length = xs₂.length
  | [], _, h => by cases h; rfl
  | _ :: _, _, h => by
    cases h with
    | cons _ hr => simp [substBisimValueList_length_eq hr]

--------------------------------------------------------------------------------
-- 5. SubstBisimEnv helpers (lookup + extend)
--------------------------------------------------------------------------------

/-- `SubstBisimEnv` always holds vacuously at depth 0. -/
theorem substBisimEnv_zero (pos : Nat) (replacement : Term) (v_repl : CekValue)
    (ρ₁ ρ₂ : CekEnv) :
    SubstBisimEnv pos replacement v_repl 0 ρ₁ ρ₂ := SubstBisimEnv.zero

/-- Lookup at `pos` (the substitution position): `ρ₁.lookup pos = some v_repl`. -/
theorem substBisimEnv_lookup_at :
    ∀ (pos : Nat) (replacement : Term) (v_repl : CekValue) (d : Nat)
      {ρ₁ ρ₂ : CekEnv},
    1 ≤ pos → pos ≤ d → SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
    ρ₁.lookup pos = some v_repl := by
  intro pos replacement v_repl d
  induction d with
  | zero => intros; omega
  | succ n ih =>
    intro ρ₁ ρ₂ hpos hnd h
    cases h with
    | succ_below h_lt h_rest _ _ _ =>
      exact ih hpos (by omega) h_rest
    | succ_at h_eq h_rest h_lookup =>
      have : pos = n + 1 := by omega
      subst this
      exact h_lookup
    | succ_above h_gt h_rest _ _ _ =>
      exact ih hpos (by omega) h_rest

/-- Lookup below pos: ρ₁.lookup n and ρ₂.lookup n are SubstBisim-related. -/
theorem substBisimEnv_lookup_below :
    ∀ (pos : Nat) (replacement : Term) (v_repl : CekValue) (d : Nat)
      {ρ₁ ρ₂ : CekEnv} {n : Nat},
    1 ≤ n → n ≤ d → n < pos → SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧
      SubstBisimValue v₁ v₂ := by
  intro pos replacement v_repl d
  induction d with
  | zero => intros; omega
  | succ d' ih =>
    intro ρ₁ ρ₂ n hn_pos hn_le hn_lt h
    cases h with
    | @succ_below _ _ _ _ _ _ v₁ v₂ h_lt h_rest h_l1 h_l2 h_v =>
      by_cases h_eq : n = d' + 1
      · subst h_eq
        exact ⟨v₁, v₂, h_l1, h_l2, h_v⟩
      · exact ih hn_pos (by omega) hn_lt h_rest
    | succ_at h_eq h_rest h_lookup =>
      exact ih hn_pos (by omega) hn_lt h_rest
    | succ_above h_gt h_rest _ _ _ =>
      by_cases h_eq : n = d' + 1
      · subst h_eq; omega
      · exact ih hn_pos (by omega) hn_lt h_rest

/-- Lookup above pos. -/
theorem substBisimEnv_lookup_above :
    ∀ (pos : Nat) (replacement : Term) (v_repl : CekValue) (d : Nat)
      {ρ₁ ρ₂ : CekEnv} {n : Nat},
    1 ≤ n → n ≤ d → n > pos → SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup (n - 1) = some v₂ ∧
      SubstBisimValue v₁ v₂ := by
  intro pos replacement v_repl d
  induction d with
  | zero => intros; omega
  | succ d' ih =>
    intro ρ₁ ρ₂ n hn_pos hn_le hn_gt h
    cases h with
    | succ_below h_lt h_rest _ _ _ =>
      by_cases h_eq : n = d' + 1
      · subst h_eq; omega
      · exact ih hn_pos (by omega) hn_gt h_rest
    | succ_at h_eq h_rest h_lookup =>
      by_cases h_eq' : n = d' + 1
      · subst h_eq'; omega
      · exact ih hn_pos (by omega) hn_gt h_rest
    | @succ_above _ _ _ _ _ _ v₁ v₂ h_gt h_rest h_l1 h_l2 h_v =>
      by_cases h_eq : n = d' + 1
      · subst h_eq
        exact ⟨v₁, v₂, h_l1, h_l2, h_v⟩
      · exact ih hn_pos (by omega) hn_gt h_rest

/-- Extending both sides of a SubstBisim-related env preserves the relation
    at the bumped depth, when the extensions are SubstBisim-related.
    Requires `pos ≥ 1` (SubstBisim always quantifies pos ≥ 1). -/
theorem substBisimEnv_extend :
    ∀ (pos : Nat) (hpos : 1 ≤ pos)
      (replacement : Term) (v_repl : CekValue) (d : Nat)
      {ρ₁ ρ₂ : CekEnv} {v₁ v₂ : CekValue},
    SubstBisimEnv pos replacement v_repl d ρ₁ ρ₂ →
    SubstBisimValue v₁ v₂ →
    SubstBisimEnv (pos + 1)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) replacement)
      v_repl (d + 1) (ρ₁.extend v₁) (ρ₂.extend v₂) := by
  intro pos hpos replacement v_repl d ρ₁ ρ₂ v₁ v₂ h hv
  induction d with
  | zero =>
    -- d = 0. Only need position 1 (the new extension). pos ≥ 1 → pos + 1 ≥ 2 > 1.
    have h_new_pos_lt : 1 < pos + 1 := by omega
    have h_rest : SubstBisimEnv (pos + 1)
        (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) replacement)
        v_repl 0 (ρ₁.extend v₁) (ρ₂.extend v₂) := SubstBisimEnv.zero
    exact SubstBisimEnv.succ_below h_new_pos_lt h_rest
      (extend_lookup_one ρ₁ v₁)
      (extend_lookup_one ρ₂ v₂) hv
  | succ d' ih =>
    cases h with
    | @succ_below _ _ _ _ _ _ v₁' v₂' h_lt h_rest h_l1 h_l2 h_v =>
      -- Position d'+1 < pos. In the extended env, position (d'+1)+1 = d'+2
      -- corresponds to position d'+1 of the old env. d'+2 < pos+1.
      have ih_rec := ih h_rest
      have h_new_lt : d' + 1 + 1 < pos + 1 := by omega
      -- Lookup at d'+2 in extended env = lookup at d'+1 in old env = v₁'/v₂'.
      refine SubstBisimEnv.succ_below h_new_lt ih_rec ?_ ?_ h_v
      · have : (ρ₁.extend v₁).lookup (d' + 1 + 1) = ρ₁.lookup (d' + 1) :=
          extend_lookup_succ ρ₁ v₁ (d' + 1) (by omega)
        rw [this]; exact h_l1
      · have : (ρ₂.extend v₂).lookup (d' + 1 + 1) = ρ₂.lookup (d' + 1) :=
          extend_lookup_succ ρ₂ v₂ (d' + 1) (by omega)
        rw [this]; exact h_l2
    | succ_at h_eq h_rest h_lookup =>
      -- Position d'+1 = pos. In extended env, position d'+2 is the original pos.
      have ih_rec := ih h_rest
      have h_new_eq : d' + 1 + 1 = pos + 1 := by omega
      refine SubstBisimEnv.succ_at h_new_eq ih_rec ?_
      have : (ρ₁.extend v₁).lookup (d' + 1 + 1) = ρ₁.lookup (d' + 1) :=
        extend_lookup_succ ρ₁ v₁ (d' + 1) (by omega)
      rw [this]; exact h_lookup
    | @succ_above _ _ _ _ _ _ v₁' v₂' h_gt h_rest h_l1 h_l2 h_v =>
      -- Position d'+1 > pos. In extended env, position d'+2 > pos+1.
      have ih_rec := ih h_rest
      have h_new_gt : d' + 1 + 1 > pos + 1 := by omega
      refine SubstBisimEnv.succ_above h_new_gt ih_rec ?_ ?_ h_v
      · have : (ρ₁.extend v₁).lookup (d' + 1 + 1) = ρ₁.lookup (d' + 1) :=
          extend_lookup_succ ρ₁ v₁ (d' + 1) (by omega)
        rw [this]; exact h_l1
      · -- Lookup at (d'+1+1) - 1 = d'+1 of (ρ₂.extend v₂).
        -- (ρ₂.extend v₂).lookup (d'+1) = ρ₂.lookup d' (for d' ≥ 1).
        -- We need this to equal ρ₂.lookup ((d'+1) - 1) = ρ₂.lookup d'. ✓
        have h_simp : (d' + 1 + 1 : Nat) - 1 = d' + 1 := by omega
        rw [h_simp]
        by_cases hd' : d' = 0
        · subst hd'
          -- h_gt : 0 + 1 > pos, so pos = 0. But pos ≥ 1 typically...
          -- Actually we don't constrain pos ≥ 1 in this lemma, but in the
          -- overall framework it holds. For d' = 0: (d'+1+1) - 1 = 1.
          -- (ρ₂.extend v₂).lookup 1 = v₂. We want this = ρ₂.lookup ((0+1)-1) = ρ₂.lookup 0.
          -- But lookup 0 is always none. Contradiction unless we handle d'=0 case.
          -- Actually h_l2 : ρ₂.lookup ((d'+1)-1) = some v₂' with d' = 0 means ρ₂.lookup 0 = some v₂'.
          -- This contradicts lookup_zero. So this branch is impossible for d' = 0.
          exfalso
          have : ρ₂.lookup 0 = none := lookup_zero ρ₂
          rw [show ((0 : Nat) + 1 - 1) = 0 from rfl] at h_l2
          rw [this] at h_l2
          exact Option.noConfusion h_l2
        · have : (ρ₂.extend v₂).lookup (d' + 1) = ρ₂.lookup d' :=
            extend_lookup_succ ρ₂ v₂ d' (by omega)
          rw [this]
          have h_l2_simp : (d' + 1 : Nat) - 1 = d' := by omega
          rw [h_l2_simp] at h_l2
          exact h_l2

--------------------------------------------------------------------------------
-- 6. List structural helpers + stack helpers
--------------------------------------------------------------------------------

theorem substBisimValueList_append : ∀ (xs₁ : List CekValue)
    {xs₂ ys₁ ys₂ : List CekValue},
    SubstBisimValueList xs₁ xs₂ → SubstBisimValueList ys₁ ys₂ →
    SubstBisimValueList (xs₁ ++ ys₁) (xs₂ ++ ys₂)
  | [], _, _, _, hxs, hys => by cases hxs; exact hys
  | _ :: rest, _, _, _, hxs, hys => by
    cases hxs with
    | cons hv hrest =>
      exact SubstBisimValueList.cons hv (substBisimValueList_append rest hrest hys)

theorem substBisimValueList_reverse : ∀ (xs₁ : List CekValue)
    {xs₂ : List CekValue},
    SubstBisimValueList xs₁ xs₂ → SubstBisimValueList xs₁.reverse xs₂.reverse
  | [], _, hxs => by cases hxs; exact SubstBisimValueList.nil
  | x :: rest, _, hxs => by
    cases hxs with
    | cons hv hrest =>
      simp only [List.reverse_cons]
      exact substBisimValueList_append _ (substBisimValueList_reverse rest hrest)
              (SubstBisimValueList.cons hv SubstBisimValueList.nil)

theorem substBisimValueList_to_applyArg_stack : ∀ (fs₁ : List CekValue)
    {fs₂ : List CekValue} {π₁ π₂ : Stack},
    SubstBisimValueList fs₁ fs₂ → SubstBisimStack π₁ π₂ →
    SubstBisimStack (fs₁.map Frame.applyArg ++ π₁) (fs₂.map Frame.applyArg ++ π₂)
  | [], _, _, _, hfs, hπ => by cases hfs; exact hπ
  | _ :: rest, _, _, _, hfs, hπ => by
    cases hfs with
    | cons hv hrest =>
      exact SubstBisimStack.cons (SubstBisimFrame.applyArg hv)
              (substBisimValueList_to_applyArg_stack rest hrest hπ)

theorem substBisim_closedAtList_get : ∀ (d : Nat) (alts : List Term)
    (n : Nat) (alt : Term),
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
    exact substBisim_closedAtList_get d rest n alt h_cl.2 h_get

--------------------------------------------------------------------------------
-- 7. extractConsts compatibility under SubstBisimValueList
--------------------------------------------------------------------------------

theorem substBisimValueList_extractConsts :
    ∀ (args₁ : List CekValue) {args₂ : List CekValue},
    SubstBisimValueList args₁ args₂ → extractConsts args₁ = extractConsts args₂ := by
  intro args₁
  induction args₁ with
  | nil =>
    intro args₂ h
    cases h
    rfl
  | cons v rest ih =>
    intro args₂ h
    obtain ⟨w, rest₂, heq, hv, hrest⟩ := substBisimValueList_cons_inv h
    subst heq
    cases hv with
    | vcon c =>
      simp only [extractConsts]
      rw [ih hrest]
    | vlam _ _ _ _ _ => rfl
    | vdelay _ _ _ _ _ => rfl
    | vconstr _ _ => rfl
    | vbuiltin _ _ _ => rfl

--------------------------------------------------------------------------------
-- 8. constToTagAndFields fields are SubstBisimValueList-reflexive
--
-- Since constToTagAndFields returns only VCon fields, they are trivially
-- related by SubstBisimValue.vcon reflexivity.
--------------------------------------------------------------------------------

theorem substBisimValueList_constToTagAndFields_refl :
    ∀ {c : Const} {tag numCtors : Nat} {fs : List CekValue},
      constToTagAndFields c = some (tag, numCtors, fs) → SubstBisimValueList fs fs := by
  intro c tag numCtors fs hc
  cases c with
  | Integer n =>
    simp only [constToTagAndFields] at hc
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc
      subst hfs
      exact SubstBisimValueList.nil
    · exact Option.noConfusion hc
  | ByteString _ => simp [constToTagAndFields] at hc
  | String _ => simp [constToTagAndFields] at hc
  | Unit =>
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc; subst hfs
    exact SubstBisimValueList.nil
  | Bool b =>
    cases b <;>
    · simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      exact SubstBisimValueList.nil
  | ConstList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      exact SubstBisimValueList.nil
    | cons head tail =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      exact SubstBisimValueList.cons (SubstBisimValue.vcon _)
              (SubstBisimValueList.cons (SubstBisimValue.vcon _) SubstBisimValueList.nil)
  | ConstDataList l =>
    cases l with
    | nil =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      exact SubstBisimValueList.nil
    | cons head tail =>
      simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨_, _, hfs⟩ := hc; subst hfs
      exact SubstBisimValueList.cons (SubstBisimValue.vcon _)
              (SubstBisimValueList.cons (SubstBisimValue.vcon _) SubstBisimValueList.nil)
  | ConstPairDataList _ => simp [constToTagAndFields] at hc
  | Pair p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc; subst hfs
    exact SubstBisimValueList.cons (SubstBisimValue.vcon _)
            (SubstBisimValueList.cons (SubstBisimValue.vcon _) SubstBisimValueList.nil)
  | PairData p =>
    obtain ⟨a, b⟩ := p
    simp only [constToTagAndFields, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨_, _, hfs⟩ := hc; subst hfs
    exact SubstBisimValueList.cons (SubstBisimValue.vcon _)
            (SubstBisimValueList.cons (SubstBisimValue.vcon _) SubstBisimValueList.nil)
  | Data _ => simp [constToTagAndFields] at hc
  | ConstArray _ => simp [constToTagAndFields] at hc
  | Bls12_381_G1_element => simp [constToTagAndFields] at hc
  | Bls12_381_G2_element => simp [constToTagAndFields] at hc
  | Bls12_381_MlResult => simp [constToTagAndFields] at hc


--------------------------------------------------------------------------------
-- 9. evalBuiltin compatibility under SubstBisimValueList
--   (adapted from BetaValueRefines via find-replace of relation names)
--------------------------------------------------------------------------------

/-- For a pass-through builtin, if LHS succeeds with `some v₁`, then RHS
    succeeds with `some v₂` where `SubstBisimValue v₁ v₂`. -/
theorem substBisimValueList_evalBuiltinPassThrough_some : ∀ (b : BuiltinFun) {args₁ args₂ : List CekValue},
    SubstBisimValueList args₁ args₂ →
    ∀ v₁, evalBuiltinPassThrough b args₁ = some v₁ →
      ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ SubstBisimValue v₁ v₂ := by
  intro b args₁ args₂ h v₁ hv₁
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    -- ==================== IfThenElse: [e, t, .VCon (.Bool cond)] ====================
    · match args₁, h, hv₁ with
      | [e₁, t₁, .VCon (.Bool cond)], h_args, hv₁ =>
        obtain ⟨e₂, _, he₁, h_e, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨t₂, _, he₂, h_t, hr'⟩ := substBisimValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := substBisimValueList_cons_inv hr'
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases substBisimValue_vcon_inv h_w
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
        obtain ⟨r₂, _, he₁, h_r, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := substBisimValueList_cons_inv hr
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases substBisimValue_vcon_inv h_w
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
        obtain ⟨r₂, _, he₁, h_r, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := substBisimValueList_cons_inv hr
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases substBisimValue_vcon_inv h_w
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
        obtain ⟨b₂, _, he₁, h_b, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨i₂, _, he₂, h_i, hr₂⟩ := substBisimValueList_cons_inv hr
        obtain ⟨l₂, _, he₃, h_l, hr₃⟩ := substBisimValueList_cons_inv hr₂
        obtain ⟨m₂, _, he₄, h_m, hr₄⟩ := substBisimValueList_cons_inv hr₃
        obtain ⟨cr₂, _, he₅, h_cr, hr₅⟩ := substBisimValueList_cons_inv hr₄
        obtain ⟨w, _, he₆, h_w, hrn⟩ := substBisimValueList_cons_inv hr₅
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃ he₄ he₅ he₆
        cases substBisimValue_vcon_inv h_w
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
        obtain ⟨c₂, _, he₁, h_c, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨n₂, _, he₂, h_n, hr'⟩ := substBisimValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := substBisimValueList_cons_inv hr'
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases substBisimValue_vcon_inv h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        refine ⟨if l.isEmpty then n₂ else c₂, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [c₁, n₁, .VCon (.ConstList l)], h_args, hv₁ =>
        obtain ⟨c₂, _, he₁, h_c, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨n₂, _, he₂, h_n, hr'⟩ := substBisimValueList_cons_inv hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := substBisimValueList_cons_inv hr'
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂ he₃
        cases substBisimValue_vcon_inv h_w
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
        obtain ⟨w₁, _, he₁, h_w₁, hr⟩ := substBisimValueList_cons_inv h_args
        obtain ⟨w₂, _, he₂, h_w₂, hrn⟩ := substBisimValueList_cons_inv hr
        have hnil := substBisimValueList_nil_inv hrn
        subst hnil he₁ he₂
        cases substBisimValue_vcon_inv h_w₁
        cases substBisimValue_vcon_inv h_w₂
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₁
        subst hv₁
        exact ⟨.VCon (.ConstList (c :: tail)), rfl, SubstBisimValue.vcon _⟩
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
theorem substBisimValueList_evalBuiltinPassThrough_some_rev : ∀ (b : BuiltinFun) {args₁ args₂ : List CekValue},
    SubstBisimValueList args₁ args₂ →
    ∀ v₂, evalBuiltinPassThrough b args₂ = some v₂ →
      ∃ v₁, evalBuiltinPassThrough b args₁ = some v₁ ∧ SubstBisimValue v₁ v₂ := by
  intro b args₁ args₂ h v₂ hv₂
  by_cases hb : b = .IfThenElse ∨ b = .ChooseUnit ∨ b = .Trace ∨
                b = .ChooseData ∨ b = .ChooseList ∨ b = .MkCons
  · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    -- IfThenElse
    · match args₂, h, hv₂ with
      | [e₂, t₂, .VCon (.Bool cond)], h_args, hv₂ =>
        obtain ⟨e₁, _, he₁, h_e, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨t₁, _, he₂, h_t, hr'⟩ := substBisimValueList_cons_inv_right hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := substBisimValueList_cons_inv_right hr'
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃
        cases substBisimValue_vcon_inv_right h_w
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
        obtain ⟨r₁, _, he₁, h_r, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := substBisimValueList_cons_inv_right hr
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂
        cases substBisimValue_vcon_inv_right h_w
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
        obtain ⟨r₁, _, he₁, h_r, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨w, _, he₂, h_w, hrn⟩ := substBisimValueList_cons_inv_right hr
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂
        cases substBisimValue_vcon_inv_right h_w
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
        obtain ⟨b₁, _, he₁, h_b, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨i₁, _, he₂, h_i, hr₂⟩ := substBisimValueList_cons_inv_right hr
        obtain ⟨l₁, _, he₃, h_l, hr₃⟩ := substBisimValueList_cons_inv_right hr₂
        obtain ⟨m₁, _, he₄, h_m, hr₄⟩ := substBisimValueList_cons_inv_right hr₃
        obtain ⟨cr₁, _, he₅, h_cr, hr₅⟩ := substBisimValueList_cons_inv_right hr₄
        obtain ⟨w, _, he₆, h_w, hrn⟩ := substBisimValueList_cons_inv_right hr₅
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃ he₄ he₅ he₆
        cases substBisimValue_vcon_inv_right h_w
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
        obtain ⟨c₁, _, he₁, h_c, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨n₁, _, he₂, h_n, hr'⟩ := substBisimValueList_cons_inv_right hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := substBisimValueList_cons_inv_right hr'
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃
        cases substBisimValue_vcon_inv_right h_w
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        refine ⟨if l.isEmpty then n₁ else c₁, rfl, ?_⟩
        by_cases hl : l.isEmpty
        · simp [hl]; exact h_n
        · simp [hl]; exact h_c
      | [c₂, n₂, .VCon (.ConstList l)], h_args, hv₂ =>
        obtain ⟨c₁, _, he₁, h_c, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨n₁, _, he₂, h_n, hr'⟩ := substBisimValueList_cons_inv_right hr
        obtain ⟨w, _, he₃, h_w, hrn⟩ := substBisimValueList_cons_inv_right hr'
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂ he₃
        cases substBisimValue_vcon_inv_right h_w
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
        obtain ⟨w₁, _, he₁, h_w₁, hr⟩ := substBisimValueList_cons_inv_right h_args
        obtain ⟨w₂, _, he₂, h_w₂, hrn⟩ := substBisimValueList_cons_inv_right hr
        have hnil := substBisimValueList_nil_inv_right hrn
        subst hnil he₁ he₂
        cases substBisimValue_vcon_inv_right h_w₁
        cases substBisimValue_vcon_inv_right h_w₂
        simp only [evalBuiltinPassThrough, Option.some.injEq] at hv₂
        subst hv₂
        exact ⟨.VCon (.ConstList (c :: tail)), rfl, SubstBisimValue.vcon _⟩
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
theorem substBisimValueList_evalBuiltinPassThrough (b : BuiltinFun)
    {args₁ args₂ : List CekValue} (h : SubstBisimValueList args₁ args₂) :
    (∀ v₁, evalBuiltinPassThrough b args₁ = some v₁ →
      ∃ v₂, evalBuiltinPassThrough b args₂ = some v₂ ∧ SubstBisimValue v₁ v₂) ∧
    (evalBuiltinPassThrough b args₁ = none ↔ evalBuiltinPassThrough b args₂ = none) := by
  refine ⟨substBisimValueList_evalBuiltinPassThrough_some b h, ?_, ?_⟩
  · intro hn
    cases heq : evalBuiltinPassThrough b args₂ with
    | none => rfl
    | some v₂ =>
      exfalso
      obtain ⟨v₁, hv₁, _⟩ :=
        substBisimValueList_evalBuiltinPassThrough_some_rev b h v₂ heq
      rw [hn] at hv₁
      exact Option.noConfusion hv₁
  · intro hn
    cases heq : evalBuiltinPassThrough b args₁ with
    | none => rfl
    | some v₁ =>
      exfalso
      obtain ⟨v₂, hv₂, _⟩ :=
        substBisimValueList_evalBuiltinPassThrough_some b h v₁ heq
      rw [hn] at hv₂
      exact Option.noConfusion hv₂

/-- Full evalBuiltin compat: bisim-preserves both Some (with related value)
    and None directions under SubstBisimValueList. -/
theorem shiftBisimValueList_evalBuiltin {b : BuiltinFun}
    {args₁ args₂ : List CekValue} (h : SubstBisimValueList args₁ args₂) :
    (∀ v₁, evalBuiltin b args₁ = some v₁ →
      ∃ v₂, evalBuiltin b args₂ = some v₂ ∧ SubstBisimValue v₁ v₂) ∧
    (evalBuiltin b args₁ = none ↔ evalBuiltin b args₂ = none) := by
  have h_ext : extractConsts args₁ = extractConsts args₂ :=
    substBisimValueList_extractConsts _ h
  obtain ⟨h_pt_some, h_pt_iff⟩ := substBisimValueList_evalBuiltinPassThrough b h
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
            exact SubstBisimValue.vcon c
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

--------------------------------------------------------------------------------
-- 10. Step + halt/error preservation theorems
--
-- Unlike ShiftBisim (which is a strong bisim with 1-1 step matching),
-- SubstBisim is a weak bisim: the Var=pos case has LHS taking 1 step
-- (lookup → ret) while RHS takes multiple steps (evaluate replacement).
--
-- We state the key property at the ObsRefines level directly, bypassing
-- a step_preserves theorem (which would be awkward with asymmetric steps).
--------------------------------------------------------------------------------

/-- `steps_trans`: stepping `m + n` equals stepping `n` after stepping `m`. -/
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

/-- `error` is a fixed point of `step`. -/
theorem steps_error_fixed : ∀ (n : Nat), steps n (.error : State) = .error
  | 0 => rfl
  | n + 1 => by simp only [steps, step]; exact steps_error_fixed n

--------------------------------------------------------------------------------
-- 11. Key direct ObsRefines lemma for SubstBisimState
--
-- The DIRECT "bisim → ObsRefines" theorem. Proven by case-analysis on the
-- state structure, exploiting:
--   - The Var=pos case where LHS takes 1 step but RHS multi-steps through
--     the replacement term's evaluation.
--   - All other compute cases where step counts match.
--   - Ret/halt/error cases which preserve directly.
--
-- The full proof is an ~400-line case analysis mirroring CEK semantics.
-- For now, state the theorem and provide the structural framework.
--------------------------------------------------------------------------------

/-- The direct lifting from `SubstBisimState` to `ObsRefines`. This is the
    key theorem for interfacing SubstBisim with the contextual refinement
    framework. Proof structure:
      - LHS halts/errors ↔ RHS halts/errors (with matching halt values via
        `SubstBisimValue`).
      - Uses CEK step analysis + the evalBuiltin/constToTagAndFields compat
        lemmas for the fiddly cases.

    The Var=pos case is the crux: LHS evaluates var 1 → lookup → v_repl in
    one step, while RHS evaluates `replacement` → same v_repl in multiple
    steps. Both converge, so ObsRefines holds. -/
theorem substBisimState_to_obsRefines :
    ∀ {s₁ s₂ : State}, SubstBisimState s₁ s₂ → ObsRefines s₁ s₂ := by
  intro s₁ s₂ h
  -- Full proof requires ~400 lines of CEK case analysis mirroring
  -- step_preserves for shift bisim + additional admin-step reasoning
  -- for the Var=pos case (where replacement multi-steps to v_repl).
  --
  -- The halt case follows from:
  --   1. Reaches s₁ (halt v₁) = ∃ n, steps n s₁ = halt v₁.
  --   2. Bisim preservation through n steps (with possibly more steps on RHS).
  --   3. RHS reaches halt v₂ with SubstBisimValue v₁ v₂.
  --   4. In particular, ∃ v₂, Reaches s₂ (halt v₂).
  --
  -- The error case: similar, with error instead of halt.
  sorry

--------------------------------------------------------------------------------
-- 12. Reflexivity of SubstBisimValue at well-formed values
--
-- The identity case: a well-formed value is SubstBisimValue-related to
-- itself when pos is BEYOND the value's env depth (so the substitution
-- doesn't reach any of the value's captured variables).
--------------------------------------------------------------------------------

mutual

/-- Reflexivity of SubstBisimValue for well-formed values (no binding is
    actually substituted). Requires pos > captured-depth. -/
theorem substBisimValue_refl_wf_aux : ∀ {v : CekValue}
    (h : ValueWellFormed v), SubstBisimValue v v
  | _, .vcon c => SubstBisimValue.vcon c
  | _, .vconstr tag hfs =>
    SubstBisimValue.vconstr tag (substBisimValueList_refl_wf_aux hfs)
  | _, .vbuiltin b ea hargs =>
    SubstBisimValue.vbuiltin b ea (substBisimValueList_refl_wf_aux hargs)
  | _, .vlam _ _ _ => sorry  -- closure reflexivity: parallels shift's vlam
  | _, .vdelay _ _ _ => sorry  -- closure reflexivity

theorem substBisimValueList_refl_wf_aux : ∀ {vs : List CekValue}
    (h : ValueListWellFormed vs), SubstBisimValueList vs vs
  | _, .nil => SubstBisimValueList.nil
  | _, .cons hv hrest =>
    SubstBisimValueList.cons (substBisimValue_refl_wf_aux hv)
      (substBisimValueList_refl_wf_aux hrest)

end

/-- Public alias. -/
theorem substBisimValue_refl_wf (v : CekValue) :
    ValueWellFormed v → SubstBisimValue v v :=
  substBisimValue_refl_wf_aux

/-- Construct initial `SubstBisimEnv` for β-substitution: the outer env
    (ρ.extend v_rhs, ρ) is related at position 1 with replacement = rhs,
    depth d+1. -/
theorem substBisimEnv_initial (d : Nat) (rhs : Term) (v_rhs : CekValue)
    (ρ : CekEnv)
    (hrhs_closed : closedAt d rhs = true)
    (hρ_wf : EnvWellFormed d ρ) :
    SubstBisimEnv 1 rhs v_rhs (d + 1) (ρ.extend v_rhs) ρ := by
  -- Build by induction on d.
  -- For position 1 (the substitution position): succ_at — looks up v_rhs.
  -- For positions 2..d+1: succ_above — each relates to ρ via shift-down.
  --
  -- We construct in the order: zero, then succ_at at d=0→1, then succ_above at each
  -- subsequent depth.
  --
  -- Technically: we need to first establish `SubstBisimEnv 1 rhs v_rhs 0 (ρ.extend v_rhs) ρ`
  -- (trivially zero). Then extend to depth 1 via succ_at. Then extend up to d+1 via succ_above.
  have h_zero : SubstBisimEnv 1 rhs v_rhs 0 (ρ.extend v_rhs) ρ := SubstBisimEnv.zero
  have h_one : SubstBisimEnv 1 rhs v_rhs 1 (ρ.extend v_rhs) ρ := by
    refine SubstBisimEnv.succ_at rfl h_zero ?_
    exact extend_lookup_one ρ v_rhs
  -- Now extend from 1 to d+1 via induction. Each step adds succ_above.
  -- We induct on the "additional depth" remaining.
  let rec go : ∀ (k : Nat), k ≤ d →
      SubstBisimEnv 1 rhs v_rhs (k + 1) (ρ.extend v_rhs) ρ := fun k hk =>
    match k, hk with
    | 0, _ => h_one
    | n + 1, hle => by
      have hrec := go n (by omega)
      -- We need envWellFormed at d to provide the lookup at n+1.
      -- Use hρ_wf and narrow to n+1 (if n+1 ≤ d).
      have hn1 : n + 1 ≤ d := hle
      have : ∃ v, ρ.lookup (n + 1) = some v ∧ ValueWellFormed v := by
        clear go
        -- Walk down hρ_wf until we find depth n+1.
        have hlookup_helper : ∀ (k : Nat) {ρ' : CekEnv},
            EnvWellFormed k ρ' → ∀ m, 1 ≤ m → m ≤ k →
            ∃ v, ρ'.lookup m = some v ∧ ValueWellFormed v := by
          intro k
          induction k with
          | zero => intros _ _ _ _ hm_le; omega
          | succ k' ih =>
            intro ρ' h' m hm_pos hm_le
            cases h' with
            | @succ _ _ v hrest _ hl hvw =>
              by_cases h_eq : m = k' + 1
              · subst h_eq; exact ⟨v, hl, hvw⟩
              · exact ih hrest m hm_pos (by omega)
        exact hlookup_helper d hρ_wf (n + 1) (by omega) hn1
      obtain ⟨v, hl, hvw⟩ := this
      have h_gt : n + 1 + 1 > 1 := by omega
      refine SubstBisimEnv.succ_above h_gt hrec ?_ ?_ (substBisimValue_refl_wf v hvw)
      · show (ρ.extend v_rhs).lookup (n + 1 + 1) = some v
        rw [extend_lookup_succ ρ v_rhs (n + 1) (by omega)]
        exact hl
      · show ρ.lookup ((n + 1 + 1) - 1) = some v
        have : (n + 1 + 1 : Nat) - 1 = n + 1 := by omega
        rw [this]
        exact hl
  exact go d (Nat.le_refl _)

end Moist.Verified.SubstBisim
