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

end Moist.Verified.SubstBisim
