import Moist.Verified.Definitions.StepIndexed
import Moist.Verified.Contextual.SoundnessRefines
import Moist.Verified.Contextual
import Moist.Verified.ClosedAt
import Moist.Verified.RenameBase
import Moist.Verified.StepLift
import Moist.Verified.FundamentalRefines
import Moist.Verified.MIR.Primitives.Shared

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

/-- Fold-extend: extends `ρ` with a list of values. `vs = [v₁, v₂, ...]`
    maps to positions 1, 2, ..., vs.length. -/
def foldrExtend (ρ : CekEnv) : List CekValue → CekEnv
  | [] => ρ
  | v :: rest => (foldrExtend ρ rest).extend v

/-- Lookup in `foldrExtend ρ vs` at position 1 returns first value. -/
theorem foldrExtend_lookup_one_cons (ρ : CekEnv) (v : CekValue) (rest : List CekValue) :
    (foldrExtend ρ (v :: rest)).lookup 1 = some v := by
  show ((foldrExtend ρ rest).extend v).lookup 1 = some v
  rfl

/-- Lookup shifts in foldrExtend: position `n+1` in `foldrExtend ρ (v :: rest)`
    equals position `n` in `foldrExtend ρ rest`. -/
theorem foldrExtend_lookup_succ_cons (ρ : CekEnv) (v : CekValue) (rest : List CekValue)
    (n : Nat) (hn : n ≥ 1) :
    (foldrExtend ρ (v :: rest)).lookup (n + 1) = (foldrExtend ρ rest).lookup n := by
  show ((foldrExtend ρ rest).extend v).lookup (n + 1) = (foldrExtend ρ rest).lookup n
  exact extend_lookup_succ _ _ _ hn

/-- Lookup in `foldrExtend ρ vs` at positions > vs.length returns values
    from ρ (shifted down by vs.length). -/
theorem foldrExtend_lookup_above : ∀ (ρ : CekEnv) (vs : List CekValue) (n : Nat),
    n > vs.length →
    (foldrExtend ρ vs).lookup n = ρ.lookup (n - vs.length)
  | _, [], n, _ => by simp [foldrExtend]
  | ρ, v :: rest, n, h_gt => by
    simp only [List.length_cons] at h_gt
    have h_n_ge_1 : n ≥ 1 := by omega
    -- n > rest.length + 1, so n ≥ rest.length + 2, so n - 1 > rest.length
    match n, h_n_ge_1 with
    | k + 1, _ =>
      have h_rec_gt : k > rest.length := by omega
      have h_extend_eq : (foldrExtend ρ (v :: rest)).lookup (k + 1)
          = (foldrExtend ρ rest).lookup k := foldrExtend_lookup_succ_cons ρ v rest k
            (by
              -- k ≥ 1 because k > rest.length ≥ 0 and for 0 we'd have 1 > rest.length + 1 false
              omega)
      rw [h_extend_eq]
      rw [foldrExtend_lookup_above ρ rest k h_rec_gt]
      show ρ.lookup (k - rest.length) = ρ.lookup (k + 1 - (rest.length + 1))
      congr 1
      omega

/-- Inversion: lookup in `foldrExtend ρ (v :: rest)` at position `n ≥ 2`
    reduces to lookup in `foldrExtend ρ rest` at position `n - 1`. -/
theorem foldrExtend_lookup_cons_ge_2 (ρ : CekEnv) (v : CekValue) (rest : List CekValue)
    (n : Nat) (hn : n ≥ 2) :
    (foldrExtend ρ (v :: rest)).lookup n = (foldrExtend ρ rest).lookup (n - 1) := by
  match n, hn with
  | k + 2, _ =>
    have h_eq : (k + 2) - 1 = k + 1 := by omega
    rw [h_eq]
    exact foldrExtend_lookup_succ_cons ρ v rest (k + 1) (by omega)

/-- `substTermList`'s `getElem` distributes through the element access.
    Copied from BetaValueRefines.lean for self-containment. -/
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

/-- Iterated shift: apply `renameTerm (shiftRename 1)` `k` times. For vs-list
    generalization, after traversing `k` binders the cached `replacement` has
    been shift-renamed `k` times. -/
def iteratedShift : Nat → Term → Term
  | 0, t => t
  | k + 1, t => Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (iteratedShift k t)

theorem iteratedShift_zero (t : Term) : iteratedShift 0 t = t := rfl

theorem iteratedShift_succ (k : Nat) (t : Term) :
    iteratedShift (k + 1) t =
    Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (iteratedShift k t) := rfl

/-- `iteratedShift` preserves closedness with depth growing by 1 per iteration. -/
theorem closedAt_iteratedShift : ∀ (k d : Nat) (t : Term),
    closedAt d t = true → closedAt (d + k) (iteratedShift k t) = true
  | 0, _, _, h => h
  | k + 1, d, t, h => by
    show closedAt (d + k + 1)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (iteratedShift k t)) = true
    exact Moist.Verified.MIR.closedAt_renameTerm_shiftRename
      (iteratedShift k t) (d + k) 1 (by omega) (by omega)
      (closedAt_iteratedShift k d t h)

/-- Iterated `shiftRename c` applied `k` times. Generalizes `iteratedShift` to
    arbitrary cutoff; `iterShiftRename k c` shifts indices ≥ c by k (preserving
    those < c). Used for the generalized `renameInsertCompute` that handles
    multiple binder insertions at once. -/
def iterShiftRename : Nat → Nat → Term → Term
  | 0, _, t => t
  | k + 1, c, t =>
      Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (iterShiftRename k c t)

@[simp] theorem iterShiftRename_zero (c : Nat) (t : Term) : iterShiftRename 0 c t = t := rfl

theorem iterShiftRename_succ (k c : Nat) (t : Term) :
    iterShiftRename (k + 1) c t =
    Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (iterShiftRename k c t) := rfl

/-- For cutoff 1, `iterShiftRename` coincides with `iteratedShift`. -/
theorem iteratedShift_eq_iterShiftRename (k : Nat) (t : Term) :
    iteratedShift k t = iterShiftRename k 1 t := by
  induction k with
  | zero => rfl
  | succ j ih =>
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (iteratedShift j t) =
         Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (iterShiftRename j 1 t)
    rw [ih]

/-- Closedness preservation for `iterShiftRename`: each iteration bumps the
    closedness bound by 1, as long as the cutoff `c` is within `[1, d + 1]`. -/
theorem closedAt_iterShiftRename : ∀ (k c d : Nat) (t : Term),
    1 ≤ c → c ≤ d + 1 →
    closedAt d t = true →
    closedAt (d + k) (iterShiftRename k c t) = true
  | 0, _, _, _, _, _, h => h
  | k + 1, c, d, t, hc1, hcd, h => by
    show closedAt (d + k + 1)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (iterShiftRename k c t)) = true
    have h_rec := closedAt_iterShiftRename k c d t hc1 hcd h
    exact Moist.Verified.MIR.closedAt_renameTerm_shiftRename
      (iterShiftRename k c t) (d + k) c hc1 (by omega) h_rec

/-- Iterated `renameTermList` with cutoff `c`, applied `k` times. -/
def iterShiftRenameList : Nat → Nat → List Term → List Term
  | 0, _, ts => ts
  | k + 1, c, ts =>
      Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
        (iterShiftRenameList k c ts)

@[simp] theorem iterShiftRenameList_zero (c : Nat) (ts : List Term) :
    iterShiftRenameList 0 c ts = ts := rfl

theorem iterShiftRenameList_succ (k c : Nat) (ts : List Term) :
    iterShiftRenameList (k + 1) c ts =
    Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
      (iterShiftRenameList k c ts) := rfl

/-- Length preservation for `iterShiftRenameList`. -/
theorem iterShiftRenameList_length : ∀ (k c : Nat) (ts : List Term),
    (iterShiftRenameList k c ts).length = ts.length
  | 0, _, _ => rfl
  | k + 1, c, ts => by
    show (Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
      (iterShiftRenameList k c ts)).length = ts.length
    rw [Moist.Verified.renameTermList_length]
    exact iterShiftRenameList_length k c ts

/-- `getElem` distributes through `iterShiftRenameList`. -/
theorem iterShiftRenameList_getElem : ∀ (k c : Nat) (ts : List Term) (i : Nat)
    (hi : i < ts.length),
    (iterShiftRenameList k c ts)[i]'(by rw [iterShiftRenameList_length]; exact hi) =
    iterShiftRename k c (ts[i])
  | 0, _, _, _, _ => rfl
  | k + 1, c, ts, i, hi => by
    show (Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
      (iterShiftRenameList k c ts))[i]'_ = _
    rw [Moist.Verified.renameTermList_getElem _ _ _
          (by rw [iterShiftRenameList_length]; exact hi)]
    rw [iterShiftRenameList_getElem k c ts i hi]
    rfl

/-- Structural: `iterShiftRename` on `Var n`. -/
theorem iterShiftRename_Var : ∀ (k c n : Nat),
    iterShiftRename k c (.Var n) = .Var (if n ≥ c then n + k else n)
  | 0, c, n => by
    show Term.Var n = Term.Var (if n ≥ c then n + 0 else n)
    by_cases h : n ≥ c
    · simp [h]
    · simp [h]
  | k + 1, c, n => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Var n)) = .Var (if n ≥ c then n + (k + 1) else n)
    rw [iterShiftRename_Var k c n]
    simp only [Moist.Verified.renameTerm]
    by_cases h : n ≥ c
    · have h_shifted : n + k ≥ c := by omega
      rw [if_pos h, if_pos h]
      show Term.Var (Moist.Verified.shiftRename c (n + k)) = Term.Var (n + (k + 1))
      rw [Moist.Verified.shiftRename_ge h_shifted]
      rfl
    · rw [if_neg h, if_neg h]
      show Term.Var (Moist.Verified.shiftRename c n) = Term.Var n
      rw [Moist.Verified.shiftRename_lt (Nat.not_le.mp h)]

/-- Structural: `iterShiftRename` on `Constant p`. -/
@[simp] theorem iterShiftRename_Constant : ∀ (k c : Nat) (p : Const × BuiltinType),
    iterShiftRename k c (.Constant p) = .Constant p
  | 0, _, _ => rfl
  | k + 1, c, p => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Constant p)) = .Constant p
    rw [iterShiftRename_Constant k c p]
    simp [Moist.Verified.renameTerm]

/-- Structural: `iterShiftRename` on `Builtin b`. -/
@[simp] theorem iterShiftRename_Builtin : ∀ (k c : Nat) (b : BuiltinFun),
    iterShiftRename k c (.Builtin b) = .Builtin b
  | 0, _, _ => rfl
  | k + 1, c, b => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Builtin b)) = .Builtin b
    rw [iterShiftRename_Builtin k c b]
    simp [Moist.Verified.renameTerm]

/-- Structural: `iterShiftRename` on `Error`. -/
@[simp] theorem iterShiftRename_Error : ∀ (k c : Nat),
    iterShiftRename k c .Error = .Error
  | 0, _ => rfl
  | k + 1, c => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c .Error) = .Error
    rw [iterShiftRename_Error k c]
    simp [Moist.Verified.renameTerm]

/-- Structural: `iterShiftRename` on `Lam name body`. Requires cutoff ≥ 1 so
    that `liftRename (shiftRename c) = shiftRename (c + 1)`. -/
theorem iterShiftRename_Lam : ∀ (k c : Nat) (name : Nat) (body : Term),
    1 ≤ c →
    iterShiftRename k c (.Lam name body) = .Lam name (iterShiftRename k (c + 1) body)
  | 0, _, _, _, _ => rfl
  | k + 1, c, name, body, hc => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Lam name body)) = _
    rw [iterShiftRename_Lam k c name body hc]
    simp only [Moist.Verified.renameTerm]
    rw [Moist.Verified.liftRename_shiftRename hc]
    rfl

/-- Structural: `iterShiftRename` on `Delay body`. -/
theorem iterShiftRename_Delay : ∀ (k c : Nat) (body : Term),
    iterShiftRename k c (.Delay body) = .Delay (iterShiftRename k c body)
  | 0, _, _ => rfl
  | k + 1, c, body => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Delay body)) = .Delay (iterShiftRename (k + 1) c body)
    rw [iterShiftRename_Delay k c body]
    simp only [Moist.Verified.renameTerm]
    rfl

/-- Structural: `iterShiftRename` on `Force e`. -/
theorem iterShiftRename_Force : ∀ (k c : Nat) (e : Term),
    iterShiftRename k c (.Force e) = .Force (iterShiftRename k c e)
  | 0, _, _ => rfl
  | k + 1, c, e => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Force e)) = .Force (iterShiftRename (k + 1) c e)
    rw [iterShiftRename_Force k c e]
    simp only [Moist.Verified.renameTerm]
    rfl

/-- Structural: `iterShiftRename` on `Apply f x`. -/
theorem iterShiftRename_Apply : ∀ (k c : Nat) (f x : Term),
    iterShiftRename k c (.Apply f x) =
    .Apply (iterShiftRename k c f) (iterShiftRename k c x)
  | 0, _, _, _ => rfl
  | k + 1, c, f, x => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Apply f x)) = _
    rw [iterShiftRename_Apply k c f x]
    simp only [Moist.Verified.renameTerm]
    rfl

/-- Structural: `iterShiftRename` on `Constr tag args` via `iterShiftRenameList`. -/
theorem iterShiftRename_Constr : ∀ (k c tag : Nat) (args : List Term),
    iterShiftRename k c (.Constr tag args) = .Constr tag (iterShiftRenameList k c args)
  | 0, _, _, _ => rfl
  | k + 1, c, tag, args => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Constr tag args)) = _
    rw [iterShiftRename_Constr k c tag args]
    simp only [Moist.Verified.renameTerm]
    rfl

/-- Structural: `iterShiftRename` on `Case scrut alts`. -/
theorem iterShiftRename_Case : ∀ (k c : Nat) (scrut : Term) (alts : List Term),
    iterShiftRename k c (.Case scrut alts) =
    .Case (iterShiftRename k c scrut) (iterShiftRenameList k c alts)
  | 0, _, _, _ => rfl
  | k + 1, c, scrut, alts => by
    show Moist.Verified.renameTerm (Moist.Verified.shiftRename c)
      (iterShiftRename k c (.Case scrut alts)) = _
    rw [iterShiftRename_Case k c scrut alts]
    simp only [Moist.Verified.renameTerm]
    rfl

/-- Structural: `iterShiftRenameList` on `[]`. -/
@[simp] theorem iterShiftRenameList_nil : ∀ (k c : Nat),
    iterShiftRenameList k c [] = []
  | 0, _ => rfl
  | k + 1, c => by
    show Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
      (iterShiftRenameList k c []) = []
    rw [iterShiftRenameList_nil k c]
    simp [Moist.Verified.renameTermList]

/-- Structural: `iterShiftRenameList` on `t :: rest`. -/
theorem iterShiftRenameList_cons : ∀ (k c : Nat) (t : Term) (rest : List Term),
    iterShiftRenameList k c (t :: rest) =
    iterShiftRename k c t :: iterShiftRenameList k c rest
  | 0, _, _, _ => rfl
  | k + 1, c, t, rest => by
    show Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
      (iterShiftRenameList k c (t :: rest)) = _
    rw [iterShiftRenameList_cons k c t rest]
    show Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
      (iterShiftRename k c t :: iterShiftRenameList k c rest) =
      Moist.Verified.renameTerm (Moist.Verified.shiftRename c) (iterShiftRename k c t) ::
        Moist.Verified.renameTermList (Moist.Verified.shiftRename c)
          (iterShiftRenameList k c rest)
    rfl

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

/-- ρ-specific halts witness: in env `ρ`, for any stack, `rep` halts to
    `v_repl` in a finite number of steps and never errors along the way.
    Additionally witnesses that `v_repl` is well-formed.

    Note: this uses literal equality to `v_repl`. Under shifts, closures
    captured at different env depths will NOT be literally equal, so
    `substHaltsAt_shift` cannot preserve this predicate verbatim for
    closure `v_repl`. The rename-shifted cases are handled at the bisim
    level via `SubstBisimValue.vlam_rename`/`vdelay_rename` constructors.

    Covers both:
    - Branches 1–3 of shouldInline (atom/value/pure): halts universally over
      any well-formed env, instantiated at `ρ₀`.
    - Branch 4 (single-use strict impure): halts in the specific `ρ₀` where
      the LHS of the inline pass already demonstrated halting. -/
def SubstHaltsAt (rep : Term) (v_repl : CekValue) (ρ : CekEnv) (d : Nat) : Prop :=
  EnvWellFormed d ρ ∧ d ≤ ρ.length ∧
  closedAt d rep = true ∧
  ValueWellFormed v_repl ∧
  ∀ (π : Stack), ∃ (m : Nat),
    steps m (.compute π ρ rep) = .ret π v_repl ∧
    ∀ (k : Nat), k ≤ m → steps k (.compute π ρ rep) ≠ .error

mutual

inductive SubstBisimState : State → State → Prop
  /-- Substitution family with vs-list generalization. `vs₁`/`vs₂` are
      bisim-related binders accumulated by traversing Lams under the substitution.
      At `vs = []` this recovers the simple compute. -/
  | compute : ∀ {π₁ π₂ : Stack} {ρ₁ ρ₂ : CekEnv} {vs₁ vs₂ : List CekValue}
      {t : Term} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (d + 1 + vs₁.length) t = true →
      SubstHaltsAt replacement v_repl ρ₂ d →
      SubstBisimStack π₁ π₂ →
      SubstBisimState
        (.compute π₁ (foldrExtend ρ₁ vs₁) t)
        (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) t))
  /-- Reflexive compute, generalized with vs-list. `vs = []` gives the base
      refl form; `vs ≠ []` lets us express bisim-related env tops with same body. -/
  | reflCompute : ∀ {π₁ π₂ : Stack} {ρ : CekEnv} {vs₁ vs₂ : List CekValue}
      {t : Term} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length) t = true →
      SubstBisimStack π₁ π₂ →
      SubstBisimState (.compute π₁ (foldrExtend ρ vs₁) t)
                      (.compute π₂ (foldrExtend ρ vs₂) t)
  /-- Rename-insert compute (generalized). Parameterized by:
      - a list of SubstBisim-related binders `(vs₁, vs₂)` on top of `ρ` (LHS)
        / `foldrExtend ρ vs_insert` (RHS).
      - `vs_insert`: the list of well-formed values inserted between `ρ` and
        the `vs₂` region on RHS.

      `vs = []`, `vs_insert = [v_x]` recovers the simple single-insertion
      renameCompute case (shift by 1).

      `vs = []`, `vs_insert = [v₁,...,v_k]` handles shift-by-k (used to close
      Var=pos+vs.length in the subst-family `compute` by relating to a
      shifted evaluation in the extended env).

      `vs ≠ []` arises from applying a `vlam_rename_list` to a new argument. -/
  | renameInsertCompute : ∀ {π₁ π₂ : Stack} {ρ : CekEnv}
      {vs₁ vs₂ vs_insert : List CekValue} {t : Term} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length) t = true →
      SubstBisimStack π₁ π₂ →
      SubstBisimState
        (.compute π₁ (foldrExtend ρ vs₁) t)
        (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) t))
  | ret : ∀ {π₁ π₂ : Stack} {v₁ v₂ : CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimStack π₁ π₂ →
      SubstBisimState (State.ret π₁ v₁) (State.ret π₂ v₂)
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
  /-- Subst-family VLam closure, generalized with vs-list. `vs = []` recovers
      the simple vlam; `vs ≠ []` captures closures reached by applying a
      subst-family Lam within a nested compute. -/
  | vlam : ∀ {body : Term} {ρ₁ ρ₂ : CekEnv} {vs₁ vs₂ : List CekValue} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (d + 2 + vs₁.length) body = true →
      SubstHaltsAt replacement v_repl ρ₂ d →
      SubstBisimValue
        (.VLam body (foldrExtend ρ₁ vs₁))
        (.VLam (Moist.Verified.substTerm (pos + vs₁.length + 1)
          (iteratedShift (vs₁.length + 1) replacement) body) (foldrExtend ρ₂ vs₂))
  /-- Subst-family VDelay closure, generalized with vs-list. -/
  | vdelay : ∀ {body : Term} {ρ₁ ρ₂ : CekEnv} {vs₁ vs₂ : List CekValue} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (d + 1 + vs₁.length) body = true →
      SubstHaltsAt replacement v_repl ρ₂ d →
      SubstBisimValue
        (.VDelay body (foldrExtend ρ₁ vs₁))
        (.VDelay (Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) body) (foldrExtend ρ₂ vs₂))
  | vconstr : ∀ (tag : Nat) {fs₁ fs₂ : List CekValue},
      SubstBisimValueList fs₁ fs₂ →
      SubstBisimValue (.VConstr tag fs₁) (.VConstr tag fs₂)
  | vbuiltin : ∀ (b : BuiltinFun) (ea : ExpectedArgs) {args₁ args₂ : List CekValue},
      SubstBisimValueList args₁ args₂ →
      SubstBisimValue (.VBuiltin b args₁ ea) (.VBuiltin b args₂ ea)
  /-- Reflexivity: any well-formed value is related to itself. Used for
      closures captured in env positions untouched by substitution. -/
  | refl : ∀ {v : CekValue}, ValueWellFormed v → SubstBisimValue v v
  /-- Refl-family VLam closure extended by vs-list. The envs differ only in
      the vs-list prefix (bisim-related), the bodies are identical. Arises
      when reflCompute with non-empty vs reaches a Lam. -/
  | vlam_refl_list : ∀ {body : Term} {ρ : CekEnv}
      {vs₁ vs₂ : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length + 1) body = true →
      SubstBisimValue
        (.VLam body (foldrExtend ρ vs₁))
        (.VLam body (foldrExtend ρ vs₂))
  /-- Refl-family VDelay closure extended by vs-list. -/
  | vdelay_refl_list : ∀ {body : Term} {ρ : CekEnv}
      {vs₁ vs₂ : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length) body = true →
      SubstBisimValue
        (.VDelay body (foldrExtend ρ vs₁))
        (.VDelay body (foldrExtend ρ vs₂))
  /-- Generalized rename-shifted VLam closure with multi-binder insertion.
      `vs_insert` holds the inserted binders (inserted between `ρ` and vs₂ on
      RHS). The body gets shifted by `iterShiftRename vs_insert.length
      (vs₁.length + 2)` (the +2 accounts for the Lam's own binder plus lifting
      through vs₁'s binders to reach the insertion point). -/
  | vlam_rename_list : ∀ {body : Term} {ρ : CekEnv}
      {vs₁ vs₂ vs_insert : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length + 1) body = true →
      SubstBisimValue
        (.VLam body (foldrExtend ρ vs₁))
        (.VLam (iterShiftRename vs_insert.length (vs₁.length + 2) body)
               (foldrExtend (foldrExtend ρ vs_insert) vs₂))
  /-- Generalized rename-shifted VDelay closure with multi-binder insertion. -/
  | vdelay_rename_list : ∀ {body : Term} {ρ : CekEnv}
      {vs₁ vs₂ vs_insert : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length) body = true →
      SubstBisimValue
        (.VDelay body (foldrExtend ρ vs₁))
        (.VDelay (iterShiftRename vs_insert.length (vs₁.length + 1) body)
                 (foldrExtend (foldrExtend ρ vs_insert) vs₂))

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
  /-- Subst-family arg frame, generalized with vs-list. -/
  | arg : ∀ {t : Term} {ρ₁ ρ₂ : CekEnv} {vs₁ vs₂ : List CekValue} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (d + 1 + vs₁.length) t = true →
      SubstHaltsAt replacement v_repl ρ₂ d →
      SubstBisimFrame
        (.arg t (foldrExtend ρ₁ vs₁))
        (.arg (Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) t) (foldrExtend ρ₂ vs₂))
  | funV : ∀ {v₁ v₂ : CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimFrame (.funV v₁) (.funV v₂)
  | applyArg : ∀ {v₁ v₂ : CekValue},
      SubstBisimValue v₁ v₂ → SubstBisimFrame (.applyArg v₁) (.applyArg v₂)
  /-- Subst-family constrField frame, generalized with vs-list. -/
  | constrField : ∀ (tag : Nat) {done₁ done₂ : List CekValue}
      {todo : List Term} {ρ₁ ρ₂ : CekEnv} {vs₁ vs₂ : List CekValue} {pos : Nat}
      {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos →
      closedAt d replacement = true →
      SubstBisimValueList done₁ done₂ →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (d + 1 + vs₁.length) todo = true →
      SubstHaltsAt replacement v_repl ρ₂ d →
      SubstBisimFrame
        (.constrField tag done₁ todo (foldrExtend ρ₁ vs₁))
        (.constrField tag done₂ (Moist.Verified.substTermList (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) todo) (foldrExtend ρ₂ vs₂))
  /-- Subst-family caseScrutinee frame, generalized with vs-list. -/
  | caseScrutinee : ∀ {alts : List Term} {ρ₁ ρ₂ : CekEnv} {vs₁ vs₂ : List CekValue}
      {pos : Nat} {replacement : Term} {v_repl : CekValue} {d : Nat},
      1 ≤ pos →
      closedAt d replacement = true →
      SubstBisimEnv pos replacement v_repl (d + 1) ρ₁ ρ₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (d + 1 + vs₁.length) alts = true →
      SubstHaltsAt replacement v_repl ρ₂ d →
      SubstBisimFrame
        (.caseScrutinee alts (foldrExtend ρ₁ vs₁))
        (.caseScrutinee (Moist.Verified.substTermList (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) alts) (foldrExtend ρ₂ vs₂))
  /-- Reflexive arg frame, generalized with vs-list. -/
  | argRefl : ∀ {t : Term} {ρ : CekEnv} {vs₁ vs₂ : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length) t = true →
      SubstBisimFrame (.arg t (foldrExtend ρ vs₁)) (.arg t (foldrExtend ρ vs₂))
  /-- Reflexive constrField frame, generalized with vs-list. -/
  | constrFieldRefl : ∀ (tag : Nat) {done : List CekValue}
      {todo : List Term} {ρ : CekEnv} {vs₁ vs₂ : List CekValue} {k : Nat},
      ValueListWellFormed done →
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (k + vs₁.length) todo = true →
      SubstBisimFrame
        (.constrField tag done todo (foldrExtend ρ vs₁))
        (.constrField tag done todo (foldrExtend ρ vs₂))
  /-- Semi-reflexive constrField (dones differ by SubstBisimValueList), generalized with vs-list. -/
  | constrFieldSemiRefl : ∀ (tag : Nat) {done₁ done₂ : List CekValue}
      {todo : List Term} {ρ : CekEnv} {vs₁ vs₂ : List CekValue} {k : Nat},
      SubstBisimValueList done₁ done₂ →
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (k + vs₁.length) todo = true →
      SubstBisimFrame
        (.constrField tag done₁ todo (foldrExtend ρ vs₁))
        (.constrField tag done₂ todo (foldrExtend ρ vs₂))
  /-- Reflexive caseScrutinee frame, generalized with vs-list. -/
  | caseScrutineeRefl : ∀ {alts : List Term} {ρ : CekEnv} {vs₁ vs₂ : List CekValue}
      {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (k + vs₁.length) alts = true →
      SubstBisimFrame
        (.caseScrutinee alts (foldrExtend ρ vs₁))
        (.caseScrutinee alts (foldrExtend ρ vs₂))
  /-- Rename-insert arg frame (multi-insertion). `vs_insert` are the inserted
      binders; the shift is by `vs_insert.length` at cutoff `vs₁.length + 1`. -/
  | argRenameInsert : ∀ {t : Term} {ρ : CekEnv}
      {vs₁ vs₂ vs_insert : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAt (k + vs₁.length) t = true →
      SubstBisimFrame
        (.arg t (foldrExtend ρ vs₁))
        (.arg (iterShiftRename vs_insert.length (vs₁.length + 1) t)
              (foldrExtend (foldrExtend ρ vs_insert) vs₂))
  /-- Rename-insert constrField frame (multi-insertion). -/
  | constrFieldRenameInsert : ∀ (tag : Nat) {done₁ done₂ : List CekValue}
      {todo : List Term} {ρ : CekEnv}
      {vs₁ vs₂ vs_insert : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList done₁ done₂ →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (k + vs₁.length) todo = true →
      SubstBisimFrame
        (.constrField tag done₁ todo (foldrExtend ρ vs₁))
        (.constrField tag done₂
          (iterShiftRenameList vs_insert.length (vs₁.length + 1) todo)
          (foldrExtend (foldrExtend ρ vs_insert) vs₂))
  /-- Rename-insert caseScrutinee frame (multi-insertion). -/
  | caseScrutineeRenameInsert : ∀ {alts : List Term} {ρ : CekEnv}
      {vs₁ vs₂ vs_insert : List CekValue} {k : Nat},
      EnvWellFormed k ρ → k ≤ ρ.length →
      SubstBisimValueList vs₁ vs₂ →
      closedAtList (k + vs₁.length) alts = true →
      SubstBisimFrame
        (.caseScrutinee alts (foldrExtend ρ vs₁))
        (.caseScrutinee
          (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)
          (foldrExtend (foldrExtend ρ vs_insert) vs₂))
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
    SubstBisimValue (.VCon c) v → v = .VCon c := by
  intro c v h
  cases h with
  | vcon _ => rfl
  | refl _ => rfl

theorem substBisimValue_vcon_inv_right : ∀ {c : Const} {v : CekValue},
    SubstBisimValue v (.VCon c) → v = .VCon c := by
  intro c v h
  cases h with
  | vcon _ => rfl
  | refl _ => rfl

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
    ∀ (pos : Nat) (_hpos : 1 ≤ pos)
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
    | vlam _ _ _ _ _ _ => rfl
    | vdelay _ _ _ _ _ _ => rfl
    | vconstr _ _ => rfl
    | vbuiltin _ _ _ => rfl
    | vlam_refl_list _ _ _ _ => rfl
    | vdelay_refl_list _ _ _ _ => rfl
    | vlam_rename_list _ _ _ _ => rfl
    | vdelay_rename_list _ _ _ _ => rfl
    | @refl v hv_wf =>
      cases v with
      | VCon c =>
        simp only [extractConsts]
        rw [ih hrest]
      | VLam _ _ => rfl
      | VDelay _ _ => rfl
      | VConstr _ _ => rfl
      | VBuiltin _ _ _ => rfl

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
theorem substBisimValueList_evalBuiltin {b : BuiltinFun}
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
theorem steps_error_fixed : ∀ (n : Nat), steps n State.error = .error
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

/-- Reflexivity of SubstBisimValue for well-formed values via the new
    `refl` constructor. -/
theorem substBisimValue_refl_wf (v : CekValue) :
    ValueWellFormed v → SubstBisimValue v v := fun h => SubstBisimValue.refl h

/-- List reflexivity derived trivially. -/
theorem substBisimValueList_refl_wf : ∀ {vs : List CekValue},
    ValueListWellFormed vs → SubstBisimValueList vs vs
  | _, .nil => SubstBisimValueList.nil
  | _, .cons hv hrest =>
    SubstBisimValueList.cons (substBisimValue_refl_wf _ hv)
      (substBisimValueList_refl_wf hrest)

/- `substTerm` is the identity on terms closed below the substitution
    position: when `pos > d` and `t` is `closedAt d`, every variable index in
    `t` is ≤ d < pos, so no substitution triggers.

    Proved by mutual structural recursion on terms and term lists. -/
mutual
theorem substTerm_id_of_above :
    ∀ (pos : Nat) (rep : Term) (t : Term) (d : Nat),
    d < pos →
    closedAt d t = true →
    Moist.Verified.substTerm pos rep t = t
  | pos, rep, .Var n, d, hd_lt, hclosed => by
    simp only [closedAt, decide_eq_true_eq] at hclosed
    have hn_ne : n ≠ pos := by omega
    have hn_not_gt : ¬ (n > pos) := by omega
    simp only [Moist.Verified.substTerm, hn_ne, hn_not_gt, if_false]
  | pos, rep, .Lam name body, d, hd_lt, hclosed => by
    simp only [closedAt] at hclosed
    simp only [Moist.Verified.substTerm]
    congr 1
    exact substTerm_id_of_above (pos + 1)
      (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) rep) body (d + 1)
      (by omega) hclosed
  | pos, rep, .Apply f x, d, hd_lt, hclosed => by
    simp only [closedAt, Bool.and_eq_true] at hclosed
    simp only [Moist.Verified.substTerm]
    rw [substTerm_id_of_above pos rep f d hd_lt hclosed.1,
        substTerm_id_of_above pos rep x d hd_lt hclosed.2]
  | pos, rep, .Force e, d, hd_lt, hclosed => by
    simp only [closedAt] at hclosed
    simp only [Moist.Verified.substTerm]
    rw [substTerm_id_of_above pos rep e d hd_lt hclosed]
  | pos, rep, .Delay e, d, hd_lt, hclosed => by
    simp only [closedAt] at hclosed
    simp only [Moist.Verified.substTerm]
    rw [substTerm_id_of_above pos rep e d hd_lt hclosed]
  | pos, rep, .Constr tag args, d, hd_lt, hclosed => by
    simp only [closedAt] at hclosed
    simp only [Moist.Verified.substTerm]
    rw [substTermList_id_of_above pos rep args d hd_lt hclosed]
  | pos, rep, .Case scrut alts, d, hd_lt, hclosed => by
    simp only [closedAt, Bool.and_eq_true] at hclosed
    simp only [Moist.Verified.substTerm]
    rw [substTerm_id_of_above pos rep scrut d hd_lt hclosed.1,
        substTermList_id_of_above pos rep alts d hd_lt hclosed.2]
  | _, _, .Constant _, _, _, _ => by simp only [Moist.Verified.substTerm]
  | _, _, .Builtin _, _, _, _ => by simp only [Moist.Verified.substTerm]
  | _, _, .Error, _, _, _ => by simp only [Moist.Verified.substTerm]

theorem substTermList_id_of_above :
    ∀ (pos : Nat) (rep : Term) (ts : List Term) (d : Nat),
    d < pos →
    closedAtList d ts = true →
    Moist.Verified.substTermList pos rep ts = ts
  | _, _, [], _, _, _ => by simp only [Moist.Verified.substTermList]
  | pos, rep, t :: rest, d, hd_lt, hclosed => by
    simp only [closedAtList, Bool.and_eq_true] at hclosed
    simp only [Moist.Verified.substTermList]
    rw [substTerm_id_of_above pos rep t d hd_lt hclosed.1,
        substTermList_id_of_above pos rep rest d hd_lt hclosed.2]
end

/-- evalBuiltin preserves well-formedness: if all args are well-formed and
    evalBuiltin succeeds, the result is well-formed.

    Every pass-through builtin arm either returns a VCon (trivially well-formed)
    or returns one of the input args (well-formed by `ValueListWellFormed` hargs).
    The constant fallback wraps the result in `.VCon`, always well-formed. -/
theorem evalBuiltin_wf : ∀ {b : BuiltinFun} {args : List CekValue} {v : CekValue},
    ValueListWellFormed args → evalBuiltin b args = some v → ValueWellFormed v := by
  intro b args v hargs heval
  -- Split into pass-through case vs constant fallback case.
  by_cases hpt_eq : evalBuiltinPassThrough b args = some v
  · -- pass-through returned v; show ValueWellFormed v by case analysis.
    -- Extract per-arg well-formedness hypotheses via repeated cases on hargs.
    have hpt : evalBuiltinPassThrough b args = some v := hpt_eq
    -- Dispatch on b to get specific arg shapes.
    unfold evalBuiltinPassThrough at hpt
    split at hpt
    all_goals (first | (exact Option.noConfusion hpt) | skip)
    -- IfThenElse
    case _ elseV thenV cond =>
      cases hargs with
      | @cons _ _ h_elseV hrest1 =>
        cases hrest1 with
        | @cons _ _ h_thenV _ =>
          simp only [Option.some.injEq] at hpt; subst hpt
          by_cases hc : cond = true
          · rw [if_pos hc]; exact h_thenV
          · rw [if_neg hc]; exact h_elseV
    -- ChooseUnit
    case _ result =>
      cases hargs with
      | @cons _ _ h_result _ =>
        simp only [Option.some.injEq] at hpt; subst hpt; exact h_result
    -- Trace
    case _ result _ =>
      cases hargs with
      | @cons _ _ h_result _ =>
        simp only [Option.some.injEq] at hpt; subst hpt; exact h_result
    -- ChooseData
    case _ bCase iCase listCase mapCase constrCase d =>
      cases hargs with
      | @cons _ _ h_b hrest1 =>
        cases hrest1 with
        | @cons _ _ h_i hrest2 =>
          cases hrest2 with
          | @cons _ _ h_l hrest3 =>
            cases hrest3 with
            | @cons _ _ h_m hrest4 =>
              cases hrest4 with
              | @cons _ _ h_c _ =>
                cases d with
                | Constr _ _ =>
                  simp only [Option.some.injEq] at hpt; subst hpt; exact h_c
                | Map _ =>
                  simp only [Option.some.injEq] at hpt; subst hpt; exact h_m
                | List _ =>
                  simp only [Option.some.injEq] at hpt; subst hpt; exact h_l
                | I _ =>
                  simp only [Option.some.injEq] at hpt; subst hpt; exact h_i
                | B _ =>
                  simp only [Option.some.injEq] at hpt; subst hpt; exact h_b
    -- ChooseList (ConstDataList)
    case _ consCase nilCase l =>
      cases hargs with
      | @cons _ _ h_c hrest1 =>
        cases hrest1 with
        | @cons _ _ h_n _ =>
          simp only [Option.some.injEq] at hpt; subst hpt
          by_cases he : l.isEmpty = true
          · rw [if_pos he]; exact h_n
          · rw [if_neg he]; exact h_c
    -- ChooseList (ConstList)
    case _ consCase nilCase l =>
      cases hargs with
      | @cons _ _ h_c hrest1 =>
        cases hrest1 with
        | @cons _ _ h_n _ =>
          simp only [Option.some.injEq] at hpt; subst hpt
          by_cases he : l.isEmpty = true
          · rw [if_pos he]; exact h_n
          · rw [if_neg he]; exact h_c
    -- MkCons + VCon elem
    case _ tail elem =>
      split at hpt
      · simp only [Option.some.injEq] at hpt; subst hpt
        exact ValueWellFormed.vcon _
      · exact Option.noConfusion hpt
  · -- pass-through didn't return v (returned none or different). In the evalBuiltin
    -- definition, if pass-through is none, we fall back to evalBuiltinConst + VCon.
    simp only [evalBuiltin] at heval
    cases hpt2 : evalBuiltinPassThrough b args with
    | some v' =>
      rw [hpt2] at heval
      simp only [Option.some.injEq] at heval
      subst heval
      exact absurd hpt2 hpt_eq
    | none =>
      rw [hpt2] at heval
      simp only at heval
      cases hec : extractConsts args with
      | some consts =>
        rw [hec] at heval
        simp only at heval
        cases hev : evalBuiltinConst b consts with
        | some c =>
          rw [hev] at heval
          simp only [Option.some.injEq] at heval
          subst heval
          exact ValueWellFormed.vcon c
        | none =>
          rw [hev] at heval
          exact Option.noConfusion heval
      | none =>
        rw [hec] at heval
        exact Option.noConfusion heval

/-- Reflexivity of `SubstBisimEnv` on `ρ ρ` for depths strictly below `pos`.

    The bisim encodes a "shift-down by one position" relation, so it is
    genuinely non-reflexive at depths ≥ pos (where the substitution either
    maps to `v_repl` at `succ_at` or shifts indices at `succ_above`).

    For `d < pos`, however, both sides look up the same positions from the
    same environment, and reflexivity follows by induction using `zero` +
    `succ_below`. -/
theorem substBisimEnv_refl_below_pos :
    ∀ (d : Nat) {ρ : CekEnv} (_hρ : EnvWellFormed d ρ)
      (pos : Nat) (_hpos : d < pos)
      (rep : Term) (v_repl : CekValue),
    SubstBisimEnv pos rep v_repl d ρ ρ := by
  intro d
  induction d with
  | zero =>
    intros _ _ _ _ _ _
    exact SubstBisimEnv.zero
  | succ k ih =>
    intros ρ hρ pos hpos rep v_repl
    cases hρ with
    | @succ _ _ v hrest _ hl hvw =>
      have hk_lt : k < pos := by omega
      have hrec := ih hrest pos hk_lt rep v_repl
      -- Use succ_below: (k+1) < pos, same lookup on both sides, related value via refl.
      refine SubstBisimEnv.succ_below ?_ hrec hl hl (SubstBisimValue.refl hvw)
      omega

/-- Empty foldrExtend is the base environment. -/
@[simp] theorem foldrExtend_nil (ρ : CekEnv) : foldrExtend ρ [] = ρ := rfl

/-- foldrExtend with cons: extend the deeper extension with the head. -/
theorem foldrExtend_cons (ρ : CekEnv) (v : CekValue) (vs : List CekValue) :
    foldrExtend ρ (v :: vs) = (foldrExtend ρ vs).extend v := rfl

/-- Lookup at position 1..vs.length gives the corresponding vs element. -/
theorem foldrExtend_lookup_in_vs (ρ : CekEnv) (vs : List CekValue) (n : Nat)
    (h_pos : 1 ≤ n) (h_le : n ≤ vs.length) :
    (foldrExtend ρ vs).lookup n = some (vs[n - 1]'(by omega)) := by
  induction vs generalizing n with
  | nil => exfalso; simp at h_le; omega
  | cons v rest ih =>
    match n, h_pos with
    | 1, _ =>
      show ((foldrExtend ρ rest).extend v).lookup 1 = some ((v :: rest)[0]'_)
      rfl
    | k + 2, _ =>
      have h_rest_le : k + 1 ≤ rest.length := by
        simp only [List.length_cons] at h_le; omega
      have h_rec := ih (n := k + 1) (by omega) h_rest_le
      have h_shift := foldrExtend_lookup_succ_cons ρ v rest (k + 1) (by omega)
      rw [h_shift, h_rec]
      -- Both sides reduce to some rest[k].
      have h_eq : rest[k + 1 - 1]'(by omega) = (v :: rest)[k + 2 - 1]'(by simp only [List.length_cons]; omega) := by
        have h1 : k + 1 - 1 = k := by omega
        have h2 : k + 2 - 1 = k + 1 := by omega
        show rest[k + 1 - 1]'(by omega) = (v :: rest)[k + 2 - 1]'_
        -- Rewrite indices
        simp only [h1, h2]
        rfl
      rw [h_eq]

/-- Positional lookup within a bisim-related vs-list gives bisim-related values. -/
theorem substBisimValueList_getElem {vs₁ vs₂ : List CekValue}
    (h : SubstBisimValueList vs₁ vs₂) (i : Nat) (hi : i < vs₁.length) :
    SubstBisimValue (vs₁[i])
      (vs₂[i]'(by rw [← substBisimValueList_length_eq h]; exact hi)) := by
  induction vs₁ generalizing vs₂ i with
  | nil => simp at hi
  | cons v₁ rest₁ ih =>
    cases h with
    | cons h_head h_tail =>
      match i with
      | 0 => exact h_head
      | k + 1 =>
        have h_rest_hi : k < rest₁.length := by
          simp only [List.length_cons] at hi; omega
        exact ih h_tail k h_rest_hi

/-- Length of iteratedShift application: shiftRename 1 composed with liftRename.
    At each Lam, the substTerm index increases by 1 and the rep gets wrapped in
    one more shiftRename. For vs-list, the body of a VLam at vs-depth k is
    substituted at position `pos + k + 1` with `iteratedShift (k + 1) rep`. -/
theorem iteratedShift_lift_commute (k : Nat) (rep : Term) :
    Moist.Verified.renameTerm (Moist.Verified.shiftRename 1) (iteratedShift k rep) =
    iteratedShift (k + 1) rep := rfl

/-- Weak step preservation: one step of LHS corresponds to ≥ 0 steps of RHS,
    maintaining the bisim. For most cases (non-Var/non-Var=pos), m = 1 (strong
    bisim). For Var=pos, m is the step count to evaluate `replacement` to its
    cached value `v_repl` plus 1 (the ret step). -/
theorem substBisimState_step_preserves_weak :
    ∀ {s₁ s₂ : State}, SubstBisimState s₁ s₂ →
    ∃ m, SubstBisimState (step s₁) (steps m s₂) := by
  intro s₁ s₂ h
  cases h with
  | halt h_v =>
    refine ⟨0, ?_⟩
    exact SubstBisimState.halt h_v
  | error =>
    refine ⟨0, ?_⟩
    exact SubstBisimState.error
  | @compute π₁ π₂ ρ₁ ρ₂ vs₁ vs₂ t pos replacement v_repl d
      hpos_le hrep_closed henv hvs hclosed h_halts hπ =>
    have hvs_len_eq : vs₁.length = vs₂.length := substBisimValueList_length_eq hvs
    cases t with
    | Var n =>
      by_cases hn_zero : n = 0
      · -- n = 0: both look up at 0 → none → error.
        subst hn_zero
        refine ⟨1, ?_⟩
        have h_subst_zero : Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Var 0) = .Var 0 := by
          simp only [Moist.Verified.substTerm]
          have h1 : (0 : Nat) ≠ pos + vs₁.length := by omega
          have h2 : ¬ (0 > pos + vs₁.length) := by omega
          simp [h1, h2]
        have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Var 0)) = .error := by
          show (match (foldrExtend ρ₁ vs₁).lookup 0 with
                | some v => State.ret π₁ v | none => State.error) = .error
          rw [lookup_zero]
        have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) (.Var 0))) = .error := by
          rw [h_subst_zero]
          simp only [steps]
          show (match (foldrExtend ρ₂ vs₂).lookup 0 with
                | some v => State.ret π₂ v | none => State.error) = .error
          rw [lookup_zero]
        rw [h_lhs, h_rhs]
        exact SubstBisimState.error
      · have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_zero
        have hn_le : n ≤ d + 1 + vs₁.length := by
          simp only [closedAt, decide_eq_true_eq] at hclosed; exact hclosed
        by_cases hn_in_vs : n ≤ vs₁.length
        · -- n ∈ [1..vs₁.length]: lookup in vs. No substitution impact (n < pos + vs₁.length since pos ≥ 1).
          have hl₁ : (foldrExtend ρ₁ vs₁).lookup n = some (vs₁[n - 1]'(by omega)) :=
            foldrExtend_lookup_in_vs ρ₁ vs₁ n hn_pos hn_in_vs
          have hn_in_vs₂ : n ≤ vs₂.length := by rw [← hvs_len_eq]; exact hn_in_vs
          have hl₂ : (foldrExtend ρ₂ vs₂).lookup n =
              some (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) :=
            foldrExtend_lookup_in_vs ρ₂ vs₂ n hn_pos hn_in_vs₂
          have hv_rel : SubstBisimValue (vs₁[n - 1]'(by omega))
              (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) :=
            substBisimValueList_getElem hvs (n - 1) (by omega)
          refine ⟨1, ?_⟩
          have h_subst_lt : Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) (.Var n) = .Var n := by
            simp only [Moist.Verified.substTerm]
            have h1 : n ≠ pos + vs₁.length := by omega
            have h2 : ¬ (n > pos + vs₁.length) := by omega
            simp [h1, h2]
          have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Var n)) =
              State.ret π₁ (vs₁[n - 1]'(by omega)) := by
            show (match (foldrExtend ρ₁ vs₁).lookup n with
                  | some v => State.ret π₁ v | none => State.error) = _
            rw [hl₁]
          have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
              (Moist.Verified.substTerm (pos + vs₁.length)
                (iteratedShift vs₁.length replacement) (.Var n))) =
              State.ret π₂ (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) := by
            rw [h_subst_lt]
            simp only [steps]
            show (match (foldrExtend ρ₂ vs₂).lookup n with
                  | some v => State.ret π₂ v | none => State.error) = _
            rw [hl₂]
          rw [h_lhs, h_rhs]
          exact SubstBisimState.ret hv_rel hπ
        · -- n > vs₁.length: lookup goes into ρ. Compare with pos.
          have hn_gt_vs : n > vs₁.length := Nat.not_le.mp hn_in_vs
          have hn_sub_pos : 1 ≤ n - vs₁.length := by omega
          have hn_sub_le : n - vs₁.length ≤ d + 1 := by omega
          by_cases hn_eq_pos : n - vs₁.length = pos
          · -- Var=pos+vs.length case. LHS lookup at pos+vs₁.length in
            -- `foldrExtend ρ₁ vs₁` reduces to `ρ₁.lookup pos = some v_repl`
            -- (via `SubstBisimEnv_at`). RHS substTerm reduces to
            -- `iteratedShift vs₁.length replacement` in `foldrExtend ρ₂ vs₂`.
            --
            -- To close: construct a `renameInsertCompute` bisim state relating
            -- `(compute π₁ ρ₂ replacement)` with the shifted RHS, then apply
            -- iterated step preservation (m₀ times from h_halts) to transport
            -- the LHS halt witness to the RHS.
            --
            -- Blocker: `substBisimState_steps_preserves_weak` is defined
            -- AFTER this theorem, and mutual recursion here requires an
            -- explicit well-founded termination measure that Lean cannot
            -- automatically derive (the recursion bound is the halt step
            -- count `m₀` extracted from `h_halts`, but `m₀` is not a
            -- structurally-decreasing argument).
            --
            -- Closing options:
            --   (A) Dedicated `renameInsertCompute_steps_halt_preserves`
            --       lemma proven by induction on the halt chain structure
            --       (independent of `step_preserves_weak`). ~500 lines.
            --   (B) Manual well-founded recursion via `termination_by` with
            --       a custom measure on `(n, halt_count_in_h)`. Requires
            --       non-trivial well-founded-ness proof.
            sorry
          · by_cases hn_lt_pos : n - vs₁.length < pos
            · -- n - vs₁.length < pos: use SubstBisimEnv_below.
              obtain ⟨w₁, w₂, hl₁_base, hl₂_base, hv_rel⟩ :=
                substBisimEnv_lookup_below pos replacement v_repl (d + 1)
                  hn_sub_pos hn_sub_le hn_lt_pos henv
              have hl₁ : (foldrExtend ρ₁ vs₁).lookup n = some w₁ := by
                rw [foldrExtend_lookup_above _ _ _ hn_gt_vs]; exact hl₁_base
              have hl₂ : (foldrExtend ρ₂ vs₂).lookup n = some w₂ := by
                have hn_gt_vs₂ : n > vs₂.length := by rw [← hvs_len_eq]; exact hn_gt_vs
                rw [foldrExtend_lookup_above _ _ _ hn_gt_vs₂,
                    show (n - vs₂.length) = (n - vs₁.length) from by rw [hvs_len_eq]]
                exact hl₂_base
              refine ⟨1, ?_⟩
              have h_subst_lt : Moist.Verified.substTerm (pos + vs₁.length)
                  (iteratedShift vs₁.length replacement) (.Var n) = .Var n := by
                simp only [Moist.Verified.substTerm]
                have h1 : n ≠ pos + vs₁.length := by omega
                have h2 : ¬ (n > pos + vs₁.length) := by omega
                simp [h1, h2]
              have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Var n)) = State.ret π₁ w₁ := by
                show (match (foldrExtend ρ₁ vs₁).lookup n with
                      | some v' => State.ret π₁ v' | none => State.error) = _
                rw [hl₁]
              have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
                  (Moist.Verified.substTerm (pos + vs₁.length)
                    (iteratedShift vs₁.length replacement) (.Var n))) = State.ret π₂ w₂ := by
                rw [h_subst_lt]
                simp only [steps]
                show (match (foldrExtend ρ₂ vs₂).lookup n with
                      | some v' => State.ret π₂ v' | none => State.error) = _
                rw [hl₂]
              rw [h_lhs, h_rhs]
              exact SubstBisimState.ret hv_rel hπ
            · -- n - vs₁.length > pos: use SubstBisimEnv_above.
              have hn_gt_pos : n - vs₁.length > pos := by omega
              obtain ⟨w₁, w₂, hl₁_base, hl₂_base, hv_rel⟩ :=
                substBisimEnv_lookup_above pos replacement v_repl (d + 1)
                  hn_sub_pos hn_sub_le hn_gt_pos henv
              have hl₁ : (foldrExtend ρ₁ vs₁).lookup n = some w₁ := by
                rw [foldrExtend_lookup_above _ _ _ hn_gt_vs]; exact hl₁_base
              -- RHS: substTerm substitutes Var n with Var (n - 1) since n > pos + vs₁.length.
              have hl₂ : (foldrExtend ρ₂ vs₂).lookup (n - 1) = some w₂ := by
                have hn1_gt_vs₂ : n - 1 > vs₂.length := by rw [← hvs_len_eq]; omega
                rw [foldrExtend_lookup_above _ _ _ hn1_gt_vs₂]
                have : n - 1 - vs₂.length = (n - vs₁.length) - 1 := by rw [hvs_len_eq]; omega
                rw [this]; exact hl₂_base
              refine ⟨1, ?_⟩
              have h_subst_gt : Moist.Verified.substTerm (pos + vs₁.length)
                  (iteratedShift vs₁.length replacement) (.Var n) = .Var (n - 1) := by
                simp only [Moist.Verified.substTerm]
                have h1 : n ≠ pos + vs₁.length := fun h => by omega
                have h2 : n > pos + vs₁.length := by omega
                simp [h1, h2]
              have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Var n)) = State.ret π₁ w₁ := by
                show (match (foldrExtend ρ₁ vs₁).lookup n with
                      | some v' => State.ret π₁ v' | none => State.error) = _
                rw [hl₁]
              have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
                  (Moist.Verified.substTerm (pos + vs₁.length)
                    (iteratedShift vs₁.length replacement) (.Var n))) = State.ret π₂ w₂ := by
                rw [h_subst_gt]
                simp only [steps]
                show (match (foldrExtend ρ₂ vs₂).lookup (n - 1) with
                      | some v' => State.ret π₂ v' | none => State.error) = _
                rw [hl₂]
              rw [h_lhs, h_rhs]
              exact SubstBisimState.ret hv_rel hπ
    | Constant ct =>
      refine ⟨1, ?_⟩
      obtain ⟨c, bt⟩ := ct
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Constant (c, bt)) = .Constant (c, bt) := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Constant (c, bt))) =
          .ret π₁ (.VCon c) := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Constant (c, bt)))) = .ret π₂ (.VCon c) := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret (SubstBisimValue.vcon c) hπ
    | Builtin b =>
      refine ⟨1, ?_⟩
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Builtin b) = .Builtin b := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Builtin b)) =
          .ret π₁ (.VBuiltin b [] (expectedArgs b)) := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Builtin b))) =
          .ret π₂ (.VBuiltin b [] (expectedArgs b)) := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vbuiltin b (expectedArgs b) SubstBisimValueList.nil) hπ
    | Error =>
      refine ⟨1, ?_⟩
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) .Error = .Error := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) .Error) = .error := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) .Error)) = .error := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.error
    | Lam name body =>
      refine ⟨1, ?_⟩
      have hbody_closed : closedAt (d + 2 + vs₁.length) body = true := by
        simp only [closedAt] at hclosed
        have : d + 1 + vs₁.length + 1 = d + 2 + vs₁.length := by omega
        rw [← this]; exact hclosed
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Lam name body) =
          .Lam name (Moist.Verified.substTerm (pos + vs₁.length + 1)
            (Moist.Verified.renameTerm (Moist.Verified.shiftRename 1)
              (iteratedShift vs₁.length replacement)) body) := by
        simp only [Moist.Verified.substTerm]
      have h_iter_eq : Moist.Verified.renameTerm (Moist.Verified.shiftRename 1)
          (iteratedShift vs₁.length replacement) =
          iteratedShift (vs₁.length + 1) replacement := rfl
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Lam name body)) =
          .ret π₁ (.VLam body (foldrExtend ρ₁ vs₁)) := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Lam name body))) =
          .ret π₂ (.VLam (Moist.Verified.substTerm (pos + vs₁.length + 1)
            (iteratedShift (vs₁.length + 1) replacement) body)
            (foldrExtend ρ₂ vs₂)) := by
        rw [h_subst, h_iter_eq]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vlam hpos_le hrep_closed henv hvs hbody_closed h_halts) hπ
    | Delay body =>
      refine ⟨1, ?_⟩
      have hbody_closed : closedAt (d + 1 + vs₁.length) body = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Delay body) =
          .Delay (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) body) := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Delay body)) =
          .ret π₁ (.VDelay body (foldrExtend ρ₁ vs₁)) := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Delay body))) =
          .ret π₂ (.VDelay (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) body)
            (foldrExtend ρ₂ vs₂)) := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vdelay hpos_le hrep_closed henv hvs hbody_closed h_halts) hπ
    | Force e =>
      refine ⟨1, ?_⟩
      have he_closed : closedAt (d + 1 + vs₁.length) e = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Force e) =
          .Force (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) e) := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Force e)) =
          .compute (.force :: π₁) (foldrExtend ρ₁ vs₁) e := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Force e))) =
          .compute (.force :: π₂) (foldrExtend ρ₂ vs₂)
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) e) := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.compute hpos_le hrep_closed henv hvs he_closed h_halts
        (SubstBisimStack.cons SubstBisimFrame.force hπ)
    | Apply f x =>
      refine ⟨1, ?_⟩
      have h_fx : closedAt (d + 1 + vs₁.length) f = true ∧
          closedAt (d + 1 + vs₁.length) x = true := by
        simp only [closedAt, Bool.and_eq_true] at hclosed; exact hclosed
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Apply f x) =
          .Apply (Moist.Verified.substTerm (pos + vs₁.length)
                    (iteratedShift vs₁.length replacement) f)
                 (Moist.Verified.substTerm (pos + vs₁.length)
                    (iteratedShift vs₁.length replacement) x) := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Apply f x)) =
          .compute (.arg x (foldrExtend ρ₁ vs₁) :: π₁) (foldrExtend ρ₁ vs₁) f := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Apply f x))) =
          .compute (.arg (Moist.Verified.substTerm (pos + vs₁.length)
                           (iteratedShift vs₁.length replacement) x)
                        (foldrExtend ρ₂ vs₂) :: π₂)
            (foldrExtend ρ₂ vs₂)
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) f) := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.compute hpos_le hrep_closed henv hvs h_fx.1 h_halts
        (SubstBisimStack.cons
          (SubstBisimFrame.arg hpos_le hrep_closed henv hvs h_fx.2 h_halts) hπ)
    | Constr tag args =>
      cases args with
      | nil =>
        refine ⟨1, ?_⟩
        have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Constr tag []) = .Constr tag [] := by
          simp only [Moist.Verified.substTerm, Moist.Verified.substTermList]
        have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Constr tag [])) =
            .ret π₁ (.VConstr tag []) := rfl
        have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) (.Constr tag []))) =
            .ret π₂ (.VConstr tag []) := by
          rw [h_subst]; simp only [steps]; rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.ret
          (SubstBisimValue.vconstr tag SubstBisimValueList.nil) hπ
      | cons m ms =>
        refine ⟨1, ?_⟩
        have h_mms : closedAt (d + 1 + vs₁.length) m = true ∧
            closedAtList (d + 1 + vs₁.length) ms = true := by
          simp only [closedAt, closedAtList, Bool.and_eq_true] at hclosed; exact hclosed
        have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Constr tag (m :: ms)) =
            .Constr tag (Moist.Verified.substTerm (pos + vs₁.length)
                          (iteratedShift vs₁.length replacement) m ::
                         Moist.Verified.substTermList (pos + vs₁.length)
                          (iteratedShift vs₁.length replacement) ms) := by
          simp only [Moist.Verified.substTerm, Moist.Verified.substTermList]
        have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Constr tag (m :: ms))) =
            .compute (.constrField tag [] ms (foldrExtend ρ₁ vs₁) :: π₁)
              (foldrExtend ρ₁ vs₁) m := rfl
        have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) (.Constr tag (m :: ms)))) =
            .compute (.constrField tag []
              (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length replacement) ms)
              (foldrExtend ρ₂ vs₂) :: π₂)
              (foldrExtend ρ₂ vs₂)
              (Moist.Verified.substTerm (pos + vs₁.length)
                (iteratedShift vs₁.length replacement) m) := by
          rw [h_subst]; simp only [steps]; rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.compute hpos_le hrep_closed henv hvs h_mms.1 h_halts
          (SubstBisimStack.cons
            (SubstBisimFrame.constrField tag hpos_le hrep_closed
              SubstBisimValueList.nil henv hvs h_mms.2 h_halts) hπ)
    | Case scrut alts =>
      refine ⟨1, ?_⟩
      have h_sa : closedAt (d + 1 + vs₁.length) scrut = true ∧
          closedAtList (d + 1 + vs₁.length) alts = true := by
        simp only [closedAt, Bool.and_eq_true] at hclosed; exact hclosed
      have h_subst : Moist.Verified.substTerm (pos + vs₁.length)
          (iteratedShift vs₁.length replacement) (.Case scrut alts) =
          .Case (Moist.Verified.substTerm (pos + vs₁.length)
                  (iteratedShift vs₁.length replacement) scrut)
                (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length replacement) alts) := by
        simp only [Moist.Verified.substTerm]
      have h_lhs : step (.compute π₁ (foldrExtend ρ₁ vs₁) (.Case scrut alts)) =
          .compute (.caseScrutinee alts (foldrExtend ρ₁ vs₁) :: π₁)
            (foldrExtend ρ₁ vs₁) scrut := rfl
      have h_rhs : steps 1 (.compute π₂ (foldrExtend ρ₂ vs₂)
          (Moist.Verified.substTerm (pos + vs₁.length)
            (iteratedShift vs₁.length replacement) (.Case scrut alts))) =
          .compute (.caseScrutinee
            (Moist.Verified.substTermList (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) alts)
            (foldrExtend ρ₂ vs₂) :: π₂)
            (foldrExtend ρ₂ vs₂)
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length replacement) scrut) := by
        rw [h_subst]; simp only [steps]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.compute hpos_le hrep_closed henv hvs h_sa.1 h_halts
        (SubstBisimStack.cons
          (SubstBisimFrame.caseScrutinee hpos_le hrep_closed henv hvs h_sa.2 h_halts) hπ)
  | @reflCompute π₁ π₂ ρ vs₁ vs₂ t k hρ_wf hρ_len hvs hclosed hπ =>
    refine ⟨1, ?_⟩
    simp only [steps]
    cases t with
    | Var n =>
      -- Dispatch: n ∈ [1..vs.length] (use vs lookup), n > vs.length (use ρ lookup)
      by_cases hn_zero : n = 0
      · subst hn_zero
        have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Var 0)) = .error := by
          show (match (foldrExtend ρ vs₁).lookup 0 with
                | some v => State.ret π₁ v | none => State.error) = .error
          rw [lookup_zero]
        have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Var 0)) = .error := by
          show (match (foldrExtend ρ vs₂).lookup 0 with
                | some v => State.ret π₂ v | none => State.error) = .error
          rw [lookup_zero]
        rw [h_lhs, h_rhs]
        exact SubstBisimState.error
      · have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_zero
        have hn_le : n ≤ k + vs₁.length := by
          simp only [closedAt, decide_eq_true_eq] at hclosed; exact hclosed
        have hvs_len_eq : vs₁.length = vs₂.length := substBisimValueList_length_eq hvs
        by_cases hn_in_vs : n ≤ vs₁.length
        · -- n ∈ [1..vs₁.length]: lookup in vs, get bisim-related values
          have hl₁ : (foldrExtend ρ vs₁).lookup n = some (vs₁[n - 1]'(by omega)) :=
            foldrExtend_lookup_in_vs ρ vs₁ n hn_pos hn_in_vs
          have hl₂ : (foldrExtend ρ vs₂).lookup n = some (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) :=
            foldrExtend_lookup_in_vs ρ vs₂ n hn_pos (by rw [← hvs_len_eq]; exact hn_in_vs)
          have hv_rel : SubstBisimValue (vs₁[n - 1]'(by omega))
              (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) :=
            substBisimValueList_getElem hvs (n - 1) (by omega)
          have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Var n)) =
              .ret π₁ (vs₁[n - 1]'(by omega)) := by
            show (match (foldrExtend ρ vs₁).lookup n with
                  | some v => State.ret π₁ v | none => State.error) = _
            rw [hl₁]
          have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Var n)) =
              .ret π₂ (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) := by
            show (match (foldrExtend ρ vs₂).lookup n with
                  | some v => State.ret π₂ v | none => State.error) = _
            rw [hl₂]
          rw [h_lhs, h_rhs]
          exact SubstBisimState.ret hv_rel hπ
        · -- n > vs₁.length: lookup goes into ρ, same value on both sides (refl)
          have hn_gt : n > vs₁.length := Nat.not_le.mp hn_in_vs
          have hn_sub_pos : 1 ≤ n - vs₁.length := by omega
          have hn_sub_le : n - vs₁.length ≤ k := by omega
          -- Use env well-formedness to get the lookup value
          have hlookup_wf : ∀ (j : Nat) {ρ' : CekEnv},
              EnvWellFormed j ρ' → ∀ m, 1 ≤ m → m ≤ j →
              ∃ v, ρ'.lookup m = some v ∧ ValueWellFormed v := by
            intro j
            induction j with
            | zero => intros _ _ _ _ hm_le; omega
            | succ j' ih =>
              intro ρ' h' m hm_pos hm_le
              cases h' with
              | @succ _ _ v hrest _ hl hvw =>
                by_cases h_eq : m = j' + 1
                · subst h_eq; exact ⟨v, hl, hvw⟩
                · exact ih hrest m hm_pos (by omega)
          obtain ⟨v, hl_eq, hvw⟩ := hlookup_wf k hρ_wf (n - vs₁.length) hn_sub_pos hn_sub_le
          have hl₁ : (foldrExtend ρ vs₁).lookup n = some v := by
            rw [foldrExtend_lookup_above _ _ _ hn_gt]; exact hl_eq
          have hl₂ : (foldrExtend ρ vs₂).lookup n = some v := by
            have hn_gt₂ : n > vs₂.length := by rw [← hvs_len_eq]; exact hn_gt
            rw [foldrExtend_lookup_above _ _ _ hn_gt₂]
            rw [show (n - vs₂.length) = (n - vs₁.length) from by rw [hvs_len_eq]]
            exact hl_eq
          have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Var n)) = .ret π₁ v := by
            show (match (foldrExtend ρ vs₁).lookup n with
                  | some v' => State.ret π₁ v' | none => State.error) = _
            rw [hl₁]
          have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Var n)) = .ret π₂ v := by
            show (match (foldrExtend ρ vs₂).lookup n with
                  | some v' => State.ret π₂ v' | none => State.error) = _
            rw [hl₂]
          rw [h_lhs, h_rhs]
          exact SubstBisimState.ret (SubstBisimValue.refl hvw) hπ
    | Constant ct =>
      obtain ⟨c, bt⟩ := ct
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Constant (c, bt))) = .ret π₁ (.VCon c) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Constant (c, bt))) = .ret π₂ (.VCon c) := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret (SubstBisimValue.refl (ValueWellFormed.vcon c)) hπ
    | Builtin b =>
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Builtin b)) = .ret π₁ (.VBuiltin b [] (expectedArgs b)) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Builtin b)) = .ret π₂ (.VBuiltin b [] (expectedArgs b)) := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.refl (ValueWellFormed.vbuiltin b (expectedArgs b) ValueListWellFormed.nil)) hπ
    | Error =>
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) .Error) = .error := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) .Error) = .error := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.error
    | Lam name body =>
      have hbody_closed : closedAt (k + vs₁.length + 1) body = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Lam name body)) =
          .ret π₁ (.VLam body (foldrExtend ρ vs₁)) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Lam name body)) =
          .ret π₂ (.VLam body (foldrExtend ρ vs₂)) := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vlam_refl_list hρ_wf hρ_len hvs hbody_closed) hπ
    | Delay body =>
      have hbody_closed : closedAt (k + vs₁.length) body = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Delay body)) =
          .ret π₁ (.VDelay body (foldrExtend ρ vs₁)) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Delay body)) =
          .ret π₂ (.VDelay body (foldrExtend ρ vs₂)) := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vdelay_refl_list hρ_wf hρ_len hvs hbody_closed) hπ
    | Force e =>
      have he_closed : closedAt (k + vs₁.length) e = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Force e)) =
          .compute (.force :: π₁) (foldrExtend ρ vs₁) e := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Force e)) =
          .compute (.force :: π₂) (foldrExtend ρ vs₂) e := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.reflCompute hρ_wf hρ_len hvs he_closed
        (SubstBisimStack.cons SubstBisimFrame.force hπ)
    | Apply f x =>
      have h_fx : closedAt (k + vs₁.length) f = true ∧ closedAt (k + vs₁.length) x = true := by
        simp only [closedAt, Bool.and_eq_true] at hclosed; exact hclosed
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Apply f x)) =
          .compute (.arg x (foldrExtend ρ vs₁) :: π₁) (foldrExtend ρ vs₁) f := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Apply f x)) =
          .compute (.arg x (foldrExtend ρ vs₂) :: π₂) (foldrExtend ρ vs₂) f := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_fx.1
        (SubstBisimStack.cons
          (SubstBisimFrame.argRefl hρ_wf hρ_len hvs h_fx.2) hπ)
    | Constr tag args =>
      cases args with
      | nil =>
        have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Constr tag [])) =
            .ret π₁ (.VConstr tag []) := rfl
        have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Constr tag [])) =
            .ret π₂ (.VConstr tag []) := rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.ret
          (SubstBisimValue.refl (ValueWellFormed.vconstr tag ValueListWellFormed.nil)) hπ
      | cons m ms =>
        have h_mms : closedAt (k + vs₁.length) m = true ∧ closedAtList (k + vs₁.length) ms = true := by
          simp only [closedAt, closedAtList, Bool.and_eq_true] at hclosed; exact hclosed
        have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Constr tag (m :: ms))) =
            .compute (.constrField tag [] ms (foldrExtend ρ vs₁) :: π₁) (foldrExtend ρ vs₁) m := rfl
        have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Constr tag (m :: ms))) =
            .compute (.constrField tag [] ms (foldrExtend ρ vs₂) :: π₂) (foldrExtend ρ vs₂) m := rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_mms.1
          (SubstBisimStack.cons
            (SubstBisimFrame.constrFieldRefl tag ValueListWellFormed.nil hρ_wf hρ_len hvs h_mms.2) hπ)
    | Case scrut alts =>
      have h_sa : closedAt (k + vs₁.length) scrut = true ∧ closedAtList (k + vs₁.length) alts = true := by
        simp only [closedAt, Bool.and_eq_true] at hclosed; exact hclosed
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Case scrut alts)) =
          .compute (.caseScrutinee alts (foldrExtend ρ vs₁) :: π₁) (foldrExtend ρ vs₁) scrut := rfl
      have h_rhs : step (.compute π₂ (foldrExtend ρ vs₂) (.Case scrut alts)) =
          .compute (.caseScrutinee alts (foldrExtend ρ vs₂) :: π₂) (foldrExtend ρ vs₂) scrut := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_sa.1
        (SubstBisimStack.cons
          (SubstBisimFrame.caseScrutineeRefl hρ_wf hρ_len hvs h_sa.2) hπ)
  | @renameInsertCompute π₁ π₂ ρ vs₁ vs₂ vs_insert t k hρ_wf hρ_len hvs hclosed hπ =>
    refine ⟨1, ?_⟩
    simp only [steps]
    have hvs_len_eq : vs₁.length = vs₂.length := substBisimValueList_length_eq hvs
    cases t with
    | Var n =>
      by_cases hn_zero : n = 0
      · subst hn_zero
        have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Var 0) = .Var 0 := by
          rw [iterShiftRename_Var]
          have : ¬ (0 ≥ vs₁.length + 1) := by omega
          rw [if_neg this]
        have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Var 0)) = .error := by
          show (match (foldrExtend ρ vs₁).lookup 0 with
                | some v => State.ret π₁ v | none => State.error) = .error
          rw [lookup_zero]
        have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
            (iterShiftRename vs_insert.length (vs₁.length + 1) (.Var 0))) = .error := by
          rw [h_rhs_term]
          show (match (foldrExtend (foldrExtend ρ vs_insert) vs₂).lookup 0 with
                | some v => State.ret π₂ v | none => State.error) = .error
          rw [lookup_zero]
        rw [h_lhs, h_rhs]
        exact SubstBisimState.error
      · have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_zero
        have hn_le : n ≤ k + vs₁.length := by
          simp only [closedAt, decide_eq_true_eq] at hclosed; exact hclosed
        by_cases hn_in_vs : n ≤ vs₁.length
        · -- n ∈ vs region: no shift, positional bisim-lookup
          have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Var n) = .Var n := by
            rw [iterShiftRename_Var]
            have : ¬ (n ≥ vs₁.length + 1) := by omega
            rw [if_neg this]
          have hl₁ : (foldrExtend ρ vs₁).lookup n = some (vs₁[n - 1]'(by omega)) :=
            foldrExtend_lookup_in_vs ρ vs₁ n hn_pos hn_in_vs
          have hn_in_vs₂ : n ≤ vs₂.length := by rw [← hvs_len_eq]; exact hn_in_vs
          have hl₂ : (foldrExtend (foldrExtend ρ vs_insert) vs₂).lookup n =
              some (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) :=
            foldrExtend_lookup_in_vs (foldrExtend ρ vs_insert) vs₂ n hn_pos hn_in_vs₂
          have hv_rel : SubstBisimValue (vs₁[n - 1]'(by omega))
              (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) :=
            substBisimValueList_getElem hvs (n - 1) (by omega)
          have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Var n)) =
              State.ret π₁ (vs₁[n - 1]'(by omega)) := by
            show (match (foldrExtend ρ vs₁).lookup n with
                  | some v => State.ret π₁ v | none => State.error) = _
            rw [hl₁]
          have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
              (iterShiftRename vs_insert.length (vs₁.length + 1) (.Var n))) =
              State.ret π₂ (vs₂[n - 1]'(by rw [← hvs_len_eq]; omega)) := by
            rw [h_rhs_term]
            show (match (foldrExtend (foldrExtend ρ vs_insert) vs₂).lookup n with
                  | some v => State.ret π₂ v | none => State.error) = _
            rw [hl₂]
          rw [h_lhs, h_rhs]
          exact SubstBisimState.ret hv_rel hπ
        · -- n > vs₁.length: look up in ρ on LHS; RHS shifts by vs_insert.length to skip vs_insert
          have hn_gt : n > vs₁.length := Nat.not_le.mp hn_in_vs
          have hn_sub_pos : 1 ≤ n - vs₁.length := by omega
          have hn_sub_le : n - vs₁.length ≤ k := by omega
          have hlookup_wf : ∀ (j : Nat) {ρ' : CekEnv},
              EnvWellFormed j ρ' → ∀ m, 1 ≤ m → m ≤ j →
              ∃ v, ρ'.lookup m = some v ∧ ValueWellFormed v := by
            intro j
            induction j with
            | zero => intros _ _ _ _ hm_le; omega
            | succ j' ih =>
              intro ρ' h' m hm_pos hm_le
              cases h' with
              | @succ _ _ v hrest _ hl hvw =>
                by_cases h_eq : m = j' + 1
                · subst h_eq; exact ⟨v, hl, hvw⟩
                · exact ih hrest m hm_pos (by omega)
          obtain ⟨v, hl_eq, hvw⟩ := hlookup_wf k hρ_wf (n - vs₁.length) hn_sub_pos hn_sub_le
          -- RHS shift: iterShiftRename vs_insert.length (vs₁.length+1) shifts n by vs_insert.length
          have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Var n) =
              .Var (n + vs_insert.length) := by
            rw [iterShiftRename_Var]
            have h_ge : n ≥ vs₁.length + 1 := by omega
            rw [if_pos h_ge]
          -- LHS lookup in foldrExtend ρ vs₁: goes to ρ.lookup (n - vs₁.length)
          have hl₁ : (foldrExtend ρ vs₁).lookup n = some v := by
            rw [foldrExtend_lookup_above _ _ _ hn_gt]; exact hl_eq
          -- RHS lookup at (n + vs_insert.length) in foldrExtend (foldrExtend ρ vs_insert) vs₂.
          -- Since n + vs_insert.length > vs₂.length, goes to (foldrExtend ρ vs_insert).
          have hn_plus_gt_vs₂ : n + vs_insert.length > vs₂.length := by
            rw [← hvs_len_eq]; omega
          have hρext_lookup : (foldrExtend (foldrExtend ρ vs_insert) vs₂).lookup
              (n + vs_insert.length) =
              (foldrExtend ρ vs_insert).lookup (n + vs_insert.length - vs₂.length) :=
            foldrExtend_lookup_above _ _ _ hn_plus_gt_vs₂
          -- n + vs_insert.length - vs₂.length = (n - vs₁.length) + vs_insert.length
          have hsub_eq : n + vs_insert.length - vs₂.length =
              (n - vs₁.length) + vs_insert.length := by
            rw [hvs_len_eq]; omega
          -- (foldrExtend ρ vs_insert).lookup ((n - vs₁.length) + vs_insert.length):
          -- This is > vs_insert.length (since n - vs₁.length ≥ 1), goes to ρ.
          have hinsert_gt : (n - vs₁.length) + vs_insert.length > vs_insert.length := by omega
          have hρinsert_lookup : (foldrExtend ρ vs_insert).lookup
              ((n - vs₁.length) + vs_insert.length) =
              ρ.lookup ((n - vs₁.length) + vs_insert.length - vs_insert.length) :=
            foldrExtend_lookup_above _ _ _ hinsert_gt
          have hsimp : (n - vs₁.length) + vs_insert.length - vs_insert.length =
              n - vs₁.length := by omega
          have hl₂ : (foldrExtend (foldrExtend ρ vs_insert) vs₂).lookup
              (n + vs_insert.length) = some v := by
            rw [hρext_lookup, hsub_eq, hρinsert_lookup, hsimp]; exact hl_eq
          have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Var n)) = State.ret π₁ v := by
            show (match (foldrExtend ρ vs₁).lookup n with
                  | some v' => State.ret π₁ v' | none => State.error) = _
            rw [hl₁]
          have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
              (iterShiftRename vs_insert.length (vs₁.length + 1) (.Var n))) =
              State.ret π₂ v := by
            rw [h_rhs_term]
            show (match (foldrExtend (foldrExtend ρ vs_insert) vs₂).lookup (n + vs_insert.length) with
                  | some v' => State.ret π₂ v' | none => State.error) = _
            rw [hl₂]
          rw [h_lhs, h_rhs]
          exact SubstBisimState.ret (SubstBisimValue.refl hvw) hπ
    | Constant ct =>
      obtain ⟨c, bt⟩ := ct
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Constant (c, bt)) =
          .Constant (c, bt) := iterShiftRename_Constant _ _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Constant (c, bt))) =
          .ret π₁ (.VCon c) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Constant (c, bt)))) =
          .ret π₂ (.VCon c) := by rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret (SubstBisimValue.vcon c) hπ
    | Builtin b =>
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Builtin b) =
          .Builtin b := iterShiftRename_Builtin _ _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Builtin b)) =
          .ret π₁ (.VBuiltin b [] (expectedArgs b)) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Builtin b))) =
          .ret π₂ (.VBuiltin b [] (expectedArgs b)) := by rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vbuiltin b (expectedArgs b) SubstBisimValueList.nil) hπ
    | Error =>
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) .Error = .Error :=
        iterShiftRename_Error _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) .Error) = .error := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) .Error)) = .error := by
        rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.error
    | Lam name body =>
      have hbody_closed : closedAt (k + vs₁.length + 1) body = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Lam name body) =
          .Lam name (iterShiftRename vs_insert.length (vs₁.length + 2) body) :=
        iterShiftRename_Lam _ _ _ _ (by omega)
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Lam name body)) =
          .ret π₁ (.VLam body (foldrExtend ρ vs₁)) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Lam name body))) =
          .ret π₂ (.VLam (iterShiftRename vs_insert.length (vs₁.length + 2) body)
            (foldrExtend (foldrExtend ρ vs_insert) vs₂)) := by
        rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vlam_rename_list hρ_wf hρ_len hvs hbody_closed) hπ
    | Delay body =>
      have hbody_closed : closedAt (k + vs₁.length) body = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Delay body) =
          .Delay (iterShiftRename vs_insert.length (vs₁.length + 1) body) :=
        iterShiftRename_Delay _ _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Delay body)) =
          .ret π₁ (.VDelay body (foldrExtend ρ vs₁)) := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Delay body))) =
          .ret π₂ (.VDelay (iterShiftRename vs_insert.length (vs₁.length + 1) body)
            (foldrExtend (foldrExtend ρ vs_insert) vs₂)) := by
        rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.ret
        (SubstBisimValue.vdelay_rename_list hρ_wf hρ_len hvs hbody_closed) hπ
    | Force e =>
      have he_closed : closedAt (k + vs₁.length) e = true := by
        simp only [closedAt] at hclosed; exact hclosed
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Force e) =
          .Force (iterShiftRename vs_insert.length (vs₁.length + 1) e) :=
        iterShiftRename_Force _ _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Force e)) =
          .compute (.force :: π₁) (foldrExtend ρ vs₁) e := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Force e))) =
          .compute (.force :: π₂) (foldrExtend (foldrExtend ρ vs_insert) vs₂)
            (iterShiftRename vs_insert.length (vs₁.length + 1) e) := by
        rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs he_closed
        (SubstBisimStack.cons SubstBisimFrame.force hπ)
    | Apply f x =>
      have h_fx : closedAt (k + vs₁.length) f = true ∧ closedAt (k + vs₁.length) x = true := by
        simp only [closedAt, Bool.and_eq_true] at hclosed; exact hclosed
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Apply f x) =
          .Apply (iterShiftRename vs_insert.length (vs₁.length + 1) f)
                 (iterShiftRename vs_insert.length (vs₁.length + 1) x) :=
        iterShiftRename_Apply _ _ _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Apply f x)) =
          .compute (.arg x (foldrExtend ρ vs₁) :: π₁) (foldrExtend ρ vs₁) f := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Apply f x))) =
          .compute (.arg (iterShiftRename vs_insert.length (vs₁.length + 1) x)
                        (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂)
            (foldrExtend (foldrExtend ρ vs_insert) vs₂)
            (iterShiftRename vs_insert.length (vs₁.length + 1) f) := by
        rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_fx.1
        (SubstBisimStack.cons
          (SubstBisimFrame.argRenameInsert hρ_wf hρ_len hvs h_fx.2) hπ)
    | Constr tag args =>
      cases args with
      | nil =>
        have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1) (.Constr tag []) =
            .Constr tag [] := by
          rw [iterShiftRename_Constr]
          rw [iterShiftRenameList_nil]
        have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Constr tag [])) =
            .ret π₁ (.VConstr tag []) := rfl
        have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
            (iterShiftRename vs_insert.length (vs₁.length + 1) (.Constr tag []))) =
            .ret π₂ (.VConstr tag []) := by rw [h_rhs_term]; rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.ret
          (SubstBisimValue.vconstr tag SubstBisimValueList.nil) hπ
      | cons m ms =>
        have h_mms : closedAt (k + vs₁.length) m = true ∧
            closedAtList (k + vs₁.length) ms = true := by
          simp only [closedAt, closedAtList, Bool.and_eq_true] at hclosed; exact hclosed
        have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1)
            (.Constr tag (m :: ms)) =
            .Constr tag (iterShiftRename vs_insert.length (vs₁.length + 1) m ::
                         iterShiftRenameList vs_insert.length (vs₁.length + 1) ms) := by
          rw [iterShiftRename_Constr]
          rw [iterShiftRenameList_cons]
        have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Constr tag (m :: ms))) =
            .compute (.constrField tag [] ms (foldrExtend ρ vs₁) :: π₁)
              (foldrExtend ρ vs₁) m := rfl
        have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
            (iterShiftRename vs_insert.length (vs₁.length + 1) (.Constr tag (m :: ms)))) =
            .compute (.constrField tag []
              (iterShiftRenameList vs_insert.length (vs₁.length + 1) ms)
              (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂)
              (foldrExtend (foldrExtend ρ vs_insert) vs₂)
              (iterShiftRename vs_insert.length (vs₁.length + 1) m) := by
          rw [h_rhs_term]; rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_mms.1
          (SubstBisimStack.cons
            (SubstBisimFrame.constrFieldRenameInsert tag hρ_wf hρ_len
              SubstBisimValueList.nil hvs h_mms.2) hπ)
    | Case scrut alts =>
      have h_sa : closedAt (k + vs₁.length) scrut = true ∧
          closedAtList (k + vs₁.length) alts = true := by
        simp only [closedAt, Bool.and_eq_true] at hclosed; exact hclosed
      have h_rhs_term : iterShiftRename vs_insert.length (vs₁.length + 1)
          (.Case scrut alts) =
          .Case (iterShiftRename vs_insert.length (vs₁.length + 1) scrut)
                (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts) :=
        iterShiftRename_Case _ _ _ _
      have h_lhs : step (.compute π₁ (foldrExtend ρ vs₁) (.Case scrut alts)) =
          .compute (.caseScrutinee alts (foldrExtend ρ vs₁) :: π₁)
            (foldrExtend ρ vs₁) scrut := rfl
      have h_rhs : step (.compute π₂ (foldrExtend (foldrExtend ρ vs_insert) vs₂)
          (iterShiftRename vs_insert.length (vs₁.length + 1) (.Case scrut alts))) =
          .compute (.caseScrutinee
            (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)
            (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂)
            (foldrExtend (foldrExtend ρ vs_insert) vs₂)
            (iterShiftRename vs_insert.length (vs₁.length + 1) scrut) := by
        rw [h_rhs_term]; rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_sa.1
        (SubstBisimStack.cons
          (SubstBisimFrame.caseScrutineeRenameInsert hρ_wf hρ_len hvs h_sa.2) hπ)
  | @ret π₁ π₂ v₁ v₂ h_v h_π =>
    cases h_π with
    | nil =>
      refine ⟨1, ?_⟩
      show SubstBisimState (step (.ret [] v₁)) (steps 1 (.ret [] v₂))
      simp only [steps]
      have h_lhs : step (.ret [] v₁) = .halt v₁ := rfl
      have h_rhs : step (.ret [] v₂) = .halt v₂ := rfl
      rw [h_lhs, h_rhs]
      exact SubstBisimState.halt h_v
    | @cons f₁ f₂ π₁' π₂' h_f h_rest =>
      refine ⟨1, ?_⟩
      show SubstBisimState (step (.ret (f₁ :: π₁') v₁)) (steps 1 (.ret (f₂ :: π₂') v₂))
      simp only [steps]
      show SubstBisimState (step (.ret (f₁ :: π₁') v₁)) (step (.ret (f₂ :: π₂') v₂))
      cases h_f with
      | force =>
        cases h_v with
        | vcon c =>
          have h_lhs : step (.ret (.force :: π₁') (.VCon c)) = .error := rfl
          have h_rhs : step (.ret (.force :: π₂') (.VCon c)) = .error := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.error
        | @vlam body ρ₁ ρ₂ vs₁ vs₂ pos rep v_repl d hpos hrep henv hvs hclosed h_halts =>
          have h_lhs : step (.ret (.force :: π₁')
              (.VLam body (foldrExtend ρ₁ vs₁))) = .error := rfl
          have h_rhs : step (.ret (.force :: π₂')
              (.VLam (Moist.Verified.substTerm (pos + vs₁.length + 1)
                (iteratedShift (vs₁.length + 1) rep) body) (foldrExtend ρ₂ vs₂))) = .error := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.error
        | @vdelay body ρ₁ ρ₂ vs₁ vs₂ pos rep v_repl d hpos hrep henv hvs hclosed h_halts =>
          have h_lhs : step (.ret (.force :: π₁')
              (.VDelay body (foldrExtend ρ₁ vs₁))) =
              .compute π₁' (foldrExtend ρ₁ vs₁) body := rfl
          have h_rhs : step (.ret (.force :: π₂')
              (.VDelay (Moist.Verified.substTerm (pos + vs₁.length)
                (iteratedShift vs₁.length rep) body) (foldrExtend ρ₂ vs₂))) =
              .compute π₂' (foldrExtend ρ₂ vs₂)
                (Moist.Verified.substTerm (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) body) := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.compute hpos hrep henv hvs hclosed h_halts h_rest
        | @vconstr tag fs₁ fs₂ hfs =>
          have h_lhs : step (.ret (.force :: π₁') (.VConstr tag fs₁)) = .error := rfl
          have h_rhs : step (.ret (.force :: π₂') (.VConstr tag fs₂)) = .error := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.error
        | @vbuiltin b ea args₁ args₂ hargs =>
          cases ea with
          | one k =>
            cases k with
            | argV => exact SubstBisimState.error
            | argQ =>
              have ⟨h_some, h_iff⟩ :=
                @substBisimValueList_evalBuiltin b args₁ args₂ hargs
              cases he₁ : evalBuiltin b args₁ with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show SubstBisimState
                  (match evalBuiltin b args₁ with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b args₂ with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact SubstBisimState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b args₂ = none := h_iff.mp he₁
                show SubstBisimState
                  (match evalBuiltin b args₁ with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b args₂ with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact SubstBisimState.error
          | more k rest =>
            cases k with
            | argV => exact SubstBisimState.error
            | argQ =>
              exact SubstBisimState.ret
                (SubstBisimValue.vbuiltin b rest hargs) h_rest
        | @vlam_refl_list body ρ vs₁ vs₂ k hρ_wf hρ_len hvs hbody_closed =>
          exact SubstBisimState.error
        | @vdelay_refl_list body ρ vs₁ vs₂ k hρ_wf hρ_len hvs hbody_closed =>
          have h_lhs : step (.ret (.force :: π₁')
              (.VDelay body (foldrExtend ρ vs₁))) =
              .compute π₁' (foldrExtend ρ vs₁) body := rfl
          have h_rhs : step (.ret (.force :: π₂')
              (.VDelay body (foldrExtend ρ vs₂))) =
              .compute π₂' (foldrExtend ρ vs₂) body := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.reflCompute hρ_wf hρ_len hvs hbody_closed h_rest
        | @vlam_rename_list body ρ vs₁ vs₂ vs_insert k _ _ _ _ =>
          exact SubstBisimState.error
        | @vdelay_rename_list body ρ vs₁ vs₂ vs_insert k hρ_wf hρ_len hvs hbody_closed =>
          exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs hbody_closed h_rest
        | refl hv_wf =>
          cases v₁ with
          | VCon c => exact SubstBisimState.error
          | VLam body ρ => exact SubstBisimState.error
          | VConstr tag fs => exact SubstBisimState.error
          | VDelay body ρ =>
            have h_lhs : step (.ret (.force :: π₁') (.VDelay body ρ)) = .compute π₁' ρ body := rfl
            have h_rhs : step (.ret (.force :: π₂') (.VDelay body ρ)) = .compute π₂' ρ body := rfl
            rw [h_lhs, h_rhs]
            cases hv_wf with
            | @vdelay _ _ k hρ_wf hρ_len hbody_closed =>
              -- Use reflCompute with vs = []
              exact SubstBisimState.reflCompute (vs₁ := []) (vs₂ := []) hρ_wf hρ_len
                SubstBisimValueList.nil (by simp; exact hbody_closed) h_rest
          | VBuiltin b args ea =>
            have hargs_wf : ValueListWellFormed args := by cases hv_wf; assumption
            have hargs_refl : SubstBisimValueList args args :=
              substBisimValueList_refl_wf hargs_wf
            cases ea with
            | one k =>
              cases k with
              | argV => exact SubstBisimState.error
              | argQ =>
                cases he₁ : evalBuiltin b args with
                | some v_r =>
                  show SubstBisimState
                    (match evalBuiltin b args with | some v => .ret π₁' v | none => .error)
                    (match evalBuiltin b args with | some v => .ret π₂' v | none => .error)
                  rw [he₁]
                  have hv_r_wf : ValueWellFormed v_r := evalBuiltin_wf hargs_wf he₁
                  exact SubstBisimState.ret (SubstBisimValue.refl hv_r_wf) h_rest
                | none =>
                  show SubstBisimState
                    (match evalBuiltin b args with | some v => .ret π₁' v | none => .error)
                    (match evalBuiltin b args with | some v => .ret π₂' v | none => .error)
                  rw [he₁]
                  exact SubstBisimState.error
            | more k rest =>
              cases k with
              | argV => exact SubstBisimState.error
              | argQ =>
                exact SubstBisimState.ret
                  (SubstBisimValue.vbuiltin b rest hargs_refl) h_rest
      | @arg t ρ₁ ρ₂ vs₁ vs₂ pos rep v_repl d hpos hrep henv hvs hclosed h_halts =>
        have h_lhs : step (.ret (.arg t (foldrExtend ρ₁ vs₁) :: π₁') v₁) =
            .compute (.funV v₁ :: π₁') (foldrExtend ρ₁ vs₁) t := rfl
        have h_rhs : step (.ret (.arg
            (Moist.Verified.substTerm (pos + vs₁.length)
              (iteratedShift vs₁.length rep) t) (foldrExtend ρ₂ vs₂) :: π₂') v₂) =
            .compute (.funV v₂ :: π₂') (foldrExtend ρ₂ vs₂)
              (Moist.Verified.substTerm (pos + vs₁.length)
                (iteratedShift vs₁.length rep) t) := rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.compute hpos hrep henv hvs hclosed h_halts
          (SubstBisimStack.cons (SubstBisimFrame.funV h_v) h_rest)
      | @funV v_f₁ v_f₂ h_vf =>
        cases h_vf with
        | vcon c =>
          have h_lhs : step (.ret (.funV (.VCon c) :: π₁') v₁) = .error := rfl
          have h_rhs : step (.ret (.funV (.VCon c) :: π₂') v₂) = .error := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.error
        | @vlam body ρ_l₁ ρ_l₂ vs_l₁ vs_l₂ pos rep v_repl d hpos hrep henv hvs_l hclosed h_halts =>
          -- funV (subst-family VLam) + v: extend vs with v₁ and v₂, continue computing body
          have hvs_len_eq : vs_l₁.length = vs_l₂.length := substBisimValueList_length_eq hvs_l
          have h_lhs : step (.ret (.funV (.VLam body (foldrExtend ρ_l₁ vs_l₁)) :: π₁') v₁) =
              .compute π₁' ((foldrExtend ρ_l₁ vs_l₁).extend v₁) body := rfl
          have h_rhs : step (.ret (.funV (.VLam
              (Moist.Verified.substTerm (pos + vs_l₁.length + 1)
                (iteratedShift (vs_l₁.length + 1) rep) body) (foldrExtend ρ_l₂ vs_l₂)) :: π₂') v₂) =
              .compute π₂' ((foldrExtend ρ_l₂ vs_l₂).extend v₂)
                (Moist.Verified.substTerm (pos + vs_l₁.length + 1)
                  (iteratedShift (vs_l₁.length + 1) rep) body) := rfl
          rw [h_lhs, h_rhs]
          -- New vs: v₁ :: vs_l₁, v₂ :: vs_l₂
          have hvs_new : SubstBisimValueList (v₁ :: vs_l₁) (v₂ :: vs_l₂) :=
            SubstBisimValueList.cons h_v hvs_l
          -- Body closedness: (v₁ :: vs_l₁).length = vs_l₁.length + 1, so d + 1 + (vs_l₁.length + 1) = d + 2 + vs_l₁.length.
          have hbody_new : closedAt (d + 1 + (v₁ :: vs_l₁).length) body = true := by
            show closedAt (d + 1 + (vs_l₁.length + 1)) body = true
            have : d + 1 + (vs_l₁.length + 1) = d + 2 + vs_l₁.length := by omega
            rw [this]; exact hclosed
          -- Transform goal to match the new compute constructor's expected shape.
          show SubstBisimState
            (.compute π₁' ((foldrExtend ρ_l₁ vs_l₁).extend v₁) body)
            (.compute π₂' ((foldrExtend ρ_l₂ vs_l₂).extend v₂)
              (Moist.Verified.substTerm (pos + vs_l₁.length + 1)
                (iteratedShift (vs_l₁.length + 1) rep) body))
          -- Rewrite env to use foldrExtend with cons.
          have h_env₁ : (foldrExtend ρ_l₁ vs_l₁).extend v₁ = foldrExtend ρ_l₁ (v₁ :: vs_l₁) := rfl
          have h_env₂ : (foldrExtend ρ_l₂ vs_l₂).extend v₂ = foldrExtend ρ_l₂ (v₂ :: vs_l₂) := rfl
          -- Rewrite (v₁ :: vs_l₁).length = vs_l₁.length + 1 for term shape match.
          have h_len : (v₁ :: vs_l₁).length = vs_l₁.length + 1 := rfl
          rw [h_env₁, h_env₂]
          show SubstBisimState
            (.compute π₁' (foldrExtend ρ_l₁ (v₁ :: vs_l₁)) body)
            (.compute π₂' (foldrExtend ρ_l₂ (v₂ :: vs_l₂))
              (Moist.Verified.substTerm (pos + vs_l₁.length + 1)
                (iteratedShift (vs_l₁.length + 1) rep) body))
          -- Use the generalized compute constructor.
          -- Need to show pos + vs_l₁.length + 1 = pos + (v₁ :: vs_l₁).length, and similarly for iteratedShift.
          have h_pos_eq : pos + vs_l₁.length + 1 = pos + (v₁ :: vs_l₁).length := rfl
          have h_iter_eq : iteratedShift (vs_l₁.length + 1) rep = iteratedShift (v₁ :: vs_l₁).length rep := rfl
          rw [h_pos_eq, h_iter_eq]
          exact SubstBisimState.compute hpos hrep henv hvs_new hbody_new h_halts h_rest
        | @vdelay body_d ρ_d₁ ρ_d₂ vs_d₁ vs_d₂ pos_d rep_d v_repl_d d_d _ _ _ _ _ _ =>
          have h_lhs : step (.ret (.funV (.VDelay body_d (foldrExtend ρ_d₁ vs_d₁)) :: π₁') v₁) = .error := rfl
          have h_rhs : step (.ret (.funV
              (.VDelay (Moist.Verified.substTerm (pos_d + vs_d₁.length)
                (iteratedShift vs_d₁.length rep_d) body_d) (foldrExtend ρ_d₂ vs_d₂)) :: π₂') v₂) = .error := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.error
        | @vconstr tag fs₁ fs₂ _ =>
          have h_lhs : step (.ret (.funV (.VConstr tag fs₁) :: π₁') v₁) = .error := rfl
          have h_rhs : step (.ret (.funV (.VConstr tag fs₂) :: π₂') v₂) = .error := rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.error
        | @vbuiltin b ea args_f₁ args_f₂ hargs_f =>
          cases ea with
          | one k =>
            cases k with
            | argQ => exact SubstBisimState.error
            | argV =>
              have h_extended : SubstBisimValueList (v₁ :: args_f₁) (v₂ :: args_f₂) :=
                SubstBisimValueList.cons h_v hargs_f
              have ⟨h_some, h_iff⟩ := @substBisimValueList_evalBuiltin b _ _ h_extended
              cases he₁ : evalBuiltin b (v₁ :: args_f₁) with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show SubstBisimState
                  (match evalBuiltin b (v₁ :: args_f₁) with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v₂ :: args_f₂) with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact SubstBisimState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b (v₂ :: args_f₂) = none := h_iff.mp he₁
                show SubstBisimState
                  (match evalBuiltin b (v₁ :: args_f₁) with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v₂ :: args_f₂) with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact SubstBisimState.error
          | more k rest =>
            cases k with
            | argQ => exact SubstBisimState.error
            | argV =>
              exact SubstBisimState.ret
                (SubstBisimValue.vbuiltin b rest (SubstBisimValueList.cons h_v hargs_f))
                h_rest
        | @vlam_refl_list body ρ vs_l₁ vs_l₂ k hρ_wf hρ_len hvs_l hbody_closed =>
          -- funV (refl-list VLam) + v: extend vs_l, continue with reflCompute.
          have h_lhs : step (.ret (.funV (.VLam body (foldrExtend ρ vs_l₁)) :: π₁') v₁) =
              .compute π₁' ((foldrExtend ρ vs_l₁).extend v₁) body := rfl
          have h_rhs : step (.ret (.funV (.VLam body (foldrExtend ρ vs_l₂)) :: π₂') v₂) =
              .compute π₂' ((foldrExtend ρ vs_l₂).extend v₂) body := rfl
          rw [h_lhs, h_rhs]
          have h_env₁ : (foldrExtend ρ vs_l₁).extend v₁ = foldrExtend ρ (v₁ :: vs_l₁) := rfl
          have h_env₂ : (foldrExtend ρ vs_l₂).extend v₂ = foldrExtend ρ (v₂ :: vs_l₂) := rfl
          rw [h_env₁, h_env₂]
          have hvs_new : SubstBisimValueList (v₁ :: vs_l₁) (v₂ :: vs_l₂) :=
            SubstBisimValueList.cons h_v hvs_l
          have hbody_new : closedAt (k + (v₁ :: vs_l₁).length) body = true := by
            show closedAt (k + (vs_l₁.length + 1)) body = true
            have : k + (vs_l₁.length + 1) = k + vs_l₁.length + 1 := by omega
            rw [this]; exact hbody_closed
          exact SubstBisimState.reflCompute hρ_wf hρ_len hvs_new hbody_new h_rest
        | @vdelay_refl_list body ρ vs_l₁ vs_l₂ k _ _ _ _ =>
          -- funV VDelay: error
          exact SubstBisimState.error
        | @vlam_rename_list body ρ vs_l₁ vs_l₂ vs_insert k hρ_wf hρ_len hvs_l hbody_closed =>
          have hvs_new : SubstBisimValueList (v₁ :: vs_l₁) (v₂ :: vs_l₂) :=
            SubstBisimValueList.cons h_v hvs_l
          have hbody_new : closedAt (k + (v₁ :: vs_l₁).length) body = true := by
            show closedAt (k + (vs_l₁.length + 1)) body = true
            have : k + (vs_l₁.length + 1) = k + vs_l₁.length + 1 := by omega
            rw [this]; exact hbody_closed
          show SubstBisimState
            (.compute π₁' (foldrExtend ρ (v₁ :: vs_l₁)) body)
            (.compute π₂' (foldrExtend (foldrExtend ρ vs_insert) (v₂ :: vs_l₂))
              (iterShiftRename vs_insert.length ((v₁ :: vs_l₁).length + 1) body))
          exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs_new hbody_new h_rest
        | @vdelay_rename_list body ρ vs_l₁ vs_l₂ vs_insert k _ _ _ _ =>
          exact SubstBisimState.error
        | refl hv_f_wf =>
          -- funV (refl v) + v: dispatch on v's shape.
          cases v_f₁ with
          | VCon _ => exact SubstBisimState.error
          | @VLam body ρ_l =>
            -- funV (VLam body ρ_l) + v: compute π' (ρ_l.extend v_i) body on each side.
            have h_lhs : step (.ret (.funV (.VLam body ρ_l) :: π₁') v₁) =
                .compute π₁' (ρ_l.extend v₁) body := rfl
            have h_rhs : step (.ret (.funV (.VLam body ρ_l) :: π₂') v₂) =
                .compute π₂' (ρ_l.extend v₂) body := rfl
            rw [h_lhs, h_rhs]
            cases hv_f_wf with
            | @vlam _ _ k hρ_wf hρ_len hbody_closed =>
              -- Use reflCompute with vs = [v₁], [v₂], ρ = ρ_l
              have hvs_new : SubstBisimValueList [v₁] [v₂] :=
                SubstBisimValueList.cons h_v SubstBisimValueList.nil
              have hbody_new : closedAt (k + [v₁].length) body = true := by
                show closedAt (k + 1) body = true; exact hbody_closed
              have h_env₁ : ρ_l.extend v₁ = foldrExtend ρ_l [v₁] := rfl
              have h_env₂ : ρ_l.extend v₂ = foldrExtend ρ_l [v₂] := rfl
              rw [h_env₁, h_env₂]
              exact SubstBisimState.reflCompute hρ_wf hρ_len hvs_new hbody_new h_rest
          | VDelay body ρ => exact SubstBisimState.error
          | VConstr tag fs => exact SubstBisimState.error
          | VBuiltin b args ea =>
            have hargs_wf : ValueListWellFormed args := by cases hv_f_wf; assumption
            have hargs_refl : SubstBisimValueList args args :=
              substBisimValueList_refl_wf hargs_wf
            cases ea with
            | one k =>
              cases k with
              | argQ => exact SubstBisimState.error
              | argV =>
                have h_extended : SubstBisimValueList (v₁ :: args) (v₂ :: args) :=
                  SubstBisimValueList.cons h_v hargs_refl
                have ⟨h_some, h_iff⟩ := @substBisimValueList_evalBuiltin b _ _ h_extended
                cases he₁ : evalBuiltin b (v₁ :: args) with
                | some v_r₁ =>
                  obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                  show SubstBisimState
                    (match evalBuiltin b (v₁ :: args) with | some v => .ret π₁' v | none => .error)
                    (match evalBuiltin b (v₂ :: args) with | some v => .ret π₂' v | none => .error)
                  rw [he₁, he₂]
                  exact SubstBisimState.ret h_v_rel h_rest
                | none =>
                  have he₂ : evalBuiltin b (v₂ :: args) = none := h_iff.mp he₁
                  show SubstBisimState
                    (match evalBuiltin b (v₁ :: args) with | some v => .ret π₁' v | none => .error)
                    (match evalBuiltin b (v₂ :: args) with | some v => .ret π₂' v | none => .error)
                  rw [he₁, he₂]
                  exact SubstBisimState.error
            | more k rest =>
              cases k with
              | argQ => exact SubstBisimState.error
              | argV =>
                exact SubstBisimState.ret
                  (SubstBisimValue.vbuiltin b rest (SubstBisimValueList.cons h_v hargs_refl)) h_rest
      | @applyArg v_x₁ v_x₂ h_vx =>
        cases h_v with
        | vcon _ =>
          exact SubstBisimState.error
        | @vlam body ρ_l₁ ρ_l₂ vs_l₁ vs_l₂ pos rep v_repl d hpos hrep henv hvs_l hclosed h_halts =>
          have h_lhs : step (.ret (.applyArg v_x₁ :: π₁') (.VLam body (foldrExtend ρ_l₁ vs_l₁))) =
              .compute π₁' ((foldrExtend ρ_l₁ vs_l₁).extend v_x₁) body := rfl
          have h_rhs : step (.ret (.applyArg v_x₂ :: π₂')
              (.VLam (Moist.Verified.substTerm (pos + vs_l₁.length + 1)
                (iteratedShift (vs_l₁.length + 1) rep) body) (foldrExtend ρ_l₂ vs_l₂))) =
              .compute π₂' ((foldrExtend ρ_l₂ vs_l₂).extend v_x₂)
                (Moist.Verified.substTerm (pos + vs_l₁.length + 1)
                  (iteratedShift (vs_l₁.length + 1) rep) body) := rfl
          rw [h_lhs, h_rhs]
          have h_env₁ : (foldrExtend ρ_l₁ vs_l₁).extend v_x₁ = foldrExtend ρ_l₁ (v_x₁ :: vs_l₁) := rfl
          have h_env₂ : (foldrExtend ρ_l₂ vs_l₂).extend v_x₂ = foldrExtend ρ_l₂ (v_x₂ :: vs_l₂) := rfl
          rw [h_env₁, h_env₂]
          have hvs_new : SubstBisimValueList (v_x₁ :: vs_l₁) (v_x₂ :: vs_l₂) :=
            SubstBisimValueList.cons h_vx hvs_l
          have hbody_new : closedAt (d + 1 + (v_x₁ :: vs_l₁).length) body = true := by
            show closedAt (d + 1 + (vs_l₁.length + 1)) body = true
            have : d + 1 + (vs_l₁.length + 1) = d + 2 + vs_l₁.length := by omega
            rw [this]; exact hclosed
          exact SubstBisimState.compute hpos hrep henv hvs_new hbody_new h_halts h_rest
        | @vdelay body_d ρ_d₁ ρ_d₂ vs_d₁ vs_d₂ pos_d rep_d v_repl_d d_d _ _ _ _ _ _ =>
          exact SubstBisimState.error
        | @vconstr tag fs₁ fs₂ _ =>
          exact SubstBisimState.error
        | @vbuiltin b ea args₁ args₂ hargs =>
          cases ea with
          | one k =>
            cases k with
            | argQ => exact SubstBisimState.error
            | argV =>
              have h_extended : SubstBisimValueList (v_x₁ :: args₁) (v_x₂ :: args₂) :=
                SubstBisimValueList.cons h_vx hargs
              have ⟨h_some, h_iff⟩ := @substBisimValueList_evalBuiltin b _ _ h_extended
              cases he₁ : evalBuiltin b (v_x₁ :: args₁) with
              | some v_r₁ =>
                obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                show SubstBisimState
                  (match evalBuiltin b (v_x₁ :: args₁) with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v_x₂ :: args₂) with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact SubstBisimState.ret h_v_rel h_rest
              | none =>
                have he₂ : evalBuiltin b (v_x₂ :: args₂) = none := h_iff.mp he₁
                show SubstBisimState
                  (match evalBuiltin b (v_x₁ :: args₁) with | some v => .ret π₁' v | none => .error)
                  (match evalBuiltin b (v_x₂ :: args₂) with | some v => .ret π₂' v | none => .error)
                rw [he₁, he₂]
                exact SubstBisimState.error
          | more k rest =>
            cases k with
            | argQ => exact SubstBisimState.error
            | argV =>
              exact SubstBisimState.ret
                (SubstBisimValue.vbuiltin b rest (SubstBisimValueList.cons h_vx hargs)) h_rest
        | @vlam_refl_list body ρ vs_l₁ vs_l₂ k hρ_wf hρ_len hvs_l hbody_closed =>
          have h_lhs : step (.ret (.applyArg v_x₁ :: π₁') (.VLam body (foldrExtend ρ vs_l₁))) =
              .compute π₁' ((foldrExtend ρ vs_l₁).extend v_x₁) body := rfl
          have h_rhs : step (.ret (.applyArg v_x₂ :: π₂') (.VLam body (foldrExtend ρ vs_l₂))) =
              .compute π₂' ((foldrExtend ρ vs_l₂).extend v_x₂) body := rfl
          rw [h_lhs, h_rhs]
          have h_env₁ : (foldrExtend ρ vs_l₁).extend v_x₁ = foldrExtend ρ (v_x₁ :: vs_l₁) := rfl
          have h_env₂ : (foldrExtend ρ vs_l₂).extend v_x₂ = foldrExtend ρ (v_x₂ :: vs_l₂) := rfl
          rw [h_env₁, h_env₂]
          have hvs_new : SubstBisimValueList (v_x₁ :: vs_l₁) (v_x₂ :: vs_l₂) :=
            SubstBisimValueList.cons h_vx hvs_l
          have hbody_new : closedAt (k + (v_x₁ :: vs_l₁).length) body = true := by
            show closedAt (k + (vs_l₁.length + 1)) body = true
            have : k + (vs_l₁.length + 1) = k + vs_l₁.length + 1 := by omega
            rw [this]; exact hbody_closed
          exact SubstBisimState.reflCompute hρ_wf hρ_len hvs_new hbody_new h_rest
        | @vdelay_refl_list body ρ vs_l₁ vs_l₂ k _ _ _ _ =>
          exact SubstBisimState.error
        | @vlam_rename_list body ρ vs_l₁ vs_l₂ vs_insert k hρ_wf hρ_len hvs_l hbody_closed =>
          have hvs_new : SubstBisimValueList (v_x₁ :: vs_l₁) (v_x₂ :: vs_l₂) :=
            SubstBisimValueList.cons h_vx hvs_l
          have hbody_new : closedAt (k + (v_x₁ :: vs_l₁).length) body = true := by
            show closedAt (k + (vs_l₁.length + 1)) body = true
            have : k + (vs_l₁.length + 1) = k + vs_l₁.length + 1 := by omega
            rw [this]; exact hbody_closed
          show SubstBisimState
            (.compute π₁' (foldrExtend ρ (v_x₁ :: vs_l₁)) body)
            (.compute π₂' (foldrExtend (foldrExtend ρ vs_insert) (v_x₂ :: vs_l₂))
              (iterShiftRename vs_insert.length ((v_x₁ :: vs_l₁).length + 1) body))
          exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs_new hbody_new h_rest
        | @vdelay_rename_list body ρ vs_l₁ vs_l₂ vs_insert k _ _ _ _ =>
          exact SubstBisimState.error
        | refl hv_wf =>
          cases v₁ with
          | VCon c => exact SubstBisimState.error
          | @VLam body ρ_l =>
            have h_lhs : step (.ret (.applyArg v_x₁ :: π₁') (.VLam body ρ_l)) =
                .compute π₁' (ρ_l.extend v_x₁) body := rfl
            have h_rhs : step (.ret (.applyArg v_x₂ :: π₂') (.VLam body ρ_l)) =
                .compute π₂' (ρ_l.extend v_x₂) body := rfl
            rw [h_lhs, h_rhs]
            cases hv_wf with
            | @vlam _ _ k hρ_wf hρ_len hbody_closed =>
              have hvs_new : SubstBisimValueList [v_x₁] [v_x₂] :=
                SubstBisimValueList.cons h_vx SubstBisimValueList.nil
              have hbody_new : closedAt (k + [v_x₁].length) body = true := by
                show closedAt (k + 1) body = true; exact hbody_closed
              have h_env₁ : ρ_l.extend v_x₁ = foldrExtend ρ_l [v_x₁] := rfl
              have h_env₂ : ρ_l.extend v_x₂ = foldrExtend ρ_l [v_x₂] := rfl
              rw [h_env₁, h_env₂]
              exact SubstBisimState.reflCompute hρ_wf hρ_len hvs_new hbody_new h_rest
          | VDelay body ρ => exact SubstBisimState.error
          | VConstr tag fs => exact SubstBisimState.error
          | VBuiltin b args ea =>
            have hargs_wf : ValueListWellFormed args := by cases hv_wf; assumption
            have hargs_refl : SubstBisimValueList args args :=
              substBisimValueList_refl_wf hargs_wf
            cases ea with
            | one k =>
              cases k with
              | argQ => exact SubstBisimState.error
              | argV =>
                have h_extended : SubstBisimValueList (v_x₁ :: args) (v_x₂ :: args) :=
                  SubstBisimValueList.cons h_vx hargs_refl
                have ⟨h_some, h_iff⟩ := @substBisimValueList_evalBuiltin b _ _ h_extended
                cases he₁ : evalBuiltin b (v_x₁ :: args) with
                | some v_r₁ =>
                  obtain ⟨v_r₂, he₂, h_v_rel⟩ := h_some v_r₁ he₁
                  show SubstBisimState
                    (match evalBuiltin b (v_x₁ :: args) with | some v => .ret π₁' v | none => .error)
                    (match evalBuiltin b (v_x₂ :: args) with | some v => .ret π₂' v | none => .error)
                  rw [he₁, he₂]
                  exact SubstBisimState.ret h_v_rel h_rest
                | none =>
                  have he₂ : evalBuiltin b (v_x₂ :: args) = none := h_iff.mp he₁
                  show SubstBisimState
                    (match evalBuiltin b (v_x₁ :: args) with | some v => .ret π₁' v | none => .error)
                    (match evalBuiltin b (v_x₂ :: args) with | some v => .ret π₂' v | none => .error)
                  rw [he₁, he₂]
                  exact SubstBisimState.error
            | more k rest =>
              cases k with
              | argQ => exact SubstBisimState.error
              | argV =>
                exact SubstBisimState.ret
                  (SubstBisimValue.vbuiltin b rest (SubstBisimValueList.cons h_vx hargs_refl)) h_rest
      | @constrField tag done₁ done₂ todo ρ₁ ρ₂ vs₁ vs₂ pos rep v_repl d hpos hrep h_done henv hvs h_todo h_halts =>
        cases todo with
        | nil =>
          have h_subst_nil : Moist.Verified.substTermList (pos + vs₁.length)
              (iteratedShift vs₁.length rep) [] = [] := by
            simp only [Moist.Verified.substTermList]
          have h_lhs : step (.ret (.constrField tag done₁ [] (foldrExtend ρ₁ vs₁) :: π₁') v₁) =
              .ret π₁' (.VConstr tag ((v₁ :: done₁).reverse)) := rfl
          have h_rhs : step (.ret (.constrField tag done₂
              (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) []) (foldrExtend ρ₂ vs₂) :: π₂') v₂) =
              .ret π₂' (.VConstr tag ((v₂ :: done₂).reverse)) := by
            rw [h_subst_nil]; rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.ret
            (SubstBisimValue.vconstr tag
              (substBisimValueList_reverse _ (SubstBisimValueList.cons h_v h_done))) h_rest
        | cons m ms =>
          have h_subst_cons : Moist.Verified.substTermList (pos + vs₁.length)
              (iteratedShift vs₁.length rep) (m :: ms) =
              Moist.Verified.substTerm (pos + vs₁.length)
                (iteratedShift vs₁.length rep) m ::
                  Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) ms := by
            simp only [Moist.Verified.substTermList]
          have h_mms : closedAt (d + 1 + vs₁.length) m = true ∧
              closedAtList (d + 1 + vs₁.length) ms = true := by
            simp only [closedAtList, Bool.and_eq_true] at h_todo
            exact h_todo
          have h_lhs : step (.ret (.constrField tag done₁ (m :: ms) (foldrExtend ρ₁ vs₁) :: π₁') v₁) =
              .compute (.constrField tag (v₁ :: done₁) ms (foldrExtend ρ₁ vs₁) :: π₁')
                (foldrExtend ρ₁ vs₁) m := rfl
          have h_rhs : step (.ret (.constrField tag done₂
              (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) (m :: ms)) (foldrExtend ρ₂ vs₂) :: π₂') v₂) =
              .compute (.constrField tag (v₂ :: done₂)
                (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) ms) (foldrExtend ρ₂ vs₂) :: π₂')
                (foldrExtend ρ₂ vs₂)
                (Moist.Verified.substTerm (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) m) := by
            rw [h_subst_cons]; rfl
          rw [h_lhs, h_rhs]
          exact SubstBisimState.compute hpos hrep henv hvs h_mms.1 h_halts
            (SubstBisimStack.cons
              (SubstBisimFrame.constrField tag hpos hrep
                (SubstBisimValueList.cons h_v h_done) henv hvs h_mms.2 h_halts) h_rest)
      | @caseScrutinee alts ρ₁ ρ₂ vs₁ vs₂ pos rep v_repl d hpos hrep henv hvs h_alts h_halts =>
        cases h_v with
        | vcon c =>
          show SubstBisimState
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₁') (foldrExtend ρ₁ vs₁) alt
                  | none => State.error
              | none => State.error)
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts).length > numCtors
                then State.error
                else match (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts)[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₂') (foldrExtend ρ₂ vs₂) alt
                  | none => State.error
              | none => State.error)
          cases hc : constToTagAndFields c with
          | none => exact SubstBisimState.error
          | some r =>
            obtain ⟨tag, numCtors, fields⟩ := r
            have h_len_eq : (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts).length = alts.length :=
              Moist.Verified.substTermList_length _ _ alts
            by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
            · have hnum' : (numCtors > 0 && (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts).length > numCtors) = true := by
                rw [h_len_eq]; exact hnum
              simp only [hnum, hnum', if_true]
              exact SubstBisimState.error
            · have hnum' : (numCtors > 0 && (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts).length > numCtors) = false := by
                rw [h_len_eq]
                cases hn : (numCtors > 0 && alts.length > numCtors) with
                | true => exact absurd hn hnum
                | false => rfl
              simp only [hnum, hnum', if_false, Bool.false_eq_true]
              cases ha : alts[tag]? with
              | none =>
                have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
                have hge' : tag ≥ (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts).length := by
                  rw [h_len_eq]; exact hge
                have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts)[tag]? = none :=
                  List.getElem?_eq_none hge'
                rw [ha']
                exact SubstBisimState.error
              | some alt =>
                have h_alt := substBisim_closedAtList_get (d + 1 + vs₁.length) alts tag alt h_alts ha
                have hlt : tag < alts.length := by
                  rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                  · exact h_case
                  · rw [List.getElem?_eq_none h_case] at ha; cases ha
                have hlt' : tag < (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts).length := by
                  rw [h_len_eq]; exact hlt
                have heq_val : alts[tag] = alt := by
                  have := List.getElem?_eq_some_iff.mp ha
                  exact this.2
                have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts)[tag]? =
                    some (Moist.Verified.substTerm (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alt) := by
                  rw [List.getElem?_eq_some_iff.mpr]
                  refine ⟨hlt', ?_⟩
                  rw [substTermList_getElem (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts tag hlt, heq_val]
                rw [ha']
                have h_fs_refl : SubstBisimValueList fields fields :=
                  substBisimValueList_constToTagAndFields_refl hc
                exact SubstBisimState.compute hpos hrep henv hvs h_alt h_halts
                        (substBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
        | vlam _ _ _ _ _ _ =>
          exact SubstBisimState.error
        | vdelay _ _ _ _ _ _ =>
          exact SubstBisimState.error
        | @vconstr tag fs₁ fs₂ h_fs =>
          show SubstBisimState
            (match alts[tag]? with
              | some alt => State.compute (fs₁.map Frame.applyArg ++ π₁') (foldrExtend ρ₁ vs₁) alt
              | none => State.error)
            (match (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts)[tag]? with
              | some alt => State.compute (fs₂.map Frame.applyArg ++ π₂') (foldrExtend ρ₂ vs₂) alt
              | none => State.error)
          have h_len_eq : (Moist.Verified.substTermList (pos + vs₁.length)
              (iteratedShift vs₁.length rep) alts).length = alts.length :=
            Moist.Verified.substTermList_length _ _ alts
          cases ha : alts[tag]? with
          | none =>
            have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
            have hge' : tag ≥ (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts).length := by
              rw [h_len_eq]; exact hge
            have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts)[tag]? = none :=
              List.getElem?_eq_none hge'
            rw [ha']
            exact SubstBisimState.error
          | some alt =>
            have h_alt := substBisim_closedAtList_get (d + 1 + vs₁.length) alts tag alt h_alts ha
            have hlt : tag < alts.length := by
              rcases Nat.lt_or_ge tag alts.length with h_case | h_case
              · exact h_case
              · rw [List.getElem?_eq_none h_case] at ha; cases ha
            have hlt' : tag < (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts).length := by
              rw [h_len_eq]; exact hlt
            have heq_val : alts[tag] = alt := by
              have := List.getElem?_eq_some_iff.mp ha
              exact this.2
            have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts)[tag]? =
                some (Moist.Verified.substTerm (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alt) := by
              rw [List.getElem?_eq_some_iff.mpr]
              refine ⟨hlt', ?_⟩
              rw [substTermList_getElem (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts tag hlt, heq_val]
            rw [ha']
            exact SubstBisimState.compute hpos hrep henv hvs h_alt h_halts
                    (substBisimValueList_to_applyArg_stack _ h_fs h_rest)
        | vbuiltin _ _ _ => exact SubstBisimState.error
        | vlam_refl_list _ _ _ _ => exact SubstBisimState.error
        | vdelay_refl_list _ _ _ _ => exact SubstBisimState.error
        | vlam_rename_list _ _ _ _ => exact SubstBisimState.error
        | vdelay_rename_list _ _ _ _ => exact SubstBisimState.error
        | refl hv_wf =>
          cases v₁ with
          | VCon c =>
            show SubstBisimState
              (match constToTagAndFields c with
                | some (tag, numCtors, fields) =>
                  if numCtors > 0 && alts.length > numCtors then State.error
                  else match alts[tag]? with
                    | some alt => State.compute (fields.map Frame.applyArg ++ π₁') (foldrExtend ρ₁ vs₁) alt
                    | none => State.error
                | none => State.error)
              (match constToTagAndFields c with
                | some (tag, numCtors, fields) =>
                  if numCtors > 0 && (Moist.Verified.substTermList (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts).length > numCtors
                  then State.error
                  else match (Moist.Verified.substTermList (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts)[tag]? with
                    | some alt => State.compute (fields.map Frame.applyArg ++ π₂') (foldrExtend ρ₂ vs₂) alt
                    | none => State.error
                | none => State.error)
            cases hc : constToTagAndFields c with
            | none => exact SubstBisimState.error
            | some r =>
              obtain ⟨tag, numCtors, fields⟩ := r
              have h_len_eq : (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts).length = alts.length :=
                Moist.Verified.substTermList_length _ _ alts
              by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
              · have hnum' : (numCtors > 0 && (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts).length > numCtors) = true := by
                  rw [h_len_eq]; exact hnum
                simp only [hnum, hnum', if_true]
                exact SubstBisimState.error
              · have hnum' : (numCtors > 0 && (Moist.Verified.substTermList (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alts).length > numCtors) = false := by
                  rw [h_len_eq]
                  cases hn : (numCtors > 0 && alts.length > numCtors) with
                  | true => exact absurd hn hnum
                  | false => rfl
                simp only [hnum, hnum', if_false, Bool.false_eq_true]
                cases ha : alts[tag]? with
                | none =>
                  have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
                  have hge' : tag ≥ (Moist.Verified.substTermList (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts).length := by
                    rw [h_len_eq]; exact hge
                  have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts)[tag]? = none :=
                    List.getElem?_eq_none hge'
                  rw [ha']
                  exact SubstBisimState.error
                | some alt =>
                  have h_alt := substBisim_closedAtList_get (d + 1 + vs₁.length) alts tag alt h_alts ha
                  have hlt : tag < alts.length := by
                    rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                    · exact h_case
                    · rw [List.getElem?_eq_none h_case] at ha; cases ha
                  have hlt' : tag < (Moist.Verified.substTermList (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts).length := by
                    rw [h_len_eq]; exact hlt
                  have heq_val : alts[tag] = alt := by
                    have := List.getElem?_eq_some_iff.mp ha
                    exact this.2
                  have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts)[tag]? =
                      some (Moist.Verified.substTerm (pos + vs₁.length)
                        (iteratedShift vs₁.length rep) alt) := by
                    rw [List.getElem?_eq_some_iff.mpr]
                    refine ⟨hlt', ?_⟩
                    rw [substTermList_getElem (pos + vs₁.length)
                      (iteratedShift vs₁.length rep) alts tag hlt, heq_val]
                  rw [ha']
                  have h_fs_refl : SubstBisimValueList fields fields :=
                    substBisimValueList_constToTagAndFields_refl hc
                  exact SubstBisimState.compute hpos hrep henv hvs h_alt h_halts
                          (substBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
          | VLam _ _ => exact SubstBisimState.error
          | VDelay _ _ => exact SubstBisimState.error
          | VConstr tag fs =>
            show SubstBisimState
              (match alts[tag]? with
                | some alt => State.compute (fs.map Frame.applyArg ++ π₁') (foldrExtend ρ₁ vs₁) alt
                | none => State.error)
              (match (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts)[tag]? with
                | some alt => State.compute (fs.map Frame.applyArg ++ π₂') (foldrExtend ρ₂ vs₂) alt
                | none => State.error)
            have h_len_eq : (Moist.Verified.substTermList (pos + vs₁.length)
                (iteratedShift vs₁.length rep) alts).length = alts.length :=
              Moist.Verified.substTermList_length _ _ alts
            cases ha : alts[tag]? with
            | none =>
              have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
              have hge' : tag ≥ (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts).length := by
                rw [h_len_eq]; exact hge
              have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts)[tag]? = none :=
                List.getElem?_eq_none hge'
              rw [ha']
              exact SubstBisimState.error
            | some alt =>
              have h_alt := substBisim_closedAtList_get (d + 1 + vs₁.length) alts tag alt h_alts ha
              have hlt : tag < alts.length := by
                rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                · exact h_case
                · rw [List.getElem?_eq_none h_case] at ha; cases ha
              have hlt' : tag < (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts).length := by
                rw [h_len_eq]; exact hlt
              have heq_val : alts[tag] = alt := by
                have := List.getElem?_eq_some_iff.mp ha
                exact this.2
              have ha' : (Moist.Verified.substTermList (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts)[tag]? =
                  some (Moist.Verified.substTerm (pos + vs₁.length)
                    (iteratedShift vs₁.length rep) alt) := by
                rw [List.getElem?_eq_some_iff.mpr]
                refine ⟨hlt', ?_⟩
                rw [substTermList_getElem (pos + vs₁.length)
                  (iteratedShift vs₁.length rep) alts tag hlt, heq_val]
              rw [ha']
              have hfs_wf : ValueListWellFormed fs := by cases hv_wf; assumption
              have hfs_refl : SubstBisimValueList fs fs :=
                substBisimValueList_refl_wf hfs_wf
              exact SubstBisimState.compute hpos hrep henv hvs h_alt h_halts
                      (substBisimValueList_to_applyArg_stack _ hfs_refl h_rest)
          | VBuiltin _ _ _ => exact SubstBisimState.error
      | @argRefl t ρ vs₁ vs₂ k hρ_wf hρ_len hvs hclosed =>
        have h_lhs : step (.ret (.arg t (foldrExtend ρ vs₁) :: π₁') v₁) =
            .compute (.funV v₁ :: π₁') (foldrExtend ρ vs₁) t := rfl
        have h_rhs : step (.ret (.arg t (foldrExtend ρ vs₂) :: π₂') v₂) =
            .compute (.funV v₂ :: π₂') (foldrExtend ρ vs₂) t := rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.reflCompute hρ_wf hρ_len hvs hclosed
          (SubstBisimStack.cons (SubstBisimFrame.funV h_v) h_rest)
      | @constrFieldRefl tag done todo ρ vs₁ vs₂ k h_done_wf hρ_wf hρ_len hvs h_todo =>
        cases todo with
        | nil =>
          have h_lhs : step (.ret (.constrField tag done [] (foldrExtend ρ vs₁) :: π₁') v₁) =
              .ret π₁' (.VConstr tag ((v₁ :: done).reverse)) := rfl
          have h_rhs : step (.ret (.constrField tag done [] (foldrExtend ρ vs₂) :: π₂') v₂) =
              .ret π₂' (.VConstr tag ((v₂ :: done).reverse)) := rfl
          rw [h_lhs, h_rhs]
          have h_done_refl : SubstBisimValueList done done :=
            substBisimValueList_refl_wf h_done_wf
          have h_cons : SubstBisimValueList (v₁ :: done) (v₂ :: done) :=
            SubstBisimValueList.cons h_v h_done_refl
          have h_rev : SubstBisimValueList ((v₁ :: done).reverse) ((v₂ :: done).reverse) :=
            substBisimValueList_reverse _ h_cons
          exact SubstBisimState.ret (SubstBisimValue.vconstr tag h_rev) h_rest
        | cons m ms =>
          have h_mms : closedAt (k + vs₁.length) m = true ∧
              closedAtList (k + vs₁.length) ms = true := by
            simp only [closedAtList, Bool.and_eq_true] at h_todo
            exact h_todo
          have h_lhs : step (.ret (.constrField tag done (m :: ms) (foldrExtend ρ vs₁) :: π₁') v₁) =
              .compute (.constrField tag (v₁ :: done) ms (foldrExtend ρ vs₁) :: π₁')
                (foldrExtend ρ vs₁) m := rfl
          have h_rhs : step (.ret (.constrField tag done (m :: ms) (foldrExtend ρ vs₂) :: π₂') v₂) =
              .compute (.constrField tag (v₂ :: done) ms (foldrExtend ρ vs₂) :: π₂')
                (foldrExtend ρ vs₂) m := rfl
          rw [h_lhs, h_rhs]
          have h_done_refl : SubstBisimValueList done done :=
            substBisimValueList_refl_wf h_done_wf
          have h_cons : SubstBisimValueList (v₁ :: done) (v₂ :: done) :=
            SubstBisimValueList.cons h_v h_done_refl
          exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_mms.1
            (SubstBisimStack.cons
              (SubstBisimFrame.constrFieldSemiRefl tag h_cons hρ_wf hρ_len hvs h_mms.2) h_rest)
      | @constrFieldSemiRefl tag done₁ done₂ todo ρ vs₁ vs₂ k h_dones hρ_wf hρ_len hvs h_todo =>
        cases todo with
        | nil =>
          have h_lhs : step (.ret (.constrField tag done₁ [] (foldrExtend ρ vs₁) :: π₁') v₁) =
              .ret π₁' (.VConstr tag ((v₁ :: done₁).reverse)) := rfl
          have h_rhs : step (.ret (.constrField tag done₂ [] (foldrExtend ρ vs₂) :: π₂') v₂) =
              .ret π₂' (.VConstr tag ((v₂ :: done₂).reverse)) := rfl
          rw [h_lhs, h_rhs]
          have h_cons : SubstBisimValueList (v₁ :: done₁) (v₂ :: done₂) :=
            SubstBisimValueList.cons h_v h_dones
          have h_rev : SubstBisimValueList ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) :=
            substBisimValueList_reverse _ h_cons
          exact SubstBisimState.ret (SubstBisimValue.vconstr tag h_rev) h_rest
        | cons m ms =>
          have h_mms : closedAt (k + vs₁.length) m = true ∧
              closedAtList (k + vs₁.length) ms = true := by
            simp only [closedAtList, Bool.and_eq_true] at h_todo
            exact h_todo
          have h_lhs : step (.ret (.constrField tag done₁ (m :: ms) (foldrExtend ρ vs₁) :: π₁') v₁) =
              .compute (.constrField tag (v₁ :: done₁) ms (foldrExtend ρ vs₁) :: π₁')
                (foldrExtend ρ vs₁) m := rfl
          have h_rhs : step (.ret (.constrField tag done₂ (m :: ms) (foldrExtend ρ vs₂) :: π₂') v₂) =
              .compute (.constrField tag (v₂ :: done₂) ms (foldrExtend ρ vs₂) :: π₂')
                (foldrExtend ρ vs₂) m := rfl
          rw [h_lhs, h_rhs]
          have h_cons : SubstBisimValueList (v₁ :: done₁) (v₂ :: done₂) :=
            SubstBisimValueList.cons h_v h_dones
          exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_mms.1
            (SubstBisimStack.cons
              (SubstBisimFrame.constrFieldSemiRefl tag h_cons hρ_wf hρ_len hvs h_mms.2) h_rest)
      | @caseScrutineeRefl alts ρ vs₁ vs₂ k hρ_wf hρ_len hvs h_alts =>
        cases h_v with
        | vcon c =>
          show SubstBisimState
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
                  | none => State.error
              | none => State.error)
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₂') (foldrExtend ρ vs₂) alt
                  | none => State.error
              | none => State.error)
          cases hc : constToTagAndFields c with
          | none => exact SubstBisimState.error
          | some r =>
            obtain ⟨tag, numCtors, fields⟩ := r
            by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
            · simp only [hnum, if_true]
              exact SubstBisimState.error
            · simp only [hnum, if_false, Bool.false_eq_true]
              cases ha : alts[tag]? with
              | none => exact SubstBisimState.error
              | some alt =>
                have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
                have h_fs_refl : SubstBisimValueList fields fields :=
                  substBisimValueList_constToTagAndFields_refl hc
                exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_alt
                        (substBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
        | vlam _ _ _ _ _ _ => exact SubstBisimState.error
        | vdelay _ _ _ _ _ _ => exact SubstBisimState.error
        | @vconstr tag fs₁ fs₂ h_fs =>
          show SubstBisimState
            (match alts[tag]? with
              | some alt => State.compute (fs₁.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
              | none => State.error)
            (match alts[tag]? with
              | some alt => State.compute (fs₂.map Frame.applyArg ++ π₂') (foldrExtend ρ vs₂) alt
              | none => State.error)
          cases ha : alts[tag]? with
          | none => exact SubstBisimState.error
          | some alt =>
            have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
            exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_alt
                    (substBisimValueList_to_applyArg_stack _ h_fs h_rest)
        | vbuiltin _ _ _ => exact SubstBisimState.error
        | vlam_refl_list _ _ _ _ => exact SubstBisimState.error
        | vdelay_refl_list _ _ _ _ => exact SubstBisimState.error
        | vlam_rename_list _ _ _ _ => exact SubstBisimState.error
        | vdelay_rename_list _ _ _ _ => exact SubstBisimState.error
        | refl hv_wf =>
          cases v₁ with
          | VCon c =>
            show SubstBisimState
              (match constToTagAndFields c with
                | some (tag, numCtors, fields) =>
                  if numCtors > 0 && alts.length > numCtors then State.error
                  else match alts[tag]? with
                    | some alt => State.compute (fields.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
                    | none => State.error
                | none => State.error)
              (match constToTagAndFields c with
                | some (tag, numCtors, fields) =>
                  if numCtors > 0 && alts.length > numCtors then State.error
                  else match alts[tag]? with
                    | some alt => State.compute (fields.map Frame.applyArg ++ π₂') (foldrExtend ρ vs₂) alt
                    | none => State.error
                | none => State.error)
            cases hc : constToTagAndFields c with
            | none => exact SubstBisimState.error
            | some r =>
              obtain ⟨tag, numCtors, fields⟩ := r
              by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
              · simp only [hnum, if_true]
                exact SubstBisimState.error
              · simp only [hnum, if_false, Bool.false_eq_true]
                cases ha : alts[tag]? with
                | none => exact SubstBisimState.error
                | some alt =>
                  have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
                  have h_fs_refl : SubstBisimValueList fields fields :=
                    substBisimValueList_constToTagAndFields_refl hc
                  exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_alt
                          (substBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
          | VLam _ _ => exact SubstBisimState.error
          | VDelay _ _ => exact SubstBisimState.error
          | VConstr tag fs =>
            show SubstBisimState
              (match alts[tag]? with
                | some alt => State.compute (fs.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
                | none => State.error)
              (match alts[tag]? with
                | some alt => State.compute (fs.map Frame.applyArg ++ π₂') (foldrExtend ρ vs₂) alt
                | none => State.error)
            cases ha : alts[tag]? with
            | none => exact SubstBisimState.error
            | some alt =>
              have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
              have hfs_wf : ValueListWellFormed fs := by cases hv_wf; assumption
              have hfs_refl : SubstBisimValueList fs fs :=
                substBisimValueList_refl_wf hfs_wf
              exact SubstBisimState.reflCompute hρ_wf hρ_len hvs h_alt
                      (substBisimValueList_to_applyArg_stack _ hfs_refl h_rest)
          | VBuiltin _ _ _ => exact SubstBisimState.error
      | @argRenameInsert t ρ vs₁ vs₂ vs_insert k hρ_wf hρ_len hvs hclosed =>
        have h_lhs : step (.ret (.arg t (foldrExtend ρ vs₁) :: π₁') v₁) =
            .compute (.funV v₁ :: π₁') (foldrExtend ρ vs₁) t := rfl
        have h_rhs : step (.ret (.arg
            (iterShiftRename vs_insert.length (vs₁.length + 1) t)
            (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂') v₂) =
            .compute (.funV v₂ :: π₂') (foldrExtend (foldrExtend ρ vs_insert) vs₂)
              (iterShiftRename vs_insert.length (vs₁.length + 1) t) := rfl
        rw [h_lhs, h_rhs]
        exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs hclosed
          (SubstBisimStack.cons (SubstBisimFrame.funV h_v) h_rest)
      | @constrFieldRenameInsert tag done₁ done₂ todo ρ vs₁ vs₂ vs_insert k hρ_wf hρ_len h_done hvs h_todo =>
        cases todo with
        | nil =>
          have h_rename_nil : iterShiftRenameList vs_insert.length (vs₁.length + 1) [] = [] :=
            iterShiftRenameList_nil _ _
          have h_lhs : step (.ret (.constrField tag done₁ [] (foldrExtend ρ vs₁) :: π₁') v₁) =
              .ret π₁' (.VConstr tag ((v₁ :: done₁).reverse)) := rfl
          have h_rhs : step (.ret (.constrField tag done₂
              (iterShiftRenameList vs_insert.length (vs₁.length + 1) [])
              (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂') v₂) =
              .ret π₂' (.VConstr tag ((v₂ :: done₂).reverse)) := by
            rw [h_rename_nil]; rfl
          rw [h_lhs, h_rhs]
          have h_cons : SubstBisimValueList (v₁ :: done₁) (v₂ :: done₂) :=
            SubstBisimValueList.cons h_v h_done
          have h_rev : SubstBisimValueList ((v₁ :: done₁).reverse) ((v₂ :: done₂).reverse) :=
            substBisimValueList_reverse _ h_cons
          exact SubstBisimState.ret (SubstBisimValue.vconstr tag h_rev) h_rest
        | cons m ms =>
          have h_mms : closedAt (k + vs₁.length) m = true ∧
              closedAtList (k + vs₁.length) ms = true := by
            simp only [closedAtList, Bool.and_eq_true] at h_todo
            exact h_todo
          have h_rename_cons : iterShiftRenameList vs_insert.length (vs₁.length + 1) (m :: ms) =
              iterShiftRename vs_insert.length (vs₁.length + 1) m ::
                iterShiftRenameList vs_insert.length (vs₁.length + 1) ms :=
            iterShiftRenameList_cons _ _ _ _
          have h_lhs : step (.ret (.constrField tag done₁ (m :: ms) (foldrExtend ρ vs₁) :: π₁') v₁) =
              .compute (.constrField tag (v₁ :: done₁) ms (foldrExtend ρ vs₁) :: π₁')
                (foldrExtend ρ vs₁) m := rfl
          have h_rhs : step (.ret (.constrField tag done₂
              (iterShiftRenameList vs_insert.length (vs₁.length + 1) (m :: ms))
              (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂') v₂) =
              .compute (.constrField tag (v₂ :: done₂)
                (iterShiftRenameList vs_insert.length (vs₁.length + 1) ms)
                (foldrExtend (foldrExtend ρ vs_insert) vs₂) :: π₂')
                (foldrExtend (foldrExtend ρ vs_insert) vs₂)
                (iterShiftRename vs_insert.length (vs₁.length + 1) m) := by
            rw [h_rename_cons]; rfl
          rw [h_lhs, h_rhs]
          have h_cons : SubstBisimValueList (v₁ :: done₁) (v₂ :: done₂) :=
            SubstBisimValueList.cons h_v h_done
          exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_mms.1
            (SubstBisimStack.cons
              (SubstBisimFrame.constrFieldRenameInsert tag hρ_wf hρ_len h_cons hvs h_mms.2)
              h_rest)
      | @caseScrutineeRenameInsert alts ρ vs₁ vs₂ vs_insert k hρ_wf hρ_len hvs h_alts =>
        cases h_v with
        | vcon c =>
          show SubstBisimState
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && alts.length > numCtors then State.error
                else match alts[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
                  | none => State.error
              | none => State.error)
            (match constToTagAndFields c with
              | some (tag, numCtors, fields) =>
                if numCtors > 0 && (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length > numCtors
                then State.error
                else match (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? with
                  | some alt => State.compute (fields.map Frame.applyArg ++ π₂') (foldrExtend (foldrExtend ρ vs_insert) vs₂) alt
                  | none => State.error
              | none => State.error)
          cases hc : constToTagAndFields c with
          | none => exact SubstBisimState.error
          | some r =>
            obtain ⟨tag, numCtors, fields⟩ := r
            have h_len_eq : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length = alts.length :=
              iterShiftRenameList_length _ _ alts
            by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
            · have hnum' : (numCtors > 0 && (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length > numCtors) = true := by
                rw [h_len_eq]; exact hnum
              simp only [hnum, hnum', if_true]
              exact SubstBisimState.error
            · have hnum' : (numCtors > 0 && (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length > numCtors) = false := by
                rw [h_len_eq]
                cases hn : (numCtors > 0 && alts.length > numCtors) with
                | true => exact absurd hn hnum
                | false => rfl
              simp only [hnum, hnum', if_false, Bool.false_eq_true]
              cases ha : alts[tag]? with
              | none =>
                have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
                have hge' : tag ≥ (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
                  rw [h_len_eq]; exact hge
                have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? = none :=
                  List.getElem?_eq_none hge'
                rw [ha']
                exact SubstBisimState.error
              | some alt =>
                have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
                have hlt : tag < alts.length := by
                  rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                  · exact h_case
                  · rw [List.getElem?_eq_none h_case] at ha; cases ha
                have hlt' : tag < (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
                  rw [h_len_eq]; exact hlt
                have heq_val : alts[tag] = alt := by
                  have := List.getElem?_eq_some_iff.mp ha
                  exact this.2
                have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? =
                    some (iterShiftRename vs_insert.length (vs₁.length + 1) alt) := by
                  rw [List.getElem?_eq_some_iff.mpr]
                  refine ⟨hlt', ?_⟩
                  rw [iterShiftRenameList_getElem vs_insert.length (vs₁.length + 1) alts tag hlt, heq_val]
                rw [ha']
                have h_fs_refl : SubstBisimValueList fields fields :=
                  substBisimValueList_constToTagAndFields_refl hc
                exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_alt
                        (substBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
        | vlam _ _ _ _ _ _ => exact SubstBisimState.error
        | vdelay _ _ _ _ _ _ => exact SubstBisimState.error
        | @vconstr tag fs₁ fs₂ h_fs =>
          show SubstBisimState
            (match alts[tag]? with
              | some alt => State.compute (fs₁.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
              | none => State.error)
            (match (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? with
              | some alt => State.compute (fs₂.map Frame.applyArg ++ π₂') (foldrExtend (foldrExtend ρ vs_insert) vs₂) alt
              | none => State.error)
          have h_len_eq : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length = alts.length :=
            iterShiftRenameList_length _ _ alts
          cases ha : alts[tag]? with
          | none =>
            have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
            have hge' : tag ≥ (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
              rw [h_len_eq]; exact hge
            have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? = none :=
              List.getElem?_eq_none hge'
            rw [ha']
            exact SubstBisimState.error
          | some alt =>
            have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
            have hlt : tag < alts.length := by
              rcases Nat.lt_or_ge tag alts.length with h_case | h_case
              · exact h_case
              · rw [List.getElem?_eq_none h_case] at ha; cases ha
            have hlt' : tag < (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
              rw [h_len_eq]; exact hlt
            have heq_val : alts[tag] = alt := by
              have := List.getElem?_eq_some_iff.mp ha
              exact this.2
            have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? =
                some (iterShiftRename vs_insert.length (vs₁.length + 1) alt) := by
              rw [List.getElem?_eq_some_iff.mpr]
              refine ⟨hlt', ?_⟩
              rw [iterShiftRenameList_getElem vs_insert.length (vs₁.length + 1) alts tag hlt, heq_val]
            rw [ha']
            exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_alt
                    (substBisimValueList_to_applyArg_stack _ h_fs h_rest)
        | vbuiltin _ _ _ => exact SubstBisimState.error
        | vlam_refl_list _ _ _ _ => exact SubstBisimState.error
        | vdelay_refl_list _ _ _ _ => exact SubstBisimState.error
        | vlam_rename_list _ _ _ _ => exact SubstBisimState.error
        | vdelay_rename_list _ _ _ _ => exact SubstBisimState.error
        | refl hv_wf =>
          cases v₁ with
          | VCon c =>
            show SubstBisimState
              (match constToTagAndFields c with
                | some (tag, numCtors, fields) =>
                  if numCtors > 0 && alts.length > numCtors then State.error
                  else match alts[tag]? with
                    | some alt => State.compute (fields.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
                    | none => State.error
                | none => State.error)
              (match constToTagAndFields c with
                | some (tag, numCtors, fields) =>
                  if numCtors > 0 && (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length > numCtors
                  then State.error
                  else match (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? with
                    | some alt => State.compute (fields.map Frame.applyArg ++ π₂') (foldrExtend (foldrExtend ρ vs_insert) vs₂) alt
                    | none => State.error
                | none => State.error)
            cases hc : constToTagAndFields c with
            | none => exact SubstBisimState.error
            | some r =>
              obtain ⟨tag, numCtors, fields⟩ := r
              have h_len_eq : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length = alts.length :=
                iterShiftRenameList_length _ _ alts
              by_cases hnum : (numCtors > 0 && alts.length > numCtors) = true
              · have hnum' : (numCtors > 0 && (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length > numCtors) = true := by
                  rw [h_len_eq]; exact hnum
                simp only [hnum, hnum', if_true]
                exact SubstBisimState.error
              · have hnum' : (numCtors > 0 && (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length > numCtors) = false := by
                  rw [h_len_eq]
                  cases hn : (numCtors > 0 && alts.length > numCtors) with
                  | true => exact absurd hn hnum
                  | false => rfl
                simp only [hnum, hnum', if_false, Bool.false_eq_true]
                cases ha : alts[tag]? with
                | none =>
                  have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
                  have hge' : tag ≥ (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
                    rw [h_len_eq]; exact hge
                  have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? = none :=
                    List.getElem?_eq_none hge'
                  rw [ha']
                  exact SubstBisimState.error
                | some alt =>
                  have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
                  have hlt : tag < alts.length := by
                    rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                    · exact h_case
                    · rw [List.getElem?_eq_none h_case] at ha; cases ha
                  have hlt' : tag < (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
                    rw [h_len_eq]; exact hlt
                  have heq_val : alts[tag] = alt := by
                    have := List.getElem?_eq_some_iff.mp ha
                    exact this.2
                  have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? =
                      some (iterShiftRename vs_insert.length (vs₁.length + 1) alt) := by
                    rw [List.getElem?_eq_some_iff.mpr]
                    refine ⟨hlt', ?_⟩
                    rw [iterShiftRenameList_getElem vs_insert.length (vs₁.length + 1) alts tag hlt, heq_val]
                  rw [ha']
                  have h_fs_refl : SubstBisimValueList fields fields :=
                    substBisimValueList_constToTagAndFields_refl hc
                  exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_alt
                          (substBisimValueList_to_applyArg_stack fields h_fs_refl h_rest)
          | VLam _ _ => exact SubstBisimState.error
          | VDelay _ _ => exact SubstBisimState.error
          | VConstr tag fs =>
            show SubstBisimState
              (match alts[tag]? with
                | some alt => State.compute (fs.map Frame.applyArg ++ π₁') (foldrExtend ρ vs₁) alt
                | none => State.error)
              (match (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? with
                | some alt => State.compute (fs.map Frame.applyArg ++ π₂') (foldrExtend (foldrExtend ρ vs_insert) vs₂) alt
                | none => State.error)
            have h_len_eq : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length = alts.length :=
              iterShiftRenameList_length _ _ alts
            cases ha : alts[tag]? with
            | none =>
              have hge : tag ≥ alts.length := List.getElem?_eq_none_iff.mp ha
              have hge' : tag ≥ (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
                rw [h_len_eq]; exact hge
              have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? = none :=
                List.getElem?_eq_none hge'
              rw [ha']
              exact SubstBisimState.error
            | some alt =>
              have h_alt := substBisim_closedAtList_get (k + vs₁.length) alts tag alt h_alts ha
              have hlt : tag < alts.length := by
                rcases Nat.lt_or_ge tag alts.length with h_case | h_case
                · exact h_case
                · rw [List.getElem?_eq_none h_case] at ha; cases ha
              have hlt' : tag < (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts).length := by
                rw [h_len_eq]; exact hlt
              have heq_val : alts[tag] = alt := by
                have := List.getElem?_eq_some_iff.mp ha
                exact this.2
              have ha' : (iterShiftRenameList vs_insert.length (vs₁.length + 1) alts)[tag]? =
                  some (iterShiftRename vs_insert.length (vs₁.length + 1) alt) := by
                rw [List.getElem?_eq_some_iff.mpr]
                refine ⟨hlt', ?_⟩
                rw [iterShiftRenameList_getElem vs_insert.length (vs₁.length + 1) alts tag hlt, heq_val]
              rw [ha']
              have hfs_wf : ValueListWellFormed fs := by cases hv_wf; assumption
              have hfs_refl : SubstBisimValueList fs fs :=
                substBisimValueList_refl_wf hfs_wf
              exact SubstBisimState.renameInsertCompute hρ_wf hρ_len hvs h_alt
                      (substBisimValueList_to_applyArg_stack _ hfs_refl h_rest)
          | VBuiltin _ _ _ => exact SubstBisimState.error

/-- Iterated step preservation. -/
theorem substBisimState_steps_preserves_weak :
    ∀ (n : Nat) {s₁ s₂ : State},
    SubstBisimState s₁ s₂ →
    ∃ m, SubstBisimState (steps n s₁) (steps m s₂) := by
  intro n
  induction n with
  | zero => intro _ _ h; exact ⟨0, h⟩
  | succ k ih =>
    intro s₁ s₂ h
    obtain ⟨m₀, h_step⟩ := substBisimState_step_preserves_weak h
    obtain ⟨m₁, h_next⟩ := ih h_step
    refine ⟨m₀ + m₁, ?_⟩
    show SubstBisimState (steps (k + 1) s₁) (steps (m₀ + m₁) s₂)
    have hlhs : steps (k + 1) s₁ = steps k (step s₁) := by simp [steps]
    have hrhs : steps (m₀ + m₁) s₂ = steps m₁ (steps m₀ s₂) :=
      steps_trans m₀ m₁ s₂
    rw [hlhs, hrhs]
    exact h_next


/-- Halt inversion: SubstBisimState (halt v₁) s forces s = halt v₂ with
    SubstBisimValue v₁ v₂. -/

theorem substBisimState_halt_inv : ∀ {v : CekValue} {s : State},
    SubstBisimState (.halt v) s → ∃ v', s = .halt v' ∧ SubstBisimValue v v'
  | _, _, .halt h_v => ⟨_, rfl, h_v⟩

/-- Error inversion. -/
theorem substBisimState_error_inv : ∀ {s : State},
    SubstBisimState .error s → s = .error
  | _, .error => rfl

/-- Ret inversion. -/
theorem substBisimState_ret_inv : ∀ {π : Stack} {v : CekValue} {s : State},
    SubstBisimState (.ret π v) s →
    ∃ π' v', s = .ret π' v' ∧ SubstBisimValue v v' ∧ SubstBisimStack π π'
  | _, _, _, .ret h_v h_π => ⟨_, _, rfl, h_v, h_π⟩

/-- The direct lifting from `SubstBisimState` to `ObsRefines`. Uses weak
    step preservation + halt/error inversions. -/
theorem substBisimState_to_obsRefines :
    ∀ {s₁ s₂ : State}, SubstBisimState s₁ s₂ → ObsRefines s₁ s₂ := by
  intro s₁ s₂ h
  refine ObsRefines.mk ?_ ?_
  · -- Halt clause
    intro ⟨v, n, hs⟩
    -- Reaches s₁ (halt v): ∃ n, steps n s₁ = halt v.
    -- Apply iterated weak step preservation: ∃ m, SubstBisimState (halt v) (steps m s₂).
    -- By halt_inv: steps m s₂ = halt v' with SubstBisimValue v v'.
    obtain ⟨m, hm⟩ := substBisimState_steps_preserves_weak n h
    rw [hs] at hm
    obtain ⟨v', hv'_eq, _hv_rel⟩ := substBisimState_halt_inv hm
    exact ⟨v', m, hv'_eq⟩
  · -- Error clause
    intro ⟨n, hs⟩
    obtain ⟨m, hm⟩ := substBisimState_steps_preserves_weak n h
    rw [hs] at hm
    have : steps m s₂ = .error := substBisimState_error_inv hm
    exact ⟨m, this⟩

--------------------------------------------------------------------------------
-- 12. Reflexivity of SubstBisimValue at well-formed values
--
-- The identity case: a well-formed value is SubstBisimValue-related to
-- itself when pos is BEYOND the value's env depth (so the substitution
-- doesn't reach any of the value's captured variables).
--------------------------------------------------------------------------------

/-- Construct initial `SubstBisimEnv` for β-substitution: the outer env
    (ρ.extend v_rhs, ρ) is related at position 1 with replacement = rhs,
    depth d+1. -/
theorem substBisimEnv_initial (d : Nat) (rhs : Term) (v_rhs : CekValue)
    (ρ : CekEnv)
    (_hrhs_closed : closedAt d rhs = true)
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
