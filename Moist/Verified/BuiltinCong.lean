import Moist.Verified.Semantics
import Moist.Verified.StepLift
import Moist.Verified.ValueEqMono

/-! # Builtin congruence lemmas

This file contains the structural congruence theorems for Plutus builtins.
They are extracted from `Congruence.lean` so that the `ValueEq.lean` module
(which contains the full bisimulation / `stateEq_stateRelated`) can call
them from its `VBuiltin` case without creating a circular dependency.

**Parameterization**: theorems that would normally call `valueEq_refl`
directly take a `(veq_refl : ∀ v, ValueEq k v v)` parameter instead. This
is the same pattern that `evalBuiltin_cong_same_level` used in the old
`ValueEqBisim.lean:1268`. The pattern lets Builtin.lean sit upstream of
`ValueEq.lean` (where `valueEq_refl` is defined) while still exposing
reflexivity-dependent congruence. `evalBuiltin_full_cong` additionally
takes `veq_trans` because its chain-intermediate step needs transitivity.

The general helpers `ret_nil_halts`, `ret_nil_not_error`,
`ret_nil_halt_eq`, `apply_error_of_fn_error`, `apply_error_of_arg_error`
are also hosted here — they do not depend on `valueEq_refl` and are used
by both the builtin proofs and the constructor congruence theorems in
`Congruence.lean`. -/

namespace Moist.Verified.BuiltinCong

open Moist.CEK
open Moist.Plutus.Term (Term Const BuiltinFun)
open Moist.Verified.Semantics
open Moist.Verified.StepLift (liftState isActive steps_liftState
  liftState_ne_halt firstInactive step_liftState_active)

/-- A state cannot both halt and error. -/
theorem not_halts_and_errors {s : State} (hh : Halts s) (he : Reaches s .error) : False :=
  let ⟨_, hv⟩ := hh; reaches_halt_not_error hv he

/-- Derive `ListValueEq` reflexivity at a single level from per-value
    reflexivity at that level. Takes the reflexivity proof as a parameter
    to avoid importing the full `valueEq_refl` from `ValueEq.lean`
    (which would create a cycle). -/
theorem listValueEq_refl_of_at (k : Nat) (veq_refl_k : ∀ v, ValueEq k v v) :
    ∀ (vs : List CekValue), ListValueEq k vs vs
  | [] => by simp [ListValueEq]
  | v :: vs => by
    simp only [ListValueEq]
    exact ⟨veq_refl_k v, listValueEq_refl_of_at k veq_refl_k vs⟩

/-! ## extractConsts congruence from ListValueEq

If `ListValueEq (k+1) args1 args2`, then `VCon` values at corresponding
positions have equal constants (from `ValueEq (k+1) (VCon c1) (VCon c2) → c1 = c2`).
Non-VCon values cause `extractConsts` to fail on both sides equally. -/

private theorem extractConsts_cong :
    ∀ (k : Nat) (as1 as2 : List CekValue),
    ListValueEq (k + 1) as1 as2 →
    Moist.CEK.extractConsts as1 = Moist.CEK.extractConsts as2
  | _, [], [], _ => rfl
  | k, .VCon c1 :: rest1, .VCon c2 :: rest2, h => by
    simp only [ListValueEq] at h
    have hve := h.1; unfold ValueEq at hve; subst hve
    simp only [Moist.CEK.extractConsts]
    rw [extractConsts_cong k rest1 rest2 h.2]
  | k, .VCon _ :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, .VCon _ :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, .VCon _ :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, .VCon _ :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, .VCon _ :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, (.VLam _ _) :: _, _ => rfl
  | k, (.VLam _ _) :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VLam _ _) :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, (.VDelay _ _) :: _, _ => rfl
  | k, (.VDelay _ _) :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VDelay _ _) :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VConstr _ _) :: _, (.VConstr _ _) :: _, _ => rfl
  | k, (.VConstr _ _) :: _, (.VBuiltin _ _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VLam _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VDelay _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VConstr _ _) :: _, h => by
    simp only [ListValueEq] at h; exact absurd h.1 (by simp [ValueEq])
  | k, (.VBuiltin _ _ _) :: _, (.VBuiltin _ _ _) :: _, _ => rfl
  | _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
  | _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])

/-! ## evalBuiltin congruence

When `ListValueEq (k+1) args1 args2` and `va` is the same value,
`evalBuiltin b (va :: args1)` and `evalBuiltin b (va :: args2)` agree on
`none` and produce `ValueEq k`-related results when both succeed.

Strategy:
- `extractConsts` produces identical constant lists (from `extractConsts_cong`),
  so the `evalBuiltinConst` path returns identical `VCon` results.
- `evalBuiltinPassThrough` either returns `none` on both sides (same pattern
  match outcome), or returns values from specific positions in the arg list
  which are `ValueEq (k+1)` (hence `ValueEq k` by mono). -/

/-- VCon constant preserved across ValueEq. -/
theorem vcon_eq_of_valueEq_succ {k : Nat} {c : Const} {v : CekValue}
    (h : ValueEq (k + 1) (.VCon c) v) : v = .VCon c := by
  cases v with
  | VCon c' => simp only [ValueEq] at h; exact (congrArg CekValue.VCon h).symm
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEq] at h

/-- If v1 is not VCon and ValueEq v1 v2, then v2 is not VCon. -/
private theorem not_vcon_of_valueEq_succ {k : Nat} {v1 v2 : CekValue}
    (h : ValueEq (k + 1) v1 v2) (hv1 : ∀ c, v1 ≠ .VCon c) : ∀ c, v2 ≠ .VCon c := by
  intro c hc; subst hc
  cases v1 with
  | VCon c1 => exact absurd rfl (hv1 c1)
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => simp [ValueEq] at h

/-- extractConsts congruence for the full list `va :: args`. -/
private theorem extractConsts_cons_cong (k : Nat) (va : CekValue)
    (as1 as2 : List CekValue) (hargs : ListValueEq (k + 1) as1 as2) :
    Moist.CEK.extractConsts (va :: as1) = Moist.CEK.extractConsts (va :: as2) := by
  cases va with
  | VCon c =>
    simp only [Moist.CEK.extractConsts]
    rw [extractConsts_cong k as1 as2 hargs]
  | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ => rfl

/-- evalBuiltin congruence: when `ListValueEq (k+1) args1 args2` and `va`
    is the same value, `evalBuiltin b (va :: args1)` and `evalBuiltin b (va :: args2)`
    agree on none and produce `ValueEq k`-related results when both succeed.

    Strategy: `extractConsts (va :: args1) = extractConsts (va :: args2)`, so the
    constant-extraction path returns identical results. For `evalBuiltinPassThrough`,
    the function only inspects VCon constants at specific positions (preserved by
    `ListValueEq (k+1)`) and returns either VCon results (identical) or closures
    from matching positions (`ValueEq (k+1)`, hence `ValueEq k` by mono). -/
theorem evalBuiltin_cong (k : Nat) (b : BuiltinFun)
    (veq_refl_k1 : ∀ v, ValueEq (k + 1) v v)
    (va : CekValue) (args1 args2 : List CekValue)
    (hargs : ListValueEq (k + 1) args1 args2) :
    (Moist.CEK.evalBuiltin b (va :: args1) = none ↔
     Moist.CEK.evalBuiltin b (va :: args2) = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b (va :: args1) = some r1 →
              Moist.CEK.evalBuiltin b (va :: args2) = some r2 →
              ValueEq k r1 r2) := by
  have hec := extractConsts_cons_cong k va args1 args2 hargs
  -- Key helper: evalBuiltinPassThrough isNone agrees on both sides
  have hpt := evalBuiltinPassThrough_isNone_eq k b va args1 args2 hargs
  simp only [Moist.CEK.evalBuiltin]
  cases hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: args1) with
  | some v1 =>
    -- hp1 says isNone = false, so hp2 must also be some
    have hp2_not_none : Moist.CEK.evalBuiltinPassThrough b (va :: args2) ≠ none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args1)).isNone = false from by simp [hp1]] at hpt
      intro h; rw [h] at hpt; simp at hpt
    have ⟨v2, hp2⟩ : ∃ v, Moist.CEK.evalBuiltinPassThrough b (va :: args2) = some v := by
      cases h : Moist.CEK.evalBuiltinPassThrough b (va :: args2) with
      | some v => exact ⟨v, rfl⟩
      | none => contradiction
    rw [hp2]
    constructor; · simp
    · intro r1 r2 h1 h2
      injection h1 with h1; injection h2 with h2; subst h1; subst h2
      exact evalBuiltinPassThrough_valueEq k b veq_refl_k1 va args1 args2 hargs hp1 hp2
  | none =>
    have hp2_none : Moist.CEK.evalBuiltinPassThrough b (va :: args2) = none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args1)).isNone = true from by simp [hp1]] at hpt
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b (va :: args2) with
      | none => rfl
      | some _ => simp [hp2] at hpt
    rw [hp2_none, hec]
    have veq_refl_k : ∀ v, ValueEq k v v := fun v =>
      valueEq_mono k (k+1) (Nat.le_succ k) v v (veq_refl_k1 v)
    exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact veq_refl_k r1⟩
where
  listValueEq_same_length : ∀ (k : Nat) (as1 as2 : List CekValue),
      ListValueEq k as1 as2 → as1.length = as2.length
    | _, [], [], _ => rfl
    | k, _ :: as1', _ :: as2', h => by
      simp only [ListValueEq] at h
      simp only [List.length_cons]
      exact congrArg Nat.succ (listValueEq_same_length k as1' as2' h.2)
    | _, [], _ :: _, h => by simp [ListValueEq] at h
    | _, _ :: _, [], h => by simp [ListValueEq] at h
  evalBuiltinPassThrough_isNone_eq (k : Nat) (b : BuiltinFun) (va : CekValue)
      (as1 as2 : List CekValue)
      (hargs : ListValueEq (k + 1) as1 as2) :
      (Moist.CEK.evalBuiltinPassThrough b (va :: as1)).isNone =
      (Moist.CEK.evalBuiltinPassThrough b (va :: as2)).isNone := by
    -- For non-passthrough builtins: `cases b <;> try simp [evalBuiltinPassThrough]`
    -- closes all non-passthrough goals. For each passthrough builtin we case-split
    -- as1 and as2 simultaneously (using listValueEq_same_length to eliminate
    -- cross-length pairs via omega), then simp [evalBuiltinPassThrough] closes
    -- wrong-length cases, and explicit `cases` on the deciding VCon element handle
    -- the matching case.
    cases b <;> try simp [Moist.CEK.evalBuiltinPassThrough]
    -- IfThenElse: exact match on [elseV, thenV, VCon (Bool cond)] (as1 = [thenV, VCon(Bool cond)])
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨y1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp
      -- Only remaining: as1 = [x1, y1], as2 = [x2, y2]
      simp only [ListValueEq] at hargs
      cases y1 with
      | VCon c1 =>
        cases y2 with
        | VCon c2 =>
          have hc : c1 = c2 := by have := hargs.2.1; simp only [ValueEq] at this; exact this
          subst hc; cases c1 <;> simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.2.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases y2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.2.1.elim
        | _ => simp
    -- ChooseUnit: exact match on [result, VCon Unit] (as1 = [VCon Unit])
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp
      -- Only remaining: as1 = [x1], as2 = [x2]
      simp only [ListValueEq] at hargs
      cases x1 with
      | VCon c1 =>
        cases x2 with
        | VCon c2 =>
          have hc : c1 = c2 := by simp only [ValueEq] at hargs; exact hargs.1
          subst hc; cases c1 <;> simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases x2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.1.elim
        | _ => simp
    -- Trace: exact match on [result, VCon (String _)] (as1 = [VCon (String _)])
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp
      -- Only remaining: as1 = [x1], as2 = [x2]
      simp only [ListValueEq] at hargs
      cases x1 with
      | VCon c1 =>
        cases x2 with
        | VCon c2 =>
          have hc : c1 = c2 := by simp only [ValueEq] at hargs; exact hargs.1
          subst hc; cases c1 <;> simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases x2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.1.elim
        | _ => simp
    -- ChooseList: exact match on [consCase, nilCase, VCon (ConstDataList/ConstList l)]
    -- as1 must have 2 elements; deciding element is as1[1]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨x1, _ | ⟨y1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨x2, _ | ⟨y2, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp
      -- Only remaining: as1 = [x1, y1], as2 = [x2, y2]
      simp only [ListValueEq] at hargs
      cases y1 with
      | VCon c1 =>
        cases y2 with
        | VCon c2 =>
          have hc : c1 = c2 := by have := hargs.2.1; simp only [ValueEq] at this; exact this
          subst hc; cases c1 <;> simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.2.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases y2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.2.1.elim
        | _ => simp
    -- MkCons: match on [VCon (ConstList tail), elem] — va itself decides
    · cases va with
      | VCon c =>
        cases c with
        | ConstList tail =>
          have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
          rcases as1 with _ | ⟨x1, _ | ⟨_, _⟩⟩ <;>
          rcases as2 with _ | ⟨x2, _ | ⟨_, _⟩⟩ <;>
          (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
          try simp
          -- Only remaining: as1 = [x1], as2 = [x2]
          simp only [ListValueEq] at hargs
          cases x1 with
          | VCon c1 =>
            cases x2 with
            | VCon c2 =>
              have hc : c1 = c2 := by simp only [ValueEq] at hargs; exact hargs.1
              subst hc; simp
            | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
              simp only [ValueEq] at hargs; exact hargs.1.elim
          | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
            cases x2 with
            | VCon _ => simp only [ValueEq] at hargs; exact hargs.1.elim
            | _ => simp
        | _ => simp
      | _ => simp
    -- ChooseData: exact match on [bCase,iCase,listCase,mapCase,constrCase,VCon(Data d)]
    -- as1 must have 5 elements; deciding element is as1[4]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨x1, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      rcases as2 with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨x2, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      try simp
      -- Only remaining: as1 = [a0,a1,a2,a3,x1], as2 = [b0,b1,b2,b3,x2]
      simp only [ListValueEq] at hargs
      cases x1 with
      | VCon c1 =>
        cases x2 with
        | VCon c2 =>
          have hc : c1 = c2 := by have := hargs.2.2.2.2.1; simp only [ValueEq] at this; exact this
          subst hc; cases c1 with
          | Data d => cases d <;> simp
          | _ => simp
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp only [ValueEq] at hargs; exact hargs.2.2.2.2.1.elim
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        cases x2 with
        | VCon _ => simp only [ValueEq] at hargs; exact hargs.2.2.2.2.1.elim
        | _ => simp
  evalBuiltinPassThrough_valueEq (k : Nat) (b : BuiltinFun)
      (veq_refl_k1 : ∀ v, ValueEq (k + 1) v v) (va : CekValue)
      (as1 as2 : List CekValue)
      (hargs : ListValueEq (k + 1) as1 as2)
      {r1 r2 : CekValue}
      (hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: as1) = some r1)
      (hp2 : Moist.CEK.evalBuiltinPassThrough b (va :: as2) = some r2) :
      ValueEq k r1 r2 := by
    have veq_refl_k : ∀ v, ValueEq k v v := fun v =>
      valueEq_mono k (k+1) (Nat.le_succ k) v v (veq_refl_k1 v)
    -- For non-passthrough builtins: hp1 becomes none=some r1 via simp → False.
    -- For passthrough builtins: case-split as1 and as2 simultaneously (using
    -- listValueEq_same_length + omega to kill cross-length pairs); simp at hp1
    -- closes wrong-length cases; then use vcon_eq_of_valueEq_succ to prove
    -- the as2 deciding element equals the as1 one, and extract the return value.
    cases b <;> try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
    -- IfThenElse: [elseV=va, thenV=as1[0], VCon(Bool cond)=as1[1]]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨a1_1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨a2_1, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0, a1_1], as2 = [a2_0, a2_1]
      -- hp1/hp2 were simplified but may have conditions; handle by cases
      simp only [ListValueEq] at hargs
      cases a1_1 with
      | VCon c1 =>
        cases c1 with
        | Bool cond =>
          have ha2_1 := vcon_eq_of_valueEq_succ hargs.2.1
          subst ha2_1
          cases cond with
          | true =>
            simp at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) a1_0 a2_0 hargs.1
          | false =>
            simp at hp1 hp2
            subst hp1; subst hp2
            exact veq_refl_k va
        | _ => simp at hp1
      | _ => simp at hp1
    -- ChooseUnit: [result=va, VCon Unit=as1[0]] → r1 = va = r2
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0], as2 = [a2_0]
      simp only [ListValueEq] at hargs
      cases a1_0 with
      | VCon c1 =>
        cases c1 with
        | Unit =>
          have ha2_0 := vcon_eq_of_valueEq_succ hargs.1
          subst ha2_0
          simp at hp1 hp2
          subst hp1; subst hp2
          exact veq_refl_k va
        | _ => simp at hp1
      | _ => simp at hp1
    -- Trace: [result=va, VCon(String s)=as1[0]] → r1 = va = r2
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨_, _⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨_, _⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0], as2 = [a2_0]
      simp only [ListValueEq] at hargs
      cases a1_0 with
      | VCon c1 =>
        cases c1 with
        | String _ =>
          have ha2_0 := vcon_eq_of_valueEq_succ hargs.1
          subst ha2_0
          simp at hp1 hp2
          subst hp1; subst hp2
          exact veq_refl_k va
        | _ => simp at hp1
      | _ => simp at hp1
    -- ChooseList: [consCase=va, nilCase=as1[0], VCon(ConstDataList/ConstList l)=as1[1]]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨a1_1, _ | ⟨_, _⟩⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨a2_1, _ | ⟨_, _⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0, a1_1], as2 = [a2_0, a2_1]
      simp only [ListValueEq] at hargs
      cases a1_1 with
      | VCon c1 =>
        have ha2_1 := vcon_eq_of_valueEq_succ hargs.2.1
        subst ha2_1
        cases c1 with
        | ConstDataList l =>
          simp at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hargs.1
          | false =>
            simp only [h] at hp1 hp2
            subst hp1; subst hp2
            exact veq_refl_k va
        | ConstList l =>
          simp at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hargs.1
          | false =>
            simp only [h] at hp1 hp2
            subst hp1; subst hp2
            exact veq_refl_k va
        | _ => simp at hp1
      | _ => simp at hp1
    -- MkCons: va = VCon (ConstList tail), elem = as1[0] = VCon c1 → r = VCon (ConstList (c1::tail))
    · cases va with
      | VCon c =>
        cases c with
        | ConstList tail =>
          have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
          rcases as1 with _ | ⟨a1_0, _ | ⟨_, _⟩⟩ <;>
          rcases as2 with _ | ⟨a2_0, _ | ⟨_, _⟩⟩ <;>
          (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          -- Only remaining: as1 = [a1_0], as2 = [a2_0]
          simp only [ListValueEq] at hargs
          cases a1_0 with
          | VCon c1 =>
            have ha2_0 := vcon_eq_of_valueEq_succ hargs.1
            subst ha2_0
            simp at hp1 hp2
            subst hp1; subst hp2
            exact veq_refl_k (.VCon (.ConstList (c1 :: tail)))
          | _ => simp at hp1
        | _ => simp at hp1
      | _ => simp at hp1
    -- ChooseData: [bCase=va, iCase=as1[0], ..., constrCase=as1[3], VCon(Data d)=as1[4]]
    · have hlen := listValueEq_same_length (k + 1) as1 as2 hargs
      rcases as1 with _ | ⟨a1_0, _ | ⟨a1_1, _ | ⟨a1_2, _ | ⟨a1_3, _ | ⟨a1_4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      rcases as2 with _ | ⟨a2_0, _ | ⟨a2_1, _ | ⟨a2_2, _ | ⟨a2_3, _ | ⟨a2_4, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      (try (simp only [List.length_cons, List.length_nil] at hlen; omega)) <;>
      simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
      -- Only remaining: as1 = [a1_0,a1_1,a1_2,a1_3,a1_4], as2 = [a2_0,...,a2_4]
      simp only [ListValueEq] at hargs
      cases a1_4 with
      | VCon c1 =>
        cases c1 with
        | Data d =>
          have ha2_4 := vcon_eq_of_valueEq_succ hargs.2.2.2.2.1
          subst ha2_4
          simp at hp1 hp2
          obtain ⟨hv0, hv1, hv2, hv3, _, _⟩ := hargs
          cases d with
          | Constr _ _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv3
          | Map _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv2
          | List _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv1
          | I _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) _ _ hv0
          | B _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact veq_refl_k va
        | _ => simp at hp1
      | _ => simp at hp1

theorem ret_nil_halts (v : CekValue) :
    Reaches (.ret [] v) (.halt v) := ⟨1, rfl⟩

/-- `ret [] v` never errors. -/
theorem ret_nil_not_error (v : CekValue)
    (h : Reaches (.ret [] v) .error) : False := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_halt] at hn

/-- Extract value from `Reaches (.ret [] v) (.halt w)`: `w = v`. -/
theorem ret_nil_halt_eq (v w : CekValue)
    (h : Reaches (.ret [] v) (.halt w)) : w = v := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [steps] at hn
  | succ n => simp [steps, step, steps_halt] at hn; exact hn.symm

/-- If `tf` errors, `Apply tf ta` errors.
    Build manually via liftState machinery (cannot use apply_compose since ta may not halt). -/
theorem apply_error_of_fn_error (ρ : CekEnv) (tf ta : Term)
    (herr : Reaches (.compute [] ρ tf) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error := by
  obtain ⟨n, hn⟩ := herr
  have h1 : steps 1 (.compute [] ρ (.Apply tf ta)) =
      .compute [.arg ta ρ] ρ tf := by simp [steps, step]
  have hlift : State.compute [.arg ta ρ] ρ tf =
      liftState [.arg ta ρ] (.compute [] ρ tf) := by simp [liftState]
  have h_inner_err : isActive (steps n (.compute [] ρ tf)) = false := by rw [hn]; rfl
  obtain ⟨K, _, hK_inact, hK_min⟩ :=
    firstInactive (.compute [] ρ tf) n ⟨n, Nat.le_refl _, h_inner_err⟩
  have h_comm := steps_liftState [.arg ta ρ] K (.compute [] ρ tf) hK_min
  generalize h_sK : steps K (.compute [] ρ tf) = sK at hK_inact h_comm
  match sK with
  | .compute .. => simp [isActive] at hK_inact
  | .ret (_ :: _) _ => simp [isActive] at hK_inact
  | .error =>
    exact ⟨1 + K, by rw [steps_trans, h1, hlift, h_comm]; simp [liftState]⟩
  | .halt v =>
    exfalso; have : steps n (.compute [] ρ tf) = .halt v := by
      have : n = K + (n - K) := by omega
      rw [this, steps_trans, h_sK, steps_halt]
    rw [hn] at this; simp at this
  | .ret [] v =>
    exfalso; exact reaches_halt_not_error ⟨K + 1, by rw [steps_trans, h_sK]; rfl⟩ ⟨n, hn⟩

/-- If `tf` halts with `vf` and `ta` errors, `Apply tf ta` errors.
    Proof: compose the tf halting phase, the 1-step arg-frame transition,
    and the ta error phase using liftState. -/
theorem apply_error_of_arg_error (ρ : CekEnv) (tf ta : Term)
    (vf : CekValue) (hf_halt : Reaches (.compute [] ρ tf) (.halt vf))
    (ha_err : Reaches (.compute [] ρ ta) .error) :
    Reaches (.compute [] ρ (.Apply tf ta)) .error := by
  -- Phase 1: show compute [funV vf] ρ ta reaches error
  -- (embed ta-error into the [funV vf] context via liftState)
  obtain ⟨Na, hNa⟩ := ha_err
  have hlift_a : State.compute [.funV vf] ρ ta =
      liftState [.funV vf] (.compute [] ρ ta) := by simp [liftState]
  have h_a_inact : isActive (steps Na (.compute [] ρ ta)) = false := by rw [hNa]; rfl
  obtain ⟨Ka, _, hKa_inact, hKa_min⟩ :=
    firstInactive (.compute [] ρ ta) Na ⟨Na, Nat.le_refl _, h_a_inact⟩
  have h_comm_a := steps_liftState [.funV vf] Ka (.compute [] ρ ta) hKa_min
  generalize h_sKa : steps Ka (.compute [] ρ ta) = sKa at hKa_inact h_comm_a
  have h_lifted_a_err : Reaches (.compute [.funV vf] ρ ta) .error := by
    match sKa with
    | .compute .. => simp [isActive] at hKa_inact
    | .ret (_ :: _) _ => simp [isActive] at hKa_inact
    | .error =>
      exact ⟨Ka, by rw [hlift_a, h_comm_a]; simp [liftState]⟩
    | .halt va =>
      exfalso
      have : steps Na (.compute [] ρ ta) = .halt va := by
        have : Na = Ka + (Na - Ka) := by omega
        rw [this, steps_trans, h_sKa, steps_halt]
      rw [hNa] at this; simp at this
    | .ret [] va =>
      exfalso
      exact reaches_halt_not_error ⟨Ka + 1, by rw [steps_trans, h_sKa]; rfl⟩ ⟨Na, hNa⟩
  -- Phase 2: ret [arg ta ρ] vf reaches error
  -- (one step to compute [funV vf] ρ ta, then error)
  obtain ⟨me, hme⟩ := h_lifted_a_err
  have h_ret_err : Reaches (.ret [.arg ta ρ] vf) .error :=
    ⟨1 + me, by rw [steps_trans]; simp [steps, step, hme]⟩
  -- Phase 3: embed tf-halt into the [arg ta ρ] context via liftState,
  -- then chain with h_ret_err to get the full Apply reaching error
  obtain ⟨Nf, hNf⟩ := hf_halt
  have hlift_f : State.compute [.arg ta ρ] ρ tf =
      liftState [.arg ta ρ] (.compute [] ρ tf) := by simp [liftState]
  have h_f_inact : isActive (steps Nf (.compute [] ρ tf)) = false := by rw [hNf]; rfl
  obtain ⟨Kf, hKf_le, hKf_inact, hKf_min⟩ :=
    firstInactive (.compute [] ρ tf) Nf ⟨Nf, Nat.le_refl _, h_f_inact⟩
  have h_comm_f := steps_liftState [.arg ta ρ] Kf (.compute [] ρ tf) hKf_min
  have h_not_error_f : steps Kf (.compute [] ρ tf) ≠ .error := by
    intro herr
    have : steps Nf (.compute [] ρ tf) = .error := by
      have : Nf = Kf + (Nf - Kf) := by omega
      rw [this, steps_trans, herr, steps_error]
    rw [hNf] at this; simp at this
  obtain ⟨mr, hmr⟩ := h_ret_err
  generalize h_sKf : steps Kf (.compute [] ρ tf) = sKf at hKf_inact h_comm_f h_not_error_f
  match sKf with
  | .compute .. => simp [isActive] at hKf_inact
  | .ret (_ :: _) _ => simp [isActive] at hKf_inact
  | .error => exact absurd rfl h_not_error_f
  | .halt vf' =>
    have hvf_eq : vf' = vf := reaches_unique ⟨Kf, h_sKf⟩ ⟨Nf, hNf⟩
    subst hvf_eq
    exact ⟨1 + Kf + mr, by
      have : 1 + Kf + mr = 1 + (Kf + mr) := by omega
      rw [this, steps_trans]; simp [steps, step]
      rw [hlift_f, steps_trans, h_comm_f]; simp [liftState, hmr]⟩
  | .ret [] vf' =>
    have hvf_eq : vf' = vf :=
      reaches_unique ⟨Kf + 1, by rw [steps_trans, h_sKf]; rfl⟩ ⟨Nf, hNf⟩
    subst hvf_eq
    exact ⟨1 + Kf + mr, by
      have : 1 + Kf + mr = 1 + (Kf + mr) := by omega
      rw [this, steps_trans]; simp [steps, step]
      rw [hlift_f, steps_trans, h_comm_f]; simp [liftState, hmr]⟩
/-- evalBuiltin congruence for differing first arg, same tail.
    If `ValueEq (k+1) va va'`, then `evalBuiltin b (va :: args)` and
    `evalBuiltin b (va' :: args)` agree on none and produce ValueEq k
    related results.

    The proof reuses the existing `evalBuiltin_cong` (which fixes the head
    and varies the tail) via a middle term: we chain
    `evalBuiltin b (va :: args)` ↔ `evalBuiltin b (va :: args)` (refl)
    against `evalBuiltin b (va :: args)` ↔ `evalBuiltin b (va' :: args)`
    using the list `ListValueEq (k+1) (va :: args) (va' :: args)`.

    Since `extractConsts_cong` already handles full-list ListValueEq, and
    `evalBuiltinPassThrough` value agreement follows from
    `evalBuiltinPassThrough_valueEq`, we can assemble both paths. -/
theorem evalBuiltin_cong_first (k : Nat) (b : BuiltinFun)
    (veq_refl_k1 : ∀ v, ValueEq (k + 1) v v)
    (va va' : CekValue) (args : List CekValue)
    (hva : ValueEq (k + 1) va va') :
    (Moist.CEK.evalBuiltin b (va :: args) = none ↔
     Moist.CEK.evalBuiltin b (va' :: args) = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b (va :: args) = some r1 →
              Moist.CEK.evalBuiltin b (va' :: args) = some r2 →
              ValueEq k r1 r2) := by
  have veq_refl_k : ∀ v, ValueEq k v v := fun v =>
    valueEq_mono k (k+1) (Nat.le_succ k) v v (veq_refl_k1 v)
  have hfull : ListValueEq (k + 1) (va :: args) (va' :: args) := by
    simp only [ListValueEq]; exact ⟨hva, listValueEq_refl_of_at (k + 1) veq_refl_k1 args⟩
  have hec : Moist.CEK.extractConsts (va :: args) =
             Moist.CEK.extractConsts (va' :: args) :=
    extractConsts_cong k _ _ hfull
  -- Same structure as evalBuiltin_cong: case-split on evalBuiltinPassThrough,
  -- using per-builtin helpers for the varying-head case.
  have hpt := evalBuiltinPassThrough_isNone_eq_first k b va va' args hva
  simp only [Moist.CEK.evalBuiltin]
  cases hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: args) with
  | some v1 =>
    have hp2_not_none : Moist.CEK.evalBuiltinPassThrough b (va' :: args) ≠ none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args)).isNone = false from by simp [hp1]] at hpt
      intro h; rw [h] at hpt; simp at hpt
    have ⟨v2, hp2⟩ : ∃ v, Moist.CEK.evalBuiltinPassThrough b (va' :: args) = some v := by
      cases h : Moist.CEK.evalBuiltinPassThrough b (va' :: args) with
      | some v => exact ⟨v, rfl⟩
      | none => contradiction
    rw [hp2]
    constructor; · simp
    · intro r1 r2 h1 h2
      injection h1 with h1; injection h2 with h2; subst h1; subst h2
      exact evalBuiltinPassThrough_valueEq_first k b veq_refl_k1 va va' args hva hp1 hp2
  | none =>
    have hp2_none : Moist.CEK.evalBuiltinPassThrough b (va' :: args) = none := by
      rw [show (Moist.CEK.evalBuiltinPassThrough b (va :: args)).isNone = true from by simp [hp1]] at hpt
      cases hp2 : Moist.CEK.evalBuiltinPassThrough b (va' :: args) with
      | none => rfl
      | some _ => simp [hp2] at hpt
    rw [hp2_none, hec]
    exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact veq_refl_k r1⟩
where
  -- isNone of evalBuiltinPassThrough agrees when the first arg varies by ValueEq (k+1).
  -- The deciding VCon element in each passthrough builtin is either in `args` (unchanged)
  -- or is the head va itself (preserved as the same VCon by vcon_eq_of_valueEq_succ).
  evalBuiltinPassThrough_isNone_eq_first (k : Nat) (b : BuiltinFun)
      (va va' : CekValue) (args : List CekValue)
      (hva : ValueEq (k + 1) va va') :
      (Moist.CEK.evalBuiltinPassThrough b (va :: args)).isNone =
      (Moist.CEK.evalBuiltinPassThrough b (va' :: args)).isNone := by
    cases b <;> try simp [Moist.CEK.evalBuiltinPassThrough]
    -- IfThenElse: args decides (args[1] = VCon (Bool cond)); va=elseV is not inspected for isNone
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try simp
      -- remaining: args = [x, y]
      cases y with
      | VCon c => cases c <;> simp
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp
    -- ChooseUnit: args decides (args[0] = VCon Unit); va=result is not inspected for isNone
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try simp
      -- remaining: args = [x]
      cases x with
      | VCon c => cases c <;> simp
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp
    -- Trace: args decides (args[0] = VCon (String _)); va=result is not inspected for isNone
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try simp
      -- remaining: args = [x]
      cases x with
      | VCon c => cases c <;> simp
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp
    -- ChooseList: args decides (args[1] = VCon (ConstDataList/ConstList)); va=consCase not inspected
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try simp
      -- remaining: args = [x, y]
      cases y with
      | VCon c => cases c <;> simp
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp
    -- MkCons: va itself is inspected (must be VCon (ConstList _)).
    -- ValueEq (k+1) preserves VCon identity: if va = VCon c then va' = VCon c (subst).
    -- After subst, both sides are identical, so isNone equality is trivially rfl.
    · cases va with
      | VCon c =>
        have hva'_eq := vcon_eq_of_valueEq_succ hva
        subst hva'_eq
        -- va' = va now; both sides identical → goal is X.isNone = X.isNone
        rfl
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        -- va is not VCon, so evalBuiltinPassThrough MkCons (va :: _) = none.
        -- By not_vcon_of_valueEq_succ, va' is also not VCon, so same for va'.
        have hva'_not_vcon : ∀ c, va' ≠ .VCon c :=
          not_vcon_of_valueEq_succ hva (by intro c; simp)
        cases va' with
        | VCon c => exact absurd rfl (hva'_not_vcon c)
        | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
          simp
    -- ChooseData: args decides (args[4] = VCon (Data d)); va=bCase not inspected for isNone
    · rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      try simp
      -- remaining: args = [a0, a1, a2, a3, x]
      cases x with
      | VCon c =>
        cases c with
        | Data d => cases d <;> simp
        | _ => simp
      | VLam _ _ | VDelay _ _ | VConstr _ _ | VBuiltin _ _ _ =>
        simp
  -- ValueEq k of results when both evalBuiltinPassThrough return some and the head varies.
  -- Returned values are either from `args` (same → valueEq_refl) or va/va' (ValueEq k by mono).
  evalBuiltinPassThrough_valueEq_first (k : Nat) (b : BuiltinFun)
      (veq_refl_k1 : ∀ v, ValueEq (k + 1) v v)
      (va va' : CekValue) (args : List CekValue)
      (hva : ValueEq (k + 1) va va')
      {r1 r2 : CekValue}
      (hp1 : Moist.CEK.evalBuiltinPassThrough b (va :: args) = some r1)
      (hp2 : Moist.CEK.evalBuiltinPassThrough b (va' :: args) = some r2) :
      ValueEq k r1 r2 := by
    have veq_refl_k : ∀ v, ValueEq k v v := fun v =>
      valueEq_mono k (k+1) (Nat.le_succ k) v v (veq_refl_k1 v)
    cases b <;> try (simp [Moist.CEK.evalBuiltinPassThrough] at hp1)
    -- IfThenElse: args = [thenV, VCon (Bool cond)]; va=elseV
    -- Wrong lengths give hp1: none = some r1, closed by simp. Matching length: args = [x, y].
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try (simp at hp1)
      -- remaining: args = [x, y]
      cases y with
      | VCon c =>
        cases c with
        | Bool cond =>
          cases cond with
          | true =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2; exact veq_refl_k x
          | false =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp at hp1
      | _ => simp at hp1
    -- ChooseUnit: args = [VCon Unit]; va=result
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try (simp at hp1)
      -- remaining: args = [x]
      cases x with
      | VCon c =>
        cases c with
        | Unit =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          subst hp1; subst hp2
          exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp at hp1
      | _ => simp at hp1
    -- Trace: args = [VCon (String s)]; va=result
    · rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
      try (simp at hp1)
      -- remaining: args = [x]
      cases x with
      | VCon c =>
        cases c with
        | String _ =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          subst hp1; subst hp2
          exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp at hp1
      | _ => simp at hp1
    -- ChooseList: args = [nilCase, VCon(l)]; va=consCase
    · rcases args with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      try (simp at hp1)
      -- remaining: args = [x, y]
      cases y with
      | VCon c =>
        cases c with
        | ConstDataList l =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2; exact veq_refl_k x
          | false =>
            simp only [h] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | ConstList l =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases h : l.isEmpty with
          | true =>
            simp only [h, ite_true] at hp1 hp2
            subst hp1; subst hp2; exact veq_refl_k x
          | false =>
            simp only [h] at hp1 hp2
            subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp at hp1
      | _ => simp at hp1
    -- MkCons: va = VCon (ConstList tail); args = [VCon c1]
    -- After vcon_eq_of_valueEq_succ + subst, va' = va, so hp2 has same LHS as hp1.
    · cases va with
      | VCon c =>
        have hva'_eq := vcon_eq_of_valueEq_succ hva
        subst hva'_eq
        cases c with
        | ConstList tail =>
          rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;>
          try (simp at hp1)
          -- remaining: args = [x]
          cases x with
          | VCon c1 =>
            simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
            subst hp1; subst hp2; exact veq_refl_k _
          | _ => simp at hp1
        | _ => simp at hp1
      | _ => simp at hp1
    -- ChooseData: args = [iCase, listCase, mapCase, constrCase, VCon (Data d)]; va=bCase
    · rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hp1)
      -- remaining: args = [a0, a1, a2, a3, x]
      cases x with
      | VCon c =>
        cases c with
        | Data d =>
          simp [Moist.CEK.evalBuiltinPassThrough] at hp1 hp2
          cases d with
          | Constr _ _ => simp at hp1 hp2; subst hp1; subst hp2; exact veq_refl_k a3
          | Map _ => simp at hp1 hp2; subst hp1; subst hp2; exact veq_refl_k a2
          | List _ => simp at hp1 hp2; subst hp1; subst hp2; exact veq_refl_k a1
          | I _ => simp at hp1 hp2; subst hp1; subst hp2; exact veq_refl_k a0
          | B _ =>
            simp at hp1 hp2; subst hp1; subst hp2
            exact valueEq_mono k (k + 1) (Nat.le_succ k) va va' hva
        | _ => simp at hp1
      | _ => simp at hp1

/-- Full-list evalBuiltin congruence: when `ListValueEq (k+1) args1 args2`,
    `evalBuiltin b args1` and `evalBuiltin b args2` agree on `none` and
    produce `ValueEq k`-related results when both succeed.

    Proof: chain via intermediate list `hd2 :: tl1` using
    `evalBuiltin_cong_first` (varying head) and `evalBuiltin_cong` (varying tail). -/
theorem evalBuiltin_full_cong (k : Nat) (b : BuiltinFun)
    (veq_refl_k1 : ∀ v, ValueEq (k + 1) v v)
    (veq_trans_k : ∀ v1 v2 v3, ValueEq k v1 v2 → ValueEq k v2 v3 → ValueEq k v1 v3)
    (args1 args2 : List CekValue)
    (hargs : ListValueEq (k + 1) args1 args2) :
    (Moist.CEK.evalBuiltin b args1 = none ↔
     Moist.CEK.evalBuiltin b args2 = none) ∧
    (∀ r1 r2, Moist.CEK.evalBuiltin b args1 = some r1 →
              Moist.CEK.evalBuiltin b args2 = some r2 →
              ValueEq k r1 r2) := by
  have veq_refl_k : ∀ v, ValueEq k v v := fun v =>
    valueEq_mono k (k+1) (Nat.le_succ k) v v (veq_refl_k1 v)
  cases args1 with
  | nil =>
    cases args2 with
    | nil => exact ⟨Iff.rfl, fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact veq_refl_k r1⟩
    | cons _ _ => simp [ListValueEq] at hargs
  | cons hd1 tl1 =>
    cases args2 with
    | nil => simp [ListValueEq] at hargs
    | cons hd2 tl2 =>
      simp only [ListValueEq] at hargs
      have ⟨hhd, htl⟩ := hargs
      have h1 := evalBuiltin_cong_first k b veq_refl_k1 hd1 hd2 tl1 hhd
      have h2 := evalBuiltin_cong k b veq_refl_k1 hd2 tl1 tl2 htl
      constructor
      · exact h1.1.trans h2.1
      · intro r1 r2 hr1 hr2
        -- Chain: evalBuiltin b (hd1::tl1) = some r1
        --        evalBuiltin b (hd2::tl2) = some r2
        -- Need intermediate: evalBuiltin b (hd2::tl1)
        cases hmid : Moist.CEK.evalBuiltin b (hd2 :: tl1) with
        | none =>
          -- hd1::tl1 → some r1, but hd2::tl1 → none; contradiction via h1.1.mpr
          exact absurd (h1.1.mpr hmid) (by rw [hr1]; simp)
        | some rmid =>
          exact veq_trans_k r1 rmid r2
            (h1.2 r1 rmid hr1 hmid)
            (h2.2 rmid r2 hmid hr2)


end Moist.Verified.BuiltinCong
