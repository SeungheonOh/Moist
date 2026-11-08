import Moist.Verified.GuardsSoundness.Shift
import Moist.Verified.FloatOut.Lowering

/-! # Exchanging two blocks of binders

A body lowered under `bB ++ bA ++ env` (innermost first) and under
`bA ++ bB ++ env` differs by the renaming `blockSwap a b`, and the two
environments binding the same values in the two orders are related by it.
-/

namespace Moist.Verified.Guards

open Moist.CEK Moist.Plutus.Term
open Moist.MIR Moist.MIR.Advanced
open Moist.Verified Moist.Verified.Equivalence Moist.Verified.Contextual
open Moist.Verified.BetaValueRefines
open Moist.Verified.ShapeFacts
open Moist.Verified.FailFast
open Moist.Verified.FloatOut (LookupShift lowerTotalExpr_lookupShift)

/-- Source positions `1..b` (the inner block) go after the `a` positions of
    the other block; positions `b+1..b+a` come first. -/
def blockSwap (a b : Nat) (i : Nat) : Nat :=
  if i = 0 then 0 else if i ≤ b then i + a else if i ≤ a + b then i - b else i

theorem is0preserving_blockSwap (a b : Nat) : FundamentalRefines.Is0Preserving (blockSwap a b) := by
  refine ⟨by simp [blockSwap], fun n hn => ?_⟩
  unfold blockSwap
  split
  · omega
  · split
    · omega
    · split <;> omega

theorem extendAll_eq_knot : ∀ (ρ : CekEnv) (fs : List CekValue), extendAll ρ fs = KnownLists.extendAll ρ fs
  | _, [] => rfl
  | ρ, f :: fs => extendAll_eq_knot (ρ.extend f) fs

theorem extendAll_lookup_low' (ρ : CekEnv) (fs : List CekValue) (n : Nat) (h₁ : 0 < n)
    (h₂ : n ≤ fs.length) : (extendAll ρ fs).lookup n = fs[fs.length - n]? := by
  rw [extendAll_eq_knot]; exact KnownLists.extendAll_lookup_low ρ fs n h₁ h₂

theorem extendAll_lookup_high' (ρ : CekEnv) (fs : List CekValue) (n : Nat) (h : fs.length < n) :
    (extendAll ρ fs).lookup n = ρ.lookup (n - fs.length) := by
  rw [extendAll_eq_knot]; exact KnownLists.extendAll_lookup_high ρ fs n h

theorem shiftBisimEnv_of_lookups {σ : Nat → Nat} {ρ₁ ρ₂ : CekEnv} :
    ∀ (D : Nat), (∀ k, 0 < k → k ≤ D → ∃ v, ρ₁.lookup k = some v ∧ ρ₂.lookup (σ k) = some v ∧
      ValueWellFormed v) → ShiftBisimEnv σ D ρ₁ ρ₂
  | 0, _ => .zero
  | D + 1, h => by
    obtain ⟨v, h1, h2, hv⟩ := h (D + 1) (by omega) (Nat.le_refl _)
    exact .succ (shiftBisimEnv_of_lookups D fun k hk hkD => h k hk (by omega)) h1 h2
      (shiftBisimValue_refl_id v hv)

theorem getElem?_wf {fs : List CekValue} (h : ValueListWellFormed fs) {i : Nat} {v : CekValue}
    (hv : fs[i]? = some v) : ValueWellFormed v := by
  induction fs generalizing i with
  | nil => simp at hv
  | cons f fs ih =>
    cases h with
    | cons hf hfs =>
      cases i with
      | zero => simp at hv; subst hv; exact hf
      | succ i => exact ih hfs (by simpa using hv)

theorem getElem?_some_of_lt {fs : List CekValue} {i : Nat} (h : i < fs.length) : ∃ v, fs[i]? = some v :=
  ⟨_, List.getElem?_eq_getElem h⟩

/-- The two orders of two blocks of values, related by `blockSwap`. -/
theorem shiftBisimEnv_blockSwap {d : Nat} {ρ : CekEnv} (henv : EnvWellFormed d ρ) (hlen : d ≤ ρ.length)
    {fa fb : List CekValue} (hfa : ValueListWellFormed fa) (hfb : ValueListWellFormed fb) :
    ShiftBisimEnv (blockSwap fa.length fb.length) (d + fa.length + fb.length)
      (extendAll (extendAll ρ fa) fb) (extendAll (extendAll ρ fb) fa) := by
  apply shiftBisimEnv_of_lookups
  intro k hk hkD
  unfold blockSwap
  simp only [show k ≠ 0 by omega, if_false]
  by_cases h1 : k ≤ fb.length
  · simp only [h1, if_true]
    obtain ⟨v, hv⟩ := getElem?_some_of_lt (fs := fb) (i := fb.length - k) (by omega)
    refine ⟨v, ?_, ?_, getElem?_wf hfb hv⟩
    · rw [extendAll_lookup_low' _ fb k hk h1, hv]
    · rw [extendAll_lookup_high' _ fa (k + fa.length) (by omega), Nat.add_sub_cancel,
        extendAll_lookup_low' _ fb k hk h1, hv]
  · simp only [h1, if_false]
    by_cases h2 : k ≤ fa.length + fb.length
    · simp only [h2, if_true]
      obtain ⟨v, hv⟩ := getElem?_some_of_lt (fs := fa) (i := fa.length - (k - fb.length)) (by omega)
      refine ⟨v, ?_, ?_, getElem?_wf hfa hv⟩
      · rw [extendAll_lookup_high' _ fb k (by omega),
          extendAll_lookup_low' _ fa (k - fb.length) (by omega) (by omega), hv]
      · rw [extendAll_lookup_low' _ fa (k - fb.length) (by omega) (by omega), hv]
    · simp only [h2, if_false]
      obtain ⟨v, hv, hvwf⟩ := envWellFormed_lookup d henv (n := k - fb.length - fa.length)
        (by omega) (by omega)
      refine ⟨v, ?_, ?_, hvwf⟩
      · rw [extendAll_lookup_high' _ fb k (by omega), extendAll_lookup_high' _ fa _ (by omega), hv]
      · rw [extendAll_lookup_high' _ fa k (by omega), extendAll_lookup_high' _ fb _ (by omega),
          show k - fa.length - fb.length = k - fb.length - fa.length by omega, hv]

/-! ## Lowering a body under the two orders -/

theorem envLookupT_append : ∀ (pre env : List VarId) (z : VarId),
    envLookupT (pre ++ env) z =
      match envLookupT pre z with
      | some i => some i
      | none => (envLookupT env z).map (· + pre.length)
  | [], env, z => by
    simp only [List.nil_append, List.length_nil]
    cases envLookupT env z <;> simp [envLookupT, envLookupT.go]
  | y :: pre, env, z => by
    rw [List.cons_append, envLookupT_cons, envLookupT_cons]
    by_cases hyz : (y == z) = true
    · simp [hyz]
    · simp only [hyz, Bool.false_eq_true, if_false]
      rw [envLookupT_append pre env z]
      cases envLookupT pre z with
      | some i => simp
      | none =>
        simp only [Option.map_map, List.length_cons]
        cases envLookupT env z with
        | none => rfl
        | some k => simp; omega

theorem envLookupT_lt_len {l : List VarId} {z : VarId} {i : Nat} (h : envLookupT l z = some i) :
    i < l.length := envLookupT_lt h

theorem lookupShift_blockSwap {bA bB : List VarId} (env : List VarId)
    (hdis : ∀ x ∈ bA, ∀ y ∈ bB, (x == y) = false) :
    LookupShift (blockSwap bA.length bB.length) (bB.reverse ++ bA.reverse ++ env)
      (bA.reverse ++ bB.reverse ++ env) := by
  intro z
  rw [List.append_assoc, List.append_assoc, envLookupT_append bA.reverse (bB.reverse ++ env),
    envLookupT_append bB.reverse env, envLookupT_append bB.reverse (bA.reverse ++ env),
    envLookupT_append bA.reverse env]
  have notBoth : (envLookupT bA.reverse z).isSome = true → envLookupT bB.reverse z = none := by
    intro ha
    cases hb : envLookupT bB.reverse z with
    | none => rfl
    | some j =>
      exfalso
      obtain ⟨x, hx, hxz⟩ := envLookupT_some_mem ha
      obtain ⟨y, hy, hyz⟩ := envLookupT_some_mem (l := bB.reverse) (z := z) (by simp [hb])
      have := hdis x (List.mem_reverse.mp hx) y (List.mem_reverse.mp hy)
      have hxy : (x == y) = true := VarId.beq_trans x z y hxz (beq_symm' hyz)
      rw [this] at hxy; cases hxy
  cases hb : envLookupT bB.reverse z with
  | some j =>
    have hj := envLookupT_lt_len hb
    cases ha : envLookupT bA.reverse z with
    | some i => exact absurd (notBoth (by simp [ha])) (by simp [hb])
    | none =>
      simp only [Option.map_some, Option.some.injEq]
      unfold blockSwap
      simp only [List.length_reverse] at hj ⊢
      simp only [show j + 1 ≠ 0 by omega, if_false, show j + 1 ≤ bB.length by omega, if_true]
      omega
  | none =>
    cases ha : envLookupT bA.reverse z with
    | some i =>
      have hi := envLookupT_lt_len ha
      simp only [Option.map_some, Option.some.injEq]
      unfold blockSwap
      simp only [List.length_reverse] at hi ⊢
      simp only [show i + bB.length + 1 ≠ 0 by omega, if_false,
        show ¬ (i + bB.length + 1 ≤ bB.length) by omega, if_false,
        show i + bB.length + 1 ≤ bA.length + bB.length by omega, if_true]
      omega
    | none =>
      cases envLookupT env z with
      | none => rfl
      | some k =>
        simp only [Option.map_some, Option.some.injEq, List.length_reverse]
        unfold blockSwap
        simp only [show k + bA.length + bB.length + 1 ≠ 0 by omega, if_false,
          show ¬ (k + bA.length + bB.length + 1 ≤ bB.length) by omega,
          show ¬ (k + bA.length + bB.length + 1 ≤ bA.length + bB.length) by omega]
        omega
where
  beq_symm' {a b : VarId} (h : (a == b) = true) : (b == a) = true := by
    rw [VarId.beq_true_iff] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩
  envLookupT_some_mem {l : List VarId} {z : VarId} (h : (envLookupT l z).isSome = true) :
      ∃ x ∈ l, (x == z) = true := by
    induction l with
    | nil => simp [envLookupT, envLookupT.go] at h
    | cons y l ih =>
      rw [envLookupT_cons] at h
      by_cases hyz : (y == z) = true
      · exact ⟨y, .head _, hyz⟩
      · simp only [hyz, Bool.false_eq_true, if_false, Option.isSome_map] at h
        obtain ⟨x, hx, hxz⟩ := ih h
        exact ⟨x, .tail _ hx, hxz⟩

end Moist.Verified.Guards
