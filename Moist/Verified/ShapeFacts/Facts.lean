import Moist.Verified.ShapeFacts.Relation
import Moist.Verified.MIR.AlphaEqBool
import Moist.MIR.Optimize.Advanced.Shapes

/-! # Fact environments

A fact environment `Γ : List (VarId × Expr)` records, for some binders, the
right-hand side whose successful evaluation produced the bound value.

`FactsHold P Γ env ρ` states that for every recorded binder `x` bound in the
lowering environment `env` at index `i`, the runtime value `ρ.lookup (i+1)`
was produced in a strictly older suffix `env.drop k` / `dropEnv k ρ` of the
current environment, as described by `P` (for instance `Produces`: the
lowered right-hand side halts there with that value). The fact is about the
very value bound in `ρ`, so it remains valid however that binder is used
afterwards, and a binding whose evaluation failed never extends `ρ`.

Lookups and suffixes agree when the lowering environment binds every name at
most once (`EnvDistinct`).
-/

namespace Moist.Verified.ShapeFacts

open Moist.CEK Moist.Plutus.Term
open Moist.MIR
open Moist.Verified Moist.Verified.Equivalence
open Moist.Verified.BetaValueRefines

/-! ## Environment suffixes -/

def dropEnv : Nat → CekEnv → CekEnv
  | 0, ρ => ρ
  | _ + 1, .nil => .nil
  | k + 1, .cons _ ρ => dropEnv k ρ

@[simp] theorem dropEnv_zero (ρ : CekEnv) : dropEnv 0 ρ = ρ := rfl

@[simp] theorem dropEnv_extend (k : Nat) (ρ : CekEnv) (v : CekValue) :
    dropEnv (k + 1) (ρ.extend v) = dropEnv k ρ := rfl

theorem dropEnv_add : ∀ (j k : Nat) (ρ : CekEnv), dropEnv k (dropEnv j ρ) = dropEnv (j + k) ρ
  | 0, k, ρ => by simp
  | j + 1, k, .nil => by
    cases k <;> simp [dropEnv] <;> (rename_i k; cases (j + 1 + (k + 1)) <;> rfl)
  | j + 1, k, .cons v ρ => by
    rw [show j + 1 + k = (j + k) + 1 by omega]
    exact dropEnv_add j k ρ

theorem dropEnv_lookup : ∀ (k : Nat) (ρ : CekEnv) (n : Nat), 0 < n →
    (dropEnv k ρ).lookup n = ρ.lookup (n + k)
  | 0, ρ, n, _ => rfl
  | k + 1, .nil, n, _ => by
    cases n with
    | zero => rfl
    | succ n => rfl
  | k + 1, .cons v ρ, n, hn => by
    rw [show n + (k + 1) = (n + k) + 1 by omega]
    show (dropEnv k ρ).lookup n = (CekEnv.cons v ρ).lookup (n + k + 1)
    rw [dropEnv_lookup k ρ n hn]
    match n + k, (show n + k ≠ 0 by omega) with
    | m + 1, _ => rfl

theorem dropEnv_length : ∀ (k : Nat) (ρ : CekEnv), (dropEnv k ρ).length = ρ.length - k
  | 0, _ => rfl
  | k + 1, .nil => by simp [dropEnv, CekEnv.length]
  | k + 1, .cons _ ρ => by
    simp only [dropEnv, dropEnv_length k ρ, CekEnv.length]
    omega

theorem envWellFormed_dropEnv {d : Nat} {ρ : CekEnv} (h : EnvWellFormed d ρ)
    (k : Nat) : EnvWellFormed (d - k) (dropEnv k ρ) := by
  induction d with
  | zero => simpa using (EnvWellFormed.zero : EnvWellFormed 0 (dropEnv k ρ))
  | succ d ih =>
    cases h with
    | succ hrest hlen hl hv =>
      by_cases hk : k ≤ d
      · rw [show d + 1 - k = (d - k) + 1 by omega]
        refine .succ (ih hrest) ?_ ?_ hv
        · rw [dropEnv_length]; omega
        · rw [dropEnv_lookup k ρ _ (by omega), show d - k + 1 + k = d + 1 by omega]; exact hl
      · rw [show d + 1 - k = 0 by omega]; exact .zero

/-! ## Distinct lowering environments -/

def EnvDistinct : List VarId → Prop
  | [] => True
  | x :: env => envLookupT env x = none ∧ EnvDistinct env

theorem envLookupT_congr {x y : VarId} (h : (x == y) = true) (env : List VarId) :
    envLookupT env x = envLookupT env y := by
  simp only [envLookupT]; exact MIR.envLookupT_go_congr h env 0

theorem varId_beq_symm {x y : VarId} (h : (x == y) = true) : (y == x) = true := by
  rw [VarId.beq_true_iff] at h ⊢; exact ⟨h.1.symm, h.2.symm⟩

theorem varId_beq_self (x : VarId) : (x == x) = true := by
  rw [VarId.beq_true_iff]; exact ⟨rfl, rfl⟩

theorem envLookupT_cons (x y : VarId) (env : List VarId) :
    envLookupT (x :: env) y = if (x == y) = true then some 0 else (envLookupT env y).map (· + 1) := by
  split
  · rename_i h; exact MIR.envLookupT_cons_of_beq h env
  · rename_i h; exact envLookupT_cons_neq x y env (by simpa using h)

theorem EnvDistinct.drop_lookup :
    ∀ {env : List VarId} (j : Nat) {y : VarId} {i : Nat}, EnvDistinct env →
      envLookupT (env.drop j) y = some i → envLookupT env y = some (i + j)
  | env, 0, y, i, _, h => by simpa using h
  | [], _ + 1, y, i, _, h => by simp [envLookupT, envLookupT.go] at h
  | x :: env, j + 1, y, i, hd, h => by
    simp only [List.drop_succ_cons] at h
    have ih := EnvDistinct.drop_lookup j hd.2 h
    rw [envLookupT_cons]
    split
    · rename_i hxy
      have := envLookupT_congr hxy env
      rw [hd.1, ih] at this
      cases this
    · rw [ih]; simp; omega

theorem EnvDistinct.drop : ∀ {env : List VarId} (j : Nat), EnvDistinct env → EnvDistinct (env.drop j)
  | env, 0, h => by simpa using h
  | [], _ + 1, _ => trivial
  | _ :: env, j + 1, h => by simpa using EnvDistinct.drop j h.2

theorem envLookupT_drop_of_ge :
    ∀ {env : List VarId} (j : Nat) {y : VarId} {i : Nat},
      envLookupT env y = some i → j ≤ i → envLookupT (env.drop j) y = some (i - j)
  | env, 0, y, i, h, _ => by simpa using h
  | [], _ + 1, y, i, h, _ => by simp [envLookupT, envLookupT.go] at h
  | x :: env, j + 1, y, i, h, hji => by
    rw [envLookupT_cons] at h
    split at h
    · cases h; omega
    · cases hl : envLookupT env y with
      | none => rw [hl] at h; cases h
      | some i' =>
        rw [hl] at h; simp at h; subst h
        simp only [List.drop_succ_cons]
        rw [envLookupT_drop_of_ge j hl (by omega)]
        congr 1; omega

/-! ## Facts -/

/-- `rhs` lowered in `env` halts in `ρ` with `v`. -/
def Produces (env : List VarId) (ρ : CekEnv) (rhs : Expr) (v : CekValue) : Prop :=
  ∃ t, lowerTotalExpr env rhs = some t ∧ Halts ρ t v

def FactsHold (P : List VarId → CekEnv → Expr → CekValue → Prop)
    (Γ : List (VarId × Expr)) (env : List VarId) (ρ : CekEnv) : Prop :=
  ∀ x entry i, Γ.find? (fun e => e.1 == x) = some entry → envLookupT env x = some i →
    ∃ v k, i < k ∧ k ≤ env.length ∧ ρ.lookup (i + 1) = some v ∧
      P (env.drop k) (dropEnv k ρ) entry.2 v

theorem FactsHold.nil (P : List VarId → CekEnv → Expr → CekValue → Prop) (env : List VarId)
    (ρ : CekEnv) : FactsHold P [] env ρ := by
  intro x entry i h; simp at h

theorem FactsHold.mono {P Q : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    (h : FactsHold P Γ env ρ) (hPQ : ∀ env ρ rhs v, P env ρ rhs v → Q env ρ rhs v) :
    FactsHold Q Γ env ρ := by
  intro x entry i hf hl
  obtain ⟨v, k, hik, hk, hv, hp⟩ := h x entry i hf hl
  exact ⟨v, k, hik, hk, hv, hPQ _ _ _ _ hp⟩

/-- A new binder, recorded together with the right-hand side that produced
    its value. -/
theorem FactsHold.push {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {x : VarId} {rhs : Expr}
    {w : CekValue} (h : FactsHold P Γ env ρ) (hw : P env ρ rhs w) :
    FactsHold P ((x, rhs) :: Γ) (x :: env) (ρ.extend w) := by
  intro y entry i hf hl
  by_cases hxy : (x == y) = true
  · simp only [List.find?_cons, hxy] at hf
    cases hf
    rw [MIR.envLookupT_cons_of_beq hxy env] at hl
    cases hl
    exact ⟨w, 1, by omega, by simp, rfl, by simpa using hw⟩
  · have hxy' : (x == y) = false := by simpa using hxy
    simp only [List.find?_cons, hxy'] at hf
    rw [envLookupT_cons_neq x y env hxy'] at hl
    cases hl' : envLookupT env y with
    | none => rw [hl'] at hl; cases hl
    | some i' =>
      rw [hl'] at hl; simp at hl; subst hl
      obtain ⟨v, k, hik, hk, hv, hp⟩ := h y entry i' hf hl'
      exact ⟨v, k + 1, by omega, by simp; omega, hv, by simpa using hp⟩

/-- A new binder without a fact. -/
theorem FactsHold.extend {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {x : VarId} (w : CekValue)
    (h : FactsHold P Γ env ρ) (hx : Γ.find? (fun e => e.1 == x) = none) :
    FactsHold P Γ (x :: env) (ρ.extend w) := by
  intro y entry i hf hl
  by_cases hxy : (x == y) = true
  · have : Γ.find? (fun e => e.1 == x) = Γ.find? (fun e => e.1 == y) := by
      congr 1; funext e
      have h1 := (VarId.beq_true_iff x y).mp hxy
      show (e.1.origin == x.origin && e.1.uid == x.uid) = (e.1.origin == y.origin && e.1.uid == y.uid)
      rw [h1.1, h1.2]
    rw [this, hf] at hx; cases hx
  · have hxy' : (x == y) = false := by simpa using hxy
    rw [envLookupT_cons_neq x y env hxy'] at hl
    cases hl' : envLookupT env y with
    | none => rw [hl'] at hl; cases hl
    | some i' =>
      rw [hl'] at hl; simp at hl; subst hl
      obtain ⟨v, k, hik, hk, hv, hp⟩ := h y entry i' hf hl'
      exact ⟨v, k + 1, by omega, by simp; omega, hv, by simpa using hp⟩

/-- Facts survive moving to an older suffix of a distinct environment. -/
theorem FactsHold.drop {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    (h : FactsHold P Γ env ρ) (hd : EnvDistinct env) (j : Nat) :
    FactsHold P Γ (env.drop j) (dropEnv j ρ) := by
  intro y entry i hf hl
  have hl' := hd.drop_lookup j hl
  obtain ⟨v, k, hik, hk, hv, hp⟩ := h y entry (i + j) hf hl'
  refine ⟨v, k - j, by omega, by simp; omega, ?_, ?_⟩
  · rw [dropEnv_lookup j ρ _ (by omega), show i + 1 + j = i + j + 1 by omega]; exact hv
  · rw [List.drop_drop, dropEnv_add, show j + (k - j) = k by omega]; exact hp

theorem find?_filter_key (keep : VarId → Bool) (congr : ∀ x y, (x == y) = true → keep x = keep y)
    (y : VarId) : ∀ (Γ : List (VarId × Expr)) {entry : VarId × Expr},
      (Γ.filter fun e => keep e.1).find? (fun e => e.1 == y) = some entry →
      Γ.find? (fun e => e.1 == y) = some entry
  | [], _, h => by simp at h
  | (x, r) :: Γ, entry, h => by
    by_cases hk : keep x = true
    · rw [List.filter_cons_of_pos (by simpa using hk)] at h
      simp only [List.find?_cons] at h ⊢
      split
      · rename_i hxy; simp only [hxy] at h; exact h
      · rename_i hxy; simp only [hxy] at h; exact find?_filter_key keep congr y Γ h
    · rw [List.filter_cons_of_neg (by simpa using hk)] at h
      have rest := find?_filter_key keep congr y Γ h
      simp only [List.find?_cons]
      split
      · rename_i hxy
        exfalso
        have hy : keep y = false := by rw [← congr x y hxy]; simpa using hk
        have found := List.find?_some h
        have mem := List.mem_of_find?_eq_some h
        rw [List.mem_filter] at mem
        have := congr _ _ found
        rw [mem.2, hy] at this
        cases this
      · exact rest

/-- Removing every fact about some binders. -/
theorem FactsHold.filter {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv}
    (h : FactsHold P Γ env ρ) (keep : VarId → Bool)
    (congr : ∀ x y, (x == y) = true → keep x = keep y) :
    FactsHold P (Γ.filter fun e => keep e.1) env ρ := by
  intro y entry i hf hl
  exact h y entry i (find?_filter_key keep congr y Γ hf) hl

/-- A Boolean fact for a binder whose value is the given Boolean. -/
theorem FactsHold.push_bool {P : List VarId → CekEnv → Expr → CekValue → Prop}
    {Γ : List (VarId × Expr)} {env : List VarId} {ρ : CekEnv} {b : VarId} {value : Bool}
    (h : FactsHold P Γ env ρ)
    (hb : ∀ i, envLookupT env b = some i → ρ.lookup (i + 1) = some (.VCon (.Bool value)))
    (hP : ∀ env ρ, P env ρ (.Lit (.Bool value, .AtomicType .TypeBool)) (.VCon (.Bool value))) :
    FactsHold P ((b, .Lit (.Bool value, .AtomicType .TypeBool)) :: Γ) env ρ := by
  intro y entry i hf hl
  by_cases hby : (b == y) = true
  · simp only [List.find?_cons, hby] at hf
    cases hf
    rw [← envLookupT_congr hby env] at hl
    have hi := envLookupT_bound env b i hl
    exact ⟨_, i + 1, by omega, by omega, hb i hl, hP _ _⟩
  · have hby' : (b == y) = false := by simpa using hby
    simp only [List.find?_cons, hby'] at hf
    exact h y entry i hf hl

end Moist.Verified.ShapeFacts
