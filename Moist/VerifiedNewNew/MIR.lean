import Moist.VerifiedNewNew.Equivalence
import Moist.VerifiedNewNew.Rename
import Moist.MIR.LowerTotal

/-! # MIR-Level Equivalence and Refinement

Lifts the biorthogonal step-indexed logical relation from UPLC terms
(defined in `Equivalence.lean`) to MIR expressions via `lowerTotalExpr`.

The `WellSizedEnv` guard ensures that all in-scope variables have
bindings, matching the runtime invariant maintained by actual CEK
execution. This enables proving correctness of optimizations that
depend on purity (like dead-let elimination).
-/

namespace Moist.VerifiedNewNew.MIR

open Moist.CEK
open Moist.MIR (Expr VarId lowerTotalExpr)
open Moist.VerifiedNewNew.Equivalence

/-- A CEK environment is well-sized at depth `d` when every variable index
    in `1..d` resolves to a value. -/
def WellSizedEnv (d : Nat) (ρ : CekEnv) : Prop :=
  ∀ n, 0 < n → n ≤ d → ∃ v, ρ.lookup n = some v

theorem wellSizedEnv_nil : WellSizedEnv 0 .nil :=
  fun _ hn hle => absurd (Nat.lt_of_lt_of_le hn hle) (Nat.lt_irrefl 0)

theorem wellSizedEnv_extend {d : Nat} {ρ : CekEnv} (h : WellSizedEnv d ρ) (v : CekValue) :
    WellSizedEnv (d + 1) (ρ.extend v) := by
  intro n hn hle
  match n with
  | 1 => exact ⟨v, rfl⟩
  | n + 2 =>
    have ⟨w, hw⟩ := h (n + 1) (by omega) (by omega)
    exact ⟨w, by simp [CekEnv.extend, CekEnv.lookup, hw]⟩

theorem wellSizedEnv_mono {d d' : Nat} {ρ : CekEnv} (h : WellSizedEnv d ρ) (hle : d' ≤ d) :
    WellSizedEnv d' ρ :=
  fun n hn hn' => h n hn (Nat.le_trans hn' hle)

/-- WellSizedEnv implies the `some` case of EnvEqK (no `none/none` pairs). -/
theorem wellSizedEnv_envEqK_isSome {k d : Nat} {ρ₁ ρ₂ : CekEnv}
    (hw₁ : WellSizedEnv d ρ₁) (hw₂ : WellSizedEnv d ρ₂)
    (henv : EnvEqK k d ρ₁ ρ₂) (n : Nat) (hn : 0 < n) (hnd : n ≤ d) :
    ∃ v₁ v₂, ρ₁.lookup n = some v₁ ∧ ρ₂.lookup n = some v₂ ∧ ValueEqK k v₁ v₂ := by
  obtain ⟨v₁, hv₁⟩ := hw₁ n hn hnd
  obtain ⟨v₂, hv₂⟩ := hw₂ n hn hnd
  have := henv n hn hnd; simp [hv₁, hv₂] at this
  exact ⟨v₁, v₂, hv₁, hv₂, this⟩

--------------------------------------------------------------------------------
-- 1. LIFTING OpenEqK TO MIR (with WellSizedEnv guard)
--------------------------------------------------------------------------------

/-- Two MIR expressions are open-equivalent at step-index `k` and depth `d`
    when, for every variable environment `env` of length `d`, their lowerings
    (if both succeed) are `OpenEqK`-related at level `k` and depth `d`.

    The `OpenEqK` quantifies over all `EnvEqK`-related environments. Since
    `EnvEqK` allows `none/none` pairs, we wrap with a `WellSizedEnv` guard
    to ensure all in-scope variables have bindings (matching the runtime
    invariant of the CEK machine). -/
def MIROpenEqK (k d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ (env : List VarId), env.length = d →
    match lowerTotalExpr env m₁, lowerTotalExpr env m₂ with
    | some t₁, some t₂ =>
      ∀ j ≤ k, ∀ ρ₁ ρ₂, WellSizedEnv d ρ₁ → WellSizedEnv d ρ₂ →
        EnvEqK j d ρ₁ ρ₂ → BehEqK ValueEqK j ρ₁ ρ₂ t₁ t₂
    | _, _ => True

/-- Step-index-free open equivalence: holds at every step index. -/
def MIROpenEq (d : Nat) (m₁ m₂ : Expr) : Prop :=
  ∀ k, MIROpenEqK k d m₁ m₂

/-- Closed equivalence: open equivalence at depth 0. -/
def MIRClosedEq (m₁ m₂ : Expr) : Prop := MIROpenEq 0 m₁ m₂

scoped infix:50 " ≈ᴹ " => MIRClosedEq

--------------------------------------------------------------------------------
-- 2. REFINEMENT
--------------------------------------------------------------------------------

def MIRRefines (m₁ m₂ : Expr) : Prop :=
  (∀ env, (lowerTotalExpr env m₁).isSome → (lowerTotalExpr env m₂).isSome) ∧
  ∀ d, MIROpenEq d m₁ m₂

scoped infix:50 " ⊑ᴹ " => MIRRefines

--------------------------------------------------------------------------------
-- 3. BASIC PROPERTIES
--------------------------------------------------------------------------------

private theorem mirOpenEqK_lower {k d : Nat} {m₁ m₂ : Expr} {env : List VarId}
    {t₁ t₂ : Moist.Plutus.Term.Term}
    (h : MIROpenEqK k d m₁ m₂) (hlen : env.length = d)
    (h₁ : lowerTotalExpr env m₁ = some t₁) (h₂ : lowerTotalExpr env m₂ = some t₂) :
    ∀ j ≤ k, ∀ ρ₁ ρ₂, WellSizedEnv d ρ₁ → WellSizedEnv d ρ₂ →
      EnvEqK j d ρ₁ ρ₂ → BehEqK ValueEqK j ρ₁ ρ₂ t₁ t₂ := by
  have := h env hlen; simp only [h₁, h₂] at this; exact this

theorem mirOpenEqK_mono {j k d : Nat} {m₁ m₂ : Expr}
    (hjk : j ≤ k) (h : MIROpenEqK k d m₁ m₂) : MIROpenEqK j d m₁ m₂ := by
  intro env hlen
  cases h₁ : lowerTotalExpr env m₁ <;> cases h₂ : lowerTotalExpr env m₂ <;>
    simp only [] <;> try trivial
  have := mirOpenEqK_lower h hlen h₁ h₂
  exact fun j' hj' => this j' (by omega)

theorem mirOpenEq_symm {d : Nat} {m₁ m₂ : Expr}
    (h : MIROpenEq d m₁ m₂) : MIROpenEq d m₂ m₁ := by
  intro k env hlen
  cases h₁ : lowerTotalExpr env m₁ <;> cases h₂ : lowerTotalExpr env m₂ <;>
    simp only [] <;> try trivial
  rename_i t₁ t₂
  intro j hj ρ₁ ρ₂ hw₁ hw₂ henv i hi π₁ π₂ hπ
  have h' := mirOpenEqK_lower (h k) hlen h₁ h₂
  exact obsEqK_symm (h' j hj ρ₂ ρ₁ hw₂ hw₁ (envEqK_symm henv) i hi π₂ π₁
    (stackRelK_symm_of (fun k' => valueEqK_symm k') hπ))

theorem mirClosedEq_symm {m₁ m₂ : Expr}
    (h : m₁ ≈ᴹ m₂) : m₂ ≈ᴹ m₁ :=
  mirOpenEq_symm h

theorem mirRefines_refl (m : Expr)
    (hclosed : ∀ env d, env.length = d → ∀ t, lowerTotalExpr env m = some t →
      Moist.VerifiedNewNew.closedAt d t = true) :
    m ⊑ᴹ m :=
  ⟨fun _ h => h, fun d k env hlen => by
    cases h : lowerTotalExpr env m <;> simp only []
    intro j hj ρ₁ ρ₂ _ _ henv
    exact openEq_refl d _ (hclosed env d hlen _ h) j j (Nat.le_refl _) ρ₁ ρ₂ henv⟩

end Moist.VerifiedNewNew.MIR
