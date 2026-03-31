import Moist.Verified.Semantics
import Moist.MIR.LowerTotal

/-! # Transitivity of Behavioral Equivalence and Refinement

This module proves that `ValueEq`, `BehEqClosed`, `BehEq`, and `Refines`
are all transitive. These are factored out from `DeadLet.lean` so they
can be reused by other optimization proofs without pulling in the full
dead-let machinery.
-/

namespace Moist.Verified.Trans

open Moist.CEK
open Moist.Plutus.Term
open Moist.MIR
open Moist.Verified.Semantics

/-! ## ValueEq / ListValueEq transitivity -/

mutual
  /-- `ValueEq` is transitive at every step index. -/
  theorem valueEq_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      ValueEq k v₁ v₂ → ValueEq k v₂ v₃ → ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    -- Matching constructors
    | _ + 1, .VCon _, .VCon _, .VCon _, h12, h23 => by
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam _ _, .VLam _ _, .VLam _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢; intro arg
      have ⟨hh12, hv12⟩ := h12 arg; have ⟨hh23, hv23⟩ := h23 arg
      refine ⟨hh12.trans hh23, fun w₁ w₃ hw₁ hw₃ => ?_⟩
      obtain ⟨_, hw₂⟩ := hh12.mp ⟨_, hw₁⟩
      exact valueEq_trans k _ _ _ (hv12 _ _ hw₁ hw₂) (hv23 _ _ hw₂ hw₃)
    | k + 1, .VDelay _ _, .VDelay _ _, .VDelay _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      refine ⟨h12.1.trans h23.1, fun w₁ w₃ hw₁ hw₃ => ?_⟩
      obtain ⟨_, hw₂⟩ := h12.1.mp ⟨_, hw₁⟩
      exact valueEq_trans k _ _ _ (h12.2 _ _ hw₁ hw₂) (h23.2 _ _ hw₂ hw₃)
    | _ + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans _ _ _ _ h12.2 h23.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans k _ _ _ h12.2.1 h23.2.1, h12.2.2.trans h23.2.2⟩
    -- h12 is False (v₁ and v₂ have different constructors)
    | _ + 1, .VCon _, .VLam _ _, _, h, _ | _ + 1, .VCon _, .VDelay _ _, _, h, _
    | _ + 1, .VCon _, .VConstr _ _, _, h, _ | _ + 1, .VCon _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VLam _ _, .VCon _, _, h, _ | _ + 1, .VLam _ _, .VDelay _ _, _, h, _
    | _ + 1, .VLam _ _, .VConstr _ _, _, h, _ | _ + 1, .VLam _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VDelay _ _, .VCon _, _, h, _ | _ + 1, .VDelay _ _, .VLam _ _, _, h, _
    | _ + 1, .VDelay _ _, .VConstr _ _, _, h, _ | _ + 1, .VDelay _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VConstr _ _, .VCon _, _, h, _ | _ + 1, .VConstr _ _, .VLam _ _, _, h, _
    | _ + 1, .VConstr _ _, .VDelay _ _, _, h, _ | _ + 1, .VConstr _ _, .VBuiltin _ _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VCon _, _, h, _ | _ + 1, .VBuiltin _ _ _, .VLam _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, _, h, _
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, _, h, _ => by simp [ValueEq] at h
    -- h23 is False (v₂ and v₃ have different constructors, v₁ matches v₂)
    | _ + 1, .VCon _, .VCon _, .VLam _ _, _, h | _ + 1, .VCon _, .VCon _, .VDelay _ _, _, h
    | _ + 1, .VCon _, .VCon _, .VConstr _ _, _, h | _ + 1, .VCon _, .VCon _, .VBuiltin _ _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VCon _, _, h | _ + 1, .VLam _ _, .VLam _ _, .VDelay _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VConstr _ _, _, h
    | _ + 1, .VLam _ _, .VLam _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VCon _, _, h | _ + 1, .VDelay _ _, .VDelay _ _, .VLam _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VConstr _ _, _, h
    | _ + 1, .VDelay _ _, .VDelay _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VCon _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VLam _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VDelay _ _, _, h
    | _ + 1, .VConstr _ _, .VConstr _ _, .VBuiltin _ _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VCon _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VLam _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VDelay _ _, _, h
    | _ + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VConstr _ _, _, h => by simp [ValueEq] at h
  /-- `ListValueEq` is transitive at every step index. -/
  theorem listValueEq_trans : ∀ (k : Nat) (vs₁ vs₂ vs₃ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₃ → ListValueEq k vs₁ vs₃
    | _, [], [], [], _, _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, _ :: _, h12, h23 => by
      simp only [ListValueEq] at h12 h23 ⊢
      exact ⟨valueEq_trans k _ _ _ h12.1 h23.1, listValueEq_trans k _ _ _ h12.2 h23.2⟩
    | _, [], _ :: _, _, h, _ | _, _ :: _, [], _, h, _ => by simp [ListValueEq] at h
    | _, [], [], _ :: _, _, h => by simp [ListValueEq] at h
    | _, _ :: _, _ :: _, [], _, h => by simp [ListValueEq] at h
end

/-! ## BehEqClosed transitivity -/

/-- Extract the content of `BehEqClosed` when both sides lower successfully. -/
private theorem behEqClosed_extract {m1 m2 : Expr} {t1 t2 : Term}
    (h1 : lowerTotal [] m1 = some t1) (h2 : lowerTotal [] m2 = some t2)
    (h : BehEqClosed m1 m2) :
    (Reaches (.compute [] .nil t1) .error ↔ Reaches (.compute [] .nil t2) .error) ∧
    (Halts (.compute [] .nil t1) ↔ Halts (.compute [] .nil t2)) ∧
    ∀ (k : Nat) (v1 v2 : CekValue),
      Reaches (.compute [] .nil t1) (.halt v1) →
      Reaches (.compute [] .nil t2) (.halt v2) →
      ValueEq k v1 v2 := by
  unfold BehEqClosed at h; rw [h1, h2] at h; exact h

/-- **Transitivity of closed behavioral equivalence.** -/
theorem behEqClosed_trans {a b c : Expr}
    {tb : Term} (hb : lowerTotal [] b = some tb)
    (h12 : a ≋ᶜ b) (h23 : b ≋ᶜ c) : a ≋ᶜ c := by
  unfold BehEqClosed
  cases ha : lowerTotal [] a with
  | none => split <;> trivial
  | some ta =>
    cases hc : lowerTotal [] c with
    | none => split <;> trivial
    | some tc =>
      simp only [ha, hc]
      have ⟨herr12, hh12, hv12⟩ := behEqClosed_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEqClosed_extract hb (show lowerTotal [] c = some tc from hc) h23
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

/-! ## BehEq transitivity -/

/-- Extract the content of `BehEq` at a specific environment when both sides lower. -/
private theorem behEq_extract {m1 m2 : Expr} {env : List MIR.VarId} {t1 t2 : Term}
    (h1 : lowerTotal env m1 = some t1) (h2 : lowerTotal env m2 = some t2)
    (h : BehEq m1 m2) :
    (∀ ρ : CekEnv, Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
    (∀ ρ : CekEnv, Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
    ∀ (k : Nat) (ρ : CekEnv) (v1 v2 : CekValue),
      Reaches (.compute [] ρ t1) (.halt v1) →
      Reaches (.compute [] ρ t2) (.halt v2) →
      ValueEq k v1 v2 := by
  have := h env; rw [h1, h2] at this; exact this

/-- **Transitivity of behavioral equivalence for open terms.**
    Requires `b` to lower wherever `a` does, so the chain is informative. -/
theorem behEq_trans {a b c : Expr}
    (hlb : ∀ env, (lowerTotal env a).isSome → (lowerTotal env b).isSome)
    (h12 : a ≋ b) (h23 : b ≋ c) : a ≋ c := by
  unfold BehEq; intro env
  cases ha : lowerTotal env a with
  | none => split <;> trivial
  | some ta =>
    obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp (hlb env (by simp [ha]))
    cases hc : lowerTotal env c with
    | none => split <;> trivial
    | some tc =>
      simp only [ha, hc]
      have ⟨herr12, hh12, hv12⟩ := behEq_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEq_extract hb hc h23
      refine ⟨fun ρ => (herr12 ρ).trans (herr23 ρ),
             fun ρ => (hh12 ρ).trans (hh23 ρ), ?_⟩
      intro k ρ v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := (hh12 ρ).mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k ρ v₁ v₂ hv₁ hv₂) (hv23 k ρ v₂ v₃ hv₂ hv₃)

/-! ## Refines transitivity -/

/-- **Unconditional transitivity of refinement.**
    The compilation clause of `Refines a b` provides the lowering guarantee
    that `behEq_trans` needs, so no extra hypothesis is required. -/
theorem refines_trans {a b c : Expr}
    (h12 : Refines a b) (h23 : Refines b c) : Refines a c :=
  ⟨fun env ha => h23.1 env (h12.1 env ha),
   behEq_trans h12.1 h12.2 h23.2⟩

end Moist.Verified.Trans
