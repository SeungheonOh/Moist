import Moist.Verified.Semantics

/-! # Fundamental Lemma & ValueEq Properties

This file contains `valueEq_refl`, `valueEq_symm`, `valueEq_trans` and
the transitivity lemmas for `BehEqClosed`, `BehEq`, and `Refines`.

It is split out of `Semantics.lean` because `valueEq_refl` for VLam
requires the **fundamental lemma** (environment-variation under bounded
steps), whose proof needs CEK step-simulation infrastructure that cannot
live in `Semantics.lean` without creating import cycles. -/

namespace Moist.Verified.Semantics

open Moist.CEK
open Moist.Plutus.Term (Term Const)
open Moist.MIR (Expr lowerTotalExpr lowerTotalExpr_eq_lowerTotal fixCount)

/-! ## Fundamental Lemma for VLam Reflexivity -/

/-- The "fundamental lemma" of the step-indexed logical relation, parameterized
    by `valueEq_refl` at indices `≤ k`.

    Given the same body and closure env, with `ValueEq k`-related extension args,
    bounded computation agrees on error/halt and produces `ValueEq k` results. -/
theorem fundemental_lemma (k : Nat)
    (veq_refl : ∀ j, j ≤ k → ∀ v : CekValue, ValueEq j v v)
    (body : Term) (env : CekEnv)
    (arg1 arg2 : CekValue) (hargs : ValueEq k arg1 arg2)
    (n : Nat) (hn : n ≤ k) :
    (steps n (.compute [] (env.extend arg1) body) = .error ↔
     steps n (.compute [] (env.extend arg2) body) = .error) ∧
    (∀ v1, steps n (.compute [] (env.extend arg1) body) = .halt v1 →
      ∃ v2, steps n (.compute [] (env.extend arg2) body) = .halt v2 ∧
        ValueEq k v1 v2) ∧
    (∀ v2, steps n (.compute [] (env.extend arg2) body) = .halt v2 →
      ∃ v1, steps n (.compute [] (env.extend arg1) body) = .halt v1 ∧
        ValueEq k v1 v2) := by
  sorry

/-! ## ValueEq properties -/

mutual
  /-- `ValueEq` is reflexive at every step index. -/
  theorem valueEq_refl : ∀ (k : Nat) (v : CekValue), ValueEq k v v
    | 0, _ => by simp [ValueEq]
    | _ + 1, .VCon _ => by simp [ValueEq]
    | k + 1, .VLam body env => by
      unfold ValueEq; intro arg1 arg2 hargs n hn
      exact fundemental_lemma k (fun j hj v => valueEq_refl j v) body env arg1 arg2 hargs n hn
    | k + 1, .VDelay _ _ => by
      unfold ValueEq; intro n hn
      exact ⟨Iff.rfl, fun v₁ hv₁ => ⟨v₁, hv₁, valueEq_refl k v₁⟩,
             fun v₂ hv₂ => ⟨v₂, hv₂, valueEq_refl k v₂⟩⟩
    | _ + 1, .VConstr _ fields => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl _ fields⟩
    | k + 1, .VBuiltin b args ea => by
      unfold ValueEq; exact ⟨rfl, listValueEq_refl k args, rfl, Iff.rfl,
        fun r1 r2 h1 h2 => by rw [h1] at h2; injection h2 with h2; subst h2; exact valueEq_refl k r1⟩
  theorem listValueEq_refl : ∀ (k : Nat) (vs : List CekValue), ListValueEq k vs vs
    | _, [] => by simp [ListValueEq]
    | k, v :: vs => by simp only [ListValueEq]; exact ⟨valueEq_refl k v, listValueEq_refl k vs⟩
  theorem valueEq_symm : ∀ (k : Nat) (v₁ v₂ : CekValue), ValueEq k v₁ v₂ → ValueEq k v₂ v₁
    | 0, _, _, _ => by simp [ValueEq]
    | _ + 1, .VCon _, .VCon _, h => by simp only [ValueEq] at h ⊢; exact h.symm
    | k + 1, .VLam _ _, .VLam _ _, h => by
      unfold ValueEq at h ⊢; intro arg1 arg2 hargs n hn
      have hargs' := valueEq_symm k _ _ hargs
      have ⟨herr, hhalt1, hhalt2⟩ := h arg2 arg1 hargs' n hn
      exact ⟨herr.symm,
             fun v1 hv1 => let ⟨v2, hv2, hve⟩ := hhalt2 v1 hv1; ⟨v2, hv2, valueEq_symm k _ _ hve⟩,
             fun v2 hv2 => let ⟨v1, hv1, hve⟩ := hhalt1 v2 hv2; ⟨v1, hv1, valueEq_symm k _ _ hve⟩⟩
    | k + 1, .VDelay _ _, .VDelay _ _, h => by
      unfold ValueEq at h ⊢; intro n hn
      have ⟨herr, hhalt1, hhalt2⟩ := h n hn
      exact ⟨herr.symm,
             fun v1 hv1 => let ⟨v2, hv2, hve⟩ := hhalt2 v1 hv1; ⟨v2, hv2, valueEq_symm k _ _ hve⟩,
             fun v2 hv2 => let ⟨v1, hv1, hve⟩ := hhalt1 v2 hv2; ⟨v1, hv1, valueEq_symm k _ _ hve⟩⟩
    | _ + 1, .VConstr _ _, .VConstr _ _, h => by
      unfold ValueEq at h ⊢; exact ⟨h.1.symm, listValueEq_symm _ _ _ h.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, h => by
      unfold ValueEq at h ⊢
      exact ⟨h.1.symm, listValueEq_symm k _ _ h.2.1, h.2.2.1.symm, h.2.2.2.1.symm,
             fun r1 r2 h1 h2 => valueEq_symm k _ _ (h.2.2.2.2 r2 r1 h2 h1)⟩
    | _ + 1, .VCon _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VCon _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VLam _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VConstr _ _, h => by simp [ValueEq] at h
    | _ + 1, .VDelay _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VConstr _ _, .VBuiltin _ _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VCon _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VLam _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VDelay _ _, h => by simp [ValueEq] at h
    | _ + 1, .VBuiltin _ _ _, .VConstr _ _, h => by simp [ValueEq] at h
  theorem listValueEq_symm : ∀ (k : Nat) (vs₁ vs₂ : List CekValue),
      ListValueEq k vs₁ vs₂ → ListValueEq k vs₂ vs₁
    | _, [], [], _ => by simp [ListValueEq]
    | k, _ :: _, _ :: _, h => by
      simp only [ListValueEq] at h ⊢
      exact ⟨valueEq_symm k _ _ h.1, listValueEq_symm k _ _ h.2⟩
    | _, [], _ :: _, h => by exact absurd h (by simp [ListValueEq])
    | _, _ :: _, [], h => by exact absurd h (by simp [ListValueEq])
  theorem valueEq_trans : ∀ (k : Nat) (v₁ v₂ v₃ : CekValue),
      ValueEq k v₁ v₂ → ValueEq k v₂ v₃ → ValueEq k v₁ v₃
    | 0, _, _, _, _, _ => by simp [ValueEq]
    -- Matching constructors
    | _ + 1, .VCon _, .VCon _, .VCon _, h12, h23 => by
      simp only [ValueEq] at h12 h23 ⊢; exact h12.trans h23
    | k + 1, .VLam _ _, .VLam _ _, .VLam _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢; intro arg1 arg3 hargs13 n hn
      -- Chain: use arg2 := arg1 for the middle
      have h12' := h12 arg1 arg1 (valueEq_refl k arg1) n hn
      have h23' := h23 arg1 arg3 hargs13 n hn
      refine ⟨h12'.1.trans h23'.1, fun v1 hv1 => ?_, fun v3 hv3 => ?_⟩
      · obtain ⟨v2, hv2, hve12⟩ := h12'.2.1 v1 hv1
        obtain ⟨v3, hv3, hve23⟩ := h23'.2.1 v2 hv2
        exact ⟨v3, hv3, valueEq_trans k _ _ _ hve12 hve23⟩
      · obtain ⟨v2, hv2, hve23⟩ := h23'.2.2 v3 hv3
        obtain ⟨v1, hv1, hve12⟩ := h12'.2.2 v2 hv2
        exact ⟨v1, hv1, valueEq_trans k _ _ _ hve12 hve23⟩
    | k + 1, .VDelay _ _, .VDelay _ _, .VDelay _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢; intro n hn
      have h12' := h12 n hn; have h23' := h23 n hn
      refine ⟨h12'.1.trans h23'.1, fun v1 hv1 => ?_, fun v3 hv3 => ?_⟩
      · obtain ⟨v2, hv2, hve12⟩ := h12'.2.1 v1 hv1
        obtain ⟨v3, hv3, hve23⟩ := h23'.2.1 v2 hv2
        exact ⟨v3, hv3, valueEq_trans k _ _ _ hve12 hve23⟩
      · obtain ⟨v2, hv2, hve23⟩ := h23'.2.2 v3 hv3
        obtain ⟨v1, hv1, hve12⟩ := h12'.2.2 v2 hv2
        exact ⟨v1, hv1, valueEq_trans k _ _ _ hve12 hve23⟩
    | _ + 1, .VConstr _ _, .VConstr _ _, .VConstr _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans _ _ _ _ h12.2 h23.2⟩
    | k + 1, .VBuiltin _ _ _, .VBuiltin _ _ _, .VBuiltin _ _ _, h12, h23 => by
      unfold ValueEq at h12 h23 ⊢
      exact ⟨h12.1.trans h23.1, listValueEq_trans k _ _ _ h12.2.1 h23.2.1,
             h12.2.2.1.trans h23.2.2.1, h12.2.2.2.1.trans h23.2.2.2.1,
             fun r1 r3 hr1 hr3 => by
               rcases h_mid : Moist.CEK.evalBuiltin _ _ with _ | r2
               · exact absurd (h12.2.2.2.1.mpr h_mid ▸ hr1) (by simp)
               · exact valueEq_trans k _ _ _ (h12.2.2.2.2 r1 r2 hr1 h_mid) (h23.2.2.2.2 r2 r3 h_mid hr3)⟩
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

/-! ## Transitivity of behavioral equivalence -/

private abbrev emptyEnv : List MIR.VarId := []

private theorem behEqClosed_extract {m1 m2 : Expr} {t1 t2 : Term}
    (h1 : lowerTotalExpr emptyEnv m1 = some t1)
    (h2 : lowerTotalExpr emptyEnv m2 = some t2)
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
    {tb : Term} (hb : lowerTotalExpr emptyEnv b = some tb)
    (h12 : a ≋ᶜ b) (h23 : b ≋ᶜ c) : a ≋ᶜ c := by
  unfold BehEqClosed
  cases ha : lowerTotalExpr emptyEnv a with
  | none => split <;> trivial
  | some ta =>
    cases hc : lowerTotalExpr emptyEnv c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have ⟨herr12, hh12, hv12⟩ := behEqClosed_extract ha hb h12
      have ⟨herr23, hh23, hv23⟩ := behEqClosed_extract hb hc h23
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

private theorem behEq_extract {m1 m2 : Expr} {env : List MIR.VarId} {t1 t2 : Term}
    (h1 : lowerTotalExpr env m1 = some t1) (h2 : lowerTotalExpr env m2 = some t2)
    (h : BehEq m1 m2) :
    ∀ ρ : CekEnv, WellSizedEnv env.length ρ →
      (Reaches (.compute [] ρ t1) .error ↔ Reaches (.compute [] ρ t2) .error) ∧
      (Halts (.compute [] ρ t1) ↔ Halts (.compute [] ρ t2)) ∧
      ∀ (k : Nat) (v1 v2 : CekValue),
        Reaches (.compute [] ρ t1) (.halt v1) →
        Reaches (.compute [] ρ t2) (.halt v2) →
        ValueEq k v1 v2 := by
  have := h env; rw [h1, h2] at this; exact this

/-- **Transitivity of behavioral equivalence for open terms.** -/
theorem behEq_trans {a b c : Expr}
    (hlb : ∀ env, (lowerTotalExpr env a).isSome → (lowerTotalExpr env b).isSome)
    (h12 : a ≋ b) (h23 : b ≋ c) : a ≋ c := by
  unfold BehEq; intro env
  cases ha : lowerTotalExpr env a with
  | none => split <;> trivial
  | some ta =>
    obtain ⟨tb, hb⟩ := Option.isSome_iff_exists.mp (hlb env (by simp [ha]))
    cases hc : lowerTotalExpr env c with
    | none => split <;> trivial
    | some tc =>
      simp only []
      have h12' := behEq_extract ha hb h12
      have h23' := behEq_extract hb hc h23
      intro ρ hwf
      have ⟨herr12, hh12, hv12⟩ := h12' ρ hwf
      have ⟨herr23, hh23, hv23⟩ := h23' ρ hwf
      refine ⟨herr12.trans herr23, hh12.trans hh23, ?_⟩
      intro k v₁ v₃ hv₁ hv₃
      obtain ⟨v₂, hv₂⟩ := hh12.mp ⟨v₁, hv₁⟩
      exact valueEq_trans k v₁ v₂ v₃ (hv12 k v₁ v₂ hv₁ hv₂) (hv23 k v₂ v₃ hv₂ hv₃)

/-- **Unconditional transitivity of refinement.** -/
theorem refines_trans {a b c : Expr}
    (h12 : Refines a b) (h23 : Refines b c) : Refines a c :=
  ⟨fun env ha => h23.1 env (h12.1 env ha),
   behEq_trans h12.1 h12.2 h23.2⟩

end Moist.Verified.Semantics
